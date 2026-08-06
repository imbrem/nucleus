//! A resident, insert-only content-addressed store.
//!
//! [`MemoryCas`] is the simplest possible [`Cas`]: every object is held whole
//! in memory, admitted by hashing complete bytes. It exists so that the rest
//! of the stack can be built against content addresses from the start, before
//! any ranged, streaming, or remote backend exists.
//!
//! Admission is bounded. Callers hand this store untrusted bytes, so an object
//! larger than the configured limit is rejected rather than allocated.
//!
//! Removal is deliberately safe rather than absent. Dropping an address from
//! the index cannot invalidate bytes another holder is already reading: every
//! handout is a cheap [`Bytes`] clone, so an object stays alive for exactly as
//! long as someone holds it. The observable effect of a removal is that
//! *future* resolutions of that address fail.

use std::collections::HashMap;
use std::ops::Range;
use std::sync::RwLock;

use bytes::Bytes;
use covalence_lib_hash::O256;

use crate::{Cas, CasObject};

/// Default largest object this store will admit.
pub const MAX_OBJECT_BYTES: u64 = 64 * 1024 * 1024;

/// Refusal to admit bytes into a [`MemoryCas`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdmissionError {
    /// Length of the rejected candidate.
    pub len: u64,
    /// Largest length this store admits.
    pub limit: u64,
}

impl std::fmt::Display for AdmissionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "object of {} bytes exceeds the {} byte admission limit",
            self.len, self.limit
        )
    }
}

impl std::error::Error for AdmissionError {}

/// A range request which does not lie inside the addressed object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidRange {
    /// Requested inclusive start offset.
    pub start: u64,
    /// Requested exclusive end offset.
    pub end: u64,
    /// Actual length of the addressed object.
    pub len: u64,
}

impl std::fmt::Display for InvalidRange {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "range {}..{} lies outside an object of {} bytes",
            self.start, self.end, self.len
        )
    }
}

impl std::error::Error for InvalidRange {}

/// Resident object counts and sizes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CasStats {
    /// Number of distinct addresses currently resolvable.
    pub objects: u64,
    /// Sum of the lengths of every resident object.
    pub bytes: u64,
    /// Length of the largest resident object.
    pub largest: u64,
}

/// A whole-object, in-memory [`Cas`].
#[derive(Debug)]
pub struct MemoryCas {
    objects: RwLock<HashMap<O256, Bytes>>,
    limit: u64,
}

impl Default for MemoryCas {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryCas {
    /// Creates an empty store admitting objects up to [`MAX_OBJECT_BYTES`].
    #[must_use]
    pub fn new() -> Self {
        Self::with_limit(MAX_OBJECT_BYTES)
    }

    /// Creates an empty store admitting objects up to `limit` bytes.
    #[must_use]
    pub fn with_limit(limit: u64) -> Self {
        Self {
            objects: RwLock::new(HashMap::new()),
            limit,
        }
    }

    /// Returns the largest object length this store admits.
    #[must_use]
    pub const fn limit(&self) -> u64 {
        self.limit
    }

    /// Hashes and admits complete bytes, returning their address.
    ///
    /// Re-inserting an object already present is a no-op which returns the
    /// same address; the store is content-addressed, so the bytes cannot
    /// differ.
    ///
    /// # Errors
    ///
    /// Returns [`AdmissionError`] when the candidate exceeds [`Self::limit`].
    pub fn insert(&self, bytes: impl Into<Bytes>) -> Result<O256, AdmissionError> {
        let bytes = bytes.into();
        let len = bytes.len() as u64;
        if len > self.limit {
            return Err(AdmissionError {
                len,
                limit: self.limit,
            });
        }
        let address = O256::from_bytes(&bytes);
        self.objects_mut().entry(address).or_insert(bytes);
        Ok(address)
    }

    /// Drops `address` from the index.
    ///
    /// Returns whether the address was resolvable beforehand. Bytes already
    /// handed out stay valid; only future resolutions are affected.
    pub fn remove(&self, address: O256) -> bool {
        self.objects_mut().remove(&address).is_some()
    }

    /// Returns whether `address` currently resolves.
    #[must_use]
    pub fn contains(&self, address: O256) -> bool {
        self.objects().contains_key(&address)
    }

    /// Returns the complete bytes for `address`, if it resolves.
    #[must_use]
    pub fn get(&self, address: O256) -> Option<Bytes> {
        self.objects().get(&address).cloned()
    }

    /// Returns every resolvable address.
    #[must_use]
    pub fn addresses(&self) -> Vec<O256> {
        self.objects().keys().copied().collect()
    }

    /// Summarises what this store currently holds.
    #[must_use]
    pub fn stats(&self) -> CasStats {
        let objects = self.objects();
        let mut stats = CasStats {
            objects: objects.len() as u64,
            ..CasStats::default()
        };
        for bytes in objects.values() {
            let len = bytes.len() as u64;
            stats.bytes += len;
            stats.largest = stats.largest.max(len);
        }
        stats
    }

    fn objects(&self) -> std::sync::RwLockReadGuard<'_, HashMap<O256, Bytes>> {
        self.objects
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn objects_mut(&self) -> std::sync::RwLockWriteGuard<'_, HashMap<O256, Bytes>> {
        self.objects
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

/// An object opened from a [`MemoryCas`].
///
/// Holds its own bytes, so it is entirely independent of the store it came
/// from: removing the address, or dropping the store, leaves it readable.
#[derive(Clone, Debug)]
pub struct ResidentObject(Bytes);

impl ResidentObject {
    /// Borrows the complete bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &Bytes {
        &self.0
    }
}

impl CasObject for ResidentObject {
    type Error = InvalidRange;

    fn len(&self) -> u64 {
        self.0.len() as u64
    }

    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
        let len = self.len();
        if range.start > range.end || range.end > len {
            return Err(InvalidRange {
                start: range.start,
                end: range.end,
                len,
            });
        }
        // Both bounds are `<= len`, which fits `usize` because the object is
        // resident.
        let start = usize::try_from(range.start).unwrap_or(usize::MAX);
        let end = usize::try_from(range.end).unwrap_or(usize::MAX);
        Ok(self.0.slice(start..end))
    }
}

impl Cas for MemoryCas {
    type Error = InvalidRange;
    type Object = ResidentObject;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        Ok(self.get(address).map(ResidentObject))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_addresses_by_content() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        assert_eq!(address, O256::from_bytes(b"hello"));
        assert!(cas.contains(address));
        assert_eq!(cas.len(address).unwrap(), Some(5));
    }

    #[test]
    fn reinsertion_is_idempotent() {
        let cas = MemoryCas::new();
        let first = cas.insert(&b"hello"[..]).unwrap();
        let second = cas.insert(&b"hello"[..]).unwrap();
        assert_eq!(first, second);
        assert_eq!(cas.stats().objects, 1);
    }

    #[test]
    fn distinct_content_gets_distinct_addresses() {
        let cas = MemoryCas::new();
        let first = cas.insert(&b"hello"[..]).unwrap();
        let second = cas.insert(&b"world"[..]).unwrap();
        assert_ne!(first, second);
        assert_eq!(cas.stats().objects, 2);
    }

    #[test]
    fn admission_is_bounded() {
        let cas = MemoryCas::with_limit(4);
        assert_eq!(
            cas.insert(&b"hello"[..]).unwrap_err(),
            AdmissionError { len: 5, limit: 4 }
        );
        assert_eq!(cas.stats(), CasStats::default());
        cas.insert(&b"four"[..]).unwrap();
        assert_eq!(cas.stats().objects, 1);
    }

    #[test]
    fn rejected_admission_leaves_no_entry() {
        let cas = MemoryCas::with_limit(4);
        let address = O256::from_bytes(b"hello");
        assert!(cas.insert(&b"hello"[..]).is_err());
        assert!(!cas.contains(address));
        assert_eq!(cas.len(address).unwrap(), None);
    }

    #[test]
    fn absent_addresses_resolve_to_none() {
        let cas = MemoryCas::new();
        let address = O256::from_bytes(b"absent");
        assert_eq!(cas.len(address).unwrap(), None);
        assert_eq!(cas.read(address, 0..0).unwrap(), None);
    }

    #[test]
    fn reads_exact_ranges() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello world"[..]).unwrap();
        assert_eq!(
            cas.read(address, 0..5).unwrap().unwrap(),
            Bytes::from_static(b"hello")
        );
        assert_eq!(
            cas.read(address, 6..11).unwrap().unwrap(),
            Bytes::from_static(b"world")
        );
        assert_eq!(
            cas.read(address, 11..11).unwrap().unwrap(),
            Bytes::from_static(b"")
        );
    }

    #[test]
    fn reads_past_the_end_are_rejected() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        assert_eq!(
            cas.read(address, 0..6).unwrap_err(),
            InvalidRange {
                start: 0,
                end: 6,
                len: 5
            }
        );
    }

    #[test]
    fn reversed_ranges_are_rejected() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let reversed = Range { start: 4, end: 1 };
        assert_eq!(
            cas.read(address, reversed).unwrap_err(),
            InvalidRange {
                start: 4,
                end: 1,
                len: 5
            }
        );
    }

    #[test]
    fn an_opened_object_survives_removal() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello world"[..]).unwrap();
        let object = cas.open(address).unwrap().unwrap();

        assert!(cas.remove(address));
        assert!(!cas.remove(address));

        // This is the guarantee: while you hold it, it reads. Removal is not
        // observable through an object already handed out.
        assert_eq!(object.len(), 11);
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
        assert_eq!(object.read(6..11).unwrap(), Bytes::from_static(b"world"));

        // Only resolution through the store is affected.
        assert!(!cas.contains(address));
        assert_eq!(cas.len(address).unwrap(), None);
        assert!(cas.open(address).unwrap().is_none());
        assert_eq!(cas.stats(), CasStats::default());
    }

    #[test]
    fn an_opened_object_outlives_the_store() {
        let object = {
            let cas = MemoryCas::new();
            let address = cas.insert(&b"hello"[..]).unwrap();
            cas.open(address).unwrap().unwrap()
        };
        // The store is gone entirely; the object is still an object.
        assert_eq!(object.len(), 5);
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
    }

    #[test]
    fn an_empty_object_is_not_an_absent_one() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b""[..]).unwrap();
        let object = cas.open(address).unwrap().expect("empty objects resolve");
        assert!(object.is_empty());
        assert_eq!(object.len(), 0);

        assert!(cas.remove(address));
        assert!(cas.open(address).unwrap().is_none());
    }

    #[test]
    fn removed_content_can_be_readmitted() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        assert!(cas.remove(address));
        assert_eq!(cas.insert(&b"hello"[..]).unwrap(), address);
        assert!(cas.contains(address));
    }

    #[test]
    fn stats_summarise_resident_objects() {
        let cas = MemoryCas::new();
        assert_eq!(cas.stats(), CasStats::default());
        cas.insert(&b"hello"[..]).unwrap();
        cas.insert(&b"hello world"[..]).unwrap();
        assert_eq!(
            cas.stats(),
            CasStats {
                objects: 2,
                bytes: 16,
                largest: 11,
            }
        );
    }

    #[test]
    fn addresses_lists_every_resident_object() {
        let cas = MemoryCas::new();
        let first = cas.insert(&b"hello"[..]).unwrap();
        let second = cas.insert(&b"world"[..]).unwrap();
        let mut addresses = cas.addresses();
        addresses.sort_unstable_by_key(|address| *address.as_bytes());
        let mut expected = vec![first, second];
        expected.sort_unstable_by_key(|address| *address.as_bytes());
        assert_eq!(addresses, expected);
    }

    #[test]
    fn empty_objects_are_admissible() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b""[..]).unwrap();
        assert_eq!(cas.len(address).unwrap(), Some(0));
        assert_eq!(
            cas.read(address, 0..0).unwrap().unwrap(),
            Bytes::from_static(b"")
        );
    }
}
