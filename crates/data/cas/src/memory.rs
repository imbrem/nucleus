//! A bounded, in-memory content-addressed store.

use std::ops::Range;
use std::sync::RwLock;

use bytes::Bytes;
use covalence_lib_error::snafu::{self, Snafu};
use covalence_lib_hash::O256;
use covalence_logic_cas::{CasFact, TrustedCas};
use hashbrown::HashTable;

use crate::{Cas, CasObject};

/// Default largest object this store will admit.
pub const MAX_OBJECT_BYTES: u64 = 64 * 1024 * 1024;

/// Refusal to admit bytes into a [`MemoryCas`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("object of {len} bytes exceeds the {limit} byte admission limit"))]
pub struct AdmissionError {
    /// Length of the rejected candidate.
    pub len: u64,
    /// Largest length this store admits.
    pub limit: u64,
}

/// Failure to select one checked fact from a [`MemoryCas`].
///
/// Absence and a genuine hash collision are deliberately distinct. A
/// colliding address retains both facts as witnesses instead of selecting one
/// blob arbitrarily.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum MemoryCasError {
    /// No fact in the store carries the requested address.
    #[snafu(display("CAS object {address} is not resident"))]
    Missing {
        /// Requested address.
        address: O256,
    },
    /// At least two distinct complete blobs carry the requested address.
    #[snafu(display("CAS address {address} has distinct checked collision witnesses"))]
    Collision {
        /// Colliding address.
        address: O256,
        /// One checked collision witness.
        first: Box<CasFact>,
        /// A distinct checked collision witness.
        second: Box<CasFact>,
    },
}

/// A range request which does not lie inside the addressed object.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("range {start}..{end} lies outside an object of {len} bytes"))]
pub struct InvalidRange {
    /// Requested inclusive start offset.
    pub start: u64,
    /// Requested exclusive end offset.
    pub end: u64,
    /// Actual length of the addressed object.
    pub len: u64,
}

/// Resident object counts and sizes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CasStats {
    /// Number of distinct checked hash/blob pairs currently resident.
    pub objects: u64,
    /// Sum of the lengths of every resident object.
    pub bytes: u64,
    /// Length of the largest resident object.
    pub largest: u64,
}

/// A whole-object, in-memory [`Cas`] whose trusted contents are [`CasFact`]s.
///
/// Facts live in one insertion-ordered [`Vec`]. The address index uses
/// [`HashTable`], hashbrown's safe public wrapper around its private
/// `RawTable`. This retains the requested raw-table-plus-vector layout without
/// pinning an obsolete hashbrown release merely to reach its unsafe internals.
///
/// The index maps one address to every fact with that address. Exact duplicate
/// insertion is idempotent, while distinct collision witnesses are both
/// retained. [`TrustedCas::get`] reports such an address as ambiguous.
pub struct MemoryCas {
    objects: RwLock<Objects>,
    limit: u64,
}

#[derive(Debug)]
struct AddressEntry {
    address: O256,
    indices: Vec<usize>,
}

#[derive(Debug, Default)]
struct Objects {
    facts: Vec<CasFact>,
    index: HashTable<AddressEntry>,
}

impl Objects {
    fn entry(&self, address: O256) -> Option<&AddressEntry> {
        self.index
            .find(address_hash(address), |entry| entry.address == address)
    }

    fn facts_at(&self, address: O256) -> impl Iterator<Item = &CasFact> {
        self.entry(address)
            .into_iter()
            .flat_map(|entry| entry.indices.iter())
            .map(|&index| &self.facts[index])
    }

    fn insert(&mut self, fact: CasFact) -> bool {
        let address = fact.hash();
        if self.facts_at(address).any(|resident| resident == &fact) {
            return false;
        }

        let fact_index = self.facts.len();
        self.facts.push(fact);
        let hash = address_hash(address);
        if let Some(entry) = self.index.find_mut(hash, |entry| entry.address == address) {
            entry.indices.push(fact_index);
        } else {
            self.index.insert_unique(
                hash,
                AddressEntry {
                    address,
                    indices: vec![fact_index],
                },
                |entry| address_hash(entry.address),
            );
        }
        true
    }

    fn remove(&mut self, address: O256) -> bool {
        let before = self.facts.len();
        self.facts.retain(|fact| fact.hash() != address);
        if self.facts.len() == before {
            return false;
        }
        self.rebuild_index();
        true
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        for (index, fact) in self.facts.iter().enumerate() {
            let address = fact.hash();
            let hash = address_hash(address);
            if let Some(entry) = self.index.find_mut(hash, |entry| entry.address == address) {
                entry.indices.push(index);
            } else {
                self.index.insert_unique(
                    hash,
                    AddressEntry {
                        address,
                        indices: vec![index],
                    },
                    |entry| address_hash(entry.address),
                );
            }
        }
    }
}

/// Uses 64 already-uniform bits of the content address as the table hash.
fn address_hash(address: O256) -> u64 {
    let bytes = address.as_bytes();
    u64::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
    ])
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
            objects: RwLock::new(Objects::default()),
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
        let fact = CasFact::from_bytes(bytes);
        let address = fact.hash();
        self.objects_mut().insert(fact);
        Ok(address)
    }

    /// Admits an already checked whole-object fact.
    ///
    /// Returns `true` when this exact hash/blob pair was new. A repeated pair
    /// is an idempotent no-op. A distinct fact with the same address is kept as
    /// a collision witness rather than replacing the resident fact.
    ///
    /// # Errors
    ///
    /// Returns [`AdmissionError`] when the fact exceeds [`Self::limit`].
    pub fn insert_fact(&self, fact: CasFact) -> Result<bool, AdmissionError> {
        let len = fact.bytes().len() as u64;
        if len > self.limit {
            return Err(AdmissionError {
                len,
                limit: self.limit,
            });
        }
        Ok(self.objects_mut().insert(fact))
    }

    /// Drops every fact carrying `address` from the relation and index.
    ///
    /// Returns whether the address was present beforehand. Bytes already
    /// handed out stay valid; only future resolutions are affected.
    pub fn remove(&self, address: O256) -> bool {
        self.objects_mut().remove(address)
    }

    /// Returns whether at least one resident fact carries `address`.
    #[must_use]
    pub fn contains(&self, address: O256) -> bool {
        self.objects().entry(address).is_some()
    }

    /// Returns the complete bytes for `address`, if it resolves.
    #[must_use]
    pub fn get(&self, address: O256) -> Option<Bytes> {
        self.get_fact(address).ok().map(|fact| fact.bytes().clone())
    }

    /// Gets the unique checked fact carrying `address`.
    ///
    /// # Errors
    ///
    /// Returns [`MemoryCasError::Missing`] when no fact carries `address`, or
    /// [`MemoryCasError::Collision`] with two witnesses when distinct facts
    /// carry it.
    pub fn get_fact(&self, address: O256) -> Result<CasFact, MemoryCasError> {
        let objects = self.objects();
        let mut facts = objects.facts_at(address);
        let Some(first) = facts.next() else {
            return Err(MemoryCasError::Missing { address });
        };
        let Some(second) = facts.next() else {
            return Ok(first.clone());
        };
        Err(MemoryCasError::Collision {
            address,
            first: Box::new(first.clone()),
            second: Box::new(second.clone()),
        })
    }

    /// Returns every resident checked pair in insertion order.
    ///
    /// Colliding pairs remain distinct, while exact duplicate insertion does
    /// not add a second entry.
    #[must_use]
    pub fn facts(&self) -> Vec<CasFact> {
        self.objects().facts.clone()
    }

    /// Returns every address carried by at least one resident fact.
    #[must_use]
    pub fn addresses(&self) -> Vec<O256> {
        self.objects()
            .index
            .iter()
            .map(|entry| entry.address)
            .collect()
    }

    /// Summarises what this store currently holds.
    #[must_use]
    pub fn stats(&self) -> CasStats {
        let objects = self.objects();
        let mut stats = CasStats {
            objects: objects.facts.len() as u64,
            ..CasStats::default()
        };
        for fact in &objects.facts {
            let len = fact.bytes().len() as u64;
            stats.bytes += len;
            stats.largest = stats.largest.max(len);
        }
        stats
    }

    fn objects(&self) -> std::sync::RwLockReadGuard<'_, Objects> {
        self.objects
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn objects_mut(&self) -> std::sync::RwLockWriteGuard<'_, Objects> {
        self.objects
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

/// An object pinned independently of its [`MemoryCas`].
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
        // Resident lengths fit `usize`.
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

impl TrustedCas for MemoryCas {
    type Error = MemoryCasError;

    fn get(&self, address: O256) -> Result<CasFact, Self::Error> {
        self.get_fact(address)
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
    fn checked_fact_admission_is_relation_membership() {
        let cas = MemoryCas::new();
        let fact = CasFact::from_bytes(Bytes::from_static(b"checked"));

        assert!(cas.insert_fact(fact.clone()).unwrap());
        assert!(!cas.insert_fact(fact.clone()).unwrap());
        assert_eq!(cas.facts(), vec![fact.clone()]);
        assert_eq!(
            covalence_logic_cas::get_exact(&cas, fact.hash()).unwrap(),
            fact
        );
    }

    #[test]
    fn checked_lookup_distinguishes_absence() {
        let cas = MemoryCas::new();
        let address = O256::from_bytes(b"absent");

        assert_eq!(
            cas.get_fact(address).unwrap_err(),
            MemoryCasError::Missing { address }
        );
        assert!(matches!(
            covalence_logic_cas::get_exact(&cas, address),
            Err(covalence_logic_cas::GetError::Provider {
                source: MemoryCasError::Missing { address: missing },
                ..
            }) if missing == address
        ));
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

        assert_eq!(object.len(), 11);
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
        assert_eq!(object.read(6..11).unwrap(), Bytes::from_static(b"world"));

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
