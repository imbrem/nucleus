use std::{convert::Infallible, ops::Range, sync::RwLock};

use bytes::Bytes;
use covalence_lib_error::snafu::{self, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_table::HashTable;
use covalence_logic_cas::{Cas, CasFact, CasLookupError, CasMut, CasObject, CasShared};

use crate::CasStatistics;

/// Refusal to admit bytes into a bounded [`SharedIndexCas`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("object of {len} bytes exceeds the {limit} byte admission limit"))]
pub struct AdmissionError {
    /// Length of the rejected candidate.
    pub len: u64,
    /// Largest length this store admits.
    pub limit: u64,
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

/// A compact insertion-ordered index of checked CAS facts.
///
/// Integer IDs are stable: removal leaves a vacant slot rather than changing
/// another fact's ID. The address table stores at most one ID per address. A
/// hypothetical hash collision therefore resolves to the fact inserted first,
/// without adding collision checks to normal operation.
#[derive(Debug, Default)]
pub struct IndexCas {
    facts: Vec<Option<CasFact>>,
    addresses: HashTable<u64>,
    count: usize,
}

impl IndexCas {
    /// Creates an empty index.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            facts: Vec::new(),
            addresses: HashTable::new(),
            count: 0,
        }
    }

    /// Returns the number of resident facts.
    #[must_use]
    pub const fn fact_count(&self) -> usize {
        self.count
    }

    /// Returns whether the index contains no facts.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Returns the stable ID for `address`, if resident.
    #[must_use]
    pub fn id(&self, address: O256) -> Option<u64> {
        self.addresses
            .find(address.addr64(), |&id| {
                self.fact(id).is_some_and(|fact| fact.hash() == address)
            })
            .copied()
    }

    /// Hashes `bytes` and returns the stable ID of the resulting address.
    #[must_use]
    pub fn id_bytes(&self, bytes: impl AsRef<[u8]>) -> Option<u64> {
        self.id(O256::from_bytes(bytes))
    }

    /// Returns the fact at a stable integer ID.
    #[must_use]
    pub fn fact(&self, id: u64) -> Option<&CasFact> {
        usize::try_from(id)
            .ok()
            .and_then(|index| self.facts.get(index))
            .and_then(Option::as_ref)
    }

    /// Returns the fact carrying `address`, if resident.
    #[must_use]
    pub fn fact_at(&self, address: O256) -> Option<&CasFact> {
        self.id(address).and_then(|id| self.fact(id))
    }

    /// Iterates over `(id, fact)` pairs in insertion order.
    pub fn facts(&self) -> impl Iterator<Item = (u64, &CasFact)> {
        self.facts
            .iter()
            .enumerate()
            .filter_map(|(index, fact)| fact.as_ref().map(|fact| (id_from_index(index), fact)))
    }

    /// Inserts complete bytes and returns their stable ID.
    pub fn insert(&mut self, bytes: impl Into<Bytes>) -> u64 {
        self.insert_fact(CasFact::from_bytes(bytes))
    }

    /// Inserts a checked fact and returns its stable ID.
    ///
    /// Repeated insertion of an address is idempotent. In the event of a real
    /// hash collision, the first fact remains the indexed representative.
    pub fn insert_fact(&mut self, fact: CasFact) -> u64 {
        let address = fact.hash();
        if let Some(id) = self.id(address) {
            return id;
        }

        let id = id_from_index(self.facts.len());
        self.facts.push(Some(fact));
        self.count += 1;

        let facts = &self.facts;
        self.addresses
            .insert_unique(address.addr64(), id, |&resident_id| {
                resident_addr64(facts, resident_id)
            });
        id
    }

    /// Removes `address` without invalidating any other fact ID.
    #[must_use = "the return value says whether the address was resident"]
    pub fn remove(&mut self, address: O256) -> bool {
        let hash = address.addr64();
        let facts = &self.facts;
        let Ok(entry) = self.addresses.find_entry(hash, |&id| {
            fact_by_id(facts, id).is_some_and(|fact| fact.hash() == address)
        }) else {
            return false;
        };
        let (id, _) = entry.remove();
        let index = index_from_id(id);
        self.facts[index] = None;
        self.count -= 1;
        true
    }
}

fn fact_by_id(facts: &[Option<CasFact>], id: u64) -> Option<&CasFact> {
    usize::try_from(id)
        .ok()
        .and_then(|index| facts.get(index))
        .and_then(Option::as_ref)
}

fn id_from_index(index: usize) -> u64 {
    u64::try_from(index).unwrap_or_else(|_| panic!("fact index exceeds u64"))
}

fn index_from_id(id: u64) -> usize {
    usize::try_from(id).unwrap_or_else(|_| unreachable!("resident ID was created from usize"))
}

fn resident_addr64(facts: &[Option<CasFact>], id: u64) -> u64 {
    fact_by_id(facts, id)
        .unwrap_or_else(|| unreachable!("address table points to a resident fact"))
        .hash()
        .addr64()
}

impl Cas for IndexCas {
    type Error = InvalidRange;
    type Object = ResidentObject;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        Ok(self
            .fact_at(address)
            .map(|fact| ResidentObject(fact.bytes().clone())))
    }

    fn get_fact(&self, address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
        Ok(self.fact_at(address).cloned())
    }
}

impl CasMut for IndexCas {
    type InsertSuccess = u64;
    type InsertError = Infallible;

    fn insert(&mut self, bytes: Bytes) -> Result<Self::InsertSuccess, Self::InsertError> {
        Ok(IndexCas::insert(self, bytes))
    }
}

/// Resident object counts and sizes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CasStats {
    /// Number of resident facts.
    pub objects: u64,
    /// Sum of their blob lengths.
    pub bytes: u64,
    /// Length of the largest resident blob.
    pub largest: u64,
}

impl CasStatistics for IndexCas {
    fn stats(&self) -> CasStats {
        let mut stats = CasStats::default();
        for (_, fact) in self.facts() {
            let len = fact.bytes().len() as u64;
            stats.objects += 1;
            stats.bytes += len;
            stats.largest = stats.largest.max(len);
        }
        stats
    }
}

/// A synchronized, optionally bounded wrapper around [`IndexCas`].
///
/// This remains available to existing shared consumers. New users which do
/// not need shared insertion can use `IndexCas` directly.
pub struct SharedIndexCas {
    index: RwLock<IndexCas>,
    limit: u64,
}

impl Default for SharedIndexCas {
    fn default() -> Self {
        Self::new()
    }
}

impl SharedIndexCas {
    /// Default largest object admitted by this wrapper.
    pub const DEFAULT_LIMIT: u64 = 64 * 1024 * 1024;

    /// Creates an empty shared index with the default admission limit.
    #[must_use]
    pub fn new() -> Self {
        Self::with_limit(Self::DEFAULT_LIMIT)
    }

    /// Creates an empty shared index admitting at most `limit` bytes per fact.
    #[must_use]
    pub fn with_limit(limit: u64) -> Self {
        Self {
            index: RwLock::new(IndexCas::new()),
            limit,
        }
    }

    /// Returns this wrapper's per-fact admission limit.
    #[must_use]
    pub const fn limit(&self) -> u64 {
        self.limit
    }

    /// Hashes and inserts complete bytes, returning their address.
    ///
    /// # Errors
    ///
    /// Returns [`AdmissionError`] when the blob exceeds [`Self::limit`].
    pub fn insert(&self, bytes: impl Into<Bytes>) -> Result<O256, AdmissionError> {
        let bytes = bytes.into();
        self.check_length(&bytes)?;
        let fact = CasFact::from_bytes(bytes);
        let address = fact.hash();
        self.index_mut().insert_fact(fact);
        Ok(address)
    }

    /// Inserts a checked fact and returns its stable integer ID.
    ///
    /// # Errors
    ///
    /// Returns [`AdmissionError`] when the blob exceeds [`Self::limit`].
    pub fn insert_fact(&self, fact: CasFact) -> Result<u64, AdmissionError> {
        self.check_length(fact.bytes())?;
        Ok(self.index_mut().insert_fact(fact))
    }

    /// Returns the stable ID for `address`, if resident.
    #[must_use]
    pub fn id(&self, address: O256) -> Option<u64> {
        self.index().id(address)
    }

    /// Hashes `bytes` and returns the stable ID of the resulting address.
    #[must_use]
    pub fn id_bytes(&self, bytes: impl AsRef<[u8]>) -> Option<u64> {
        self.index().id_bytes(bytes)
    }

    /// Returns a snapshot of the fact at `id`.
    #[must_use]
    pub fn fact(&self, id: u64) -> Option<CasFact> {
        self.index().fact(id).cloned()
    }

    /// Returns a snapshot of the fact carrying `address`.
    #[must_use]
    pub fn fact_at(&self, address: O256) -> Option<CasFact> {
        self.index().fact_at(address).cloned()
    }

    /// Removes `address` without invalidating any other fact ID.
    #[must_use = "the return value says whether the address was resident"]
    pub fn remove(&self, address: O256) -> bool {
        self.index_mut().remove(address)
    }

    /// Returns whether `address` is resident.
    #[must_use]
    pub fn contains(&self, address: O256) -> bool {
        self.id(address).is_some()
    }

    /// Returns whether this wrapper contains no facts.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.index().is_empty()
    }

    /// Returns resident facts in insertion order.
    #[must_use]
    pub fn facts(&self) -> Vec<CasFact> {
        self.index().facts().map(|(_, fact)| fact.clone()).collect()
    }

    /// Returns resident addresses in insertion order.
    #[must_use]
    pub fn addresses(&self) -> Vec<O256> {
        self.index().facts().map(|(_, fact)| fact.hash()).collect()
    }

    fn check_length(&self, bytes: &Bytes) -> Result<(), AdmissionError> {
        let len = bytes.len() as u64;
        if len <= self.limit {
            Ok(())
        } else {
            Err(AdmissionError {
                len,
                limit: self.limit,
            })
        }
    }

    fn index(&self) -> std::sync::RwLockReadGuard<'_, IndexCas> {
        self.index
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn index_mut(&self) -> std::sync::RwLockWriteGuard<'_, IndexCas> {
        self.index
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

impl Cas for SharedIndexCas {
    type Error = InvalidRange;
    type Object = ResidentObject;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        Ok(self
            .fact_at(address)
            .map(|fact| ResidentObject(fact.bytes().clone())))
    }

    fn get_fact(&self, address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
        Ok(self.fact_at(address))
    }
}

impl CasShared for SharedIndexCas {
    type InsertSuccess = O256;
    type InsertError = AdmissionError;

    fn insert(&self, bytes: Bytes) -> Result<Self::InsertSuccess, Self::InsertError> {
        SharedIndexCas::insert(self, bytes)
    }
}

impl CasStatistics for SharedIndexCas {
    fn stats(&self) -> CasStats {
        self.index().stats()
    }
}

/// An object pinned independently of its source CAS.
#[derive(Clone, Debug)]
pub struct ResidentObject(Bytes);

impl ResidentObject {
    /// Borrows the complete bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> &Bytes {
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
        let start = usize::try_from(range.start).expect("resident offset fits usize");
        let end = usize::try_from(range.end).expect("resident offset fits usize");
        Ok(self.0.slice(start..end))
    }
}

#[cfg(test)]
mod tests {
    use covalence_logic_cas::CasExt;

    use super::*;

    #[test]
    fn index_exposes_stable_integer_ids() {
        let mut cas = IndexCas::new();
        let hello = cas.insert(Bytes::from_static(b"hello"));
        let world = cas.insert(Bytes::from_static(b"world"));
        let hello_hash = O256::from_bytes(b"hello");

        assert_eq!(hello, 0);
        assert_eq!(world, 1);
        assert_eq!(cas.id(hello_hash), Some(hello));
        assert_eq!(cas.id_bytes(b"hello"), Some(hello));
        assert_eq!(cas.fact(hello).unwrap().bytes().as_ref(), b"hello");

        assert!(cas.remove(hello_hash));
        assert_eq!(cas.fact(hello), None);
        assert_eq!(cas.fact(world).unwrap().bytes().as_ref(), b"world");
        assert_eq!(cas.insert(Bytes::from_static(b"again")), 2);
    }

    #[test]
    fn reinsertion_is_idempotent() {
        let mut cas = IndexCas::new();
        let first = cas.insert(Bytes::from_static(b"hello"));
        let second = cas.insert(Bytes::from_static(b"hello"));
        assert_eq!(first, second);
        assert_eq!(cas.fact_count(), 1);
    }

    #[test]
    fn checked_lookup_is_exact_without_rehashing() {
        let mut cas = IndexCas::new();
        let id = cas.insert(Bytes::from_static(b"checked"));
        let fact = cas.fact(id).unwrap().clone();

        assert_eq!(cas.get_checked(fact.hash()).unwrap(), Some(fact));
    }

    #[test]
    fn ranges_are_exact() {
        let mut cas = IndexCas::new();
        cas.insert(Bytes::from_static(b"hello world"));
        let address = O256::from_bytes(b"hello world");

        assert_eq!(
            cas.get_range(address, 6..11).unwrap(),
            Some(Bytes::from_static(b"world"))
        );
        assert_eq!(
            cas.get_range(address, 0..12).unwrap_err(),
            InvalidRange {
                start: 0,
                end: 12,
                len: 11,
            }
        );
    }

    #[test]
    fn shared_wrapper_preserves_existing_objects_after_removal() {
        let cas = SharedIndexCas::new();
        let address = cas.insert(Bytes::from_static(b"hello")).unwrap();
        let object = cas.open(address).unwrap().unwrap();

        assert!(cas.remove(address));
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
        assert!(cas.open(address).unwrap().is_none());
    }

    #[test]
    fn shared_wrapper_enforces_its_limit() {
        let cas = SharedIndexCas::with_limit(4);
        assert_eq!(
            cas.insert(Bytes::from_static(b"hello")).unwrap_err(),
            AdmissionError { len: 5, limit: 4 }
        );
        assert!(cas.is_empty());
    }

    #[test]
    fn shared_wrapper_reports_statistics_on_demand() {
        let cas = SharedIndexCas::new();
        cas.insert(Bytes::from_static(b"hello")).unwrap();
        cas.insert(Bytes::from_static(b"hello world")).unwrap();
        assert_eq!(
            cas.stats(),
            CasStats {
                objects: 2,
                bytes: 16,
                largest: 11,
            }
        );
    }
}
