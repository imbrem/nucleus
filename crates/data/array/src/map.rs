//! Flat index maps: hash arrays read as key-value pairs.
//!
//! A flat index map is a hash array of even length, read as consecutive
//! `(key, value)` entries. Like a flat set it adds only an invariant, so the
//! same blob can be read as an array, and as a map, without re-encoding.
//!
//! Ordering by key is not part of the invariant, because an entry sequence is
//! meaningful in its own right. [`FlatIndexMap::lookup`] serves the sorted
//! case in logarithmic time, and [`FlatIndexMap::get`] the general one.

use std::{cmp::Ordering, fmt, iter::FusedIterator, marker::PhantomData};

use covalence_lib_error::snafu;
use covalence_lib_hash::{Cov, Namespace, Obj};
use snafu::Snafu;

use crate::{Hashes, width};

/// A hash array whose element count was odd.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("expected an even element count, found {len}"))]
pub struct ParityError {
    /// The array's element count.
    pub len: usize,
}

/// A borrowed flat index map: an even-length hash array of `(key, value)`
/// entries.
pub struct FlatIndexMap<'a, N: Namespace = Cov> {
    hashes: Hashes<'a, N>,
}

impl<'a, N: Namespace> FlatIndexMap<'a, N> {
    /// Reads a hash array as a flat index map.
    ///
    /// # Errors
    ///
    /// Returns an error if the element count is odd.
    pub fn new(hashes: Hashes<'a, N>) -> Result<Self, ParityError> {
        if !hashes.len().is_multiple_of(2) {
            return Err(ParityError { len: hashes.len() });
        }
        Ok(Self { hashes })
    }

    /// Returns the empty map.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            hashes: Hashes::empty(),
        }
    }

    /// Borrows the underlying array, of twice [`len`](Self::len) elements.
    #[must_use]
    pub const fn hashes(&self) -> Hashes<'a, N> {
        self.hashes
    }

    /// Borrows the normal form.
    #[must_use]
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.hashes.as_bytes()
    }

    /// Returns the number of entries, which is half the element count.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.hashes.len() / 2
    }

    /// Returns whether there are no entries.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.hashes.is_empty()
    }

    /// Returns the entry at `index`.
    #[must_use]
    pub fn entry(&self, index: usize) -> Option<(Obj<N>, Obj<N>)> {
        let key = index.checked_mul(2)?;
        Some((self.hashes.get(key)?, self.hashes.get(key.checked_add(1)?)?))
    }

    /// Returns the key of the entry at `index`.
    #[must_use]
    pub fn key(&self, index: usize) -> Option<Obj<N>> {
        self.entry(index).map(|(key, _)| key)
    }

    /// Returns the value of the entry at `index`.
    #[must_use]
    pub fn value(&self, index: usize) -> Option<Obj<N>> {
        self.entry(index).map(|(_, value)| value)
    }

    /// Iterates over the entries in order.
    #[must_use]
    pub fn iter(&self) -> Entries<'a, N> {
        Entries {
            chunks: self.hashes.as_bytes().chunks_exact(width::<N>() * 2),
            namespace: PhantomData,
        }
    }

    /// Iterates over the keys in order.
    #[must_use]
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = Obj<N>> + ExactSizeIterator {
        self.iter().map(|(key, _)| key)
    }

    /// Iterates over the values in order.
    #[must_use]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = Obj<N>> + ExactSizeIterator {
        self.iter().map(|(_, value)| value)
    }

    /// Returns the value of the first entry keyed by `key`.
    ///
    /// This scans, so it is linear in the number of entries. Prefer
    /// [`lookup`](Self::lookup) when the keys are known to be ascending.
    #[must_use]
    pub fn get(&self, key: &Obj<N>) -> Option<Obj<N>> {
        self.iter()
            .find(|(candidate, _)| candidate == key)
            .map(|(_, value)| value)
    }

    /// Returns whether some entry is keyed by `key`.
    #[must_use]
    pub fn contains_key(&self, key: &Obj<N>) -> bool {
        self.get(key).is_some()
    }

    /// Returns whether the keys are in ascending order.
    #[must_use]
    pub fn is_sorted_by_key(&self) -> bool {
        self.keys().is_sorted()
    }

    /// Returns whether the keys are in strictly ascending order.
    ///
    /// This is the canonical form for lookup: it makes the keys a flat set and
    /// so makes each key's value unique.
    #[must_use]
    pub fn is_strictly_sorted_by_key(&self) -> bool {
        self.keys().is_sorted_by(|left, right| left < right)
    }

    /// Returns the value keyed by `key`, in logarithmic time.
    ///
    /// The result is unspecified, though still safe, unless the keys are
    /// ascending.
    #[must_use]
    pub fn lookup(&self, key: &Obj<N>) -> Option<Obj<N>> {
        let (mut low, mut high) = (0, self.len());
        while low < high {
            let middle = low + (high - low) / 2;
            let (candidate, value) = self.entry(middle)?;
            match candidate.cmp(key) {
                Ordering::Less => low = middle + 1,
                Ordering::Greater => high = middle,
                Ordering::Equal => return Some(value),
            }
        }
        None
    }
}

impl<N: Namespace> Copy for FlatIndexMap<'_, N> {}
impl<N: Namespace> Clone for FlatIndexMap<'_, N> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<N: Namespace> Default for FlatIndexMap<'_, N> {
    fn default() -> Self {
        Self::empty()
    }
}
impl<N: Namespace> PartialEq for FlatIndexMap<'_, N> {
    fn eq(&self, other: &Self) -> bool {
        self.hashes == other.hashes
    }
}
impl<N: Namespace> Eq for FlatIndexMap<'_, N> {}
impl<N: Namespace> fmt::Debug for FlatIndexMap<'_, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_map()
            .entries(self.iter().map(|(key, value)| (Hex(key), Hex(value))))
            .finish()
    }
}

/// A hexadecimal map key or value.
struct Hex<N: Namespace>(Obj<N>);

impl<N: Namespace> fmt::Debug for Hex<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0.hex())
    }
}

impl<'a, N: Namespace> IntoIterator for FlatIndexMap<'a, N> {
    type Item = (Obj<N>, Obj<N>);
    type IntoIter = Entries<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, N: Namespace> IntoIterator for &FlatIndexMap<'a, N> {
    type Item = (Obj<N>, Obj<N>);
    type IntoIter = Entries<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the entries of a flat index map.
pub struct Entries<'a, N: Namespace = Cov> {
    chunks: std::slice::ChunksExact<'a, u8>,
    namespace: PhantomData<fn(N) -> N>,
}

/// Reads one entry from a chunk of exactly `2 * width::<N>()` bytes.
fn entry<N: Namespace>(chunk: &[u8]) -> Option<(Obj<N>, Obj<N>)> {
    let hashes = Hashes::<N>::new(chunk).ok()?;
    Some((hashes.get(0)?, hashes.get(1)?))
}

impl<N: Namespace> Iterator for Entries<'_, N> {
    type Item = (Obj<N>, Obj<N>);

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().and_then(entry)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.chunks.size_hint()
    }
}

impl<N: Namespace> DoubleEndedIterator for Entries<'_, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.chunks.next_back().and_then(entry)
    }
}

impl<N: Namespace> ExactSizeIterator for Entries<'_, N> {}
impl<N: Namespace> FusedIterator for Entries<'_, N> {}

impl<N: Namespace> Clone for Entries<'_, N> {
    fn clone(&self) -> Self {
        Self {
            chunks: self.chunks.clone(),
            namespace: PhantomData,
        }
    }
}

impl<N: Namespace> fmt::Debug for Entries<'_, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Entries")
            .field("remaining", &self.chunks.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::{Cov, O256};

    use super::{FlatIndexMap, ParityError};
    use crate::HashArray;

    fn obj(byte: u8) -> O256 {
        O256::from_array([byte; 32])
    }

    fn array(bytes: &[u8]) -> HashArray {
        bytes.iter().copied().map(obj).collect()
    }

    #[test]
    fn only_even_length_arrays_are_maps() {
        assert!(array(&[1, 2]).as_hashes().flat_index_map().is_ok());
        assert!(array(&[]).as_hashes().flat_index_map().is_ok());
        assert_eq!(
            array(&[1, 2, 3]).as_hashes().flat_index_map(),
            Err(ParityError { len: 3 })
        );
        assert_eq!(FlatIndexMap::<Cov>::default().len(), 0);
    }

    #[test]
    fn entries_pair_adjacent_elements() {
        let values = array(&[1, 10, 2, 20]);
        let map = values.as_hashes().flat_index_map().unwrap();

        assert_eq!(map.len(), 2);
        assert_eq!(map.hashes().len(), 4);
        assert_eq!(map.as_bytes(), values.as_bytes());
        assert_eq!(map.entry(0), Some((obj(1), obj(10))));
        assert_eq!(map.entry(1), Some((obj(2), obj(20))));
        assert_eq!(map.entry(2), None);
        assert_eq!(map.key(1), Some(obj(2)));
        assert_eq!(map.value(1), Some(obj(20)));
        assert_eq!(map.keys().collect::<Vec<_>>(), vec![obj(1), obj(2)]);
        assert_eq!(map.values().collect::<Vec<_>>(), vec![obj(10), obj(20)]);
        assert_eq!(map.iter().len(), 2);
        assert_eq!(map.iter().next_back(), Some((obj(2), obj(20))));
    }

    #[test]
    fn lookup_serves_sorted_keys_and_get_serves_any() {
        let values = array(&[1, 10, 3, 30, 5, 50]);
        let map = values.as_hashes().flat_index_map().unwrap();

        assert!(map.is_sorted_by_key());
        assert!(map.is_strictly_sorted_by_key());
        assert_eq!(map.lookup(&obj(3)), Some(obj(30)));
        assert_eq!(map.lookup(&obj(1)), Some(obj(10)));
        assert_eq!(map.lookup(&obj(5)), Some(obj(50)));
        assert_eq!(map.lookup(&obj(4)), None);
        assert_eq!(map.get(&obj(3)), Some(obj(30)));
        assert!(map.contains_key(&obj(5)));
        assert!(!map.contains_key(&obj(6)));
    }

    #[test]
    fn unsorted_and_repeated_keys_are_still_maps() {
        let values = array(&[5, 50, 1, 10, 5, 55]);
        let map = values.as_hashes().flat_index_map().unwrap();

        assert!(!map.is_sorted_by_key());
        assert!(!map.is_strictly_sorted_by_key());
        assert_eq!(map.get(&obj(5)), Some(obj(50)));
        assert_eq!(map.get(&obj(1)), Some(obj(10)));
        assert_eq!(map.get(&obj(9)), None);

        let repeated = array(&[1, 10, 1, 11]);
        let repeated = repeated.as_hashes().flat_index_map().unwrap();
        assert!(repeated.is_sorted_by_key());
        assert!(!repeated.is_strictly_sorted_by_key());
        assert_eq!(repeated.get(&obj(1)), Some(obj(10)));
    }

    #[test]
    fn maps_are_built_by_collecting_pairs() {
        let built: HashArray = vec![(obj(1), obj(10)), (obj(2), obj(20))]
            .into_iter()
            .collect();
        let map = built.as_hashes().flat_index_map().unwrap();
        assert_eq!(
            map.iter().collect::<Vec<_>>(),
            vec![(obj(1), obj(10)), (obj(2), obj(20))]
        );
    }
}
