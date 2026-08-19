//! Flat sequences of fixed-width objects.
//!
//! [`Hashes`] borrows a normal-form blob; [`HashArray`] owns one. Both keep the
//! bytes as the authoritative representation and materialize [`Obj`] values on
//! demand, so a blob read from a content-addressed store is usable without
//! being decoded first.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Bound, RangeBounds},
};

use covalence_lib_error::snafu;
use covalence_lib_hash::{ByteArray, Cov, Namespace, Obj};
use snafu::Snafu;

use crate::{FlatSet, OrderError};

/// The serialized width of one element of namespace `N`, in bytes.
#[must_use]
pub const fn width<N: Namespace>() -> usize {
    <N::Bytes as ByteArray>::LEN
}

/// A blob whose length was not a whole number of elements.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("expected a multiple of {width} bytes, found {len}"))]
pub struct WidthError {
    /// The blob's length in bytes.
    pub len: usize,
    /// The element width in bytes.
    pub width: usize,
}

/// Reads one element from a chunk of exactly `width::<N>()` bytes.
fn element<N: Namespace>(chunk: &[u8]) -> Obj<N> {
    let mut bytes = N::Bytes::default();
    bytes.as_mut().copy_from_slice(chunk);
    Obj::from_array(bytes)
}

/// A borrowed hash array.
///
/// The normal form is the concatenation of the elements' fixed-width
/// representations and nothing else: no header, no length prefix, no element
/// count. A blob is a hash array exactly when its length is a multiple of
/// [`width::<N>()`](width), and it holds `len / width` elements.
pub struct Hashes<'a, N: Namespace = Cov> {
    bytes: &'a [u8],
    namespace: PhantomData<fn(N) -> N>,
}

/// A descriptive alias for the borrowed hash-array view.
///
/// [`Hashes`] is retained as the concise spelling used by the original API;
/// new code may prefer this name beside the owned [`HashArray`].
pub type HashArrayRef<'a, N = Cov> = Hashes<'a, N>;

impl<'a, N: Namespace> Hashes<'a, N> {
    /// Views a normal-form blob as a hash array.
    ///
    /// # Errors
    ///
    /// Returns an error if the length is not a whole number of elements.
    pub const fn new(bytes: &'a [u8]) -> Result<Self, WidthError> {
        let width = width::<N>();
        if width == 0 || !bytes.len().is_multiple_of(width) {
            return Err(WidthError {
                len: bytes.len(),
                width,
            });
        }
        Ok(Self {
            bytes,
            namespace: PhantomData,
        })
    }

    /// Returns the empty hash array.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            bytes: &[],
            namespace: PhantomData,
        }
    }

    /// Borrows the normal form.
    #[must_use]
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Returns the number of elements.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.bytes.len() / width::<N>()
    }

    /// Returns whether there are no elements.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Borrows the element at `index` in its serialized form.
    fn chunk(&self, index: usize) -> Option<&'a [u8]> {
        let width = width::<N>();
        let start = index.checked_mul(width)?;
        self.bytes.get(start..start.checked_add(width)?)
    }

    /// Returns the element at `index`.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<Obj<N>> {
        self.chunk(index).map(element)
    }

    /// Returns the first element.
    #[must_use]
    pub fn first(&self) -> Option<Obj<N>> {
        self.get(0)
    }

    /// Returns the last element.
    #[must_use]
    pub fn last(&self) -> Option<Obj<N>> {
        self.get(self.len().checked_sub(1)?)
    }

    /// Iterates over the elements.
    #[must_use]
    pub fn iter(&self) -> Iter<'a, N> {
        Iter {
            chunks: self.bytes.chunks_exact(width::<N>()),
            namespace: PhantomData,
        }
    }

    /// Returns the subarray covering the element positions in `range`.
    #[must_use]
    pub fn slice<R: RangeBounds<usize>>(&self, range: R) -> Option<Self> {
        let start = match range.start_bound() {
            Bound::Included(&bound) => bound,
            Bound::Excluded(&bound) => bound.checked_add(1)?,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&bound) => bound.checked_add(1)?,
            Bound::Excluded(&bound) => bound,
            Bound::Unbounded => self.len(),
        };
        if start > end || end > self.len() {
            return None;
        }
        let width = width::<N>();
        let bytes = self
            .bytes
            .get(start.checked_mul(width)?..end.checked_mul(width)?)?;
        Some(Self {
            bytes,
            namespace: PhantomData,
        })
    }

    /// Splits into the elements before and from `index`.
    #[must_use]
    pub fn split_at(&self, index: usize) -> Option<(Self, Self)> {
        Some((self.slice(..index)?, self.slice(index..)?))
    }

    /// Collects the elements.
    #[must_use]
    pub fn to_vec(&self) -> Vec<Obj<N>> {
        self.iter().collect()
    }

    /// Collects the elements in ascending order.
    #[must_use]
    fn sorted_vec(&self) -> Vec<Obj<N>> {
        let mut values = self.to_vec();
        values.sort_unstable();
        values
    }

    /// Collects the distinct elements in ascending order.
    #[must_use]
    fn set_vec(&self) -> Vec<Obj<N>> {
        let mut values = self.sorted_vec();
        values.dedup();
        values
    }

    /// Returns whether the elements are in ascending order.
    ///
    /// Object ordering is bytewise, so this is exactly lexicographic ordering
    /// of the normal form.
    #[must_use]
    pub fn is_sorted(&self) -> bool {
        self.bytes.chunks_exact(width::<N>()).is_sorted()
    }

    /// Returns whether the elements are in strictly ascending order.
    ///
    /// This is sortedness together with distinctness: the canonical form of a
    /// [`FlatSet`].
    #[must_use]
    pub fn is_strictly_sorted(&self) -> bool {
        self.bytes
            .chunks_exact(width::<N>())
            .is_sorted_by(|left, right| left < right)
    }

    /// Returns whether any element is the null object.
    #[must_use]
    pub fn contains_null(&self) -> bool {
        self.bytes
            .chunks_exact(width::<N>())
            .any(|chunk| chunk.iter().all(|byte| *byte == 0))
    }

    /// Returns whether no element is the null object.
    #[must_use]
    pub fn is_non_null(&self) -> bool {
        !self.contains_null()
    }

    /// Returns whether `value` occurs, in time linear in the length.
    ///
    /// Prefer [`FlatSet::contains`] when the array is known to be sorted.
    #[must_use]
    pub fn contains(&self, value: &Obj<N>) -> bool {
        self.position(value).is_some()
    }

    /// Returns the position of the first occurrence of `value`.
    #[must_use]
    pub fn position(&self, value: &Obj<N>) -> Option<usize> {
        self.bytes
            .chunks_exact(width::<N>())
            .position(|chunk| chunk == value.as_ref())
    }

    /// Returns the number of occurrences of `value`.
    #[must_use]
    pub fn count(&self, value: &Obj<N>) -> usize {
        self.bytes
            .chunks_exact(width::<N>())
            .filter(|chunk| *chunk == value.as_ref())
            .count()
    }

    /// Searches a sorted array for `value`.
    ///
    /// The result is unspecified, though still safe, if the array is not
    /// sorted.
    ///
    /// # Errors
    ///
    /// Returns the position at which `value` could be inserted while keeping
    /// the array sorted, if it does not occur.
    pub fn binary_search(&self, value: &Obj<N>) -> Result<usize, usize> {
        let (mut low, mut high) = (0, self.len());
        while low < high {
            let middle = low + (high - low) / 2;
            let Some(chunk) = self.chunk(middle) else {
                break;
            };
            match chunk.cmp(value.as_ref()) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(middle),
            }
        }
        Err(low)
    }

    /// Returns whether every element occurs in `other` at least as often.
    ///
    /// This sorts a copy of each array. [`FlatSet::is_subset_of`] answers the
    /// same question by merge when both are already canonical.
    #[must_use]
    pub fn is_subbag_of(&self, other: Hashes<'_, N>) -> bool {
        is_subbag(&self.sorted_vec(), &other.sorted_vec())
    }

    /// Returns whether every element occurs in `other`, ignoring multiplicity.
    ///
    /// This sorts and deduplicates a copy of each array.
    #[must_use]
    pub fn is_subset_of(&self, other: Hashes<'_, N>) -> bool {
        is_subbag(&self.set_vec(), &other.set_vec())
    }

    /// Returns whether the arrays agree up to order.
    ///
    /// This sorts a copy of each array. Arrays already in canonical form can
    /// be compared bytewise instead.
    #[must_use]
    pub fn bag_eq(&self, other: Hashes<'_, N>) -> bool {
        self.len() == other.len() && self.sorted_vec() == other.sorted_vec()
    }

    /// Returns whether the arrays agree up to order and multiplicity.
    ///
    /// This sorts and deduplicates a copy of each array.
    #[must_use]
    pub fn set_eq(&self, other: Hashes<'_, N>) -> bool {
        self.set_vec() == other.set_vec()
    }

    /// Reads the array as a flat set.
    ///
    /// # Errors
    ///
    /// Returns an error unless the elements are strictly ascending.
    pub fn flat_set(self) -> Result<FlatSet<'a, N>, OrderError> {
        FlatSet::new(self)
    }

    /// Returns whether this is a sparse refinement of `other`.
    ///
    /// Arrays must have the same length. At each position this array must
    /// either contain the null object or equal `other`. Null is special only
    /// to this explicitly indexed relation; set and bag operations below
    /// treat it as an ordinary element.
    #[must_use]
    pub fn is_sparse_refinement_of(&self, other: Hashes<'_, N>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other)
                .all(|(left, right)| is_null(&left) || left == right)
    }

    /// Returns whether the arrays have disjoint non-null support.
    ///
    /// Arrays must have the same length. This is symmetric and distinct from
    /// sparse refinement.
    #[must_use]
    pub fn has_disjoint_support_with(&self, other: Hashes<'_, N>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other)
                .all(|(left, right)| is_null(&left) || is_null(&right))
    }

    /// Returns the canonical set containing these elements.
    ///
    /// The result is ascending and deduplicated. Null is an ordinary element.
    #[must_use]
    pub fn canonical_set(&self) -> HashArray<N> {
        self.iter().collect::<BTreeSet<_>>().into_iter().collect()
    }

    /// Returns the canonical bag containing these elements.
    ///
    /// The result is ascending and retains every multiplicity, including null.
    #[must_use]
    pub fn canonical_bag(&self) -> HashArray<N> {
        self.sorted_vec().into_iter().collect()
    }

    /// Returns the canonical set union.
    #[must_use]
    pub fn set_union(&self, other: Hashes<'_, N>) -> HashArray<N> {
        self.iter()
            .chain(other)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    /// Returns the canonical set intersection.
    #[must_use]
    pub fn set_intersection(&self, other: Hashes<'_, N>) -> HashArray<N> {
        let left: BTreeSet<_> = self.iter().collect();
        let right: BTreeSet<_> = other.iter().collect();
        left.intersection(&right).copied().collect()
    }

    /// Returns the canonical set difference `self - other`.
    #[must_use]
    pub fn set_difference(&self, other: Hashes<'_, N>) -> HashArray<N> {
        let left: BTreeSet<_> = self.iter().collect();
        let right: BTreeSet<_> = other.iter().collect();
        left.difference(&right).copied().collect()
    }

    /// Returns the canonical set symmetric difference.
    #[must_use]
    pub fn set_symmetric_difference(&self, other: Hashes<'_, N>) -> HashArray<N> {
        let left: BTreeSet<_> = self.iter().collect();
        let right: BTreeSet<_> = other.iter().collect();
        left.symmetric_difference(&right).copied().collect()
    }

    /// Returns the canonical bag union using maximum multiplicities.
    #[must_use]
    pub fn bag_union_max(&self, other: Hashes<'_, N>) -> HashArray<N> {
        combine_bags(*self, other, usize::max)
    }

    /// Returns the canonical additive bag sum.
    #[must_use]
    pub fn bag_sum(&self, other: Hashes<'_, N>) -> HashArray<N> {
        combine_bags(*self, other, usize::saturating_add)
    }

    /// Returns the canonical bag intersection using minimum multiplicities.
    #[must_use]
    pub fn bag_intersection(&self, other: Hashes<'_, N>) -> HashArray<N> {
        combine_bags(*self, other, usize::min)
    }

    /// Returns the canonical bag difference using saturating subtraction.
    #[must_use]
    pub fn bag_difference(&self, other: Hashes<'_, N>) -> HashArray<N> {
        combine_bags(*self, other, usize::saturating_sub)
    }

    /// Returns the canonical bag symmetric difference.
    #[must_use]
    pub fn bag_symmetric_difference(&self, other: Hashes<'_, N>) -> HashArray<N> {
        combine_bags(*self, other, usize::abs_diff)
    }
}

fn is_null<N: Namespace>(value: &Obj<N>) -> bool {
    value.as_ref().iter().all(|byte| *byte == 0)
}

fn counts<N: Namespace>(hashes: Hashes<'_, N>) -> BTreeMap<Obj<N>, usize> {
    let mut counts = BTreeMap::new();
    for value in hashes {
        *counts.entry(value).or_default() += 1;
    }
    counts
}

fn combine_bags<N: Namespace>(
    left: Hashes<'_, N>,
    right: Hashes<'_, N>,
    combine: fn(usize, usize) -> usize,
) -> HashArray<N> {
    let left = counts(left);
    let right = counts(right);
    let keys: BTreeSet<_> = left.keys().chain(right.keys()).copied().collect();
    let mut result = HashArray::default();
    for key in keys {
        let count = combine(
            left.get(&key).copied().unwrap_or_default(),
            right.get(&key).copied().unwrap_or_default(),
        );
        result.extend(std::iter::repeat_n(key, count));
    }
    result
}

/// Returns whether sorted `left` is contained in sorted `right` as a multiset.
fn is_subbag<N: Namespace>(left: &[Obj<N>], right: &[Obj<N>]) -> bool {
    let mut right = right.iter();
    left.iter()
        .all(|value| right.any(|candidate| candidate == value))
}

impl<N: Namespace> Copy for Hashes<'_, N> {}
impl<N: Namespace> Clone for Hashes<'_, N> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<N: Namespace> Default for Hashes<'_, N> {
    fn default() -> Self {
        Self::empty()
    }
}
impl<N: Namespace> PartialEq for Hashes<'_, N> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}
impl<N: Namespace> Eq for Hashes<'_, N> {}
impl<N: Namespace> PartialOrd for Hashes<'_, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<N: Namespace> Ord for Hashes<'_, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes.cmp(other.bytes)
    }
}
impl<N: Namespace> std::hash::Hash for Hashes<'_, N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}
impl<N: Namespace> fmt::Debug for Hashes<'_, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_list()
            .entries(self.iter().map(Entry))
            .finish()
    }
}

impl<'a, N: Namespace> IntoIterator for Hashes<'a, N> {
    type Item = Obj<N>;
    type IntoIter = Iter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, N: Namespace> IntoIterator for &Hashes<'a, N> {
    type Item = Obj<N>;
    type IntoIter = Iter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A hexadecimal list entry.
struct Entry<N: Namespace>(Obj<N>);

impl<N: Namespace> fmt::Debug for Entry<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0.hex())
    }
}

/// An iterator over the elements of a hash array.
pub struct Iter<'a, N: Namespace = Cov> {
    chunks: std::slice::ChunksExact<'a, u8>,
    namespace: PhantomData<fn(N) -> N>,
}

impl<N: Namespace> Iterator for Iter<'_, N> {
    type Item = Obj<N>;

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(element)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.chunks.size_hint()
    }
}

impl<N: Namespace> DoubleEndedIterator for Iter<'_, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.chunks.next_back().map(element)
    }
}

impl<N: Namespace> ExactSizeIterator for Iter<'_, N> {}
impl<N: Namespace> FusedIterator for Iter<'_, N> {}

impl<N: Namespace> Clone for Iter<'_, N> {
    fn clone(&self) -> Self {
        Self {
            chunks: self.chunks.clone(),
            namespace: PhantomData,
        }
    }
}

impl<N: Namespace> fmt::Debug for Iter<'_, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Iter")
            .field("remaining", &self.chunks.len())
            .finish()
    }
}

/// An owned hash array.
///
/// This is the building form: push, sort, and deduplicate, then hand the
/// normal form to a content-addressed store.
pub struct HashArray<N: Namespace = Cov> {
    bytes: Vec<u8>,
    namespace: PhantomData<fn(N) -> N>,
}

impl<N: Namespace> HashArray<N> {
    /// Creates the one-element array containing `value`.
    #[must_use]
    pub fn singleton(value: Obj<N>) -> Self {
        std::iter::once(value).collect()
    }

    /// Takes ownership of a normal-form blob.
    ///
    /// # Errors
    ///
    /// Returns an error if the length is not a whole number of elements.
    pub fn new(bytes: Vec<u8>) -> Result<Self, WidthError> {
        Hashes::<N>::new(&bytes)?;
        Ok(Self {
            bytes,
            namespace: PhantomData,
        })
    }

    /// Creates an empty array with room for `elements` elements.
    #[must_use]
    pub fn with_capacity(elements: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(elements.saturating_mul(width::<N>())),
            namespace: PhantomData,
        }
    }

    /// Borrows the array.
    #[must_use]
    pub fn as_hashes(&self) -> Hashes<'_, N> {
        Hashes {
            bytes: &self.bytes,
            namespace: PhantomData,
        }
    }

    /// Borrows the normal form.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the normal form.
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Returns the number of elements.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bytes.len() / width::<N>()
    }

    /// Returns whether there are no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns the element at `index`.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<Obj<N>> {
        self.as_hashes().get(index)
    }

    /// Iterates over the elements.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, N> {
        self.as_hashes().iter()
    }

    /// Appends an element.
    pub fn push(&mut self, value: Obj<N>) {
        self.bytes.extend_from_slice(value.as_ref());
    }

    /// Removes and returns the last element.
    pub fn pop(&mut self) -> Option<Obj<N>> {
        let last = self.as_hashes().last()?;
        self.bytes.truncate(self.bytes.len() - width::<N>());
        Some(last)
    }

    /// Removes all elements.
    pub fn clear(&mut self) {
        self.bytes.clear();
    }

    /// Shortens the array to `elements` elements, if it is longer.
    pub fn truncate(&mut self, elements: usize) {
        if elements < self.len() {
            self.bytes.truncate(elements * width::<N>());
        }
    }

    /// Replaces the contents with `values`.
    fn store(&mut self, values: &[Obj<N>]) {
        self.bytes.clear();
        for value in values {
            self.bytes.extend_from_slice(value.as_ref());
        }
    }

    /// Sorts the elements into ascending order.
    pub fn sort(&mut self) {
        let values = self.as_hashes().sorted_vec();
        self.store(&values);
    }

    /// Removes consecutive repeated elements.
    ///
    /// This removes every duplicate only when the array is already sorted.
    pub fn dedup(&mut self) {
        let mut values = self.as_hashes().to_vec();
        values.dedup();
        self.store(&values);
    }

    /// Sorts the elements and removes duplicates.
    ///
    /// The result is the canonical [`FlatSet`] form of the same elements, so
    /// [`Hashes::flat_set`] succeeds afterwards.
    pub fn sort_dedup(&mut self) {
        let values = self.as_hashes().set_vec();
        self.store(&values);
    }
}

impl<N: Namespace> Default for HashArray<N> {
    fn default() -> Self {
        Self {
            bytes: Vec::new(),
            namespace: PhantomData,
        }
    }
}

impl<N: Namespace> Clone for HashArray<N> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            namespace: PhantomData,
        }
    }
}

impl<N: Namespace> PartialEq for HashArray<N> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}
impl<N: Namespace> Eq for HashArray<N> {}
impl<N: Namespace> PartialOrd for HashArray<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<N: Namespace> Ord for HashArray<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes.cmp(&other.bytes)
    }
}
impl<N: Namespace> std::hash::Hash for HashArray<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}
impl<N: Namespace> fmt::Debug for HashArray<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.as_hashes(), formatter)
    }
}

impl<N: Namespace> From<Hashes<'_, N>> for HashArray<N> {
    fn from(hashes: Hashes<'_, N>) -> Self {
        Self {
            bytes: hashes.as_bytes().to_vec(),
            namespace: PhantomData,
        }
    }
}

impl<N: Namespace> FromIterator<Obj<N>> for HashArray<N> {
    fn from_iter<I: IntoIterator<Item = Obj<N>>>(values: I) -> Self {
        let mut array = Self::default();
        array.extend(values);
        array
    }
}

impl<N: Namespace> Extend<Obj<N>> for HashArray<N> {
    fn extend<I: IntoIterator<Item = Obj<N>>>(&mut self, values: I) {
        for value in values {
            self.push(value);
        }
    }
}

impl<'a, N: Namespace> IntoIterator for &'a HashArray<N> {
    type Item = Obj<N>;
    type IntoIter = Iter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;

    use super::{HashArray, Hashes, WidthError, width};

    fn obj(byte: u8) -> O256 {
        O256::from_array([byte; 32])
    }

    fn array(bytes: &[u8]) -> HashArray {
        bytes.iter().copied().map(obj).collect()
    }

    #[test]
    fn blobs_are_arrays_exactly_when_their_length_is_a_multiple_of_the_width() {
        assert_eq!(width::<covalence_lib_hash::Cov>(), 32);
        assert_eq!(
            Hashes::<covalence_lib_hash::Cov>::new(&[]).unwrap().len(),
            0
        );
        assert!(Hashes::<covalence_lib_hash::Cov>::new(&[0; 32]).is_ok());
        assert!(Hashes::<covalence_lib_hash::Cov>::new(&[0; 64]).is_ok());
        assert_eq!(
            Hashes::<covalence_lib_hash::Cov>::new(&[0; 31]),
            Err(WidthError { len: 31, width: 32 })
        );
        assert!(HashArray::<covalence_lib_hash::Cov>::new(vec![0; 33]).is_err());
    }

    #[test]
    fn elements_round_trip_through_the_normal_form() {
        let values = array(&[3, 1, 2]);
        assert_eq!(values.len(), 3);
        assert_eq!(values.as_bytes().len(), 96);
        assert_eq!(values.get(0), Some(obj(3)));
        assert_eq!(values.get(2), Some(obj(2)));
        assert_eq!(values.get(3), None);
        assert_eq!(values.as_hashes().first(), Some(obj(3)));
        assert_eq!(values.as_hashes().last(), Some(obj(2)));
        assert_eq!(
            values.iter().collect::<Vec<_>>(),
            vec![obj(3), obj(1), obj(2)]
        );
        assert_eq!(values.iter().next_back(), Some(obj(2)));
        assert_eq!(values.iter().len(), 3);

        let restored = HashArray::new(values.as_bytes().to_vec()).unwrap();
        assert_eq!(restored, values);
        assert_eq!(HashArray::from(values.as_hashes()), values);
    }

    #[test]
    fn empty_arrays_are_uniform() {
        let empty = HashArray::<covalence_lib_hash::Cov>::default();
        assert!(empty.is_empty());
        assert_eq!(empty.len(), 0);
        assert_eq!(empty.as_hashes(), Hashes::empty());
        assert!(Hashes::<covalence_lib_hash::Cov>::empty().is_empty());
        assert_eq!(empty.as_hashes().last(), None);
    }

    #[test]
    fn slicing_addresses_elements_not_bytes() {
        let values = array(&[0, 1, 2, 3]);
        let hashes = values.as_hashes();
        assert_eq!(hashes.slice(1..3).unwrap().to_vec(), vec![obj(1), obj(2)]);
        assert_eq!(hashes.slice(..).unwrap(), hashes);
        assert_eq!(hashes.slice(2..).unwrap().to_vec(), vec![obj(2), obj(3)]);
        assert_eq!(hashes.slice(..=1).unwrap().to_vec(), vec![obj(0), obj(1)]);
        assert_eq!(hashes.slice(4..4).unwrap().len(), 0);
        assert_eq!(hashes.slice(0..5), None);
        let (start, end) = (3, 1);
        assert_eq!(hashes.slice(start..end), None);

        let (left, right) = hashes.split_at(1).unwrap();
        assert_eq!(left.to_vec(), vec![obj(0)]);
        assert_eq!(right.to_vec(), vec![obj(1), obj(2), obj(3)]);
    }

    #[test]
    fn sortedness_matches_lexicographic_order_of_the_normal_form() {
        assert!(array(&[1, 2, 3]).as_hashes().is_sorted());
        assert!(array(&[1, 2, 2]).as_hashes().is_sorted());
        assert!(!array(&[2, 1]).as_hashes().is_sorted());
        assert!(array(&[1, 2, 3]).as_hashes().is_strictly_sorted());
        assert!(!array(&[1, 2, 2]).as_hashes().is_strictly_sorted());
        assert!(array(&[]).as_hashes().is_strictly_sorted());

        let sorted = array(&[1, 2, 3]);
        let mut bytes = sorted.as_bytes().to_vec();
        bytes.sort_unstable();
        assert_eq!(bytes, sorted.as_bytes());
    }

    #[test]
    fn nullness_detects_the_zero_object() {
        assert!(array(&[1, 2]).as_hashes().is_non_null());
        assert!(!array(&[1, 0]).as_hashes().is_non_null());
        assert!(array(&[0]).as_hashes().contains_null());
        assert!(!array(&[]).as_hashes().contains_null());
    }

    #[test]
    fn membership_is_available_linearly_and_by_binary_search() {
        let values = array(&[1, 3, 3, 7]);
        let hashes = values.as_hashes();
        assert!(hashes.contains(&obj(3)));
        assert!(!hashes.contains(&obj(4)));
        assert_eq!(hashes.position(&obj(3)), Some(1));
        assert_eq!(hashes.count(&obj(3)), 2);
        assert_eq!(hashes.count(&obj(4)), 0);
        assert_eq!(hashes.binary_search(&obj(1)), Ok(0));
        assert_eq!(hashes.binary_search(&obj(7)), Ok(3));
        assert_eq!(hashes.binary_search(&obj(0)), Err(0));
        assert_eq!(hashes.binary_search(&obj(4)), Err(3));
        assert_eq!(hashes.binary_search(&obj(9)), Err(4));
    }

    #[test]
    fn containment_distinguishes_bags_from_sets() {
        let single = array(&[1, 2]);
        let double = array(&[2, 1, 1]);
        assert!(single.as_hashes().is_subset_of(double.as_hashes()));
        assert!(double.as_hashes().is_subset_of(single.as_hashes()));
        assert!(single.as_hashes().is_subbag_of(double.as_hashes()));
        assert!(!double.as_hashes().is_subbag_of(single.as_hashes()));

        assert!(single.as_hashes().set_eq(double.as_hashes()));
        assert!(!single.as_hashes().bag_eq(double.as_hashes()));
        assert!(
            array(&[1, 2])
                .as_hashes()
                .bag_eq(array(&[2, 1]).as_hashes())
        );
        assert!(
            !array(&[1])
                .as_hashes()
                .is_subbag_of(array(&[2]).as_hashes())
        );
        assert!(array(&[]).as_hashes().is_subbag_of(single.as_hashes()));
    }

    #[test]
    fn indexed_relations_name_null_semantics_explicitly() {
        let sparse = array(&[1, 0, 3]);
        let filled = array(&[1, 2, 3]);
        let incompatible = array(&[9, 2, 3]);
        assert!(
            sparse
                .as_hashes()
                .is_sparse_refinement_of(filled.as_hashes())
        );
        assert!(
            !filled
                .as_hashes()
                .is_sparse_refinement_of(sparse.as_hashes())
        );
        assert!(
            !sparse
                .as_hashes()
                .is_sparse_refinement_of(incompatible.as_hashes())
        );
        assert!(
            array(&[1, 0])
                .as_hashes()
                .has_disjoint_support_with(array(&[0, 2]).as_hashes())
        );
        assert!(
            !array(&[1])
                .as_hashes()
                .has_disjoint_support_with(array(&[2]).as_hashes())
        );
        assert!(
            !array(&[0])
                .as_hashes()
                .is_sparse_refinement_of(array(&[0, 1]).as_hashes())
        );
    }

    #[test]
    fn set_algebra_is_sorted_distinct_and_keeps_null() {
        let left = array(&[3, 0, 1, 1]);
        let right = array(&[2, 0, 3, 3]);
        assert_eq!(left.as_hashes().canonical_set(), array(&[0, 1, 3]));
        assert_eq!(
            left.as_hashes().set_union(right.as_hashes()),
            array(&[0, 1, 2, 3])
        );
        assert_eq!(
            left.as_hashes().set_intersection(right.as_hashes()),
            array(&[0, 3])
        );
        assert_eq!(
            left.as_hashes().set_difference(right.as_hashes()),
            array(&[1])
        );
        assert_eq!(
            left.as_hashes().set_symmetric_difference(right.as_hashes()),
            array(&[1, 2])
        );
        assert_eq!(HashArray::singleton(obj(0)), array(&[0]));
    }

    #[test]
    fn bag_algebra_has_explicit_multiplicity_laws() {
        let left = array(&[2, 0, 1, 1]);
        let right = array(&[0, 1, 2, 2]);
        assert_eq!(left.as_hashes().canonical_bag(), array(&[0, 1, 1, 2]));
        assert_eq!(
            left.as_hashes().bag_union_max(right.as_hashes()),
            array(&[0, 1, 1, 2, 2])
        );
        assert_eq!(
            left.as_hashes().bag_sum(right.as_hashes()),
            array(&[0, 0, 1, 1, 1, 2, 2, 2])
        );
        assert_eq!(
            left.as_hashes().bag_intersection(right.as_hashes()),
            array(&[0, 1, 2])
        );
        assert_eq!(
            left.as_hashes().bag_difference(right.as_hashes()),
            array(&[1])
        );
        assert_eq!(
            left.as_hashes().bag_symmetric_difference(right.as_hashes()),
            array(&[1, 2])
        );
    }

    #[test]
    fn building_sorts_deduplicates_and_pops() {
        let mut values = array(&[3, 1, 3, 2]);
        values.sort();
        assert_eq!(values, array(&[1, 2, 3, 3]));
        values.dedup();
        assert_eq!(values, array(&[1, 2, 3]));

        let mut values = array(&[3, 1, 3, 2]);
        values.sort_dedup();
        assert_eq!(values, array(&[1, 2, 3]));
        assert!(values.as_hashes().flat_set().is_ok());

        let mut values = array(&[1, 2]);
        assert_eq!(values.pop(), Some(obj(2)));
        assert_eq!(values, array(&[1]));
        values.push(obj(9));
        assert_eq!(values, array(&[1, 9]));
        values.truncate(1);
        assert_eq!(values, array(&[1]));
        values.truncate(7);
        assert_eq!(values, array(&[1]));
        values.clear();
        assert!(values.is_empty());
        assert_eq!(values.pop(), None);
    }

    #[test]
    fn debug_renders_elements_as_hexadecimal() {
        let rendered = format!("{:?}", array(&[0xab]));
        assert_eq!(rendered, format!("[{}]", "ab".repeat(32)));
    }
}
