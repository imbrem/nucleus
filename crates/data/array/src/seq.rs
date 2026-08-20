//! Flat O256 sequences.

use std::{fmt, slice::SliceIndex};

use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use snafu::Snafu;
use zerocopy::{FromBytes, IntoBytes};

/// O256 width in bytes.
pub const WIDTH: usize = 32;

/// A noncanonical byte length.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("expected a multiple of {WIDTH} bytes, found {len}"))]
pub struct WidthError {
    /// Actual byte length.
    pub len: usize,
}

/// An O256 sequence backed by `V`.
#[repr(transparent)]
#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HashSeq<V = Vec<O256>>(V);

/// A borrowed hash sequence.
pub type HashSeqRef<'a> = HashSeq<&'a [O256]>;

impl<V> HashSeq<V> {
    /// Wraps `storage`.
    #[must_use]
    pub const fn new(storage: V) -> Self {
        Self(storage)
    }

    /// Returns the backing storage.
    #[must_use]
    pub fn into_storage(self) -> V {
        self.0
    }
}

impl<V: AsRef<[O256]>> HashSeq<V> {
    /// Returns the elements.
    #[must_use]
    pub fn as_slice(&self) -> &[O256] {
        self.0.as_ref()
    }

    /// Returns the bare concatenation of element bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.as_slice().as_bytes()
    }

    /// Returns the number of elements.
    #[must_use]
    pub fn len(&self) -> usize {
        self.as_slice().len()
    }

    /// Returns whether there are no elements.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.as_slice().is_empty()
    }

    /// Returns the element at `index`.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<O256> {
        self.as_slice().get(index).copied()
    }

    /// Returns the first element.
    #[must_use]
    pub fn first(&self) -> Option<O256> {
        self.as_slice().first().copied()
    }

    /// Returns the last element.
    #[must_use]
    pub fn last(&self) -> Option<O256> {
        self.as_slice().last().copied()
    }

    /// Iterates over copied elements.
    #[must_use]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = O256> + ExactSizeIterator + '_ {
        self.as_slice().iter().copied()
    }

    /// Returns a borrowed checked element subrange.
    #[must_use]
    pub fn slice<I>(&self, index: I) -> Option<HashSeqRef<'_>>
    where
        I: SliceIndex<[O256], Output = [O256]>,
    {
        self.as_slice().get(index).map(HashSeq::new)
    }

    /// Splits into borrowed views before and from `index`.
    #[must_use]
    pub fn split_at(&self, index: usize) -> Option<(HashSeqRef<'_>, HashSeqRef<'_>)> {
        let (left, right) = self.as_slice().split_at_checked(index)?;
        Some((HashSeq::new(left), HashSeq::new(right)))
    }

    /// Returns whether `value` occurs.
    #[must_use]
    pub fn contains(&self, value: &O256) -> bool {
        self.as_slice().contains(value)
    }

    /// Returns the first position of `value`.
    #[must_use]
    pub fn position(&self, value: &O256) -> Option<usize> {
        self.as_slice()
            .iter()
            .position(|candidate| candidate == value)
    }

    /// Returns the number of occurrences of `value`.
    #[must_use]
    pub fn count(&self, value: &O256) -> usize {
        self.as_slice()
            .iter()
            .filter(|candidate| *candidate == value)
            .count()
    }
}

impl<'a> HashSeq<&'a [O256]> {
    /// Casts canonical bytes without copying.
    ///
    /// # Errors
    ///
    /// Returns [`WidthError`] unless `bytes.len()` is a multiple of 32.
    pub fn from_bytes(bytes: &'a [u8]) -> Result<Self, WidthError> {
        let values =
            <[O256]>::ref_from_bytes(bytes).map_err(|_| WidthError { len: bytes.len() })?;
        Ok(Self::new(values))
    }

    /// Returns the empty borrowed sequence.
    #[must_use]
    pub const fn empty() -> Self {
        Self::new(&[])
    }
}

impl HashSeq<Vec<O256>> {
    /// Copies canonical bytes into owned storage.
    ///
    /// # Errors
    ///
    /// Returns [`WidthError`] unless `bytes.len()` is a multiple of 32.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, WidthError> {
        Ok(Self::new(
            HashSeq::<&[O256]>::from_bytes(bytes)?.as_slice().to_vec(),
        ))
    }

    /// Creates the one-element sequence.
    #[must_use]
    pub fn singleton(value: O256) -> Self {
        Self::new(vec![value])
    }

    /// Creates an empty sequence with element capacity.
    #[must_use]
    pub fn with_capacity(elements: usize) -> Self {
        Self::new(Vec::with_capacity(elements))
    }

    /// Appends an element.
    pub fn push(&mut self, value: O256) {
        self.0.push(value);
    }

    /// Removes and returns the last element.
    pub fn pop(&mut self) -> Option<O256> {
        self.0.pop()
    }

    /// Removes every element.
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Shortens the sequence to at most `elements` elements.
    pub fn truncate(&mut self, elements: usize) {
        self.0.truncate(elements);
    }
}

impl<V: AsRef<[O256]>> std::ops::Deref for HashSeq<V> {
    type Target = [O256];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<V: AsRef<[O256]>> fmt::Debug for HashSeq<V> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_list()
            .entries(self.as_slice().iter().map(Hex))
            .finish()
    }
}

struct Hex<'a>(&'a O256);

impl fmt::Debug for Hex<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0.hex())
    }
}

impl From<Vec<O256>> for HashSeq {
    fn from(values: Vec<O256>) -> Self {
        Self::new(values)
    }
}

impl From<HashSeq<&[O256]>> for HashSeq {
    fn from(values: HashSeq<&[O256]>) -> Self {
        Self::new(values.as_slice().to_vec())
    }
}

impl FromIterator<O256> for HashSeq {
    fn from_iter<I: IntoIterator<Item = O256>>(values: I) -> Self {
        Self::new(values.into_iter().collect())
    }
}

impl Extend<O256> for HashSeq {
    fn extend<I: IntoIterator<Item = O256>>(&mut self, values: I) {
        self.0.extend(values);
    }
}

impl IntoIterator for HashSeq {
    type Item = O256;
    type IntoIter = std::vec::IntoIter<O256>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, V: AsRef<[O256]>> IntoIterator for &'a HashSeq<V> {
    type Item = &'a O256;
    type IntoIter = std::slice::Iter<'a, O256>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::O256;

    use super::{HashSeq, WIDTH, WidthError};

    fn obj(byte: u8) -> O256 {
        O256::from_array([byte; WIDTH])
    }

    fn array(bytes: &[u8]) -> HashSeq {
        bytes.iter().copied().map(obj).collect()
    }

    #[test]
    fn checked_bytes_borrow_as_typed_elements() {
        let values = array(&[3, 1, 2]);
        let borrowed = HashSeq::<&[O256]>::from_bytes(values.as_bytes()).unwrap();
        assert_eq!(borrowed.as_slice(), values.as_slice());
        assert_eq!(borrowed.as_bytes(), values.as_bytes());
        assert_eq!(borrowed.get(1), Some(obj(1)));
        assert_eq!(
            HashSeq::<&[O256]>::from_bytes(&[0; 31]),
            Err(WidthError { len: 31 })
        );
    }

    #[test]
    fn storage_is_generic_but_sequence_methods_are_shared() {
        let vector = array(&[3, 1, 1]);
        let boxed = HashSeq::new(vector.as_slice().to_vec().into_boxed_slice());
        let borrowed = HashSeq::new(vector.as_slice());
        assert_eq!(vector.count(&obj(1)), 2);
        assert_eq!(boxed.count(&obj(1)), 2);
        assert_eq!(borrowed.count(&obj(1)), 2);
        assert_eq!(vector.as_bytes(), boxed.as_bytes());
    }

    #[test]
    fn owned_storage_has_vec_like_mutation() {
        let mut values = array(&[3, 1, 1]);
        values.push(obj(2));
        assert_eq!(values.pop(), Some(obj(2)));
        values.truncate(2);
        assert_eq!(values.into_storage(), vec![obj(3), obj(1)]);
    }

    #[test]
    fn slices_and_splits_are_element_indexed() {
        let values = array(&[0, 1, 2, 3]);
        assert_eq!(values.slice(1..3).unwrap().as_slice(), &[obj(1), obj(2)]);
        assert_eq!(values.slice(0..5), None);
        let (left, right) = values.split_at(2).unwrap();
        assert_eq!(left.as_slice(), &[obj(0), obj(1)]);
        assert_eq!(right.as_slice(), &[obj(2), obj(3)]);
    }

    #[test]
    fn byte_layout_is_bare_concatenation() {
        let values = array(&[1, 2]);
        assert_eq!(values.as_bytes().len(), 2 * WIDTH);
        assert_eq!(&values.as_bytes()[..WIDTH], &[1; WIDTH]);
        assert_eq!(&values.as_bytes()[WIDTH..], &[2; WIDTH]);
        assert!(HashSeq::<&[O256]>::empty().is_empty());
        assert_eq!(HashSeq::singleton(obj(0)), array(&[0]));
    }
}
