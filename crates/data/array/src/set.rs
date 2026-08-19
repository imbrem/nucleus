//! Flat sets: hash arrays read as sets.
//!
//! A flat set is a hash array whose elements are strictly ascending. That is
//! the whole representation — the normal form is the array's, so a set costs
//! nothing beyond the invariant, and any blob can be checked in a linear scan.

use std::{cmp::Ordering, fmt};

use covalence_lib_error::snafu;
use covalence_lib_hash::{Cov, Namespace, Obj};
use snafu::Snafu;

use crate::{HashArray, Hashes, Iter, width};

/// A hash array that was not strictly ascending.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum OrderError {
    /// An element was smaller than its predecessor.
    #[snafu(display("element {index} is smaller than its predecessor"))]
    Unsorted {
        /// The offending element's position.
        index: usize,
    },
    /// An element repeated its predecessor.
    #[snafu(display("element {index} repeats its predecessor"))]
    Duplicate {
        /// The offending element's position.
        index: usize,
    },
}

/// A borrowed flat set: a strictly ascending hash array.
pub struct FlatSet<'a, N: Namespace = Cov> {
    hashes: Hashes<'a, N>,
}

impl<'a, N: Namespace> FlatSet<'a, N> {
    /// Reads a hash array as a flat set.
    ///
    /// # Errors
    ///
    /// Returns an error unless the elements are strictly ascending, naming the
    /// first position that breaks the invariant.
    pub fn new(hashes: Hashes<'a, N>) -> Result<Self, OrderError> {
        let mut previous: Option<&[u8]> = None;
        for (index, chunk) in hashes.as_bytes().chunks_exact(width::<N>()).enumerate() {
            match previous.map(|previous| chunk.cmp(previous)) {
                Some(Ordering::Less) => return Err(OrderError::Unsorted { index }),
                Some(Ordering::Equal) => return Err(OrderError::Duplicate { index }),
                _ => previous = Some(chunk),
            }
        }
        Ok(Self { hashes })
    }

    /// Returns the empty set.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            hashes: Hashes::empty(),
        }
    }

    /// Borrows the underlying array.
    #[must_use]
    pub const fn hashes(&self) -> Hashes<'a, N> {
        self.hashes
    }

    /// Borrows the normal form.
    #[must_use]
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.hashes.as_bytes()
    }

    /// Returns the number of elements.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.hashes.len()
    }

    /// Returns whether the set is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.hashes.is_empty()
    }

    /// Returns the element at `index` in ascending order.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<Obj<N>> {
        self.hashes.get(index)
    }

    /// Iterates over the elements in ascending order.
    #[must_use]
    pub fn iter(&self) -> Iter<'a, N> {
        self.hashes.iter()
    }

    /// Returns whether `value` is a member, in logarithmic time.
    #[must_use]
    pub fn contains(&self, value: &Obj<N>) -> bool {
        self.hashes.binary_search(value).is_ok()
    }

    /// Returns `value`'s rank, or where it would be inserted.
    ///
    /// # Errors
    ///
    /// Returns the insertion position if `value` is not a member.
    pub fn rank(&self, value: &Obj<N>) -> Result<usize, usize> {
        self.hashes.binary_search(value)
    }

    /// Returns whether every element is a member of `other`.
    #[must_use]
    pub fn is_subset_of(&self, other: FlatSet<'_, N>) -> bool {
        let mut other = other.iter();
        self.iter()
            .all(|value| other.any(|candidate| candidate == value))
    }

    /// Returns whether the sets share no element.
    #[must_use]
    pub fn is_disjoint_from(&self, other: FlatSet<'_, N>) -> bool {
        !self.iter().any(|value| other.contains(&value))
    }

    /// Returns the elements of either set, in canonical form.
    #[must_use]
    pub fn union(&self, other: FlatSet<'_, N>) -> HashArray<N> {
        let mut result = HashArray::with_capacity(self.len().saturating_add(other.len()));
        let mut left = self.iter().peekable();
        let mut right = other.iter().peekable();
        loop {
            let order = match (left.peek(), right.peek()) {
                (Some(first), Some(second)) => first.cmp(second),
                (Some(_), None) => Ordering::Less,
                (None, Some(_)) => Ordering::Greater,
                (None, None) => break,
            };
            match order {
                Ordering::Less => result.extend(left.next()),
                Ordering::Greater => result.extend(right.next()),
                Ordering::Equal => {
                    result.extend(left.next());
                    right.next();
                }
            }
        }
        result
    }

    /// Returns the elements of both sets, in canonical form.
    #[must_use]
    pub fn intersection(&self, other: FlatSet<'_, N>) -> HashArray<N> {
        let mut result = HashArray::with_capacity(self.len().min(other.len()));
        let mut left = self.iter().peekable();
        let mut right = other.iter().peekable();
        while let (Some(first), Some(second)) = (left.peek(), right.peek()) {
            match first.cmp(second) {
                Ordering::Less => {
                    left.next();
                }
                Ordering::Greater => {
                    right.next();
                }
                Ordering::Equal => {
                    result.extend(left.next());
                    right.next();
                }
            }
        }
        result
    }

    /// Returns the elements of this set absent from `other`, in canonical form.
    #[must_use]
    pub fn difference(&self, other: FlatSet<'_, N>) -> HashArray<N> {
        let mut result = HashArray::with_capacity(self.len());
        let mut left = self.iter().peekable();
        let mut right = other.iter().peekable();
        loop {
            let order = match (left.peek(), right.peek()) {
                (Some(first), Some(second)) => first.cmp(second),
                (Some(_), None) => Ordering::Less,
                (None, _) => break,
            };
            match order {
                Ordering::Less => result.extend(left.next()),
                Ordering::Greater => {
                    right.next();
                }
                Ordering::Equal => {
                    left.next();
                    right.next();
                }
            }
        }
        result
    }

    /// Returns elements belonging to exactly one set, in canonical form.
    #[must_use]
    pub fn symmetric_difference(&self, other: FlatSet<'_, N>) -> HashArray<N> {
        self.hashes.set_symmetric_difference(other.hashes)
    }
}

impl<N: Namespace> Copy for FlatSet<'_, N> {}
impl<N: Namespace> Clone for FlatSet<'_, N> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<N: Namespace> Default for FlatSet<'_, N> {
    fn default() -> Self {
        Self::empty()
    }
}
impl<N: Namespace> PartialEq for FlatSet<'_, N> {
    fn eq(&self, other: &Self) -> bool {
        self.hashes == other.hashes
    }
}
impl<N: Namespace> Eq for FlatSet<'_, N> {}
impl<N: Namespace> fmt::Debug for FlatSet<'_, N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.hashes, formatter)
    }
}

impl<'a, N: Namespace> IntoIterator for FlatSet<'a, N> {
    type Item = Obj<N>;
    type IntoIter = Iter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, N: Namespace> IntoIterator for &FlatSet<'a, N> {
    type Item = Obj<N>;
    type IntoIter = Iter<'a, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::{Cov, O256};

    use super::{FlatSet, OrderError};
    use crate::HashArray;

    fn obj(byte: u8) -> O256 {
        O256::from_array([byte; 32])
    }

    fn array(bytes: &[u8]) -> HashArray {
        bytes.iter().copied().map(obj).collect()
    }

    #[test]
    fn only_strictly_ascending_arrays_are_sets() {
        let ascending = array(&[1, 2, 3]);
        assert!(ascending.as_hashes().flat_set().is_ok());

        let descending = array(&[2, 1]);
        assert_eq!(
            descending.as_hashes().flat_set(),
            Err(OrderError::Unsorted { index: 1 })
        );

        let repeated = array(&[1, 1]);
        assert_eq!(
            repeated.as_hashes().flat_set(),
            Err(OrderError::Duplicate { index: 1 })
        );

        let empty = array(&[]);
        assert!(empty.as_hashes().flat_set().unwrap().is_empty());
        assert_eq!(FlatSet::<Cov>::default().len(), 0);
    }

    #[test]
    fn a_set_shares_the_arrays_normal_form() {
        let values = array(&[1, 2, 3]);
        let set = values.as_hashes().flat_set().unwrap();
        assert_eq!(set.as_bytes(), values.as_bytes());
        assert_eq!(set.hashes(), values.as_hashes());
        assert_eq!(set.len(), 3);
        assert_eq!(set.get(1), Some(obj(2)));
        assert_eq!(set.iter().collect::<Vec<_>>(), vec![obj(1), obj(2), obj(3)]);
    }

    #[test]
    fn membership_is_logarithmic() {
        let values = array(&[1, 3, 5]);
        let set = values.as_hashes().flat_set().unwrap();
        assert!(set.contains(&obj(3)));
        assert!(!set.contains(&obj(4)));
        assert_eq!(set.rank(&obj(5)), Ok(2));
        assert_eq!(set.rank(&obj(4)), Err(2));
    }

    #[test]
    fn merges_produce_canonical_sets() {
        let (first, second) = (array(&[1, 3, 5]), array(&[3, 4]));
        let left = first.as_hashes().flat_set().unwrap();
        let right = second.as_hashes().flat_set().unwrap();

        assert_eq!(left.union(right), array(&[1, 3, 4, 5]));
        assert_eq!(left.intersection(right), array(&[3]));
        assert_eq!(left.difference(right), array(&[1, 5]));
        assert_eq!(right.difference(left), array(&[4]));
        assert_eq!(left.symmetric_difference(right), array(&[1, 4, 5]));

        for merged in [
            left.union(right),
            left.intersection(right),
            left.difference(right),
        ] {
            assert!(merged.as_hashes().flat_set().is_ok());
        }
    }

    #[test]
    fn merges_handle_exhausted_and_empty_sides() {
        let (first, second) = (array(&[1, 2]), array(&[]));
        let left = first.as_hashes().flat_set().unwrap();
        let empty = second.as_hashes().flat_set().unwrap();

        assert_eq!(left.union(empty), array(&[1, 2]));
        assert_eq!(empty.union(left), array(&[1, 2]));
        assert_eq!(left.intersection(empty), array(&[]));
        assert_eq!(left.difference(empty), array(&[1, 2]));
        assert_eq!(empty.difference(left), array(&[]));
        assert!(left.is_disjoint_from(empty));
    }

    #[test]
    fn containment_agrees_with_the_merge_operations() {
        let (first, second) = (array(&[1, 3]), array(&[1, 2, 3]));
        let left = first.as_hashes().flat_set().unwrap();
        let right = second.as_hashes().flat_set().unwrap();

        assert!(left.is_subset_of(right));
        assert!(!right.is_subset_of(left));
        assert!(left.is_subset_of(left));
        assert!(!left.is_disjoint_from(right));
        assert_eq!(left.difference(right).len(), 0);
    }
}
