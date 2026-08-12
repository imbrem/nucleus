//! JSON objects with their invariant carried by construction.
//!
//! A [`Map`] is a slice of entries sorted strictly by key: sorted so that
//! serialization is canonical without a pass over the data, and strictly so
//! that duplicate keys — which RFC 8259 merely discourages and I-JSON
//! (RFC 7493) forbids — cannot be represented at all. Everything that makes a
//! `Map` checks this, so everything that has one may rely on it.

use std::fmt;

use crate::{Build, Index, Json};

/// One `key: value` pair of a JSON object.
pub struct Entry<I: Index> {
    /// The key. [`Map`] keeps entries sorted and unique by this.
    pub key: I::Str,
    /// The value.
    pub value: Json<I>,
}

impl<I: Index> Entry<I> {
    /// The key as a plain string slice.
    #[must_use]
    pub fn key(&self) -> &str {
        &self.key
    }
}

impl<I: Index> Clone for Entry<I> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            value: self.value.clone(),
        }
    }
}

impl<I: Index, J: Index> PartialEq<Entry<J>> for Entry<I> {
    fn eq(&self, other: &Entry<J>) -> bool {
        (crate::order::same_str(&self.key, &other.key) || *self.key == *other.key)
            && self.value == other.value
    }
}

impl<I: Index> Eq for Entry<I> {}

impl<I: Index> fmt::Debug for Entry<I> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Entry")
            .field("key", &&*self.key)
            .field("value", &self.value)
            .finish()
    }
}

/// A JSON object: entries sorted strictly by key.
///
/// The invariant is established by every constructor and never rechecked, so
/// lookup is a binary search and serialization emits canonical key order by
/// walking the entries as they are.
pub struct Map<I: Index>(I::Entries);

/// Why a sequence of entries is not a [`Map`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MapError {
    /// The same key appeared more than once.
    Duplicate {
        /// The repeated key.
        key: String,
    },
    /// Entries handed over as already-sorted were not sorted.
    Unsorted {
        /// The index of the first entry smaller than its predecessor.
        index: usize,
    },
}

impl fmt::Display for MapError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Duplicate { key } => write!(formatter, "duplicate object key {key:?}"),
            Self::Unsorted { index } => {
                write!(formatter, "object entry {index} is out of order")
            }
        }
    }
}

impl std::error::Error for MapError {}

impl<I: Index> Map<I> {
    /// Wraps entries that are already sorted strictly by key, checking that
    /// they are.
    ///
    /// This is the constructor available to borrowed families such as
    /// [`Refs`](crate::Refs), which cannot allocate a sorted copy; the check
    /// is one ordered pass.
    ///
    /// # Errors
    ///
    /// [`MapError::Unsorted`] if an entry is smaller than its predecessor, and
    /// [`MapError::Duplicate`] if it is equal to it.
    pub fn from_sorted(entries: I::Entries) -> Result<Self, MapError> {
        for (index, window) in entries.windows(2).enumerate() {
            match (*window[0].key).cmp(&window[1].key) {
                std::cmp::Ordering::Less => {}
                std::cmp::Ordering::Equal => {
                    return Err(MapError::Duplicate {
                        key: window[1].key.to_string(),
                    });
                }
                std::cmp::Ordering::Greater => {
                    return Err(MapError::Unsorted { index: index + 1 });
                }
            }
        }
        Ok(Self(entries))
    }

    /// The entries, sorted strictly by key.
    #[must_use]
    pub fn entries(&self) -> &[Entry<I>] {
        &self.0
    }

    /// The value under `key`, if any.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&Json<I>> {
        let entries = self.entries();
        entries
            .binary_search_by(|entry| (*entry.key).cmp(key))
            .ok()
            .map(|index| &entries[index].value)
    }

    /// Whether `key` is present.
    #[must_use]
    pub fn contains_key(&self, key: &str) -> bool {
        self.get(key).is_some()
    }

    /// The number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries().len()
    }

    /// Whether the object is `{}`.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries().is_empty()
    }

    /// The entries in key order.
    pub fn iter(&self) -> std::slice::Iter<'_, Entry<I>> {
        self.entries().iter()
    }

    /// The keys in order.
    pub fn keys(&self) -> impl Iterator<Item = &str> {
        self.iter().map(Entry::key)
    }

    /// The values in key order.
    pub fn values(&self) -> impl Iterator<Item = &Json<I>> {
        self.iter().map(|entry| &entry.value)
    }
}

impl<I: Build> Map<I> {
    /// Builds a map from entries in any order.
    ///
    /// # Errors
    ///
    /// [`MapError::Duplicate`] if two entries share a key.
    pub fn from_entries(mut entries: Vec<Entry<I>>) -> Result<Self, MapError> {
        entries.sort_by(|left, right| (*left.key).cmp(&right.key));
        if let Some(window) = entries.windows(2).find(|w| *w[0].key == *w[1].key) {
            return Err(MapError::Duplicate {
                key: window[0].key.to_string(),
            });
        }
        Ok(Self(I::entries(entries)))
    }

    /// Builds a map from entries whose keys are known to be distinct, such as
    /// another map's.
    ///
    /// Sorts, then trusts distinctness rather than re-verifying it; a caller
    /// that cannot vouch for its keys wants [`Map::from_entries`].
    pub(crate) fn from_unique(mut entries: Vec<Entry<I>>) -> Self {
        entries.sort_by(|left, right| (*left.key).cmp(&right.key));
        debug_assert!(entries.windows(2).all(|w| *w[0].key < *w[1].key));
        Self(I::entries(entries))
    }
}

impl<'a, I: Index> IntoIterator for &'a Map<I> {
    type Item = &'a Entry<I>;
    type IntoIter = std::slice::Iter<'a, Entry<I>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<I: Index> Clone for Map<I> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<I: Index, J: Index> PartialEq<Map<J>> for Map<I> {
    fn eq(&self, other: &Map<J>) -> bool {
        crate::order::same_slice(self.entries(), other.entries())
            || (self.len() == other.len()
                && self
                    .iter()
                    .zip(other.iter())
                    .all(|(left, right)| left == right))
    }
}

impl<I: Index> Eq for Map<I> {}

impl<I: Index> fmt::Debug for Map<I> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_map()
            .entries(self.iter().map(|entry| (&*entry.key, &entry.value)))
            .finish()
    }
}
