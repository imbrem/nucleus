//! Non-overlapping maps over half-open integer ranges.
//!
//! [`SegmentMap`] stores one namespace. [`KeyedSegmentMap`] partitions the
//! same invariant by key, which is useful for files, integer namespaces, and
//! other collections of independently addressed ranges.

use std::{
    collections::{BTreeMap, btree_map},
    error::Error,
    fmt,
    ops::Bound,
};

/// A checked, non-empty half-open range.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentRange {
    lo: u64,
    hi: u64,
}

impl SegmentRange {
    /// Constructs `lo..hi`, rejecting empty and reversed ranges.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidRange`] unless `lo < hi`.
    pub const fn new(lo: u64, hi: u64) -> Result<Self, InvalidRange> {
        if lo < hi {
            Ok(Self { lo, hi })
        } else {
            Err(InvalidRange { lo, hi })
        }
    }

    /// Inclusive lower bound.
    #[must_use]
    pub const fn lo(self) -> u64 {
        self.lo
    }

    /// Exclusive upper bound.
    #[must_use]
    pub const fn hi(self) -> u64 {
        self.hi
    }

    /// Width of this range.
    #[must_use]
    pub const fn width(self) -> u64 {
        self.hi - self.lo
    }

    /// Returns whether `point` belongs to this range.
    #[must_use]
    pub const fn contains(self, point: u64) -> bool {
        self.lo <= point && point < self.hi
    }

    /// Returns whether this range overlaps `other`.
    #[must_use]
    pub const fn overlaps(self, other: Self) -> bool {
        self.lo < other.hi && other.lo < self.hi
    }
}

/// An empty or reversed range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvalidRange {
    /// Supplied lower endpoint.
    pub lo: u64,
    /// Supplied upper endpoint.
    pub hi: u64,
}

impl fmt::Display for InvalidRange {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "invalid half-open range {}..{}",
            self.lo, self.hi
        )
    }
}

impl Error for InvalidRange {}

/// Stable identity of a row while that exact segment remains in the map.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentId(u64);

impl SegmentId {
    /// Numeric representation, suitable for an `SQLite` integer key.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// One non-overlapping segment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Segment<V> {
    id: SegmentId,
    range: SegmentRange,
    value: V,
}

impl<V> Segment<V> {
    /// Stable identity of this exact segment.
    #[must_use]
    pub const fn id(&self) -> SegmentId {
        self.id
    }

    /// Covered half-open range.
    #[must_use]
    pub const fn range(&self) -> SegmentRange {
        self.range
    }

    /// Payload associated with the whole range.
    #[must_use]
    pub const fn value(&self) -> &V {
        &self.value
    }

    /// Consumes the segment and returns its payload.
    #[must_use]
    pub fn into_value(self) -> V {
        self.value
    }
}

/// A rejected insertion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InsertError {
    /// The new range intersects an existing segment.
    Overlap {
        /// Existing segment which blocks insertion.
        existing: SegmentId,
        /// Existing segment's range.
        range: SegmentRange,
    },
    /// No further stable IDs can be allocated.
    IdExhausted,
}

impl fmt::Display for InsertError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overlap { existing, range } => write!(
                formatter,
                "segment {} at {}..{} overlaps the requested range",
                existing.get(),
                range.lo(),
                range.hi()
            ),
            Self::IdExhausted => formatter.write_str("segment IDs exhausted"),
        }
    }
}

impl Error for InsertError {}

/// Result of replacing or removing a range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Surgery<V> {
    /// Complete old segments removed by the operation.
    pub removed: Vec<Segment<V>>,
    /// IDs of retained fragments and, for replacement, the new segment.
    pub inserted: Vec<SegmentId>,
}

/// Non-overlapping segments in one namespace.
#[derive(Clone, Debug)]
pub struct SegmentMap<V> {
    inner: KeyedSegmentMap<(), V>,
}

impl<V> Default for SegmentMap<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V> SegmentMap<V> {
    /// Constructs an empty map.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            inner: KeyedSegmentMap::new(),
        }
    }

    /// Number of segments.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether no segments are present.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Inserts a range if it does not overlap an existing segment.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::Overlap`] for intersecting geometry or
    /// [`InsertError::IdExhausted`] when no identity remains available.
    pub fn insert(&mut self, range: SegmentRange, value: V) -> Result<SegmentId, InsertError> {
        self.inner.insert((), range, value)
    }

    /// Segment containing `point`, if any.
    #[must_use]
    pub fn get(&self, point: u64) -> Option<&Segment<V>> {
        self.inner.get(&(), point)
    }

    /// Segment with this ID, if it has not been removed or split.
    #[must_use]
    pub fn get_id(&self, id: SegmentId) -> Option<&Segment<V>> {
        self.inner.get_id(id).map(|((), segment)| segment)
    }

    /// Segments intersecting `range`, in increasing range order.
    #[must_use]
    pub fn overlapping(&self, range: SegmentRange) -> Overlapping<'_, V> {
        self.inner.overlapping(&(), range)
    }

    /// Removes one exact segment by identity.
    pub fn remove(&mut self, id: SegmentId) -> Option<Segment<V>> {
        self.inner.remove(id).map(|((), segment)| segment)
    }

    /// Removes `range`, retaining left/right fragments made by `split`.
    ///
    /// Every affected old ID is retired, including when one fragment retains
    /// the old segment's complete payload semantics.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::IdExhausted`] if retained fragments cannot all
    /// receive fresh identities. The map is unchanged in that case.
    pub fn remove_range(
        &mut self,
        range: SegmentRange,
        split: impl FnMut(&Segment<V>, SegmentRange) -> V,
    ) -> Result<Surgery<V>, InsertError> {
        self.inner.remove_range(&(), range, split)
    }

    /// Replaces `range`, splitting every intersected old segment first.
    ///
    /// The operation validates ID capacity and all resulting geometry before
    /// mutating the map.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::IdExhausted`] if the replacement and retained
    /// fragments cannot all receive fresh identities. The map is unchanged in
    /// that case.
    pub fn replace(
        &mut self,
        range: SegmentRange,
        value: V,
        split: impl FnMut(&Segment<V>, SegmentRange) -> V,
    ) -> Result<Surgery<V>, InsertError> {
        self.inner.replace(&(), range, value, split)
    }
}

/// Non-overlapping segments partitioned by a key.
#[derive(Clone, Debug)]
pub struct KeyedSegmentMap<K, V> {
    by_key: BTreeMap<K, BTreeMap<u64, Segment<V>>>,
    by_id: BTreeMap<SegmentId, (K, u64)>,
    next_id: u64,
    len: usize,
}

impl<K, V> Default for KeyedSegmentMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> KeyedSegmentMap<K, V> {
    /// Constructs an empty keyed map.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            by_key: BTreeMap::new(),
            by_id: BTreeMap::new(),
            next_id: 1,
            len: 0,
        }
    }

    /// Number of segments across every key.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether no segments are present.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<K: Clone + Ord, V> KeyedSegmentMap<K, V> {
    /// Inserts a range if it does not overlap another range for `key`.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::Overlap`] for intersecting geometry under the
    /// same key, or [`InsertError::IdExhausted`] when identities are exhausted.
    pub fn insert(
        &mut self,
        key: K,
        range: SegmentRange,
        value: V,
    ) -> Result<SegmentId, InsertError> {
        if let Some(existing) = self.find_overlap(&key, range) {
            return Err(InsertError::Overlap {
                existing: existing.id,
                range: existing.range,
            });
        }
        let id = self.reserve_ids(1)?;
        self.insert_with_id(key, range, value, id);
        Ok(id)
    }

    /// Segment containing `point` for `key`, if any.
    #[must_use]
    pub fn get(&self, key: &K, point: u64) -> Option<&Segment<V>> {
        let segments = self.by_key.get(key)?;
        let (_, segment) = segments.range(..=point).next_back()?;
        segment.range.contains(point).then_some(segment)
    }

    /// Segment and key with this ID, if it remains present.
    #[must_use]
    pub fn get_id(&self, id: SegmentId) -> Option<(&K, &Segment<V>)> {
        let (key, lo) = self.by_id.get(&id)?;
        let segment = self.by_key.get(key)?.get(lo)?;
        Some((key, segment))
    }

    /// Segments for `key` intersecting `range`, in increasing range order.
    #[must_use]
    pub fn overlapping(&self, key: &K, range: SegmentRange) -> Overlapping<'_, V> {
        let Some(segments) = self.by_key.get(key) else {
            return Overlapping { inner: None };
        };
        let start = segments
            .range(..=range.lo)
            .next_back()
            .filter(|(_, segment)| segment.range.overlaps(range))
            .map_or(range.lo, |(&lo, _)| lo);
        Overlapping {
            inner: Some(segments.range((Bound::Included(start), Bound::Excluded(range.hi)))),
        }
    }

    /// Removes one exact segment by identity.
    pub fn remove(&mut self, id: SegmentId) -> Option<(K, Segment<V>)> {
        let (key, lo) = self.by_id.remove(&id)?;
        let segments = self.by_key.get_mut(&key)?;
        let segment = segments.remove(&lo)?;
        if segments.is_empty() {
            self.by_key.remove(&key);
        }
        self.len -= 1;
        Some((key, segment))
    }

    /// Removes `range` for `key`, retaining split fragments.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::IdExhausted`] before mutation if retained
    /// fragments cannot all receive fresh identities.
    pub fn remove_range(
        &mut self,
        key: &K,
        range: SegmentRange,
        split: impl FnMut(&Segment<V>, SegmentRange) -> V,
    ) -> Result<Surgery<V>, InsertError> {
        self.surgery(key, range, None, split)
    }

    /// Replaces `range` for `key`, retaining split fragments.
    ///
    /// # Errors
    ///
    /// Returns [`InsertError::IdExhausted`] before mutation if the replacement
    /// and retained fragments cannot all receive fresh identities.
    pub fn replace(
        &mut self,
        key: &K,
        range: SegmentRange,
        value: V,
        split: impl FnMut(&Segment<V>, SegmentRange) -> V,
    ) -> Result<Surgery<V>, InsertError> {
        self.surgery(key, range, Some(value), split)
    }

    fn surgery(
        &mut self,
        key: &K,
        range: SegmentRange,
        replacement: Option<V>,
        mut split: impl FnMut(&Segment<V>, SegmentRange) -> V,
    ) -> Result<Surgery<V>, InsertError> {
        let affected = self
            .overlapping(key, range)
            .map(|segment| segment.id)
            .collect::<Vec<_>>();
        let fragment_count = affected
            .iter()
            .map(|id| {
                let (_, segment) = self.get_id(*id).expect("overlap came from this map");
                usize::from(segment.range.lo < range.lo) + usize::from(range.hi < segment.range.hi)
            })
            .sum::<usize>();
        let insert_count = fragment_count + usize::from(replacement.is_some());
        let first_id = self.reserve_ids(insert_count)?;

        let mut removed = Vec::with_capacity(affected.len());
        for id in affected {
            let (_, segment) = self.remove(id).expect("overlap came from this map");
            removed.push(segment);
        }

        let mut planned = Vec::with_capacity(insert_count);
        for segment in &removed {
            if segment.range.lo < range.lo {
                let retained = SegmentRange {
                    lo: segment.range.lo,
                    hi: range.lo,
                };
                planned.push((retained, split(segment, retained)));
            }
            if range.hi < segment.range.hi {
                let retained = SegmentRange {
                    lo: range.hi,
                    hi: segment.range.hi,
                };
                planned.push((retained, split(segment, retained)));
            }
        }
        if let Some(value) = replacement {
            planned.push((range, value));
        }
        planned.sort_by_key(|(range, _)| range.lo);

        let mut inserted = Vec::with_capacity(planned.len());
        for (offset, (range, value)) in planned.into_iter().enumerate() {
            let id = SegmentId(first_id.0 + u64::try_from(offset).expect("IDs were reserved"));
            self.insert_with_id(key.clone(), range, value, id);
            inserted.push(id);
        }
        Ok(Surgery { removed, inserted })
    }

    fn find_overlap(&self, key: &K, range: SegmentRange) -> Option<&Segment<V>> {
        let segments = self.by_key.get(key)?;
        if let Some((_, previous)) = segments.range(..=range.lo).next_back()
            && previous.range.overlaps(range)
        {
            return Some(previous);
        }
        segments
            .range(range.lo..range.hi)
            .next()
            .map(|(_, segment)| segment)
    }

    fn reserve_ids(&mut self, count: usize) -> Result<SegmentId, InsertError> {
        let count = u64::try_from(count).map_err(|_| InsertError::IdExhausted)?;
        let first = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(count)
            .ok_or(InsertError::IdExhausted)?;
        Ok(SegmentId(first))
    }

    fn insert_with_id(&mut self, key: K, range: SegmentRange, value: V, id: SegmentId) {
        self.by_id.insert(id, (key.clone(), range.lo));
        self.by_key
            .entry(key)
            .or_default()
            .insert(range.lo, Segment { id, range, value });
        self.len += 1;
    }
}

/// Iterator over segments intersecting one requested range.
pub struct Overlapping<'a, V> {
    inner: Option<btree_map::Range<'a, u64, Segment<V>>>,
}

impl<'a, V> Iterator for Overlapping<'a, V> {
    type Item = &'a Segment<V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.as_mut()?.next().map(|(_, segment)| segment)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner
            .as_ref()
            .map_or((0, Some(0)), Iterator::size_hint)
    }
}

impl<V> std::iter::FusedIterator for Overlapping<'_, V> {}

/// Affine translation from one integer namespace into another.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Translation<N> {
    /// Source namespace.
    pub source: N,
    /// Source point corresponding to the target segment's lower endpoint.
    pub source_lo: u64,
}

impl<N> Translation<N> {
    /// Translates a target point known to belong to `target`.
    #[must_use]
    pub const fn translate(&self, target: SegmentRange, point: u64) -> Option<u64> {
        if !target.contains(point) {
            return None;
        }
        self.source_lo.checked_add(point - target.lo)
    }
}
