//! Source-independent incremental Merkle-tree caching.

use std::{
    collections::{BTreeSet, HashMap},
    convert::Infallible,
    fmt,
    ops::Range,
};

use crate::{
    Blake3Hash,
    blake3::{Blake3Cv, Blake3Merkle},
};

/// Index of an actual scheme leaf, before retention grouping.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LeafIndex(pub u64);

/// Retained-level geometry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Retention {
    /// Lowest retained level above actual leaves.
    pub start: u8,
    /// Additional levels omitted between retained levels.
    pub skip: u8,
}

impl Retention {
    /// Retains leaves and every binary parent level.
    pub const FULL: Self = Self { start: 0, skip: 0 };

    fn group_leaves(self) -> Option<u64> {
        1u64.checked_shl(u32::from(self.start))
    }

    fn retains(self, count: u64) -> bool {
        if !count.is_power_of_two() {
            return false;
        }
        let level = count.trailing_zeros();
        let start = u32::from(self.start);
        level >= start && (level - start).is_multiple_of(u32::from(self.skip) + 1)
    }
}

mod sealed {
    pub trait Geometry {}
}

/// Geometry shared by static and dynamic incremental trees.
pub trait TreeGeometry: sealed::Geometry + Clone {
    /// Logical byte length.
    fn bytes(&self) -> u64;
    /// Bytes represented by one actual leaf.
    fn leaf_bytes(&self) -> u64;
    /// Retained-level configuration.
    fn retention(&self) -> Retention;

    /// Number of actual leaves.
    fn leaves(&self) -> u64 {
        let bytes = self.bytes();
        let leaf_bytes = self.leaf_bytes();
        if bytes == 0 {
            0
        } else {
            bytes.div_ceil(leaf_bytes)
        }
    }
}

/// Validated runtime tree geometry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DynamicGeometry {
    bytes: u64,
    leaf_bytes: u64,
    retention: Retention,
}

impl DynamicGeometry {
    /// Constructs runtime geometry.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero leaf width or unsupported retention shift.
    pub fn new(bytes: u64, leaf_bytes: u64, retention: Retention) -> Result<Self, GeometryError> {
        if leaf_bytes == 0 {
            return Err(GeometryError::ZeroLeafBytes);
        }
        if retention.group_leaves().is_none() {
            return Err(GeometryError::RetentionTooDeep {
                start: retention.start,
            });
        }
        Ok(Self {
            bytes,
            leaf_bytes,
            retention,
        })
    }

    /// Returns this geometry with a different logical byte length.
    #[must_use]
    pub const fn with_bytes(self, bytes: u64) -> Self {
        Self { bytes, ..self }
    }
}

impl sealed::Geometry for DynamicGeometry {}
impl TreeGeometry for DynamicGeometry {
    fn bytes(&self) -> u64 {
        self.bytes
    }

    fn leaf_bytes(&self) -> u64 {
        self.leaf_bytes
    }

    fn retention(&self) -> Retention {
        self.retention
    }
}

/// Compile-time tree geometry.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StaticGeometry<const BYTES: u64, const LEAF_BYTES: u64, const START: u8, const SKIP: u8>;

impl<const BYTES: u64, const LEAF_BYTES: u64, const START: u8, const SKIP: u8> sealed::Geometry
    for StaticGeometry<BYTES, LEAF_BYTES, START, SKIP>
{
}

impl<const BYTES: u64, const LEAF_BYTES: u64, const START: u8, const SKIP: u8> TreeGeometry
    for StaticGeometry<BYTES, LEAF_BYTES, START, SKIP>
{
    fn bytes(&self) -> u64 {
        BYTES
    }

    fn leaf_bytes(&self) -> u64 {
        assert_ne!(LEAF_BYTES, 0, "static leaf width must be non-zero");
        LEAF_BYTES
    }

    fn retention(&self) -> Retention {
        Retention {
            start: START,
            skip: SKIP,
        }
    }
}

/// Geometry construction failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GeometryError {
    /// Leaves must represent at least one byte.
    ZeroLeafBytes,
    /// The lowest retained level cannot be represented.
    RetentionTooDeep { start: u8 },
}

impl fmt::Display for GeometryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroLeafBytes => formatter.write_str("leaf width must be non-zero"),
            Self::RetentionTooDeep { start } => {
                write!(formatter, "retention start depth {start} is too large")
            }
        }
    }
}

impl std::error::Error for GeometryError {}

/// Hashing operations needed by the incremental cache.
pub trait MerkleScheme {
    /// Cached non-root value.
    type Node: Clone;
    /// Externally meaningful root value.
    type Root: Clone;
    /// Evidence for one actual leaf.
    type Leaf: Clone;

    /// Extracts a non-root node from leaf evidence.
    fn leaf_node(&self, leaf: &Self::Leaf) -> Self::Node;
    /// Combines two child nodes into a non-root parent.
    fn merge(&self, left: Self::Node, right: Self::Node) -> Self::Node;
    /// Combines the final pair into a root.
    fn root(&self, left: Self::Node, right: Self::Node) -> Self::Root;
    /// Finalizes an empty tree.
    fn empty_root(&self) -> Self::Root;
    /// Finalizes a one-leaf tree when the evidence carries enough information.
    fn single_root(&self, leaf: &Self::Leaf) -> Option<Self::Root>;
}

/// BLAKE3 evidence for one actual chunk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Blake3Leaf {
    cv: Blake3Cv,
    single_root: Option<Blake3Hash>,
}

impl Blake3Leaf {
    /// Wraps a CV that is sufficient for multi-chunk trees.
    #[must_use]
    pub const fn from_cv(cv: Blake3Cv) -> Self {
        Self {
            cv,
            single_root: None,
        }
    }

    /// Hashes a non-empty positioned chunk.
    ///
    /// The standard root digest is retained when this is chunk zero, making
    /// the evidence sufficient for a one-chunk tree.
    ///
    /// # Panics
    ///
    /// Panics under the same invalid offset/length conditions as
    /// [`Blake3Cv::from_subtree`].
    #[must_use]
    pub fn from_chunk(index: LeafIndex, bytes: impl AsRef<[u8]>) -> Self {
        let bytes = bytes.as_ref();
        let offset = index.0 * blake3::CHUNK_LEN as u64;
        Self {
            cv: Blake3Cv::from_subtree(offset, bytes),
            single_root: (index.0 == 0).then(|| Blake3Hash::from_bytes(bytes)),
        }
    }

    /// Returns the chaining value.
    #[must_use]
    pub const fn cv(self) -> Blake3Cv {
        self.cv
    }
}

impl MerkleScheme for Blake3Merkle {
    type Node = Blake3Cv;
    type Root = Blake3Hash;
    type Leaf = Blake3Leaf;

    fn leaf_node(&self, leaf: &Self::Leaf) -> Self::Node {
        leaf.cv
    }

    fn merge(&self, left: Self::Node, right: Self::Node) -> Self::Node {
        left.merge(right)
    }

    fn root(&self, left: Self::Node, right: Self::Node) -> Self::Root {
        left.root(right)
    }

    fn empty_root(&self) -> Self::Root {
        Blake3Hash::from_bytes([])
    }

    fn single_root(&self, leaf: &Self::Leaf) -> Option<Self::Root> {
        leaf.single_root
    }
}

/// A batch of already-computed actual leaf values.
pub struct NewCvs<I>(pub I);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Span {
    start: u64,
    count: u64,
}

/// Source-independent incremental tree state.
#[derive(Clone)]
pub struct CvTree<G: TreeGeometry, S: MerkleScheme> {
    geometry: G,
    scheme: S,
    nodes: HashMap<Span, S::Node>,
    pending: HashMap<LeafIndex, S::Leaf>,
    dirty: BTreeSet<LeafIndex>,
    root: Option<S::Root>,
}

impl<G: TreeGeometry, S: MerkleScheme> CvTree<G, S> {
    /// Constructs a tree with every leaf awaiting initial evidence.
    #[must_use]
    pub fn new(geometry: G, scheme: S) -> Self {
        let dirty = (0..geometry.leaves()).map(LeafIndex).collect();
        Self {
            geometry,
            scheme,
            nodes: HashMap::new(),
            pending: HashMap::new(),
            dirty,
            root: None,
        }
    }

    /// Returns the geometry.
    #[must_use]
    pub const fn geometry(&self) -> &G {
        &self.geometry
    }

    /// Returns whether the tree has a cached clean root.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.root.is_some() && self.dirty.is_empty() && self.pending.is_empty()
    }

    /// Invalidates the lowest retained group containing `leaf`.
    ///
    /// # Errors
    ///
    /// Returns an error when the leaf is outside the geometry.
    pub fn dirty(&mut self, leaf: LeafIndex) -> Result<(), UpdateError> {
        if leaf.0 >= self.geometry.leaves() {
            return Err(UpdateError::LeafOutOfBounds {
                leaf,
                leaves: self.geometry.leaves(),
            });
        }
        let group = self
            .geometry
            .retention()
            .group_leaves()
            .ok_or(UpdateError::RetentionTooDeep)?;
        let start = leaf.0 / group * group;
        let end = start.saturating_add(group).min(self.geometry.leaves());
        self.invalidate(start..end);
        Ok(())
    }

    /// Invalidates every retained group touched by `range`.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reversed, or out-of-bounds range.
    pub fn dirty_range(&mut self, range: Range<LeafIndex>) -> Result<(), UpdateError> {
        if range.start >= range.end || range.end.0 > self.geometry.leaves() {
            return Err(UpdateError::InvalidRange {
                start: range.start,
                end: range.end,
                leaves: self.geometry.leaves(),
            });
        }
        let group = self
            .geometry
            .retention()
            .group_leaves()
            .ok_or(UpdateError::RetentionTooDeep)?;
        let start = range.start.0 / group * group;
        let end = range
            .end
            .0
            .div_ceil(group)
            .saturating_mul(group)
            .min(self.geometry.leaves());
        self.invalidate(start..end);
        Ok(())
    }

    /// Supplies already-computed leaf evidence.
    ///
    /// # Errors
    ///
    /// Returns an error when an update names an out-of-bounds leaf.
    pub fn update<I>(&mut self, values: NewCvs<I>) -> Result<(), UpdateError>
    where
        I: IntoIterator<Item = (LeafIndex, S::Leaf)>,
    {
        let values: Vec<_> = values.0.into_iter().collect();
        let leaves = self.geometry.leaves();
        let group = self
            .geometry
            .retention()
            .group_leaves()
            .ok_or(UpdateError::RetentionTooDeep)?;
        let mut groups = BTreeSet::new();
        for (index, _) in &values {
            if index.0 >= leaves {
                return Err(UpdateError::LeafOutOfBounds {
                    leaf: *index,
                    leaves,
                });
            }
            groups.insert(index.0 / group * group);
        }
        for start in groups {
            self.invalidate(start..start.saturating_add(group).min(leaves));
        }
        for (index, value) in values {
            self.pending.insert(index, value);
            self.dirty.remove(&index);
        }
        Ok(())
    }

    /// Returns actual leaves still needed to rebuild the tree.
    pub fn refill_frontier(&self) -> impl Iterator<Item = LeafIndex> + '_ {
        self.dirty
            .iter()
            .copied()
            .filter(|index| !self.pending.contains_key(index))
    }

    /// Rebuilds the root, requesting missing actual leaves from `source`.
    ///
    /// # Errors
    ///
    /// Returns a [`RebuildError::Leaf`] containing the exact failed index, or
    /// [`RebuildError::MissingSingleRoot`] when one-leaf evidence lacks the
    /// scheme-specific root output.
    pub fn try_root_with<E>(
        &mut self,
        mut source: impl FnMut(LeafIndex) -> Result<S::Leaf, E>,
    ) -> Result<S::Root, RebuildError<E>> {
        if self.is_clean()
            && let Some(root) = &self.root
        {
            return Ok(root.clone());
        }
        let leaves = self.geometry.leaves();
        let result = match leaves {
            0 => self.scheme.empty_root(),
            1 => {
                let leaf = self.leaf(LeafIndex(0), &mut source)?;
                self.scheme
                    .single_root(&leaf)
                    .ok_or(RebuildError::MissingSingleRoot)?
            }
            _ => {
                let left_count = left_subtree_leaves(leaves);
                let left = self.node(
                    Span {
                        start: 0,
                        count: left_count,
                    },
                    &mut source,
                )?;
                let right = self.node(
                    Span {
                        start: left_count,
                        count: leaves - left_count,
                    },
                    &mut source,
                )?;
                self.scheme.root(left, right)
            }
        };
        self.root = Some(result.clone());
        self.dirty.clear();
        self.pending.clear();
        Ok(result)
    }

    /// Infallible-source convenience for [`Self::try_root_with`].
    ///
    /// # Errors
    ///
    /// Returns [`RebuildError::MissingSingleRoot`] when necessary.
    pub fn root_with(
        &mut self,
        mut source: impl FnMut(LeafIndex) -> S::Leaf,
    ) -> Result<S::Root, RebuildError<Infallible>> {
        self.try_root_with(|index| Ok(source(index)))
    }

    fn leaf<E>(
        &self,
        index: LeafIndex,
        source: &mut impl FnMut(LeafIndex) -> Result<S::Leaf, E>,
    ) -> Result<S::Leaf, RebuildError<E>> {
        match self.pending.get(&index) {
            Some(value) => Ok(value.clone()),
            None => source(index).map_err(|source| RebuildError::Leaf { index, source }),
        }
    }

    fn node<E>(
        &mut self,
        span: Span,
        source: &mut impl FnMut(LeafIndex) -> Result<S::Leaf, E>,
    ) -> Result<S::Node, RebuildError<E>> {
        if self.retains(span.count)
            && let Some(value) = self.nodes.get(&span)
        {
            return Ok(value.clone());
        }
        let value = if span.count == 1 {
            let leaf = self.leaf(LeafIndex(span.start), source)?;
            self.scheme.leaf_node(&leaf)
        } else {
            let left_count = left_subtree_leaves(span.count);
            let left = self.node(
                Span {
                    start: span.start,
                    count: left_count,
                },
                source,
            )?;
            let right = self.node(
                Span {
                    start: span.start + left_count,
                    count: span.count - left_count,
                },
                source,
            )?;
            self.scheme.merge(left, right)
        };
        if self.retains(span.count) {
            self.nodes.insert(span, value.clone());
        }
        Ok(value)
    }

    fn retains(&self, count: u64) -> bool {
        self.geometry.retention().retains(count)
    }

    fn invalidate(&mut self, range: Range<u64>) {
        self.root = None;
        self.nodes
            .retain(|span, _| span.start + span.count <= range.start || span.start >= range.end);
        for index in range {
            let index = LeafIndex(index);
            self.pending.remove(&index);
            self.dirty.insert(index);
        }
    }
}

impl<S: MerkleScheme> CvTree<DynamicGeometry, S> {
    /// Changes the logical byte length and invalidates the changed right edge.
    #[must_use]
    pub fn resize(mut self, bytes: u64) -> Self {
        let old_leaves = self.geometry.leaves();
        self.geometry = self.geometry.with_bytes(bytes);
        let new_leaves = self.geometry.leaves();
        self.root = None;
        self.nodes
            .retain(|span, _| span.start + span.count <= new_leaves);
        self.pending.retain(|index, _| index.0 < new_leaves);
        self.dirty.retain(|index| index.0 < new_leaves);
        let frontier = old_leaves.min(new_leaves).saturating_sub(1);
        if new_leaves > 0 {
            let _ = self.dirty(LeafIndex(frontier.min(new_leaves - 1)));
        }
        if new_leaves > old_leaves {
            for index in old_leaves..new_leaves {
                self.dirty.insert(LeafIndex(index));
            }
        }
        self
    }

    /// Returns a resized clone, preserving the original tree.
    #[must_use]
    pub fn truncate_clone(&self, bytes: u64) -> Self
    where
        S: Clone,
    {
        self.clone().resize(bytes)
    }
}

/// A tree proven clean at wrapper construction time.
pub struct CleanTree<G: TreeGeometry, S: MerkleScheme>(CvTree<G, S>);

impl<G: TreeGeometry, S: MerkleScheme> CleanTree<G, S> {
    /// Returns the cached root without source access.
    ///
    /// # Panics
    ///
    /// Panics only if the private clean-wrapper invariant is violated.
    #[must_use]
    pub fn root(&self) -> &S::Root {
        self.0.root.as_ref().expect("clean-tree invariant")
    }

    /// Applies a leaf batch without exposing dirtying methods.
    ///
    /// # Errors
    ///
    /// Returns the potentially dirty tree when the supplied batch is
    /// incomplete or invalid.
    pub fn update<I>(self, values: NewCvs<I>) -> Result<Self, IncompleteUpdate<G, S>>
    where
        I: IntoIterator<Item = (LeafIndex, S::Leaf)>,
    {
        let mut tree = self.0;
        if tree.update(values).is_err() {
            return Err(IncompleteUpdate { tree });
        }
        match tree.try_root_with::<()>(|_| Err(())) {
            Ok(_) => Ok(Self(tree)),
            Err(_) => Err(IncompleteUpdate { tree }),
        }
    }
}

impl<G: TreeGeometry, S: MerkleScheme> From<CleanTree<G, S>> for CvTree<G, S> {
    fn from(value: CleanTree<G, S>) -> Self {
        value.0
    }
}

impl<G: TreeGeometry, S: MerkleScheme> TryFrom<CvTree<G, S>> for CleanTree<G, S> {
    type Error = CvTree<G, S>;

    fn try_from(value: CvTree<G, S>) -> Result<Self, Self::Error> {
        if value.is_clean() {
            Ok(Self(value))
        } else {
            Err(value)
        }
    }
}

/// An update that needs additional leaf evidence.
pub struct IncompleteUpdate<G: TreeGeometry, S: MerkleScheme> {
    /// Potentially dirty tree retaining the applied update.
    pub tree: CvTree<G, S>,
}

/// Update validation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UpdateError {
    /// Leaf index was outside the geometry.
    LeafOutOfBounds { leaf: LeafIndex, leaves: u64 },
    /// Leaf range was empty, reversed, or outside the geometry.
    InvalidRange {
        start: LeafIndex,
        end: LeafIndex,
        leaves: u64,
    },
    /// Retention start depth cannot be represented.
    RetentionTooDeep,
}

impl fmt::Display for UpdateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for UpdateError {}

/// Root reconstruction failure.
#[derive(Debug)]
pub enum RebuildError<E> {
    /// Leaf source failed.
    Leaf {
        /// Requested leaf.
        index: LeafIndex,
        /// Source error.
        source: E,
    },
    /// One-leaf evidence did not carry the scheme's root output.
    MissingSingleRoot,
}

impl<E: fmt::Display> fmt::Display for RebuildError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf { index, source } => {
                write!(formatter, "failed to load leaf {}: {source}", index.0)
            }
            Self::MissingSingleRoot => {
                formatter.write_str("one-leaf evidence lacks root finalization data")
            }
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for RebuildError<E> {}

fn left_subtree_leaves(leaves: u64) -> u64 {
    1 << (u64::BITS - 1 - (leaves - 1).leading_zeros())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(length: usize) -> Vec<u8> {
        (0u8..=250).cycle().take(length).collect()
    }

    fn leaf(input: &[u8], index: LeafIndex) -> Blake3Leaf {
        let start = usize::try_from(index.0).unwrap() * blake3::CHUNK_LEN;
        let end = (start + blake3::CHUNK_LEN).min(input.len());
        Blake3Leaf::from_chunk(index, &input[start..end])
    }

    fn tree(input: &[u8], retention: Retention) -> CvTree<DynamicGeometry, Blake3Merkle> {
        let geometry =
            DynamicGeometry::new(input.len() as u64, blake3::CHUNK_LEN as u64, retention).unwrap();
        CvTree::new(geometry, Blake3Merkle)
    }

    #[test]
    fn every_retention_geometry_matches_one_shot_blake3() {
        for length in [0, 1, 1_024, 1_025, 3_001, 16_385] {
            let input = bytes(length);
            let expected = Blake3Hash::from_bytes(&input);
            for start in 0..=3 {
                for skip in 0..=2 {
                    let mut tree = tree(&input, Retention { start, skip });
                    assert_eq!(
                        tree.root_with(|index| leaf(&input, index)).unwrap(),
                        expected,
                        "{length}, {start}, {skip}"
                    );
                    assert!(tree.is_clean());
                    assert_eq!(tree.refill_frontier().count(), 0);
                }
            }
        }
    }

    #[test]
    fn one_chunk_requires_explicit_root_evidence() {
        let input = bytes(73);
        let mut missing = tree(&input, Retention::FULL);
        assert!(matches!(
            missing.root_with(|index| Blake3Leaf::from_cv(leaf(&input, index).cv())),
            Err(RebuildError::MissingSingleRoot)
        ));

        let mut complete = tree(&input, Retention::FULL);
        assert_eq!(
            complete.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }

    #[test]
    fn dirtying_requests_only_the_lowest_retained_group() {
        let input = bytes(8 * blake3::CHUNK_LEN);
        let mut tree = tree(&input, Retention { start: 2, skip: 1 });
        tree.root_with(|index| leaf(&input, index)).unwrap();
        tree.dirty(LeafIndex(5)).unwrap();
        assert_eq!(
            tree.refill_frontier().collect::<Vec<_>>(),
            vec![LeafIndex(4), LeafIndex(5), LeafIndex(6), LeafIndex(7)]
        );

        let mut requested = Vec::new();
        let root = tree
            .root_with(|index| {
                requested.push(index);
                leaf(&input, index)
            })
            .unwrap();
        assert_eq!(root, Blake3Hash::from_bytes(input));
        assert_eq!(
            requested,
            vec![LeafIndex(4), LeafIndex(5), LeafIndex(6), LeafIndex(7)]
        );
    }

    #[test]
    fn callback_errors_report_the_leaf_and_are_retryable() {
        let input = bytes(3 * blake3::CHUNK_LEN);
        let mut tree = tree(&input, Retention::FULL);
        let error = tree
            .try_root_with(|index| {
                if index == LeafIndex(1) {
                    Err("offline")
                } else {
                    Ok(leaf(&input, index))
                }
            })
            .unwrap_err();
        assert!(matches!(
            error,
            RebuildError::Leaf {
                index: LeafIndex(1),
                source: "offline"
            }
        ));
        assert_eq!(
            tree.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }

    #[test]
    fn clean_wrapper_accepts_complete_cv_updates() {
        let mut input = bytes(4 * blake3::CHUNK_LEN);
        let mut raw = tree(&input, Retention::FULL);
        raw.root_with(|index| leaf(&input, index)).unwrap();
        let clean = CleanTree::try_from(raw).ok().unwrap();

        input[blake3::CHUNK_LEN..2 * blake3::CHUNK_LEN].fill(0xee);
        let changed = leaf(&input, LeafIndex(1));
        let clean = clean
            .update(NewCvs([(LeafIndex(1), changed)]))
            .ok()
            .unwrap();
        assert_eq!(clean.root(), &Blake3Hash::from_bytes(input));
    }

    #[test]
    fn dynamic_resize_and_truncate_clone_rebuild_the_right_frontier() {
        let input = bytes(5 * blake3::CHUNK_LEN);
        let mut original = tree(&input, Retention::FULL);
        original.root_with(|index| leaf(&input, index)).unwrap();

        let shorter_bytes = &input[..3 * blake3::CHUNK_LEN];
        let mut shorter = original.truncate_clone(shorter_bytes.len() as u64);
        assert_eq!(
            shorter
                .root_with(|index| leaf(shorter_bytes, index))
                .unwrap(),
            Blake3Hash::from_bytes(shorter_bytes)
        );
        assert_eq!(
            original.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }

    #[test]
    fn geometry_and_dirty_ranges_reject_invalid_inputs() {
        assert_eq!(
            DynamicGeometry::new(1, 0, Retention::FULL),
            Err(GeometryError::ZeroLeafBytes)
        );
        assert_eq!(
            DynamicGeometry::new(
                1,
                1,
                Retention {
                    start: u8::MAX,
                    skip: 0,
                },
            ),
            Err(GeometryError::RetentionTooDeep { start: u8::MAX })
        );

        let input = bytes(2 * blake3::CHUNK_LEN);
        let mut tree = tree(&input, Retention::FULL);
        assert!(matches!(
            tree.dirty(LeafIndex(2)),
            Err(UpdateError::LeafOutOfBounds { .. })
        ));
        assert!(matches!(
            tree.dirty_range(LeafIndex(1)..LeafIndex(1)),
            Err(UpdateError::InvalidRange { .. })
        ));
        assert!(matches!(
            tree.dirty_range(LeafIndex(1)..LeafIndex(3)),
            Err(UpdateError::InvalidRange { .. })
        ));
    }

    #[test]
    fn static_geometry_uses_the_same_tree_implementation() {
        let input = bytes(2048);
        let mut tree = CvTree::new(StaticGeometry::<2048, 1024, 0, 0>, Blake3Merkle);
        assert_eq!(
            tree.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }
}
