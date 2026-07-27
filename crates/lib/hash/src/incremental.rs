//! Source-independent incremental Merkle-tree caching.

use std::{convert::Infallible, fmt, ops::Range};

use crate::{
    Blake3Hash, OpaqueObj,
    blake3::{Blake3Cv, Blake3Merkle},
};

type Node = OpaqueObj<32>;

/// Index of an actual scheme leaf.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LeafIndex(pub u64);

/// Validated runtime tree geometry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DynamicGeometry {
    bytes: u64,
    leaf_bytes: u64,
}

impl DynamicGeometry {
    /// Constructs runtime geometry.
    ///
    /// # Errors
    ///
    /// Returns an error for a zero leaf width or a tree too large to index.
    pub fn new(bytes: u64, leaf_bytes: u64) -> Result<Self, GeometryError> {
        if leaf_bytes == 0 {
            return Err(GeometryError::ZeroLeafBytes);
        }
        let geometry = Self { bytes, leaf_bytes };
        geometry.node_count()?;
        Ok(geometry)
    }

    /// Returns the logical byte length.
    #[must_use]
    pub const fn bytes(self) -> u64 {
        self.bytes
    }

    /// Returns the number of bytes represented by one leaf.
    #[must_use]
    pub const fn leaf_bytes(self) -> u64 {
        self.leaf_bytes
    }

    /// Returns the number of logical leaves.
    #[must_use]
    pub const fn leaves(self) -> u64 {
        if self.bytes == 0 {
            0
        } else {
            self.bytes.div_ceil(self.leaf_bytes)
        }
    }

    /// Returns this geometry with a different logical byte length.
    ///
    /// # Errors
    ///
    /// Returns an error when the resized tree is too large to index.
    pub fn with_bytes(self, bytes: u64) -> Result<Self, GeometryError> {
        Self::new(bytes, self.leaf_bytes)
    }

    fn node_count(self) -> Result<usize, GeometryError> {
        let leaves = usize::try_from(self.leaves()).map_err(|_| GeometryError::TreeTooLarge)?;
        if leaves == 0 {
            Ok(0)
        } else {
            leaves
                .checked_mul(2)
                .and_then(|nodes| nodes.checked_sub(1))
                .ok_or(GeometryError::TreeTooLarge)
        }
    }
}

/// Geometry construction failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GeometryError {
    /// Leaves must represent at least one byte.
    ZeroLeafBytes,
    /// The exact flat tree cannot be represented on this platform.
    TreeTooLarge,
}

impl fmt::Display for GeometryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroLeafBytes => formatter.write_str("leaf width must be non-zero"),
            Self::TreeTooLarge => formatter.write_str("tree is too large to index"),
        }
    }
}

impl std::error::Error for GeometryError {}

/// Hashing operations needed by the incremental cache.
///
/// Nodes are stored as opaque 256-bit values. A scheme gives those bytes
/// meaning only while combining or finalizing them.
pub trait MerkleScheme {
    /// Externally meaningful root value.
    type Root: Clone;
    /// Evidence for one actual leaf.
    type Leaf: Clone;

    /// Extracts an opaque non-root node from leaf evidence.
    fn leaf_node(&self, leaf: &Self::Leaf) -> Node;
    /// Combines two opaque child nodes into a non-root parent.
    fn merge(&self, left: Node, right: Node) -> Node;
    /// Combines the final pair into a root.
    fn root(&self, left: Node, right: Node) -> Self::Root;
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
    type Root = Blake3Hash;
    type Leaf = Blake3Leaf;

    fn leaf_node(&self, leaf: &Self::Leaf) -> Node {
        leaf.cv.opaque()
    }

    fn merge(&self, left: Node, right: Node) -> Node {
        left.coerce::<Blake3Merkle>().merge(right.coerce()).opaque()
    }

    fn root(&self, left: Node, right: Node) -> Self::Root {
        left.coerce::<Blake3Merkle>().root(right.coerce())
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

/// Source-independent dynamic tree state.
///
/// The exact in-order layout contains `2 * leaves - 1` opaque nodes. Leaf `i`
/// is always stored at slot `2 * i`; every internal node sits between its
/// recursively flattened children. A parallel validity vector distinguishes
/// missing nodes without reserving any opaque value as a sentinel.
#[derive(Clone)]
pub struct CvTree<S: MerkleScheme> {
    geometry: DynamicGeometry,
    scheme: S,
    nodes: Vec<Node>,
    valid: Vec<bool>,
    single_root: Option<S::Root>,
    root: Option<S::Root>,
}

impl<S: MerkleScheme> CvTree<S> {
    /// Constructs a tree with every leaf awaiting initial evidence.
    ///
    /// # Errors
    ///
    /// Returns an error if the geometry cannot be represented on this platform.
    pub fn new(geometry: DynamicGeometry, scheme: S) -> Result<Self, GeometryError> {
        let node_count = geometry.node_count()?;
        Ok(Self {
            geometry,
            scheme,
            nodes: vec![Node::default(); node_count],
            valid: vec![false; node_count],
            single_root: None,
            root: None,
        })
    }

    /// Returns the geometry.
    #[must_use]
    pub const fn geometry(&self) -> DynamicGeometry {
        self.geometry
    }

    /// Returns the number of allocated opaque node slots.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns whether the tree has a cached clean root.
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.root.is_some()
    }

    /// Invalidates a leaf and every ancestor on its canonical path.
    ///
    /// # Errors
    ///
    /// Returns an error when the leaf is outside the geometry.
    pub fn dirty(&mut self, leaf: LeafIndex) -> Result<(), UpdateError> {
        let leaves = self.geometry.leaves();
        if leaf.0 >= leaves {
            return Err(UpdateError::LeafOutOfBounds { leaf, leaves });
        }
        self.root = None;
        self.single_root = None;
        self.invalidate_path(0, leaves, leaf.0);
        Ok(())
    }

    /// Invalidates every leaf touched by `range`.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reversed, or out-of-bounds range.
    pub fn dirty_range(&mut self, range: Range<LeafIndex>) -> Result<(), UpdateError> {
        let leaves = self.geometry.leaves();
        if range.start >= range.end || range.end.0 > leaves {
            return Err(UpdateError::InvalidRange {
                start: range.start,
                end: range.end,
                leaves,
            });
        }
        for leaf in range.start.0..range.end.0 {
            self.dirty(LeafIndex(leaf))?;
        }
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
        for (index, _) in &values {
            if index.0 >= leaves {
                return Err(UpdateError::LeafOutOfBounds {
                    leaf: *index,
                    leaves,
                });
            }
        }
        for (index, value) in values {
            self.dirty(index)?;
            let slot = leaf_slot(index.0);
            self.nodes[slot] = self.scheme.leaf_node(&value);
            self.valid[slot] = true;
            if leaves == 1 {
                self.single_root = self.scheme.single_root(&value);
            }
        }
        Ok(())
    }

    /// Returns actual leaves still needed to rebuild the tree.
    pub fn refill_frontier(&self) -> impl Iterator<Item = LeafIndex> + '_ {
        (0..self.geometry.leaves())
            .filter(|leaf| !self.valid[leaf_slot(*leaf)])
            .map(LeafIndex)
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
        if let Some(root) = &self.root {
            return Ok(root.clone());
        }
        let leaves = self.geometry.leaves();
        let root = match leaves {
            0 => self.scheme.empty_root(),
            1 => {
                if self.single_root.is_none() {
                    let evidence = source(LeafIndex(0)).map_err(|source| RebuildError::Leaf {
                        index: LeafIndex(0),
                        source,
                    })?;
                    let slot = leaf_slot(0);
                    self.nodes[slot] = self.scheme.leaf_node(&evidence);
                    self.valid[slot] = true;
                    self.single_root = self.scheme.single_root(&evidence);
                }
                self.single_root
                    .clone()
                    .ok_or(RebuildError::MissingSingleRoot)?
            }
            _ => {
                let left_count = left_subtree_leaves(leaves);
                let left = self.node(0, left_count, &mut source)?;
                let right = self.node(left_count, leaves - left_count, &mut source)?;
                let root = self.scheme.root(left, right);
                let slot = internal_slot(0, leaves);
                self.nodes[slot] = self.scheme.merge(left, right);
                self.valid[slot] = true;
                root
            }
        };
        self.root = Some(root.clone());
        Ok(root)
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

    /// Changes the logical byte length.
    ///
    /// Valid leaves keep their stable even-numbered slots. Internal nodes are
    /// conservatively invalidated because a slot on the old right spine can
    /// represent a different subtree after resizing.
    ///
    /// # Errors
    ///
    /// Returns an error when the resized geometry is too large to represent.
    pub fn resize(&mut self, bytes: u64) -> Result<(), GeometryError> {
        if bytes == self.geometry.bytes {
            return Ok(());
        }
        let old_geometry = self.geometry;
        let new_geometry = self.geometry.with_bytes(bytes)?;
        let mut nodes = vec![Node::default(); new_geometry.node_count()?];
        let mut valid = vec![false; nodes.len()];
        let preserved = old_geometry.leaves().min(new_geometry.leaves());
        for leaf in 0..preserved {
            let slot = leaf_slot(leaf);
            nodes[slot] = self.nodes[slot];
            valid[slot] = self.valid[slot];
        }
        self.geometry = new_geometry;
        self.nodes = nodes;
        self.valid = valid;
        self.root = None;
        self.single_root = None;

        if preserved > 0 {
            self.invalidate_path(0, new_geometry.leaves(), preserved - 1);
        }
        Ok(())
    }

    /// Returns a resized clone, preserving the original tree.
    ///
    /// # Errors
    ///
    /// Returns an error when the resized geometry is too large to represent.
    pub fn truncate_clone(&self, bytes: u64) -> Result<Self, GeometryError>
    where
        S: Clone,
    {
        let mut tree = self.clone();
        tree.resize(bytes)?;
        Ok(tree)
    }

    fn node<E>(
        &mut self,
        start: u64,
        count: u64,
        source: &mut impl FnMut(LeafIndex) -> Result<S::Leaf, E>,
    ) -> Result<Node, RebuildError<E>> {
        let slot = subtree_slot(start, count);
        if self.valid[slot] {
            return Ok(self.nodes[slot]);
        }
        let value = if count == 1 {
            let index = LeafIndex(start);
            let leaf = source(index).map_err(|source| RebuildError::Leaf { index, source })?;
            self.scheme.leaf_node(&leaf)
        } else {
            let left_count = left_subtree_leaves(count);
            let left = self.node(start, left_count, source)?;
            let right = self.node(start + left_count, count - left_count, source)?;
            self.scheme.merge(left, right)
        };
        self.nodes[slot] = value;
        self.valid[slot] = true;
        Ok(value)
    }

    fn invalidate_path(&mut self, start: u64, count: u64, leaf: u64) {
        let slot = subtree_slot(start, count);
        self.valid[slot] = false;
        if count == 1 {
            return;
        }
        let left_count = left_subtree_leaves(count);
        if leaf < start + left_count {
            self.invalidate_path(start, left_count, leaf);
        } else {
            self.invalidate_path(start + left_count, count - left_count, leaf);
        }
    }
}

/// A tree proven clean at wrapper construction time.
pub struct CleanTree<S: MerkleScheme>(CvTree<S>);

impl<S: MerkleScheme> CleanTree<S> {
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
    pub fn update<I>(self, values: NewCvs<I>) -> Result<Self, IncompleteUpdate<S>>
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

impl<S: MerkleScheme> From<CleanTree<S>> for CvTree<S> {
    fn from(value: CleanTree<S>) -> Self {
        value.0
    }
}

impl<S: MerkleScheme> TryFrom<CvTree<S>> for CleanTree<S> {
    type Error = CvTree<S>;

    fn try_from(value: CvTree<S>) -> Result<Self, Self::Error> {
        if value.is_clean() {
            Ok(Self(value))
        } else {
            Err(value)
        }
    }
}

/// An update that needs additional leaf evidence.
pub struct IncompleteUpdate<S: MerkleScheme> {
    /// Potentially dirty tree retaining the applied update.
    pub tree: CvTree<S>,
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

fn leaf_slot(leaf: u64) -> usize {
    usize::try_from(leaf).expect("validated geometry") * 2
}

fn subtree_slot(start: u64, count: u64) -> usize {
    if count == 1 {
        leaf_slot(start)
    } else {
        internal_slot(start, count)
    }
}

fn internal_slot(start: u64, count: u64) -> usize {
    let left_count = left_subtree_leaves(count);
    leaf_slot(start) + usize::try_from(left_count).expect("validated geometry") * 2 - 1
}

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

    fn tree(input: &[u8]) -> CvTree<Blake3Merkle> {
        let geometry = DynamicGeometry::new(input.len() as u64, blake3::CHUNK_LEN as u64).unwrap();
        CvTree::new(geometry, Blake3Merkle).unwrap()
    }

    #[test]
    fn exact_flat_layout_matches_one_shot_blake3() {
        for length in [0, 1, 1_024, 1_025, 3_001, 7_169, 16_385] {
            let input = bytes(length);
            let mut tree = tree(&input);
            let leaves = tree.geometry().leaves();
            assert_eq!(
                tree.node_count(),
                usize::try_from(
                    leaves
                        .saturating_mul(2)
                        .saturating_sub(u64::from(leaves > 0))
                )
                .unwrap()
            );
            assert_eq!(
                tree.root_with(|index| leaf(&input, index)).unwrap(),
                Blake3Hash::from_bytes(&input),
                "{length}"
            );
            assert!(tree.is_clean());
            assert_eq!(tree.refill_frontier().count(), 0);
        }
    }

    #[test]
    fn leaf_slots_are_stable_and_every_slot_is_used() {
        let input = bytes(7 * blake3::CHUNK_LEN);
        let mut tree = tree(&input);
        tree.root_with(|index| leaf(&input, index)).unwrap();
        assert!(tree.valid.iter().all(|valid| *valid));
        for index in 0..7 {
            assert_eq!(
                tree.nodes[leaf_slot(index)],
                leaf(&input, LeafIndex(index)).cv().opaque()
            );
        }
    }

    #[test]
    fn one_chunk_requires_explicit_root_evidence() {
        let input = bytes(73);
        let mut tree = tree(&input);
        tree.update(NewCvs([(
            LeafIndex(0),
            Blake3Leaf::from_cv(leaf(&input, LeafIndex(0)).cv()),
        )]))
        .unwrap();
        assert!(matches!(
            tree.try_root_with::<()>(|_| Err(())),
            Err(RebuildError::Leaf {
                index: LeafIndex(0),
                ..
            })
        ));

        assert_eq!(
            tree.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }

    #[test]
    fn dirtying_requests_only_changed_leaves() {
        let input = bytes(8 * blake3::CHUNK_LEN);
        let mut tree = tree(&input);
        tree.root_with(|index| leaf(&input, index)).unwrap();
        tree.dirty(LeafIndex(5)).unwrap();
        assert_eq!(
            tree.refill_frontier().collect::<Vec<_>>(),
            vec![LeafIndex(5)]
        );

        let mut requested = Vec::new();
        let root = tree
            .root_with(|index| {
                requested.push(index);
                leaf(&input, index)
            })
            .unwrap();
        assert_eq!(root, Blake3Hash::from_bytes(input));
        assert_eq!(requested, vec![LeafIndex(5)]);
    }

    #[test]
    fn callback_errors_report_the_leaf_and_are_retryable() {
        let input = bytes(3 * blake3::CHUNK_LEN);
        let mut tree = tree(&input);
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
    fn clean_wrapper_accepts_complete_updates() {
        let mut input = bytes(4 * blake3::CHUNK_LEN);
        let mut raw = tree(&input);
        raw.root_with(|index| leaf(&input, index)).unwrap();
        let clean = CleanTree::try_from(raw).ok().unwrap();

        input[blake3::CHUNK_LEN..2 * blake3::CHUNK_LEN].fill(0xee);
        let clean = clean
            .update(NewCvs([(LeafIndex(1), leaf(&input, LeafIndex(1)))]))
            .ok()
            .unwrap();
        assert_eq!(clean.root(), &Blake3Hash::from_bytes(input));
    }

    #[test]
    fn resize_preserves_leaves_and_rebuilds_shape() {
        let input = bytes(5 * blake3::CHUNK_LEN);
        let mut original = tree(&input);
        original.root_with(|index| leaf(&input, index)).unwrap();

        let shorter_bytes = &input[..3 * blake3::CHUNK_LEN];
        let mut shorter = original.truncate_clone(shorter_bytes.len() as u64).unwrap();
        assert_eq!(shorter.node_count(), 5);
        let mut requested = Vec::new();
        assert_eq!(
            shorter
                .root_with(|index| {
                    requested.push(index);
                    leaf(shorter_bytes, index)
                })
                .unwrap(),
            Blake3Hash::from_bytes(shorter_bytes)
        );
        assert_eq!(requested, vec![LeafIndex(2)]);
        assert_eq!(
            original.root_with(|index| leaf(&input, index)).unwrap(),
            Blake3Hash::from_bytes(input)
        );
    }

    #[test]
    fn geometry_and_dirty_ranges_reject_invalid_inputs() {
        assert_eq!(
            DynamicGeometry::new(1, 0),
            Err(GeometryError::ZeroLeafBytes)
        );

        let input = bytes(2 * blake3::CHUNK_LEN);
        let mut tree = tree(&input);
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
}
