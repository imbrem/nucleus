//! I/O-free experiments for eager, lazy, and immutable BLAKE3 trees.
//!
//! These types never fetch or retain file bytes. Callers execute explicit
//! [`LeafRequest`] values however they choose, hash the returned bytes with
//! [`LeafValue::from_bytes`], and supply the result back to the tree.

use std::{fmt, ops::Range};

use super::{Blake3Cv, Blake3Hash};

/// BLAKE3's native chunk width.
pub const CHUNK_BYTES: u64 = blake3::CHUNK_LEN as u64;

/// A useful retained-leaf width for `SQLite`'s common page size.
pub const SQLITE_PAGE_BYTES: u64 = 4 * CHUNK_BYTES;

/// Index of one retained tree leaf.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LeafIndex(pub u64);

/// Fixed byte and retained-leaf geometry for a BLAKE3 tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Geometry {
    bytes: u64,
    leaf_bytes: u64,
    leaves: u64,
}

impl Geometry {
    /// Validates a fixed tree geometry.
    ///
    /// Retained leaves are power-of-two multiples of BLAKE3's 1 KiB chunks.
    /// This lets every full retained leaf stand for one canonical subtree.
    ///
    /// # Errors
    ///
    /// Returns an error for a noncanonical retained-leaf width or a tree too
    /// large to index on this platform.
    pub fn new(bytes: u64, leaf_bytes: u64) -> Result<Self, GeometryError> {
        if leaf_bytes < CHUNK_BYTES
            || !leaf_bytes.is_power_of_two()
            || !leaf_bytes.is_multiple_of(CHUNK_BYTES)
        {
            return Err(GeometryError::InvalidLeafBytes { leaf_bytes });
        }
        let leaves = bytes.div_ceil(leaf_bytes);
        let leaves_usize = usize::try_from(leaves).map_err(|_| GeometryError::TreeTooLarge)?;
        if leaves_usize
            .checked_mul(2)
            .and_then(|slots| slots.checked_sub(usize::from(leaves_usize != 0)))
            .is_none()
        {
            return Err(GeometryError::TreeTooLarge);
        }
        Ok(Self {
            bytes,
            leaf_bytes,
            leaves,
        })
    }

    /// Returns the logical byte length.
    #[must_use]
    pub const fn bytes(self) -> u64 {
        self.bytes
    }

    /// Returns the number of bytes in each full retained leaf.
    #[must_use]
    pub const fn leaf_bytes(self) -> u64 {
        self.leaf_bytes
    }

    /// Returns the number of retained leaves.
    #[must_use]
    pub const fn leaves(self) -> u64 {
        self.leaves
    }

    fn node_count(self) -> usize {
        self.leaf_count_usize()
            .saturating_mul(2)
            .saturating_sub(usize::from(self.leaves != 0))
    }

    fn leaf_count_usize(self) -> usize {
        usize::try_from(self.leaves).expect("geometry constructor validated leaf count")
    }

    fn leaf_range(self, index: LeafIndex) -> Result<Range<u64>, LeafError> {
        if index.0 >= self.leaves {
            return Err(LeafError::OutOfBounds {
                index,
                leaves: self.leaves,
            });
        }
        let start = index.0 * self.leaf_bytes;
        Ok(start..(start + self.leaf_bytes).min(self.bytes))
    }
}

/// Invalid fixed geometry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GeometryError {
    /// Retained leaves must be power-of-two multiples of 1 KiB.
    InvalidLeafBytes { leaf_bytes: u64 },
    /// The exact flat tree cannot be indexed on this platform.
    TreeTooLarge,
}

impl fmt::Display for GeometryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for GeometryError {}

/// A verifier-selected request for one retained leaf.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeafRequest {
    /// Requested retained leaf.
    pub index: LeafIndex,
    /// Exact byte range to hash.
    pub bytes: Range<u64>,
}

impl LeafRequest {
    fn new(geometry: Geometry, index: LeafIndex) -> Result<Self, LeafError> {
        Ok(Self {
            index,
            bytes: geometry.leaf_range(index)?,
        })
    }
}

/// A retained leaf value computed from exact bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LeafValue {
    index: LeafIndex,
    offset: u64,
    bytes: u64,
    cv: Blake3Cv,
    single_root: Option<Blake3Hash>,
}

impl LeafValue {
    /// Hashes the exact bytes requested for a retained leaf.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is outside `geometry` or `bytes` does not
    /// have the exact selected length.
    pub fn from_bytes(
        geometry: Geometry,
        index: LeafIndex,
        bytes: impl AsRef<[u8]>,
    ) -> Result<Self, LeafError> {
        let range = geometry.leaf_range(index)?;
        let bytes = bytes.as_ref();
        let expected = range.end - range.start;
        if bytes.len() as u64 != expected {
            return Err(LeafError::WrongLength {
                index,
                expected,
                actual: bytes.len() as u64,
            });
        }
        Ok(Self {
            index,
            offset: range.start,
            bytes: expected,
            cv: Blake3Cv::from_subtree(range.start, bytes),
            single_root: (geometry.leaves == 1).then(|| Blake3Hash::from_bytes(bytes)),
        })
    }

    /// Returns this leaf's index.
    #[must_use]
    pub const fn index(self) -> LeafIndex {
        self.index
    }

    /// Returns this leaf's non-root chaining value.
    #[must_use]
    pub const fn cv(self) -> Blake3Cv {
        self.cv
    }
}

/// A completed response to a verifier-selected request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeafResult {
    /// The request that selected these bytes.
    pub request: LeafRequest,
    /// The locally computed value of the requested bytes.
    pub value: LeafValue,
}

impl LeafResult {
    /// Hashes bytes only after checking that the request belongs to `geometry`.
    ///
    /// # Errors
    ///
    /// Returns an error if the request is not canonical for `geometry` or its
    /// bytes do not have the exact selected length.
    pub fn from_bytes(
        geometry: Geometry,
        request: LeafRequest,
        bytes: impl AsRef<[u8]>,
    ) -> Result<Self, LeafError> {
        let expected = LeafRequest::new(geometry, request.index)?;
        if request != expected {
            return Err(LeafError::WrongRequest {
                expected,
                actual: request,
            });
        }
        let index = request.index;
        Ok(Self {
            request,
            value: LeafValue::from_bytes(geometry, index, bytes)?,
        })
    }
}

/// Invalid leaf evidence or request.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LeafError {
    /// The leaf does not exist in this geometry.
    OutOfBounds { index: LeafIndex, leaves: u64 },
    /// The supplied byte count differs from the selected leaf.
    WrongLength {
        index: LeafIndex,
        expected: u64,
        actual: u64,
    },
    /// A result was paired with a different range than the verifier selected.
    WrongRequest {
        expected: LeafRequest,
        actual: LeafRequest,
    },
    /// The value was constructed for a different retained leaf geometry.
    WrongValue { index: LeafIndex },
}

impl fmt::Display for LeafError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for LeafError {}

/// An eager, always-clean fixed-length BLAKE3 tree.
///
/// It stores one CV per retained leaf and internal node, but no file bytes.
/// Replacing a leaf updates only its canonical ancestor path.
#[derive(Clone)]
pub struct FixedTree {
    geometry: Geometry,
    nodes: Vec<Blake3Cv>,
    root: Blake3Hash,
}

impl FixedTree {
    /// Constructs a clean tree from one ordered value per retained leaf.
    ///
    /// # Errors
    ///
    /// Returns an error unless there is exactly one correctly positioned value
    /// for every retained leaf.
    pub fn new(geometry: Geometry, leaves: Vec<LeafValue>) -> Result<Self, BuildError> {
        if leaves.len() != geometry.leaf_count_usize() {
            return Err(BuildError::WrongLeafCount {
                expected: geometry.leaves,
                actual: leaves.len() as u64,
            });
        }
        if geometry.leaves == 0 {
            return Ok(Self {
                geometry,
                nodes: Vec::new(),
                root: Blake3Hash::from_bytes([]),
            });
        }

        let mut nodes = vec![Blake3Cv::default(); geometry.node_count()];
        for (expected, leaf) in (0..geometry.leaves).zip(leaves) {
            validate_leaf(geometry, leaf, LeafIndex(expected)).map_err(BuildError::Leaf)?;
            nodes[leaf_slot(expected)] = leaf.cv;
            if geometry.leaves == 1 {
                return Ok(Self {
                    geometry,
                    nodes,
                    root: leaf.single_root.ok_or(BuildError::MissingSingleRoot)?,
                });
            }
        }
        let left_count = left_subtree_leaves(geometry.leaves);
        let left = rebuild_subtree(&mut nodes, 0, left_count);
        let right = rebuild_subtree(&mut nodes, left_count, geometry.leaves - left_count);
        let root = left.root(right);
        nodes[internal_slot(0, geometry.leaves)] = left.merge(right);
        Ok(Self {
            geometry,
            nodes,
            root,
        })
    }

    /// Returns the fixed geometry.
    #[must_use]
    pub const fn geometry(&self) -> Geometry {
        self.geometry
    }

    /// Returns the current root digest.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.root
    }

    /// Replaces one retained leaf and recomputes its ancestors in logarithmic time.
    ///
    /// # Errors
    ///
    /// Returns an error if the value was made for a different leaf or geometry.
    pub fn update(&mut self, leaf: LeafValue) -> Result<(), LeafError> {
        validate_leaf(self.geometry, leaf, leaf.index)?;
        if self.geometry.leaves == 1 {
            self.nodes[0] = leaf.cv;
            self.root = leaf
                .single_root
                .ok_or(LeafError::WrongValue { index: leaf.index })?;
            return Ok(());
        }
        self.nodes[leaf_slot(leaf.index.0)] = leaf.cv;
        recompute_path(&mut self.nodes, 0, self.geometry.leaves, leaf.index.0);
        let left_count = left_subtree_leaves(self.geometry.leaves);
        let left = self.nodes[subtree_slot(0, left_count)];
        let right = self.nodes[subtree_slot(left_count, self.geometry.leaves - left_count)];
        self.root = left.root(right);
        Ok(())
    }

    fn leaf(&self, index: LeafIndex) -> Result<Blake3Cv, LeafError> {
        self.geometry.leaf_range(index)?;
        Ok(self.nodes[leaf_slot(index.0)])
    }
}

/// Failure to build an eager tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    /// The input did not contain exactly one value per retained leaf.
    WrongLeafCount { expected: u64, actual: u64 },
    /// One value did not match the geometry or its ordered position.
    Leaf(LeafError),
    /// A one-leaf BLAKE3 tree needs root-finalization evidence, not only a CV.
    MissingSingleRoot,
}

impl fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for BuildError {}

/// The next pure action needed to produce a current root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RootPlan {
    /// No leaf is dirty.
    Clean(Blake3Hash),
    /// The caller must retrieve and hash these exact ranges.
    Fetch(Vec<LeafRequest>),
    /// Every dirty value has been supplied and can be committed atomically.
    Rebuild(Vec<LeafIndex>),
}

/// A fixed tree with an explicit dirty list and staged leaf results.
///
/// Dirtying and supplying values never performs I/O. A rebuild commits only
/// after every dirty leaf has a result, leaving retries straightforward.
pub struct LazyTree {
    clean: FixedTree,
    dirty: Vec<bool>,
    dirty_list: Vec<LeafIndex>,
    staged: Vec<Option<LeafValue>>,
}

impl LazyTree {
    /// Wraps a clean tree with initially empty dirty state.
    #[must_use]
    pub fn new(clean: FixedTree) -> Self {
        let leaves = clean.geometry.leaf_count_usize();
        Self {
            clean,
            dirty: vec![false; leaves],
            dirty_list: Vec::new(),
            staged: vec![None; leaves],
        }
    }

    /// Returns the clean root, or `None` while any leaf is dirty.
    #[must_use]
    pub fn root(&self) -> Option<Blake3Hash> {
        self.dirty_list.is_empty().then(|| self.clean.root())
    }

    /// Returns the previous clean root even while changes are pending.
    #[must_use]
    pub const fn stale_root(&self) -> Blake3Hash {
        self.clean.root()
    }

    /// Marks one retained leaf dirty, preserving first-dirtied order.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is outside the fixed geometry.
    pub fn dirty(&mut self, index: LeafIndex) -> Result<(), LeafError> {
        self.clean.geometry.leaf_range(index)?;
        self.mark_dirty_valid(index);
        Ok(())
    }

    fn mark_dirty_valid(&mut self, index: LeafIndex) {
        let slot = leaf_index_usize(index);
        if !self.dirty[slot] {
            self.dirty[slot] = true;
            self.dirty_list.push(index);
        }
        self.staged[slot] = None;
    }

    /// Marks each retained leaf intersecting a byte range dirty.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reversed, or out-of-bounds byte range.
    pub fn dirty_bytes(&mut self, bytes: Range<u64>) -> Result<(), DirtyRangeError> {
        if bytes.start >= bytes.end || bytes.end > self.clean.geometry.bytes {
            return Err(DirtyRangeError {
                bytes,
                tree_bytes: self.clean.geometry.bytes,
            });
        }
        let first = bytes.start / self.clean.geometry.leaf_bytes;
        let last = (bytes.end - 1) / self.clean.geometry.leaf_bytes;
        for index in first..=last {
            self.mark_dirty_valid(LeafIndex(index));
        }
        Ok(())
    }

    /// Describes the next fetch or rebuild action without executing it.
    #[must_use]
    pub fn plan(&self) -> RootPlan {
        if self.dirty_list.is_empty() {
            return RootPlan::Clean(self.clean.root());
        }
        let requests: Vec<_> = self
            .dirty_list
            .iter()
            .copied()
            .filter(|index| self.staged[leaf_index_usize(*index)].is_none())
            .map(|index| request_valid(self.clean.geometry, index))
            .collect();
        if requests.is_empty() {
            RootPlan::Rebuild(self.dirty_list.clone())
        } else {
            RootPlan::Fetch(requests)
        }
    }

    /// Stages one locally verified leaf result.
    ///
    /// # Errors
    ///
    /// Returns an error if the response does not match a verifier-selected
    /// dirty leaf in this tree.
    pub fn supply(&mut self, result: LeafResult) -> Result<(), SupplyError> {
        let expected = LeafRequest::new(self.clean.geometry, result.request.index)
            .map_err(SupplyError::Leaf)?;
        if result.request != expected {
            return Err(SupplyError::Leaf(LeafError::WrongRequest {
                expected,
                actual: result.request,
            }));
        }
        validate_leaf(self.clean.geometry, result.value, result.request.index)
            .map_err(SupplyError::Leaf)?;
        let slot = leaf_index_usize(result.request.index);
        if !self.dirty[slot] {
            return Err(SupplyError::NotDirty(result.request.index));
        }
        self.staged[slot] = Some(result.value);
        Ok(())
    }

    /// Commits all staged values when the plan is ready.
    ///
    /// # Errors
    ///
    /// Returns every exact leaf request still missing. No staged update is
    /// committed on failure.
    pub fn rebuild(&mut self) -> Result<Blake3Hash, RebuildError> {
        let missing: Vec<_> = match self.plan() {
            RootPlan::Fetch(requests) => requests,
            RootPlan::Clean(root) => return Ok(root),
            RootPlan::Rebuild(_) => Vec::new(),
        };
        if !missing.is_empty() {
            return Err(RebuildError { missing });
        }
        self.commit_ready();
        Ok(self.clean.root())
    }

    fn commit_ready(&mut self) {
        for index in self.dirty_list.drain(..) {
            let slot = leaf_index_usize(index);
            let value = self.staged[slot].take().expect("ready plan");
            self.clean.update(value).expect("staged value validated");
            self.dirty[slot] = false;
        }
    }
}

/// Invalid byte range supplied to [`LazyTree::dirty_bytes`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirtyRangeError {
    /// Invalid requested range.
    pub bytes: Range<u64>,
    /// Logical file length.
    pub tree_bytes: u64,
}

impl fmt::Display for DirtyRangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DirtyRangeError {}

/// Failure to stage a leaf result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SupplyError {
    /// The result does not match this tree's verifier-selected request.
    Leaf(LeafError),
    /// Results are accepted only for explicitly dirty leaves.
    NotDirty(LeafIndex),
}

impl fmt::Display for SupplyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for SupplyError {}

/// A rebuild attempted before every requested range was supplied.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RebuildError {
    /// Exact requests still outstanding; a failed external request remains here.
    pub missing: Vec<LeafRequest>,
}

impl fmt::Display for RebuildError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "missing {} retained leaves", self.missing.len())
    }
}

impl std::error::Error for RebuildError {}

/// An immutable tree retaining digests independently of resident bytes.
///
/// Eviction only changes residency metadata. A reloaded range becomes resident
/// after its locally computed CV matches the retained CV; changed bytes are
/// rejected without changing the remembered tree.
pub struct ImmutableTree {
    clean: FixedTree,
    resident: Vec<bool>,
}

impl ImmutableTree {
    /// Treats every retained leaf of a clean tree as initially resident.
    #[must_use]
    pub fn new(clean: FixedTree) -> Self {
        let leaves = clean.geometry.leaf_count_usize();
        Self {
            clean,
            resident: vec![true; leaves],
        }
    }

    /// Returns the immutable file root.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.clean.root()
    }

    /// Discards residency for one leaf while retaining its authenticated CV.
    ///
    /// # Errors
    ///
    /// Returns an error if the leaf is outside the fixed geometry.
    pub fn evict(&mut self, index: LeafIndex) -> Result<(), LeafError> {
        self.clean.geometry.leaf_range(index)?;
        self.resident[leaf_index_usize(index)] = false;
        Ok(())
    }

    /// Plans reloads for evicted leaves intersecting a byte range.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reversed, or out-of-bounds byte range.
    pub fn reload_plan(&self, bytes: Range<u64>) -> Result<Vec<LeafRequest>, DirtyRangeError> {
        if bytes.start >= bytes.end || bytes.end > self.clean.geometry.bytes {
            return Err(DirtyRangeError {
                bytes,
                tree_bytes: self.clean.geometry.bytes,
            });
        }
        let first = bytes.start / self.clean.geometry.leaf_bytes;
        let last = (bytes.end - 1) / self.clean.geometry.leaf_bytes;
        Ok((first..=last)
            .filter(|index| !self.resident[leaf_index_usize(LeafIndex(*index))])
            .map(|index| request_valid(self.clean.geometry, LeafIndex(index)))
            .collect())
    }

    /// Accepts a reloaded leaf only if it matches the remembered immutable CV.
    ///
    /// # Errors
    ///
    /// Returns an error if the response is not for the selected leaf or its CV
    /// differs from the retained immutable CV.
    pub fn accept_reload(&mut self, result: LeafResult) -> Result<(), ReloadError> {
        let expected_request = LeafRequest::new(self.clean.geometry, result.request.index)
            .map_err(ReloadError::Leaf)?;
        if result.request != expected_request {
            return Err(ReloadError::Leaf(LeafError::WrongRequest {
                expected: expected_request,
                actual: result.request,
            }));
        }
        validate_leaf(self.clean.geometry, result.value, result.request.index)
            .map_err(ReloadError::Leaf)?;
        let expected = self
            .clean
            .leaf(result.request.index)
            .map_err(ReloadError::Leaf)?;
        if result.value.cv != expected {
            return Err(ReloadError::Changed {
                index: result.request.index,
                expected,
                actual: result.value.cv,
            });
        }
        self.resident[leaf_index_usize(result.request.index)] = true;
        Ok(())
    }

    /// Converts immutable state into an explicit copy-on-write dirty tree.
    #[must_use]
    pub fn into_cow(self) -> LazyTree {
        LazyTree::new(self.clean)
    }
}

/// A reload violated the immutable-source contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReloadError {
    /// The response did not match the selected range.
    Leaf(LeafError),
    /// Reloaded bytes hash differently from the retained range.
    Changed {
        index: LeafIndex,
        expected: Blake3Cv,
        actual: Blake3Cv,
    },
}

impl fmt::Display for ReloadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ReloadError {}

fn validate_leaf(
    geometry: Geometry,
    leaf: LeafValue,
    expected_index: LeafIndex,
) -> Result<(), LeafError> {
    let range = geometry.leaf_range(expected_index)?;
    if leaf.index != expected_index
        || leaf.offset != range.start
        || leaf.bytes != range.end - range.start
    {
        return Err(LeafError::WrongValue {
            index: expected_index,
        });
    }
    Ok(())
}

fn leaf_index_usize(index: LeafIndex) -> usize {
    usize::try_from(index.0).expect("geometry validated every reachable leaf index")
}

fn request_valid(geometry: Geometry, index: LeafIndex) -> LeafRequest {
    LeafRequest {
        index,
        bytes: geometry
            .leaf_range(index)
            .expect("internal leaf index belongs to geometry"),
    }
}

fn leaf_slot(index: u64) -> usize {
    usize::try_from(index).expect("validated geometry") * 2
}

fn subtree_slot(start: u64, count: u64) -> usize {
    if count == 1 {
        leaf_slot(start)
    } else {
        internal_slot(start, count)
    }
}

fn internal_slot(start: u64, count: u64) -> usize {
    leaf_slot(start) + usize::try_from(left_subtree_leaves(count)).expect("validated geometry") * 2
        - 1
}

fn left_subtree_leaves(leaves: u64) -> u64 {
    1 << (u64::BITS - 1 - (leaves - 1).leading_zeros())
}

fn rebuild_subtree(nodes: &mut [Blake3Cv], start: u64, count: u64) -> Blake3Cv {
    if count == 1 {
        return nodes[leaf_slot(start)];
    }
    let left_count = left_subtree_leaves(count);
    let left = rebuild_subtree(nodes, start, left_count);
    let right = rebuild_subtree(nodes, start + left_count, count - left_count);
    let parent = left.merge(right);
    nodes[internal_slot(start, count)] = parent;
    parent
}

fn recompute_path(nodes: &mut [Blake3Cv], start: u64, count: u64, target: u64) -> Blake3Cv {
    if count == 1 {
        return nodes[leaf_slot(start)];
    }
    let left_count = left_subtree_leaves(count);
    let boundary = start + left_count;
    let (left, right) = if target < boundary {
        (
            recompute_path(nodes, start, left_count, target),
            nodes[subtree_slot(boundary, count - left_count)],
        )
    } else {
        (
            nodes[subtree_slot(start, left_count)],
            recompute_path(nodes, boundary, count - left_count, target),
        )
    };
    let parent = left.merge(right);
    nodes[internal_slot(start, count)] = parent;
    parent
}
