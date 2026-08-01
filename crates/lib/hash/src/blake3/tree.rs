//! I/O-free eager BLAKE3 trees.
//!
//! These types deliberately know nothing about files, readers, caches, or
//! proofs. They are an experiment in the smallest useful in-memory protocol:
//! retain one chaining value per [`EagerTree::leaf_bytes`] bytes, retain the
//! incomplete trailing leaf's bytes, and eagerly maintain the parent levels.
//!
//! Increasing `LEAF_BYTES` prunes lower BLAKE3 levels. It reduces retained CVs
//! but also raises the minimum replacement unit: a `EagerTree<4096>` caller
//! must supply all 4 KiB to replace a leaf, while `EagerTree<1024>` can replace
//! individual BLAKE3 chunks. The trailing buffer has the same upper bound.

use std::{error::Error, fmt};

use super::{Blake3Cv, Blake3Hash};

/// BLAKE3's native chunk geometry.
pub const CHUNK_BYTES: usize = ::blake3::CHUNK_LEN;

/// An eager BLAKE3 tree retaining one CV per `LEAF_BYTES` bytes.
///
/// `LEAF_BYTES` must be a power-of-two multiple of 1 KiB. Complete retained
/// leaves discard their source bytes. Only the incomplete final leaf keeps its
/// bytes, which is exactly the state needed to support [`Self::append`].
///
/// The tree is entirely I/O-free. Persisting leaves, supplying replacement
/// bytes, and synchronizing concurrent edits are caller responsibilities.
#[derive(Clone, Debug)]
pub struct EagerTree<const LEAF_BYTES: usize = CHUNK_BYTES> {
    len: usize,
    /// Level zero contains retained leaves; each subsequent level contains
    /// pairwise parents, with an unmatched right-edge node promoted unchanged.
    levels: Vec<Vec<Blake3Cv>>,
    trailing: Vec<u8>,
    /// A CV cannot be finalized as a root. Cache the root while a sole complete
    /// retained leaf's bytes are still available.
    single_leaf_root: Blake3Hash,
}

/// A fixed-length, update-only eager tree.
///
/// This wrapper intentionally exposes no append operation. It is useful when
/// the input geometry is part of a higher-level protocol.
#[derive(Clone, Debug)]
pub struct FixedTree<const LEAF_BYTES: usize = CHUNK_BYTES> {
    tree: EagerTree<LEAF_BYTES>,
}

/// A rejected eager-tree operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TreeError {
    /// The retained-leaf index is outside this tree.
    LeafOutOfBounds { index: usize, leaf_count: usize },
    /// Replacement data does not have the existing retained leaf's length.
    WrongLeafLength { expected: usize, actual: usize },
    /// A replacement range is not an integral number of retained leaves.
    UnalignedRange { len: usize, leaf_bytes: usize },
    /// Arithmetic would overflow the platform's addressable length.
    LengthOverflow,
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::LeafOutOfBounds { index, leaf_count } => {
                write!(f, "leaf {index} is outside a tree with {leaf_count} leaves")
            }
            Self::WrongLeafLength { expected, actual } => {
                write!(
                    f,
                    "replacement leaf has {actual} bytes; expected {expected}"
                )
            }
            Self::UnalignedRange { len, leaf_bytes } => write!(
                f,
                "replacement range has {len} bytes; expected a multiple of {leaf_bytes}"
            ),
            Self::LengthOverflow => f.write_str("tree length overflow"),
        }
    }
}

impl Error for TreeError {}

impl<const LEAF_BYTES: usize> Default for EagerTree<LEAF_BYTES> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const LEAF_BYTES: usize> EagerTree<LEAF_BYTES> {
    /// Makes an empty tree.
    ///
    /// # Panics
    ///
    /// Panics when `LEAF_BYTES` is not a power-of-two multiple of 1 KiB.
    #[must_use]
    pub fn new() -> Self {
        Self::assert_geometry();
        Self {
            len: 0,
            levels: vec![Vec::new()],
            trailing: Vec::new(),
            single_leaf_root: Blake3Hash::from_bytes([]),
        }
    }

    /// Builds a tree from bytes.
    ///
    /// # Panics
    ///
    /// Panics when `LEAF_BYTES` is not a power-of-two multiple of 1 KiB.
    #[must_use]
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        let bytes = bytes.as_ref();
        let mut tree = Self::new();
        // This cannot overflow because the tree starts empty.
        tree.append(bytes).expect("a slice length fits in usize");
        tree
    }

    /// Number of bytes represented by this tree.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether this tree represents the empty byte string.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Retained leaf geometry in bytes.
    #[must_use]
    pub const fn leaf_bytes(&self) -> usize {
        LEAF_BYTES
    }

    /// Number of retained leaves, including a partial trailing leaf.
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        self.levels[0].len()
    }

    /// Bytes retained for future append operations.
    ///
    /// This is empty when the length is retained-leaf-aligned.
    #[must_use]
    pub fn trailing_bytes(&self) -> &[u8] {
        &self.trailing
    }

    /// Returns the standard BLAKE3 root hash for the represented bytes.
    #[must_use]
    pub fn root(&self) -> Blake3Hash {
        match self.leaf_count() {
            0 | 1 => self.single_leaf_root,
            _ => {
                let root_children = &self.levels[self.levels.len() - 2];
                debug_assert_eq!(root_children.len(), 2);
                root_children[0].root(root_children[1])
            }
        }
    }

    /// Appends bytes, retaining only a new incomplete trailing leaf.
    ///
    /// Complete retained leaves are hashed and their input bytes discarded.
    /// Parent work is logarithmic per appended retained leaf.
    ///
    /// # Errors
    ///
    /// Returns [`TreeError::LengthOverflow`] if the resulting byte length does
    /// not fit in `usize`.
    pub fn append(&mut self, bytes: impl AsRef<[u8]>) -> Result<(), TreeError> {
        let mut bytes = bytes.as_ref();
        let new_len = self
            .len
            .checked_add(bytes.len())
            .ok_or(TreeError::LengthOverflow)?;
        if bytes.is_empty() {
            return Ok(());
        }

        if !self.trailing.is_empty() {
            let take = (LEAF_BYTES - self.trailing.len()).min(bytes.len());
            self.trailing.extend_from_slice(&bytes[..take]);
            bytes = &bytes[take..];
            let index = self.leaf_count() - 1;
            self.replace_cv(index, Self::leaf_cv(index, &self.trailing));
            self.single_leaf_root = Blake3Hash::from_bytes(&self.trailing);
            if self.trailing.len() == LEAF_BYTES {
                self.trailing.clear();
            }
        }

        while bytes.len() >= LEAF_BYTES {
            let (leaf, rest) = bytes.split_at(LEAF_BYTES);
            let index = self.leaf_count();
            self.push_cv(Self::leaf_cv(index, leaf));
            if index == 0 {
                self.single_leaf_root = Blake3Hash::from_bytes(leaf);
            }
            bytes = rest;
        }

        if !bytes.is_empty() {
            let index = self.leaf_count();
            self.trailing.extend_from_slice(bytes);
            self.push_cv(Self::leaf_cv(index, &self.trailing));
            if index == 0 {
                self.single_leaf_root = Blake3Hash::from_bytes(&self.trailing);
            }
        }

        self.len = new_len;
        Ok(())
    }

    /// Replaces one retained leaf and updates its ancestors in logarithmic time.
    ///
    /// The replacement must have exactly the leaf's existing length. Thus only
    /// the final leaf may be shorter than `LEAF_BYTES`.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is outside the tree or the replacement has
    /// a different length from the existing leaf.
    pub fn replace_leaf(&mut self, index: usize, bytes: impl AsRef<[u8]>) -> Result<(), TreeError> {
        let bytes = bytes.as_ref();
        let expected = self.leaf_len(index)?;
        if bytes.len() != expected {
            return Err(TreeError::WrongLeafLength {
                expected,
                actual: bytes.len(),
            });
        }

        if index + 1 == self.leaf_count() && expected < LEAF_BYTES {
            self.trailing.clear();
            self.trailing.extend_from_slice(bytes);
        }
        self.replace_cv(index, Self::leaf_cv(index, bytes));
        if self.leaf_count() == 1 {
            self.single_leaf_root = Blake3Hash::from_bytes(bytes);
        }
        Ok(())
    }

    /// Replaces an aligned run of complete retained leaves.
    ///
    /// This intentionally cannot include a short final leaf; use
    /// [`Self::replace_leaf`] for that leaf.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte range is not retained-leaf-aligned, is
    /// outside the tree, or includes a short final leaf.
    pub fn replace_leaves(
        &mut self,
        first: usize,
        bytes: impl AsRef<[u8]>,
    ) -> Result<(), TreeError> {
        let bytes = bytes.as_ref();
        if bytes.len() % LEAF_BYTES != 0 {
            return Err(TreeError::UnalignedRange {
                len: bytes.len(),
                leaf_bytes: LEAF_BYTES,
            });
        }
        let count = bytes.len() / LEAF_BYTES;
        if first
            .checked_add(count)
            .is_none_or(|end| end > self.leaf_count())
        {
            return Err(TreeError::LeafOutOfBounds {
                index: first.saturating_add(count).saturating_sub(1),
                leaf_count: self.leaf_count(),
            });
        }
        for index in first..first + count {
            let expected = self.leaf_len(index)?;
            if expected != LEAF_BYTES {
                return Err(TreeError::WrongLeafLength {
                    expected,
                    actual: LEAF_BYTES,
                });
            }
        }
        for (offset, leaf) in bytes.chunks_exact(LEAF_BYTES).enumerate() {
            let index = first + offset;
            self.replace_cv(index, Self::leaf_cv(index, leaf));
        }
        if self.leaf_count() == 1 && count == 1 {
            self.single_leaf_root = Blake3Hash::from_bytes(bytes);
        }
        Ok(())
    }

    fn assert_geometry() {
        assert!(
            LEAF_BYTES >= CHUNK_BYTES
                && LEAF_BYTES.is_power_of_two()
                && LEAF_BYTES.is_multiple_of(CHUNK_BYTES),
            "retained BLAKE3 leaves must be a power-of-two multiple of 1024 bytes"
        );
    }

    fn leaf_len(&self, index: usize) -> Result<usize, TreeError> {
        if index >= self.leaf_count() {
            return Err(TreeError::LeafOutOfBounds {
                index,
                leaf_count: self.leaf_count(),
            });
        }
        if index + 1 == self.leaf_count() && !self.trailing.is_empty() {
            Ok(self.trailing.len())
        } else {
            Ok(LEAF_BYTES)
        }
    }

    fn leaf_cv(index: usize, bytes: &[u8]) -> Blake3Cv {
        let offset = index
            .checked_mul(LEAF_BYTES)
            .and_then(|n| u64::try_from(n).ok())
            .expect("a BLAKE3 input offset must fit in u64");
        Blake3Cv::from_subtree(offset, bytes)
    }

    fn push_cv(&mut self, cv: Blake3Cv) {
        let index = self.levels[0].len();
        self.levels[0].push(cv);
        self.update_ancestors(index);
    }

    fn replace_cv(&mut self, index: usize, cv: Blake3Cv) {
        self.levels[0][index] = cv;
        self.update_ancestors(index);
    }

    fn update_ancestors(&mut self, mut index: usize) {
        let mut level = 0;
        while self.levels[level].len() > 1 {
            let parent_index = index / 2;
            let child_index = parent_index * 2;
            let parent = if let Some(right) = self.levels[level].get(child_index + 1) {
                self.levels[level][child_index].merge(*right)
            } else {
                self.levels[level][child_index]
            };

            if self.levels.len() == level + 1 {
                self.levels.push(Vec::new());
            }
            let parent_count = self.levels[level].len().div_ceil(2);
            let parents = &mut self.levels[level + 1];
            if parent_index == parents.len() {
                parents.push(parent);
            } else {
                parents[parent_index] = parent;
            }
            parents.truncate(parent_count);
            index = parent_index;
            level += 1;
        }
        self.levels.truncate(level + 1);
    }
}

impl<const LEAF_BYTES: usize> FixedTree<LEAF_BYTES> {
    /// Builds a fixed-length tree from bytes.
    ///
    /// # Panics
    ///
    /// Panics when `LEAF_BYTES` is not a power-of-two multiple of 1 KiB.
    #[must_use]
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        Self {
            tree: EagerTree::from_bytes(bytes),
        }
    }

    /// Number of bytes represented by this tree.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.tree.len()
    }

    /// Whether this tree represents the empty byte string.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Number of retained leaves.
    #[must_use]
    pub fn leaf_count(&self) -> usize {
        self.tree.leaf_count()
    }

    /// Returns the standard BLAKE3 root hash.
    #[must_use]
    pub fn root(&self) -> Blake3Hash {
        self.tree.root()
    }

    /// Replaces one retained leaf without changing the fixed length.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is outside the tree or the replacement has
    /// a different length from the existing leaf.
    pub fn replace_leaf(&mut self, index: usize, bytes: impl AsRef<[u8]>) -> Result<(), TreeError> {
        self.tree.replace_leaf(index, bytes)
    }

    /// Replaces an aligned run of complete retained leaves.
    ///
    /// # Errors
    ///
    /// Returns an error if the byte range is not retained-leaf-aligned, is
    /// outside the tree, or includes a short final leaf.
    pub fn replace_leaves(
        &mut self,
        first: usize,
        bytes: impl AsRef<[u8]>,
    ) -> Result<(), TreeError> {
        self.tree.replace_leaves(first, bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn painted(len: usize) -> Vec<u8> {
        (0..len)
            .map(|index| {
                let index = index as u64;
                index
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .rotate_left(17)
                    .to_le_bytes()[0]
            })
            .collect()
    }

    fn assert_reference<const LEAF_BYTES: usize>(bytes: &[u8]) {
        let tree = EagerTree::<LEAF_BYTES>::from_bytes(bytes);
        assert_eq!(tree.len(), bytes.len());
        assert_eq!(tree.is_empty(), bytes.is_empty());
        assert_eq!(tree.root(), Blake3Hash::from_bytes(bytes));
        assert_eq!(tree.leaf_count(), bytes.len().div_ceil(LEAF_BYTES));
        assert_eq!(
            tree.trailing_bytes(),
            &bytes[bytes.len() / LEAF_BYTES * LEAF_BYTES..]
        );
    }

    fn assert_boundaries<const LEAF_BYTES: usize>() {
        for len in [
            0,
            1,
            63,
            64,
            CHUNK_BYTES - 1,
            CHUNK_BYTES,
            CHUNK_BYTES + 1,
            LEAF_BYTES - 1,
            LEAF_BYTES,
            LEAF_BYTES + 1,
            2 * LEAF_BYTES - 1,
            2 * LEAF_BYTES,
            2 * LEAF_BYTES + 1,
            3 * LEAF_BYTES + 17,
            8 * LEAF_BYTES,
            8 * LEAF_BYTES + CHUNK_BYTES + 3,
        ] {
            assert_reference::<LEAF_BYTES>(&painted(len));
        }
    }

    #[test]
    fn roots_match_blake3_at_native_and_pruned_boundaries() {
        assert_boundaries::<1024>();
        assert_boundaries::<4096>();
        assert_boundaries::<65536>();
    }

    fn assert_fragmented_append<const LEAF_BYTES: usize>() {
        let bytes = painted(5 * LEAF_BYTES + CHUNK_BYTES + 79);
        let mut tree = EagerTree::<LEAF_BYTES>::new();
        let mut offset: usize = 0;
        for requested in [
            1,
            17,
            CHUNK_BYTES - 18,
            1,
            LEAF_BYTES - CHUNK_BYTES,
            LEAF_BYTES + 3,
            2 * LEAF_BYTES - 5,
            7,
            usize::MAX,
        ] {
            let end = offset.saturating_add(requested).min(bytes.len());
            tree.append(&bytes[offset..end]).unwrap();
            offset = end;
            assert_eq!(tree.root(), Blake3Hash::from_bytes(&bytes[..offset]));
            assert_eq!(tree.len(), offset);
            if offset == bytes.len() {
                break;
            }
        }
        assert_eq!(offset, bytes.len());
    }

    #[test]
    fn fragmented_append_preserves_only_the_incomplete_leaf() {
        assert_fragmented_append::<1024>();
        assert_fragmented_append::<4096>();
        assert_fragmented_append::<65536>();
    }

    fn assert_edits<const LEAF_BYTES: usize>() {
        let mut bytes = painted(4 * LEAF_BYTES + LEAF_BYTES / 2 + 19);
        let mut tree = EagerTree::<LEAF_BYTES>::from_bytes(&bytes);

        for index in [0, 2, 3, 1] {
            let byte = u8::try_from(index)
                .unwrap_or_default()
                .wrapping_mul(53)
                .wrapping_add(11);
            let replacement = vec![byte; LEAF_BYTES];
            tree.replace_leaf(index, &replacement).unwrap();
            bytes[index * LEAF_BYTES..(index + 1) * LEAF_BYTES].copy_from_slice(&replacement);
            assert_eq!(tree.root(), Blake3Hash::from_bytes(&bytes));
        }

        let final_index = tree.leaf_count() - 1;
        let final_len = bytes.len() - final_index * LEAF_BYTES;
        let replacement = vec![0xd7; final_len];
        tree.replace_leaf(final_index, &replacement).unwrap();
        bytes[final_index * LEAF_BYTES..].copy_from_slice(&replacement);
        assert_eq!(tree.trailing_bytes(), replacement);
        assert_eq!(tree.root(), Blake3Hash::from_bytes(&bytes));

        let replacements = vec![0x4b; 2 * LEAF_BYTES];
        tree.replace_leaves(1, &replacements).unwrap();
        bytes[LEAF_BYTES..3 * LEAF_BYTES].copy_from_slice(&replacements);
        assert_eq!(tree.root(), Blake3Hash::from_bytes(&bytes));
    }

    #[test]
    fn aligned_edits_match_reference_hashes_for_each_geometry() {
        assert_edits::<1024>();
        assert_edits::<4096>();
        assert_edits::<65536>();
    }

    #[test]
    fn sole_complete_leaf_keeps_a_root_without_keeping_its_bytes() {
        let original = painted(4096);
        let mut tree = EagerTree::<4096>::from_bytes(&original);
        assert!(tree.trailing_bytes().is_empty());
        assert_eq!(tree.root(), Blake3Hash::from_bytes(&original));

        let replacement = vec![0xa5; 4096];
        tree.replace_leaf(0, &replacement).unwrap();
        assert!(tree.trailing_bytes().is_empty());
        assert_eq!(tree.root(), Blake3Hash::from_bytes(&replacement));

        tree.append(b"right edge").unwrap();
        let mut expected = replacement;
        expected.extend_from_slice(b"right edge");
        assert_eq!(tree.root(), Blake3Hash::from_bytes(expected));
    }

    #[test]
    fn fixed_tree_updates_but_does_not_change_geometry() {
        let mut bytes = painted(2 * 4096 + 777);
        let mut tree = FixedTree::<4096>::from_bytes(&bytes);
        let len = tree.len();
        let leaves = tree.leaf_count();

        let replacement = vec![0x31; 4096];
        tree.replace_leaf(1, &replacement).unwrap();
        bytes[4096..8192].copy_from_slice(&replacement);
        assert_eq!(tree.len(), len);
        assert_eq!(tree.leaf_count(), leaves);
        assert_eq!(tree.root(), Blake3Hash::from_bytes(bytes));
    }

    #[test]
    fn invalid_edits_are_rejected_without_changing_the_root() {
        let bytes = painted(4096 + 19);
        let mut tree = EagerTree::<4096>::from_bytes(&bytes);
        let root = tree.root();

        assert_eq!(
            tree.replace_leaf(2, []),
            Err(TreeError::LeafOutOfBounds {
                index: 2,
                leaf_count: 2,
            })
        );
        assert_eq!(
            tree.replace_leaf(0, [0; 17]),
            Err(TreeError::WrongLeafLength {
                expected: 4096,
                actual: 17,
            })
        );
        assert_eq!(
            tree.replace_leaves(0, [0; 4097]),
            Err(TreeError::UnalignedRange {
                len: 4097,
                leaf_bytes: 4096,
            })
        );
        assert_eq!(
            tree.replace_leaves(0, [0; 8192]),
            Err(TreeError::WrongLeafLength {
                expected: 19,
                actual: 4096,
            })
        );
        assert_eq!(tree.root(), root);
    }

    #[test]
    #[should_panic(expected = "power-of-two multiple")]
    fn invalid_retained_geometry_is_rejected() {
        let _ = EagerTree::<3072>::new();
    }
}
