//! Preallocated, I/O-free state for ordinary unkeyed BLAKE3 proofs.
//!
//! The total byte length fixes the complete tree geometry, so construction
//! allocates every non-root CV slot and its validity bitmap exactly once.
//! Callers may then stream bytes from the beginning with [`Blake3ProofState::append`]
//! or fill complete chunk-aligned ranges out of order with
//! [`Blake3ProofState::insert_aligned`].

use std::{collections::BTreeMap, error::Error, fmt, ops::Range};

use super::{Blake3Cv, Blake3Hash};

const CHUNK_BYTES: u64 = blake3::CHUNK_LEN as u64;

/// A canonical non-root position in a fixed BLAKE3 tree.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Blake3Node {
    first_chunk: u64,
    chunks: u64,
}

impl Blake3Node {
    /// Describes a non-empty candidate subtree in chunk units.
    ///
    /// Canonicality depends on the complete input length and is checked when
    /// the node enters a [`Blake3ProofState`].
    ///
    /// # Errors
    ///
    /// Returns [`ProofStateError::InvalidNode`] for zero chunks or overflow.
    pub const fn new(first_chunk: u64, chunks: u64) -> Result<Self, ProofStateError> {
        if chunks == 0 || first_chunk.checked_add(chunks).is_none() {
            Err(ProofStateError::InvalidNode {
                node: Self {
                    first_chunk,
                    chunks,
                },
            })
        } else {
            Ok(Self {
                first_chunk,
                chunks,
            })
        }
    }

    /// Index of the first 1 KiB BLAKE3 chunk.
    #[must_use]
    pub const fn first_chunk(self) -> u64 {
        self.first_chunk
    }

    /// Number of BLAKE3 chunks represented by this node.
    #[must_use]
    pub const fn chunks(self) -> u64 {
        self.chunks
    }
}

/// One untrusted canonical CV assertion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Blake3ProofNode {
    /// Claimed tree position.
    pub node: Blake3Node,
    /// Claimed non-root chaining value.
    pub cv: Blake3Cv,
}

/// Chunk-rounded disclosure geometry and its outside proof frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3Proof {
    /// Exact caller-requested byte range.
    pub requested: Range<u64>,
    /// Chunk-rounded bytes which must be disclosed.
    pub disclosed: Range<u64>,
    /// Canonical outside frontier, ordered left-to-right.
    pub nodes: Vec<Blake3ProofNode>,
}

/// Invalid geometry, contradictory evidence, or failed root verification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStateError {
    /// The fixed tree cannot be represented on this platform.
    TreeTooLarge,
    /// Invalid byte range for the fixed input.
    InvalidRange {
        /// Inclusive byte offset.
        offset: u64,
        /// Supplied byte count.
        length: u64,
        /// Complete input length.
        size: u64,
    },
    /// Sequential input would exceed the declared size.
    AppendPastEnd {
        /// Bytes already appended.
        appended: u64,
        /// Additional bytes offered.
        additional: u64,
        /// Complete input length.
        size: u64,
    },
    /// The node is empty, overflowing, outside, the virtual root, or not a
    /// canonical subtree of this fixed tree.
    InvalidNode {
        /// Rejected node.
        node: Blake3Node,
    },
    /// Existing and newly supplied evidence disagree.
    ConflictingNode {
        /// Position of the first detected disagreement.
        node: Blake3Node,
    },
    /// Complete evidence derives a different root from the expected root.
    RootMismatch {
        /// Root supplied when the state was constructed.
        expected: Blake3Hash,
        /// Root derived from supplied bytes and CVs.
        actual: Blake3Hash,
    },
    /// Proof generation lacks one or more canonical outside nodes.
    MissingProof {
        /// Minimal missing frontier.
        nodes: Vec<Blake3Node>,
    },
}

impl fmt::Display for ProofStateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for ProofStateError {}

/// Fixed-size, preallocated proof state for ordinary unkeyed BLAKE3.
///
/// No reader, callback, file, database, or async operation is stored here.
/// Imported CVs remain untrusted evidence. Supplying enough evidence derives a
/// pure [`Blake3Hash`], and an optional expected root is checked before the
/// evidence is committed.
#[derive(Clone)]
pub struct Blake3ProofState {
    size: u64,
    chunks: u64,
    expected_root: Option<Blake3Hash>,
    nodes: Vec<Blake3Cv>,
    known: KnownBits,
    claimed_root: Option<Blake3Hash>,
    appended: u64,
    trailing: Vec<u8>,
}

impl Blake3ProofState {
    /// Allocates the exact non-root CV buffer for `size`.
    ///
    /// `expected_root` changes verification, not tree geometry. With no
    /// expected root the state can instead generate a root from complete
    /// evidence.
    ///
    /// # Errors
    ///
    /// Returns [`ProofStateError::TreeTooLarge`] when the node count cannot be
    /// indexed on this platform.
    pub fn new(size: u64, expected_root: Option<Blake3Hash>) -> Result<Self, ProofStateError> {
        let chunks = size.div_ceil(CHUNK_BYTES);
        let node_count = match chunks {
            0 => 0,
            1 => 1,
            _ => chunks
                .checked_mul(2)
                .and_then(|count| count.checked_sub(2))
                .ok_or(ProofStateError::TreeTooLarge)?,
        };
        let node_count = usize::try_from(node_count).map_err(|_| ProofStateError::TreeTooLarge)?;
        let claimed_root = (size == 0).then(|| Blake3Hash::from_bytes([]));
        if let (Some(expected), Some(actual)) = (expected_root, claimed_root)
            && expected != actual
        {
            return Err(ProofStateError::RootMismatch { expected, actual });
        }
        Ok(Self {
            size,
            chunks,
            expected_root,
            nodes: vec![Blake3Cv::default(); node_count],
            known: KnownBits::new(node_count),
            claimed_root,
            appended: 0,
            trailing: Vec::new(),
        })
    }

    /// Complete byte length fixed at construction.
    #[must_use]
    pub const fn size(&self) -> u64 {
        self.size
    }

    /// Number of native BLAKE3 chunks, with zero for empty input.
    #[must_use]
    pub const fn chunks(&self) -> u64 {
        self.chunks
    }

    /// Exact number of allocated non-root CV slots.
    #[must_use]
    pub fn node_capacity(&self) -> usize {
        self.nodes.len()
    }

    /// Root against which imported evidence is checked, if any.
    #[must_use]
    pub const fn expected_root(&self) -> Option<Blake3Hash> {
        self.expected_root
    }

    /// Derived pure BLAKE3 root once sufficient evidence is present.
    #[must_use]
    pub const fn claimed_root(&self) -> Option<Blake3Hash> {
        self.claimed_root
    }

    /// Number of bytes accepted through sequential [`Self::append`] calls.
    #[must_use]
    pub const fn appended(&self) -> u64 {
        self.appended
    }

    /// Incomplete sequential chunk retained for a later append.
    #[must_use]
    pub fn trailing_bytes(&self) -> &[u8] {
        &self.trailing
    }

    /// Appends the next sequential bytes without changing fixed geometry.
    ///
    /// Complete chunks are reduced to CVs immediately. At most one native
    /// BLAKE3 chunk remains in `trailing_bytes`.
    ///
    /// # Errors
    ///
    /// Returns an error before mutation if the bytes exceed `size`, conflict
    /// with evidence already inserted out of order, or derive the wrong root.
    pub fn append(&mut self, bytes: impl AsRef<[u8]>) -> Result<(), ProofStateError> {
        let bytes = bytes.as_ref();
        let additional = u64::try_from(bytes.len()).map_err(|_| ProofStateError::TreeTooLarge)?;
        let new_appended =
            self.appended
                .checked_add(additional)
                .ok_or(ProofStateError::AppendPastEnd {
                    appended: self.appended,
                    additional,
                    size: self.size,
                })?;
        if new_appended > self.size {
            return Err(ProofStateError::AppendPastEnd {
                appended: self.appended,
                additional,
                size: self.size,
            });
        }
        if bytes.is_empty() {
            return Ok(());
        }

        let mut trailing = self.trailing.clone();
        let mut input = bytes;
        let mut completed = Vec::new();
        let trailing_len =
            u64::try_from(trailing.len()).map_err(|_| ProofStateError::TreeTooLarge)?;
        let mut chunk_start = self.appended - trailing_len;
        while !input.is_empty() {
            let expected = usize::try_from(self.chunk_length(chunk_start / CHUNK_BYTES))
                .map_err(|_| ProofStateError::TreeTooLarge)?;
            let take = (expected - trailing.len()).min(input.len());
            trailing.extend_from_slice(&input[..take]);
            input = &input[take..];
            if trailing.len() == expected {
                let node = Blake3Node {
                    first_chunk: chunk_start / CHUNK_BYTES,
                    chunks: 1,
                };
                completed.push((
                    Blake3ProofNode {
                        node,
                        cv: Blake3Cv::from_subtree(chunk_start, &trailing),
                    },
                    (self.chunks == 1).then(|| Blake3Hash::from_bytes(&trailing)),
                ));
                trailing.clear();
                chunk_start +=
                    u64::try_from(expected).map_err(|_| ProofStateError::TreeTooLarge)?;
            }
        }

        let single_root = completed.iter().find_map(|(_, root)| *root);
        self.insert_batch(completed.into_iter().map(|(node, _)| node), single_root)?;
        self.appended = new_appended;
        self.trailing = trailing;
        Ok(())
    }

    /// Hashes and inserts a non-empty chunk-aligned byte range.
    ///
    /// The range end may be unaligned only at the complete input's end. This
    /// path is independent of the sequential append cursor.
    ///
    /// # Errors
    ///
    /// Returns an error before mutation for invalid geometry, contradictory
    /// evidence, or a derived root mismatch.
    pub fn insert_aligned(
        &mut self,
        offset: u64,
        bytes: impl AsRef<[u8]>,
    ) -> Result<(), ProofStateError> {
        let bytes = bytes.as_ref();
        let length = u64::try_from(bytes.len()).map_err(|_| ProofStateError::TreeTooLarge)?;
        self.validate_byte_range(offset, length)?;
        let mut evidence = Vec::with_capacity(bytes.len().div_ceil(blake3::CHUNK_LEN));
        for (index, chunk) in bytes.chunks(blake3::CHUNK_LEN).enumerate() {
            let chunk_offset = offset
                + u64::try_from(index).map_err(|_| ProofStateError::TreeTooLarge)? * CHUNK_BYTES;
            evidence.push(Blake3ProofNode {
                node: Blake3Node {
                    first_chunk: chunk_offset / CHUNK_BYTES,
                    chunks: 1,
                },
                cv: Blake3Cv::from_subtree(chunk_offset, chunk),
            });
        }
        let single_root = (self.chunks == 1).then(|| Blake3Hash::from_bytes(bytes));
        self.insert_batch(evidence, single_root)
    }

    /// Inserts one externally supplied, untrusted CV claim.
    ///
    /// # Errors
    ///
    /// Returns an error before mutation unless the node is canonical and
    /// compatible with all existing evidence and the optional expected root.
    pub fn insert_node(&mut self, evidence: Blake3ProofNode) -> Result<(), ProofStateError> {
        self.insert_batch([evidence], None)
    }

    /// Inserts several externally supplied CV claims atomically.
    ///
    /// # Errors
    ///
    /// Returns an error before mutation for invalid geometry, contradictory
    /// evidence, or a derived root mismatch.
    pub fn insert_nodes(
        &mut self,
        evidence: impl IntoIterator<Item = Blake3ProofNode>,
    ) -> Result<(), ProofStateError> {
        self.insert_batch(evidence, None)
    }

    /// Minimal canonical frontier still needed to derive a root.
    #[must_use]
    pub fn holes(&self) -> Vec<Blake3Node> {
        if self.claimed_root.is_some() {
            return Vec::new();
        }
        if self.chunks == 0 {
            return Vec::new();
        }
        if self.chunks == 1 {
            return vec![Blake3Node {
                first_chunk: 0,
                chunks: 1,
            }];
        }
        let (left, right) = children(Blake3Node {
            first_chunk: 0,
            chunks: self.chunks,
        });
        let mut output = Vec::new();
        self.collect_holes(left, &mut output);
        self.collect_holes(right, &mut output);
        output
    }

    /// Builds the minimal outside frontier for a requested byte range.
    ///
    /// The returned `disclosed` range is rounded out to native BLAKE3 chunks.
    /// This method returns proof CVs only; the caller obtains the disclosed
    /// bytes independently.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty/out-of-bounds request or when required
    /// outside CVs are not present.
    pub fn proof(&self, requested: Range<u64>) -> Result<Blake3Proof, ProofStateError> {
        if requested.start >= requested.end || requested.end > self.size {
            return Err(ProofStateError::InvalidRange {
                offset: requested.start,
                length: requested.end.saturating_sub(requested.start),
                size: self.size,
            });
        }
        let disclosed = (requested.start / CHUNK_BYTES * CHUNK_BYTES)
            ..requested
                .end
                .div_ceil(CHUNK_BYTES)
                .saturating_mul(CHUNK_BYTES)
                .min(self.size);
        if self.chunks <= 1 {
            return Ok(Blake3Proof {
                requested,
                disclosed,
                nodes: Vec::new(),
            });
        }

        let (left, right) = children(Blake3Node {
            first_chunk: 0,
            chunks: self.chunks,
        });
        let mut nodes = Vec::new();
        let mut missing = Vec::new();
        self.collect_proof(left, &disclosed, &mut nodes, &mut missing);
        self.collect_proof(right, &disclosed, &mut nodes, &mut missing);
        if missing.is_empty() {
            Ok(Blake3Proof {
                requested,
                disclosed,
                nodes,
            })
        } else {
            Err(ProofStateError::MissingProof { nodes: missing })
        }
    }

    fn insert_batch(
        &mut self,
        evidence: impl IntoIterator<Item = Blake3ProofNode>,
        single_root: Option<Blake3Hash>,
    ) -> Result<(), ProofStateError> {
        let mut staged = BTreeMap::new();
        let mut proposed_root = self.claimed_root.or(single_root);
        if let (Some(existing), Some(supplied)) = (self.claimed_root, single_root)
            && existing != supplied
        {
            return Err(ProofStateError::RootMismatch {
                expected: existing,
                actual: supplied,
            });
        }

        for evidence in evidence {
            let slot = self
                .slot(evidence.node)
                .ok_or(ProofStateError::InvalidNode {
                    node: evidence.node,
                })?;
            self.stage_value(evidence.node, slot, evidence.cv, &mut staged)?;
            if let Some(derived) = self.derive_from_children(evidence.node, &staged)
                && derived != evidence.cv
            {
                return Err(ProofStateError::ConflictingNode {
                    node: evidence.node,
                });
            }

            let mut current = evidence.node;
            while let Some((parent, sibling, current_is_left)) = self.parent_step(current) {
                let Some(current_cv) = self.value(current, &staged) else {
                    break;
                };
                let Some(sibling_cv) = self.value(sibling, &staged) else {
                    break;
                };
                let (left, right) = if current_is_left {
                    (current_cv, sibling_cv)
                } else {
                    (sibling_cv, current_cv)
                };
                if let Some(parent) = parent {
                    let parent_cv = left.merge(right);
                    let parent_slot = self.slot(parent).expect("canonical non-root parent");
                    self.stage_value(parent, parent_slot, parent_cv, &mut staged)?;
                    current = parent;
                } else {
                    let root = left.root(right);
                    if let Some(existing) = proposed_root
                        && existing != root
                    {
                        return Err(ProofStateError::RootMismatch {
                            expected: existing,
                            actual: root,
                        });
                    }
                    proposed_root = Some(root);
                    break;
                }
            }
        }

        if let (Some(expected), Some(actual)) = (self.expected_root, proposed_root)
            && expected != actual
        {
            return Err(ProofStateError::RootMismatch { expected, actual });
        }
        for (slot, cv) in staged {
            self.nodes[slot] = cv;
            self.known.insert(slot);
        }
        self.claimed_root = proposed_root;
        Ok(())
    }

    fn stage_value(
        &self,
        node: Blake3Node,
        slot: usize,
        cv: Blake3Cv,
        staged: &mut BTreeMap<usize, Blake3Cv>,
    ) -> Result<(), ProofStateError> {
        if let Some(existing) = staged
            .get(&slot)
            .copied()
            .or_else(|| self.known.contains(slot).then(|| self.nodes[slot]))
            && existing != cv
        {
            return Err(ProofStateError::ConflictingNode { node });
        }
        staged.insert(slot, cv);
        Ok(())
    }

    fn value(&self, node: Blake3Node, staged: &BTreeMap<usize, Blake3Cv>) -> Option<Blake3Cv> {
        let slot = self.slot(node)?;
        staged
            .get(&slot)
            .copied()
            .or_else(|| self.known.contains(slot).then(|| self.nodes[slot]))
    }

    fn stored_value(&self, node: Blake3Node) -> Option<Blake3Cv> {
        let slot = self.slot(node)?;
        self.known.contains(slot).then(|| self.nodes[slot])
    }

    fn derive_from_children(
        &self,
        node: Blake3Node,
        staged: &BTreeMap<usize, Blake3Cv>,
    ) -> Option<Blake3Cv> {
        if node.chunks == 1 {
            return None;
        }
        let (left, right) = children(node);
        Some(self.value(left, staged)?.merge(self.value(right, staged)?))
    }

    fn validate_byte_range(&self, offset: u64, length: u64) -> Result<(), ProofStateError> {
        let end = offset.checked_add(length);
        let valid = length != 0
            && offset.is_multiple_of(CHUNK_BYTES)
            && end.is_some_and(|end| {
                end <= self.size && (end == self.size || end.is_multiple_of(CHUNK_BYTES))
            });
        if valid {
            Ok(())
        } else {
            Err(ProofStateError::InvalidRange {
                offset,
                length,
                size: self.size,
            })
        }
    }

    fn chunk_length(&self, chunk: u64) -> u64 {
        (self.size - chunk * CHUNK_BYTES).min(CHUNK_BYTES)
    }

    fn slot(&self, needle: Blake3Node) -> Option<usize> {
        if self.chunks == 0 || needle.first_chunk + needle.chunks > self.chunks {
            return None;
        }
        if self.chunks == 1 {
            return (needle
                == Blake3Node {
                    first_chunk: 0,
                    chunks: 1,
                })
            .then_some(0);
        }
        let root = Blake3Node {
            first_chunk: 0,
            chunks: self.chunks,
        };
        if needle == root {
            return None;
        }
        let root_slot = inorder_internal_slot(root);
        canonical_in(root, needle).map(|inorder| {
            let packed = if inorder < root_slot {
                inorder
            } else {
                inorder - 1
            };
            usize::try_from(packed).expect("constructor validated node count")
        })
    }

    fn parent_step(&self, needle: Blake3Node) -> Option<(Option<Blake3Node>, Blake3Node, bool)> {
        if self.chunks <= 1 {
            return None;
        }
        parent_step_in(
            Blake3Node {
                first_chunk: 0,
                chunks: self.chunks,
            },
            needle,
            true,
        )
    }

    fn collect_holes(&self, node: Blake3Node, output: &mut Vec<Blake3Node>) {
        if self.stored_value(node).is_some() {
            return;
        }
        if node.chunks == 1 || !self.has_stored_descendant(node) {
            output.push(node);
        } else {
            let (left, right) = children(node);
            self.collect_holes(left, output);
            self.collect_holes(right, output);
        }
    }

    fn has_stored_descendant(&self, node: Blake3Node) -> bool {
        if node.chunks == 1 {
            return false;
        }
        let (left, right) = children(node);
        self.stored_value(left).is_some()
            || self.stored_value(right).is_some()
            || self.has_stored_descendant(left)
            || self.has_stored_descendant(right)
    }

    fn collect_proof(
        &self,
        node: Blake3Node,
        disclosed: &Range<u64>,
        output: &mut Vec<Blake3ProofNode>,
        missing: &mut Vec<Blake3Node>,
    ) {
        let bytes = self.node_bytes(node);
        let overlaps = bytes.start < disclosed.end && disclosed.start < bytes.end;
        if !overlaps {
            if let Some(cv) = self.stored_value(node) {
                output.push(Blake3ProofNode { node, cv });
            } else {
                missing.push(node);
            }
        } else if node.chunks > 1 {
            let (left, right) = children(node);
            self.collect_proof(left, disclosed, output, missing);
            self.collect_proof(right, disclosed, output, missing);
        }
    }

    fn node_bytes(&self, node: Blake3Node) -> Range<u64> {
        let start = node.first_chunk * CHUNK_BYTES;
        start..((node.first_chunk + node.chunks) * CHUNK_BYTES).min(self.size)
    }
}

#[derive(Clone)]
struct KnownBits {
    words: Vec<u64>,
}

impl KnownBits {
    fn new(bits: usize) -> Self {
        Self {
            words: vec![0; bits.div_ceil(u64::BITS as usize)],
        }
    }

    fn contains(&self, bit: usize) -> bool {
        self.words
            .get(bit / u64::BITS as usize)
            .is_some_and(|word| word & (1 << (bit % u64::BITS as usize)) != 0)
    }

    fn insert(&mut self, bit: usize) {
        self.words[bit / u64::BITS as usize] |= 1 << (bit % u64::BITS as usize);
    }
}

fn left_chunks(chunks: u64) -> u64 {
    1 << (u64::BITS - 1 - (chunks - 1).leading_zeros())
}

fn children(node: Blake3Node) -> (Blake3Node, Blake3Node) {
    let left = left_chunks(node.chunks);
    (
        Blake3Node {
            first_chunk: node.first_chunk,
            chunks: left,
        },
        Blake3Node {
            first_chunk: node.first_chunk + left,
            chunks: node.chunks - left,
        },
    )
}

fn inorder_internal_slot(node: Blake3Node) -> u64 {
    node.first_chunk * 2 + left_chunks(node.chunks) * 2 - 1
}

fn canonical_in(root: Blake3Node, needle: Blake3Node) -> Option<u64> {
    let root_end = root.first_chunk.checked_add(root.chunks)?;
    let needle_end = needle.first_chunk.checked_add(needle.chunks)?;
    if needle.first_chunk < root.first_chunk || needle_end > root_end {
        return None;
    }
    if root == needle {
        return Some(if root.chunks == 1 {
            root.first_chunk * 2
        } else {
            inorder_internal_slot(root)
        });
    }
    if root.chunks == 1 {
        return None;
    }
    let (left, right) = children(root);
    if needle_end <= right.first_chunk {
        canonical_in(left, needle)
    } else if needle.first_chunk >= right.first_chunk {
        canonical_in(right, needle)
    } else {
        None
    }
}

fn parent_step_in(
    root: Blake3Node,
    needle: Blake3Node,
    virtual_root: bool,
) -> Option<(Option<Blake3Node>, Blake3Node, bool)> {
    let (left, right) = children(root);
    if needle == left {
        return Some(((!virtual_root).then_some(root), right, true));
    }
    if needle == right {
        return Some(((!virtual_root).then_some(root), left, false));
    }
    if needle.first_chunk < right.first_chunk {
        parent_step_in(left, needle, false)
    } else {
        parent_step_in(right, needle, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(size: usize) -> Vec<u8> {
        (0..size)
            .map(|index| index.wrapping_mul(31).wrapping_add(index / 7).to_le_bytes()[0])
            .collect()
    }

    fn chunk_range(data: &[u8], chunk: usize) -> (u64, &[u8]) {
        let start = chunk * blake3::CHUNK_LEN;
        let end = (start + blake3::CHUNK_LEN).min(data.len());
        (u64::try_from(start).unwrap(), &data[start..end])
    }

    #[test]
    fn allocation_matches_fixed_tree_geometry() {
        let cases = [(0, 0), (1, 1), (2, 2), (3, 4), (4, 6), (5, 8)];
        for (chunks, slots) in cases {
            let size = chunks * blake3::CHUNK_LEN;
            let state = Blake3ProofState::new(u64::try_from(size).unwrap(), None).unwrap();
            assert_eq!(state.node_capacity(), slots);
        }
    }

    #[test]
    fn fragmented_append_reproduces_roots_without_growing_geometry() {
        for size in [0, 1, 63, 1_024, 1_025, 3_089, 7_211] {
            let data = bytes(size);
            let mut state = Blake3ProofState::new(u64::try_from(size).unwrap(), None).unwrap();
            let capacity = state.node_capacity();
            let mut offset = 0;
            for width in [1, 17, 1_003, 2, 2_111] {
                if offset == data.len() {
                    break;
                }
                let end = (offset + width).min(data.len());
                state.append(&data[offset..end]).unwrap();
                assert_eq!(state.node_capacity(), capacity);
                offset = end;
            }
            if offset < data.len() {
                state.append(&data[offset..]).unwrap();
            }
            assert_eq!(state.appended(), u64::try_from(size).unwrap());
            assert!(state.trailing_bytes().is_empty());
            assert_eq!(state.claimed_root(), Some(Blake3Hash::from_bytes(data)));
            assert!(state.holes().is_empty());
        }
    }

    #[test]
    fn aligned_chunks_may_arrive_out_of_order() {
        for chunks in [2, 3, 5, 8] {
            let data = bytes(chunks * blake3::CHUNK_LEN - 37);
            let expected = Blake3Hash::from_bytes(&data);
            let mut state = Blake3ProofState::new(data.len() as u64, Some(expected)).unwrap();
            for chunk in (0..chunks).rev() {
                let (offset, input) = chunk_range(&data, chunk);
                state.insert_aligned(offset, input).unwrap();
            }
            assert_eq!(state.claimed_root(), Some(expected));
        }
    }

    #[test]
    fn generated_range_proof_verifies_disclosed_bytes() {
        let data = bytes(6 * blake3::CHUNK_LEN + 317);
        let expected = Blake3Hash::from_bytes(&data);
        let mut source = Blake3ProofState::new(data.len() as u64, None).unwrap();
        source.insert_aligned(0, &data).unwrap();

        let requested = 2 * CHUNK_BYTES + 13..4 * CHUNK_BYTES + 29;
        let proof = source.proof(requested.clone()).unwrap();
        assert_eq!(proof.requested, requested);
        assert_eq!(proof.disclosed, 2 * CHUNK_BYTES..5 * CHUNK_BYTES);

        let mut verifier = Blake3ProofState::new(data.len() as u64, Some(expected)).unwrap();
        verifier.insert_nodes(proof.nodes).unwrap();
        let disclosed = proof.disclosed;
        let start = usize::try_from(disclosed.start).unwrap();
        let end = usize::try_from(disclosed.end).unwrap();
        verifier
            .insert_aligned(disclosed.start, &data[start..end])
            .unwrap();
        assert_eq!(verifier.claimed_root(), Some(expected));
    }

    #[test]
    fn proof_reports_the_minimal_missing_frontier() {
        let size = 4 * CHUNK_BYTES;
        let state = Blake3ProofState::new(size, None).unwrap();
        let error = state.proof(CHUNK_BYTES..2 * CHUNK_BYTES).unwrap_err();
        let ProofStateError::MissingProof { nodes } = error else {
            panic!("unexpected error: {error:?}");
        };
        assert_eq!(
            nodes,
            vec![
                Blake3Node::new(0, 1).unwrap(),
                Blake3Node::new(2, 2).unwrap(),
            ]
        );
    }

    #[test]
    fn internal_evidence_satisfies_holes_without_expanding_it() {
        let mut state = Blake3ProofState::new(4 * CHUNK_BYTES, None).unwrap();
        let left = Blake3Node::new(0, 2).unwrap();
        state
            .insert_node(Blake3ProofNode {
                node: left,
                cv: Blake3Cv::from_array([7; 32]),
            })
            .unwrap();
        assert_eq!(state.holes()[0], Blake3Node::new(2, 2).unwrap());
        assert_eq!(state.holes().len(), 1);
    }

    #[test]
    fn noncanonical_and_virtual_root_nodes_are_rejected() {
        let mut state = Blake3ProofState::new(4 * CHUNK_BYTES, None).unwrap();
        for node in [
            Blake3Node::new(1, 2).unwrap(),
            Blake3Node::new(0, 4).unwrap(),
            Blake3Node::new(4, 1).unwrap(),
        ] {
            assert!(matches!(
                state.insert_node(Blake3ProofNode {
                    node,
                    cv: Blake3Cv::default(),
                }),
                Err(ProofStateError::InvalidNode { .. })
            ));
        }
    }

    #[test]
    fn failed_batch_is_atomic() {
        let data = bytes(3 * blake3::CHUNK_LEN);
        let mut state = Blake3ProofState::new(data.len() as u64, None).unwrap();
        let (offset, chunk0) = chunk_range(&data, 0);
        state.insert_aligned(offset, chunk0).unwrap();
        let holes_before = state.holes();
        let (_, chunk1) = chunk_range(&data, 1);
        let error = state
            .insert_nodes([
                Blake3ProofNode {
                    node: Blake3Node::new(1, 1).unwrap(),
                    cv: Blake3Cv::from_subtree(CHUNK_BYTES, chunk1),
                },
                Blake3ProofNode {
                    node: Blake3Node::new(0, 1).unwrap(),
                    cv: Blake3Cv::default(),
                },
            ])
            .unwrap_err();
        assert!(matches!(error, ProofStateError::ConflictingNode { .. }));
        assert_eq!(state.holes(), holes_before);
    }

    #[test]
    fn wrong_expected_root_rejects_complete_input_atomically() {
        let data = bytes(2 * blake3::CHUNK_LEN);
        let wrong = Blake3Hash::from_array([42; 32]);
        let mut state = Blake3ProofState::new(data.len() as u64, Some(wrong)).unwrap();
        let holes = state.holes();
        assert!(matches!(
            state.insert_aligned(0, &data),
            Err(ProofStateError::RootMismatch { expected, .. }) if expected == wrong
        ));
        assert_eq!(state.holes(), holes);
        assert_eq!(state.claimed_root(), None);
    }

    #[test]
    fn invalid_ranges_and_append_overflow_do_not_mutate_state() {
        let mut state = Blake3ProofState::new(2 * CHUNK_BYTES, None).unwrap();
        assert!(matches!(
            state.insert_aligned(1, [0; 32]),
            Err(ProofStateError::InvalidRange { .. })
        ));
        assert!(matches!(
            state.append(vec![0; 2 * blake3::CHUNK_LEN + 1]),
            Err(ProofStateError::AppendPastEnd { .. })
        ));
        assert_eq!(state.appended(), 0);
        assert_eq!(state.holes().len(), 2);
    }
}
