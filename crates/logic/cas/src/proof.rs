//! Checking a byte range against the BLAKE3 tree above it.
//!
//! # The level-`l` view
//!
//! BLAKE3 splits its input into 1024-byte chunks and builds a *left-complete*
//! binary tree over them: every node's left child is the largest power of two
//! of chunks that fits strictly inside it. Two consequences drive everything
//! here. Every aligned, complete subtree is a real node of that tree, and so is
//! every truncated node along its right edge.
//!
//! So a blob of `n` bytes viewed at level `l` is `n.div_ceil(1024 << l)` leaves,
//! all complete but possibly the last, and the tree above those leaves is again
//! the left-complete binary tree. A larger level simply makes the leaves
//! coarser: it shortens the spines, at the cost of forcing ranges onto coarser
//! boundaries.
//!
//! # The proof object
//!
//! A [`RangeProof`] is the level plus the two *spines*: the chaining values of
//! the siblings met while climbing from the proven range to the root, on the
//! left and on the right. The left spine is the maximal aligned blocks of the
//! leaves before the range, widest first, so it has one entry per set bit of
//! the range's first leaf index. The right spine is whatever hangs off the
//! climb to the right, truncated right-edge nodes included, which is why the
//! proof needs no length field: a truncated node arrives as a single chaining
//! value rather than as a decomposition whose shape only the blob's length
//! would reveal.
//!
//! # What a successful check means
//!
//! [`RangeProof::check`] recomputes the root through a genuine BLAKE3 tree
//! computation, with the range's own bytes hashed at the offsets the range
//! claims for them. If that reproduces the claimed address then, under BLAKE3's
//! collision resistance, the blob at that address really does hold those bytes
//! there. Spines describing a tree of the wrong shape simply fail.
//!
//! One case does not follow from the hash alone. A range with an open upper
//! bound also claims the blob *ends* where its bytes end, and a non-empty right
//! spine would let the first half of a blob pass as the whole of it, so such
//! proofs must carry no right spine at all.

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::blake3::Blake3Cv;

use crate::{BlobRange, Bytes, CasCheckError, CasRangeAssertion, CasRangeFact, O256};

/// The number of bytes in a level-zero block: one BLAKE3 chunk.
pub const BLOCK_LEN: u64 = Blake3Cv::CHUNK_LEN;

/// The largest level whose block length fits in a `u64`.
pub const MAX_LEVEL: u32 = u64::BITS - 1 - BLOCK_LEN.trailing_zeros();

/// Returns the number of bytes in a level-`level` block.
#[must_use]
pub const fn block_len(level: u32) -> Option<u64> {
    if level <= MAX_LEVEL {
        Some(BLOCK_LEN << level)
    } else {
        None
    }
}

/// The chaining values surrounding a proven range.
///
/// [`Given`] reads them from a proof and [`Computed`] derives them from a
/// complete blob, which lets checking and proving share one fold.
pub(crate) trait Spine {
    /// Returns the chaining value of the left-spine block `[start, start + capacity)`.
    fn left(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv>;

    /// Returns the chaining value of the right sibling of `[start, start + capacity)`.
    fn right(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv>;

    /// Reports whether `[start, start + capacity)` has a right sibling.
    fn has_right(&self, start: u64, capacity: u64) -> bool;
}

impl<S: Spine + ?Sized> Spine for &mut S {
    fn left(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv> {
        (**self).left(start, capacity)
    }

    fn right(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv> {
        (**self).right(start, capacity)
    }

    fn has_right(&self, start: u64, capacity: u64) -> bool {
        (**self).has_right(start, capacity)
    }
}

/// Chaining values read from a proof, in order.
struct Given<'proof> {
    left: &'proof [Blake3Cv],
    right: &'proof [Blake3Cv],
}

impl Spine for Given<'_> {
    fn left(&mut self, _start: u64, _capacity: u64) -> Option<Blake3Cv> {
        let (head, rest) = self.left.split_first()?;
        self.left = rest;
        Some(*head)
    }

    fn right(&mut self, _start: u64, _capacity: u64) -> Option<Blake3Cv> {
        let (head, rest) = self.right.split_first()?;
        self.right = rest;
        Some(*head)
    }

    fn has_right(&self, _start: u64, _capacity: u64) -> bool {
        !self.right.is_empty()
    }
}

/// A node of the level-`l` tree, addressed in leaves.
///
/// `capacity` is the node's width in a complete tree. A node on the right edge
/// spans fewer leaves than that and reaches its parent by doubling its capacity
/// without merging with anything.
#[derive(Clone, Copy, Debug)]
struct Node {
    start: u64,
    capacity: u64,
    cv: Blake3Cv,
}

/// The stack fold rebuilding a root from a covered leaf range and its spines.
struct Fold<S> {
    stack: Vec<Node>,
    spine: S,
    pending: u64,
}

impl<S: Spine> Fold<S> {
    /// Reports whether a merge producing `[start, ..)` with the given capacity
    /// is the root merge: nothing is left to push, and nothing is left to merge
    /// with.
    fn is_root(&self, height: usize, start: u64, capacity: u64) -> bool {
        height == 1 && start == 0 && self.pending == 0 && !self.spine.has_right(start, capacity)
    }

    /// Merges while the top of the stack is a right child, so that on return
    /// the top is a left child and can take a right sibling.
    fn settle(&mut self) -> Result<Option<O256>, RangeProofError> {
        loop {
            let Some(&Node {
                start, capacity, ..
            }) = self.stack.last()
            else {
                return Ok(None);
            };
            if (start / capacity) % 2 == 0 {
                return Ok(None);
            }
            if self.stack.len() < 2 {
                return Err(RangeProofError::Malformed);
            }
            let top = self.stack.pop().ok_or(RangeProofError::Malformed)?;
            let below = self.stack.pop().ok_or(RangeProofError::Malformed)?;
            if below.capacity != top.capacity
                || below.start.checked_add(below.capacity) != Some(top.start)
            {
                return Err(RangeProofError::Malformed);
            }
            let capacity = below
                .capacity
                .checked_mul(2)
                .ok_or(RangeProofError::Overflow)?;
            if self.is_root(self.stack.len() + 1, below.start, capacity) {
                return Ok(Some(below.cv.root(top.cv).into_o256()));
            }
            self.stack.push(Node {
                start: below.start,
                capacity,
                cv: below.cv.merge(top.cv),
            });
        }
    }

    /// Climbs from a settled stack to the root.
    fn climb(&mut self) -> Result<O256, RangeProofError> {
        loop {
            let Some(&Node {
                start,
                capacity,
                cv,
            }) = self.stack.last()
            else {
                return Err(RangeProofError::Malformed);
            };
            let doubled = capacity.checked_mul(2).ok_or(RangeProofError::Overflow)?;
            if let Some(sibling) = self.spine.right(start, capacity) {
                self.stack.pop();
                if self.is_root(self.stack.len() + 1, start, doubled) {
                    return Ok(cv.root(sibling).into_o256());
                }
                self.stack.push(Node {
                    start,
                    capacity: doubled,
                    cv: cv.merge(sibling),
                });
            } else if self.stack.len() == 1 {
                // Nothing is left to merge with, yet no merge produced a root.
                return Err(RangeProofError::Malformed);
            } else {
                // The right sibling is past the end of the blob, so this node
                // stands in for its own parent.
                let top = self.stack.last_mut().ok_or(RangeProofError::Malformed)?;
                top.capacity = doubled;
            }
            if let Some(root) = self.settle()? {
                return Ok(root);
            }
        }
    }
}

/// Recomputes a blob's root from `bytes`, which cover `leaves` leaves starting
/// at leaf `first`, together with the surrounding chaining values.
pub(crate) fn fold<S: Spine>(
    spine: S,
    block: u64,
    first: u64,
    leaves: u64,
    bytes: &[u8],
) -> Result<O256, RangeProofError> {
    let mut fold = Fold {
        stack: Vec::new(),
        spine,
        pending: leaves,
    };

    if first == 0 && leaves == 1 && !fold.spine.has_right(0, 1) {
        // The blob is a single leaf, so the range is the whole blob and its
        // root is an ordinary hash rather than the result of any merge.
        return Ok(O256::from_bytes(bytes));
    }

    // The leaves before the range decompose into maximal aligned blocks, one
    // per set bit of `first`, widest first.
    for bit in (0..u64::BITS).rev() {
        let capacity = 1u64 << bit;
        if first & capacity == 0 {
            continue;
        }
        let start = first & !(capacity | (capacity - 1));
        let cv = fold
            .spine
            .left(start, capacity)
            .ok_or(RangeProofError::Malformed)?;
        fold.stack.push(Node {
            start,
            capacity,
            cv,
        });
    }

    for index in 0..leaves {
        let leaf = first.checked_add(index).ok_or(RangeProofError::Overflow)?;
        let offset = index.checked_mul(block).ok_or(RangeProofError::Overflow)?;
        let from = usize::try_from(offset).map_err(|_| RangeProofError::Overflow)?;
        let to = usize::try_from(offset.checked_add(block).ok_or(RangeProofError::Overflow)?)
            .unwrap_or(usize::MAX)
            .min(bytes.len());
        let chunk = bytes.get(from..to).filter(|chunk| !chunk.is_empty());
        let chunk = chunk.ok_or(RangeProofError::Malformed)?;
        let start = leaf.checked_mul(block).ok_or(RangeProofError::Overflow)?;
        fold.pending -= 1;
        fold.stack.push(Node {
            start: leaf,
            capacity: 1,
            cv: Blake3Cv::from_subtree(start, chunk),
        });
        if let Some(root) = fold.settle()? {
            return Ok(root);
        }
    }

    fold.climb()
}

/// The chaining values a byte range needs to reach its blob's root.
///
/// This is ordinary, unchecked data: it becomes a fact only by passing
/// [`Self::check`]. See the [module documentation](self) for what the level and
/// the two spines mean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangeProof {
    level: u32,
    left: Box<[Blake3Cv]>,
    right: Box<[Blake3Cv]>,
}

impl RangeProof {
    /// Assembles a proof object without validating it.
    #[must_use]
    pub fn new(
        level: u32,
        left: impl Into<Box<[Blake3Cv]>>,
        right: impl Into<Box<[Blake3Cv]>>,
    ) -> Self {
        Self {
            level,
            left: left.into(),
            right: right.into(),
        }
    }

    /// Returns the tree level the spines are taken at.
    #[must_use]
    pub const fn level(&self) -> u32 {
        self.level
    }

    /// Returns the number of bytes in one block at this proof's level.
    #[must_use]
    pub const fn block_len(&self) -> Option<u64> {
        block_len(self.level)
    }

    /// Borrows the chaining values left of the range, widest first.
    #[must_use]
    pub const fn left(&self) -> &[Blake3Cv] {
        &self.left
    }

    /// Borrows the chaining values right of the range, in climbing order.
    #[must_use]
    pub const fn right(&self) -> &[Blake3Cv] {
        &self.right
    }

    /// Checks that `bytes` are `range` of the blob at `hash`.
    ///
    /// A range with a closed upper bound must both start and end on a block
    /// boundary for this proof's level. A range with an open upper bound must
    /// start on one, may end anywhere, since a blob's last block is the only
    /// short one, and must carry an empty right spine.
    ///
    /// # Errors
    ///
    /// Returns [`RangeProofError`] when the range is unusable at this level,
    /// when the spines do not describe a tree, or when the rebuilt root is not
    /// `hash`.
    pub fn check<R: BlobRange>(
        &self,
        hash: O256,
        range: R,
        bytes: impl Into<Bytes>,
    ) -> Result<CasRangeFact<R>, RangeProofError> {
        let block = self
            .block_len()
            .ok_or(RangeProofError::Level { level: self.level })?;
        let bytes = bytes.into();
        let len = u64::try_from(bytes.len()).map_err(|_| RangeProofError::Overflow)?;
        let start = range.start();
        if let Some(end) = range.end() {
            check_span(block, start, end, true)?;
            if end - start != len {
                return Err(RangeProofError::Length {
                    expected: end - start,
                    actual: len,
                });
            }
        } else {
            if !self.right.is_empty() {
                return Err(RangeProofError::UnboundedRight {
                    actual: self.right.len(),
                });
            }
            let end = start.checked_add(len).ok_or(RangeProofError::Overflow)?;
            check_span(block, start, end, false)?;
        }

        let first = start / block;
        let expected = usize::try_from(first.count_ones()).unwrap_or(usize::MAX);
        if self.left.len() != expected {
            return Err(RangeProofError::LeftSpine {
                expected,
                actual: self.left.len(),
            });
        }

        let spine = Given {
            left: &self.left,
            right: &self.right,
        };
        let computed = fold(spine, block, first, len.div_ceil(block), &bytes)?;
        if computed != hash {
            return Err(RangeProofError::Root {
                source: CasCheckError {
                    claimed: hash,
                    computed,
                },
            });
        }
        Ok(CasRangeFact::trust(CasRangeAssertion {
            hash,
            range,
            bytes,
        }))
    }
}

/// Checks that a range is non-empty and block-aligned below, and above too
/// when its upper bound is closed.
pub(crate) fn check_span(
    block: u64,
    start: u64,
    end: u64,
    closed: bool,
) -> Result<(), RangeProofError> {
    if end < start {
        return Err(RangeProofError::Backwards { start, end });
    }
    if end == start {
        return Err(RangeProofError::Empty { start });
    }
    if !start.is_multiple_of(block) {
        return Err(RangeProofError::Misaligned {
            offset: start,
            block,
        });
    }
    if closed && !end.is_multiple_of(block) {
        return Err(RangeProofError::Misaligned { offset: end, block });
    }
    Ok(())
}

/// Failure to check or derive a range proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RangeProofError {
    /// The level's block length does not fit in a `u64`.
    #[snafu(display("tree level {level} exceeds {MAX_LEVEL}"))]
    Level {
        /// Requested level.
        level: u32,
    },
    /// A range bound does not fall on a block boundary.
    #[snafu(display("offset {offset} is not a multiple of the block length {block}"))]
    Misaligned {
        /// Offending offset.
        offset: u64,
        /// Block length at the proof's level.
        block: u64,
    },
    /// The range ends before it starts.
    #[snafu(display("range start {start} is after range end {end}"))]
    Backwards {
        /// First byte of the range.
        start: u64,
        /// End of the range.
        end: u64,
    },
    /// The range covers no bytes, so there is nothing to prove.
    #[snafu(display("range at {start} is empty"))]
    Empty {
        /// First byte of the range.
        start: u64,
    },
    /// The byte count does not match the range.
    #[snafu(display("range covers {expected} bytes but {actual} were given"))]
    Length {
        /// Bytes the range covers.
        expected: u64,
        /// Bytes supplied.
        actual: u64,
    },
    /// The range reaches past the end of the blob being proven.
    #[snafu(display("range end {end} is past the blob length {len}"))]
    Bounds {
        /// End of the range.
        end: u64,
        /// Length of the blob.
        len: u64,
    },
    /// The left spine does not have one entry per aligned block before the
    /// range.
    #[snafu(display("left spine needs {expected} chaining values, found {actual}"))]
    LeftSpine {
        /// Entries the range requires.
        expected: usize,
        /// Entries supplied.
        actual: usize,
    },
    /// A range running to the end of the blob carried a right spine, which
    /// would let a prefix of the blob pass as all of it.
    #[snafu(display("open-ended range carries {actual} right chaining values"))]
    UnboundedRight {
        /// Entries supplied.
        actual: usize,
    },
    /// The spines do not describe a BLAKE3 tree above the range.
    #[snafu(display("spines do not describe a tree above the range"))]
    Malformed,
    /// A leaf index or block offset did not fit in a `u64`.
    #[snafu(display("range exceeds the addressable blob length"))]
    Overflow,
    /// The rebuilt root is not the claimed address.
    #[snafu(display("range proof does not reach the claimed address: {source}"))]
    Root {
        /// Claimed against rebuilt address.
        source: CasCheckError,
    },
}

#[cfg(all(test, feature = "prove"))]
mod tests {
    use std::ops::Range;

    use super::*;
    use crate::CasFact;

    /// A blob whose every byte position is distinguishable.
    fn blob(len: usize) -> Bytes {
        Bytes::from(
            (0..len)
                .map(|index| u8::try_from(index % 251).unwrap_or_default())
                .collect::<Vec<_>>(),
        )
    }

    /// Blob lengths whose level-`level` leaf counts exercise complete trees,
    /// odd trees with long right edges, and short final blocks.
    fn lengths(block: u64) -> Vec<usize> {
        let block = usize::try_from(block).unwrap();
        let mut lengths = Vec::new();
        for leaves in [1, 2, 3, 4, 5, 6, 7, 8, 11, 13, 16, 17] {
            lengths.push(leaves * block);
            lengths.push(leaves * block + 1);
            lengths.push(leaves * block + block / 2);
        }
        lengths
    }

    #[test]
    fn every_aligned_range_round_trips() {
        for level in 0..3 {
            let block = block_len(level).unwrap();
            for len in lengths(block) {
                let blob = blob(len);
                let fact = CasFact::from_bytes(blob.clone());
                let whole = u64::try_from(len).unwrap();
                let complete = whole / block;
                for first in 0..complete {
                    for last in (first + 1)..=complete {
                        let range = first * block..last * block;
                        let proof = RangeProof::prove(level, &range, &blob).unwrap();
                        let bytes = blob.slice(
                            usize::try_from(range.start).unwrap()
                                ..usize::try_from(range.end).unwrap(),
                        );
                        let checked = proof
                            .check(fact.hash(), range.clone(), bytes.clone())
                            .unwrap_or_else(|error| {
                                panic!("level {level}, len {len}, range {range:?}: {error}")
                            });
                        assert_eq!(checked.hash(), fact.hash());
                        assert_eq!(checked.bytes(), &bytes);
                        assert_eq!(checked.range(), &range);
                        assert_eq!(proof.left().len(), first.count_ones() as usize);
                    }
                }
            }
        }
    }

    #[test]
    fn open_ended_ranges_reach_a_short_final_block() {
        for level in 0..3 {
            let block = block_len(level).unwrap();
            for len in lengths(block) {
                let blob = blob(len);
                let fact = CasFact::from_bytes(blob.clone());
                let whole = u64::try_from(len).unwrap();
                for first in 0..whole.div_ceil(block) {
                    let range = first * block..;
                    let proof = RangeProof::prove(level, &range, &blob).unwrap();
                    assert!(proof.right().is_empty(), "level {level}, len {len}");
                    let bytes = blob.slice(usize::try_from(range.start).unwrap()..);
                    let checked = proof
                        .check(fact.hash(), range.clone(), bytes.clone())
                        .unwrap_or_else(|error| {
                            panic!("level {level}, len {len}, from {first}: {error}")
                        });
                    assert_eq!(checked.bytes(), &bytes);
                    // An open upper bound pins the blob's length.
                    assert_eq!(checked.extent().end, whole);
                }
            }
        }
    }

    #[test]
    fn whole_blob_proof_reproduces_the_blake3_root() {
        for level in 0..3 {
            let block = block_len(level).unwrap();
            for len in lengths(block) {
                let blob = blob(len);
                let proof = RangeProof::prove(level, &(..), &blob).unwrap();
                assert!(proof.left().is_empty());
                assert!(proof.right().is_empty());
                let fact = proof
                    .check(O256::from_bytes(&blob), .., blob.clone())
                    .unwrap();
                assert_eq!(fact.bytes(), &blob);
            }
        }
    }

    #[test]
    fn tampering_with_the_bytes_is_rejected() {
        let blob = blob(11 * 1024 + 7);
        let hash = O256::from_bytes(&blob);
        let range = 2048..6144;
        let proof = RangeProof::prove(0, &range, &blob).unwrap();
        let mut bytes = blob[2048..6144].to_vec();
        bytes[10] ^= 1;

        let error = proof.check(hash, range, bytes).unwrap_err();
        assert!(matches!(error, RangeProofError::Root { .. }), "{error}");
    }

    #[test]
    fn tampering_with_a_spine_is_rejected() {
        let blob = blob(11 * 1024 + 7);
        let hash = O256::from_bytes(&blob);
        let range = 4096..6144;
        let proof = RangeProof::prove(0, &range, &blob).unwrap();
        let bytes = blob.slice(4096..6144);
        assert!(!proof.left().is_empty() && !proof.right().is_empty());

        for spine in [proof.left(), proof.right()] {
            for index in 0..spine.len() {
                let mut left = proof.left().to_vec();
                let mut right = proof.right().to_vec();
                let target = if std::ptr::eq(spine, proof.left()) {
                    &mut left
                } else {
                    &mut right
                };
                let mut cv = target[index].into_bytes();
                cv[0] ^= 1;
                target[index] = Blake3Cv::from_array(cv);
                let forged = RangeProof::new(0, left, right);
                let error = forged
                    .check(hash, range.clone(), bytes.clone())
                    .unwrap_err();
                assert!(matches!(error, RangeProofError::Root { .. }), "{error}");
            }
        }
    }

    #[test]
    fn a_prefix_cannot_pass_as_the_whole_blob() {
        // The blob is sixteen chunks; the first eight are a real subtree, so
        // their root plus the right sibling is the real root. Claiming `0..`
        // for just those eight would be a claim about the blob's length.
        let blob = blob(16 * 1024);
        let hash = O256::from_bytes(&blob);
        let range = 0..8 * 1024;
        let proof = RangeProof::prove(0, &range, &blob).unwrap();
        let bytes = blob.slice(0..8 * 1024);
        assert!(proof.check(hash, range, bytes.clone()).is_ok());

        let smuggled = RangeProof::new(0, proof.left().to_vec(), proof.right().to_vec());
        let error = smuggled.check(hash, 0.., bytes).unwrap_err();
        assert!(
            matches!(error, RangeProofError::UnboundedRight { actual: 1 }),
            "{error}"
        );
    }

    #[test]
    fn a_left_spine_of_the_wrong_length_is_rejected() {
        let blob = blob(8 * 1024);
        let hash = O256::from_bytes(&blob);
        let range = 5 * 1024..6 * 1024;
        let proof = RangeProof::prove(0, &range, &blob).unwrap();
        assert_eq!(proof.left().len(), 2);

        let short = RangeProof::new(0, vec![proof.left()[0]], proof.right().to_vec());
        let error = short
            .check(hash, range, blob.slice(5 * 1024..6 * 1024))
            .unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::LeftSpine {
                    expected: 2,
                    actual: 1
                }
            ),
            "{error}"
        );
    }

    #[test]
    fn ranges_off_the_block_grid_are_rejected() {
        let blob = blob(4 * 1024);
        let hash = O256::from_bytes(&blob);
        let proof = RangeProof::prove(0, &(1024..2048), &blob).unwrap();

        let error = proof
            .check(hash, 1000..2048, blob.slice(1000..2048))
            .unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::Misaligned {
                    offset: 1000,
                    block: 1024
                }
            ),
            "{error}"
        );
        let error = proof
            .check(hash, 1024..2000, blob.slice(1024..2000))
            .unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::Misaligned {
                    offset: 2000,
                    block: 1024
                }
            ),
            "{error}"
        );
        let error = proof.check(hash, 1024..1024, Bytes::new()).unwrap_err();
        assert!(
            matches!(error, RangeProofError::Empty { start: 1024 }),
            "{error}"
        );
        let error = proof
            .check(hash, 1024..2048, blob.slice(1024..1536))
            .unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::Length {
                    expected: 1024,
                    actual: 512
                }
            ),
            "{error}"
        );
    }

    #[test]
    fn a_level_beyond_the_addressable_range_is_rejected() {
        assert_eq!(block_len(MAX_LEVEL), Some(1 << 63));
        assert_eq!(block_len(MAX_LEVEL + 1), None);

        let error = RangeProof::prove(MAX_LEVEL + 1, &(0..1024), b"").unwrap_err();
        assert!(matches!(error, RangeProofError::Level { .. }), "{error}");

        let proof = RangeProof::new(MAX_LEVEL + 1, Vec::new(), Vec::new());
        let error = proof
            .check(O256::default(), 0..1024, Bytes::new())
            .unwrap_err();
        assert!(matches!(error, RangeProofError::Level { .. }), "{error}");
    }

    #[test]
    fn proving_past_the_end_of_the_blob_is_rejected() {
        let blob = blob(2 * 1024);
        let error = RangeProof::prove(0, &(0..4 * 1024), &blob).unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::Bounds {
                    end: 4096,
                    len: 2048
                }
            ),
            "{error}"
        );
        let error = RangeProof::prove(0, &(..), b"").unwrap_err();
        assert!(
            matches!(error, RangeProofError::Empty { start: 0 }),
            "{error}"
        );
    }

    #[test]
    fn a_prefix_range_proves_as_a_range_to() {
        let blob = blob(11 * 1024 + 7);
        let hash = O256::from_bytes(&blob);
        let proof = RangeProof::prove(0, &(..4096), &blob).unwrap();

        assert!(proof.left().is_empty());
        let fact = proof.check(hash, ..4096, blob.slice(..4096)).unwrap();
        assert_eq!(fact.range(), &(..4096));
        assert_eq!(fact.extent(), 0..4096);

        // The same bytes at the same place, named as a bounded range.
        let bounded = RangeProof::prove(0, &(0..4096), &blob).unwrap();
        assert_eq!(bounded, proof);
    }

    #[test]
    fn a_proof_does_not_move_its_bytes_to_another_offset() {
        let blob = blob(8 * 1024);
        let hash = O256::from_bytes(&blob);
        let proof = RangeProof::prove(0, &(1024..2048), &blob).unwrap();
        let bytes = blob.slice(1024..2048);
        assert!(proof.check(hash, 1024..2048, bytes.clone()).is_ok());

        // Leaf chaining values are bound to their offset, and the left spine
        // is bound to the range's first leaf index, so the same proof cannot
        // relocate its bytes.
        let error = proof.check(hash, 2048..3072, bytes.clone()).unwrap_err();
        assert!(matches!(error, RangeProofError::Root { .. }), "{error}");
        let error = proof.check(hash, 3072..4096, bytes).unwrap_err();
        assert!(
            matches!(
                error,
                RangeProofError::LeftSpine {
                    expected: 2,
                    actual: 1
                }
            ),
            "{error}"
        );
    }

    #[test]
    fn a_proof_for_one_blob_does_not_check_against_another() {
        let subject = blob(8 * 1024);
        let other = blob(8 * 1024 + 1);
        let range: Range<u64> = 2048..4096;
        let proof = RangeProof::prove(0, &range, &subject).unwrap();

        let error = proof
            .check(O256::from_bytes(&other), range, subject.slice(2048..4096))
            .unwrap_err();
        assert!(matches!(error, RangeProofError::Root { .. }), "{error}");
    }
}
