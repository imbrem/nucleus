//! Deriving the chaining values a range proof carries.
//!
//! This is the counterpart of [`RangeProof::check`](crate::RangeProof::check)
//! and is not part of the trusted base. Producing a proof cannot produce a
//! fact: nothing here reaches the checked-fact constructor, so whatever this
//! module derives still has to pass the check.
//!
//! It is a reference producer, kept here so the verifier has something to test
//! against and so callers have a working implementation to start from. The
//! intended production shape, per issue #874, stores BLAKE3 chaining-value
//! trees alongside blobs and serves proofs from them. This module is behind the
//! default-on `prove` feature; a consumer that wants nothing but the verifier
//! compiled into its trusted surface can take the crate with
//! `default-features = false`.

use covalence_lib_hash::blake3::Blake3Cv;

use crate::{
    BlobRange, RangeProof, RangeProofError,
    proof::{Spine, block_len, check_span, fold},
};

/// Chaining values derived from a complete blob, recorded as they are used.
struct Computed<'blob> {
    blob: &'blob [u8],
    block: u64,
    leaves: u64,
    left: Vec<Blake3Cv>,
    right: Vec<Blake3Cv>,
}

impl Spine for Computed<'_> {
    fn left(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv> {
        let cv = subtree_cv(self.blob, self.block, start, capacity, self.leaves)?;
        self.left.push(cv);
        Some(cv)
    }

    fn right(&mut self, start: u64, capacity: u64) -> Option<Blake3Cv> {
        let sibling = start.checked_add(capacity)?;
        let cv = subtree_cv(self.blob, self.block, sibling, capacity, self.leaves)?;
        self.right.push(cv);
        Some(cv)
    }

    fn has_right(&self, start: u64, capacity: u64) -> bool {
        start
            .checked_add(capacity)
            .is_some_and(|sibling| sibling < self.leaves)
    }
}

/// Returns the chaining value of the node covering `[start, start + capacity)`
/// leaves, truncated to `leaves`, or `None` when the node is entirely past the
/// end of the blob.
///
/// A node lying wholly inside the blob is one aligned subtree and hashes
/// directly. A node overhanging the end is a right-edge node, whose right child
/// is either absent, in which case the node collapses onto its left child, or
/// is itself another right-edge node.
fn subtree_cv(blob: &[u8], block: u64, start: u64, capacity: u64, leaves: u64) -> Option<Blake3Cv> {
    if start >= leaves {
        return None;
    }
    let offset = start.checked_mul(block)?;
    let stop = start.checked_add(capacity)?;
    if capacity == 1 || stop <= leaves {
        let from = usize::try_from(offset).ok()?;
        let to = usize::try_from(stop.checked_mul(block)?)
            .unwrap_or(usize::MAX)
            .min(blob.len());
        return Some(Blake3Cv::from_subtree(offset, blob.get(from..to)?));
    }
    let half = capacity / 2;
    let left = subtree_cv(blob, block, start, half, leaves)?;
    match subtree_cv(blob, block, start.checked_add(half)?, half, leaves) {
        Some(right) => Some(left.merge(right)),
        None => Some(left),
    }
}

impl RangeProof {
    /// Derives the proof that `range` of `blob` sits under `blob`'s root.
    ///
    /// This is the counterpart of [`Self::check`] and is not part of the
    /// trusted base: what it produces still has to pass the check.
    ///
    /// # Errors
    ///
    /// Returns [`RangeProofError`] when `level` is too large, when `range` is
    /// not aligned to that level's blocks, or when `range` is empty or reaches
    /// past the end of `blob`.
    pub fn prove<R: BlobRange>(
        level: u32,
        range: &R,
        blob: &[u8],
    ) -> Result<Self, RangeProofError> {
        let block = block_len(level).ok_or(RangeProofError::Level { level })?;
        let blob_len = u64::try_from(blob.len()).map_err(|_| RangeProofError::Overflow)?;
        let start = range.start();
        let closed = range.end();
        let end = closed.unwrap_or(blob_len);
        check_span(block, start, end, closed.is_some())?;
        if end > blob_len {
            return Err(RangeProofError::Bounds { end, len: blob_len });
        }
        let from = usize::try_from(start).map_err(|_| RangeProofError::Overflow)?;
        let to = usize::try_from(end).map_err(|_| RangeProofError::Overflow)?;
        let mut spine = Computed {
            blob,
            block,
            leaves: blob_len.div_ceil(block),
            left: Vec::new(),
            right: Vec::new(),
        };
        // Running the checker's fold records exactly the values it asks for.
        fold(
            &mut spine,
            block,
            start / block,
            (end - start).div_ceil(block),
            &blob[from..to],
        )?;
        Ok(Self::new(level, spine.left, spine.right))
    }
}
