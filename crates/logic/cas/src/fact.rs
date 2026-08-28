use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    ops::{Range, RangeFrom, RangeFull},
};

use bytes::BytesMut;
use covalence_lib_error::snafu::Snafu;

use crate::{BlobRange, BlobSpan, Bytes, FuseRange, O256};

/// Returns a byte count as a `u64`.
///
/// `usize` is at most 64 bits on every supported target, so the saturation is
/// unreachable; it exists only to keep the fact rules panic-free.
fn byte_len(bytes: &Bytes) -> u64 {
    u64::try_from(bytes.len()).unwrap_or(u64::MAX)
}

/// An unchecked claim that `bytes` are the `range` of the blob at `hash`.
///
/// Constructing an assertion establishes no invariant. The whole-blob shape
/// [`CasAssertion`] is checked by [`CasAssertion::check`], which hashes every
/// byte; other shapes are checked by
/// [`RangeProof::check`](crate::RangeProof::check).
#[derive(Clone, Debug)]
pub struct CasRangeAssertion<R = Range<u64>> {
    /// Claimed `O256` hash of the complete blob.
    pub hash: O256,
    /// Claimed position of `bytes` within that blob.
    pub range: R,
    /// Claimed bytes at that position.
    pub bytes: Bytes,
}

/// An unchecked claim that a complete blob has a given content hash.
pub type CasAssertion = CasRangeAssertion<RangeFull>;

impl<R: BlobRange> CasRangeAssertion<R> {
    /// Constructs an unchecked assertion without hashing `bytes`.
    #[must_use]
    pub fn new(hash: O256, range: R, bytes: impl Into<Bytes>) -> Self {
        Self {
            hash,
            range,
            bytes: bytes.into(),
        }
    }

    /// Returns the byte range the claimed bytes actually span.
    ///
    /// This resolves an open upper bound: an assertion about `start..` claims
    /// its bytes run to the end of the blob, so the blob ends at the returned
    /// offset.
    #[must_use]
    pub fn extent(&self) -> Range<u64> {
        let start = self.range.start();
        start..start.saturating_add(byte_len(&self.bytes))
    }

    /// The value this shape compares, orders, and hashes by.
    fn key(&self) -> (O256, u64, Option<u64>, &Bytes) {
        (self.hash, self.range.start(), self.range.end(), &self.bytes)
    }
}

impl CasAssertion {
    /// Checks the claimed address against every byte of the blob.
    ///
    /// # Errors
    ///
    /// Returns [`CasCheckError`] when the computed and claimed addresses
    /// differ.
    pub fn check(self) -> Result<CasFact, CasCheckError> {
        let computed = O256::from_bytes(&self.bytes);
        if computed == self.hash {
            Ok(CasFact { assertion: self })
        } else {
            Err(CasCheckError {
                claimed: self.hash,
                computed,
            })
        }
    }
}

impl<R: BlobRange> PartialEq for CasRangeAssertion<R> {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}

impl<R: BlobRange> Eq for CasRangeAssertion<R> {}

impl<R: BlobRange> PartialOrd for CasRangeAssertion<R> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<R: BlobRange> Ord for CasRangeAssertion<R> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(&other.key())
    }
}

impl<R: BlobRange> Hash for CasRangeAssertion<R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// Failure to validate a whole-object CAS assertion.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("claimed hash {claimed} does not match computed hash {computed}"))]
pub struct CasCheckError {
    /// Hash claimed by the assertion.
    pub claimed: O256,
    /// Hash computed over all of the assertion's bytes.
    pub computed: O256,
}

/// A checked fact that `range` of the blob at `hash` holds specific bytes.
///
/// The whole-blob shape [`CasFact`] is the erased runtime counterpart of
/// Lean's `Nucleus.CasPair`. Its private representation is the LCF boundary:
/// safe code can inspect and clone a fact, but only the checking rules in this
/// crate can construct one. Those rules are
///
/// - hashing every byte, through [`CasFact::from_bytes`] or
///   [`CasAssertion::check`];
/// - narrowing a fact to a sub-range, through [`Self::slice`];
/// - joining two facts about the same blob, through [`Self::fuse`];
/// - checking a BLAKE3 spine, through
///   [`RangeProof::check`](crate::RangeProof::check).
///
/// In Lean, [`CasFact::from_bytes`] corresponds to `Nucleus.CasPair.ofBlob`,
/// the projections correspond to `Nucleus.CasPair.hash` and
/// `Nucleus.CasPair.blob`, and the invariant is `Nucleus.CasPair.valid_hash`.
/// [`CasAssertion::check`] corresponds to `Nucleus.CasAssertion.check?`. The
/// range rules have no Lean counterpart yet.
///
/// ```compile_fail
/// use bytes::Bytes;
/// use covalence_logic_cas::CasFact;
///
/// let assertion = CasFact::from_bytes(Bytes::new()).into_assertion();
/// let forged = CasFact { assertion };
/// ```
#[derive(Clone, Debug)]
pub struct CasRangeFact<R = Range<u64>> {
    assertion: CasRangeAssertion<R>,
}

/// A checked fact that a complete blob has an `O256` hash.
pub type CasFact = CasRangeFact<RangeFull>;

impl CasFact {
    /// Checks a specific address and complete blob, then introduces a fact.
    ///
    /// # Errors
    ///
    /// Returns [`CasCheckError`] when `hash` is not the blob's address.
    pub fn new(hash: O256, blob: impl Into<Bytes>) -> Result<Self, CasCheckError> {
        CasAssertion::new(hash, .., blob).check()
    }

    /// Hashes the complete bytes and introduces a checked fact.
    ///
    /// `Bytes` is reference counted, so passing an existing [`Bytes`] value
    /// retains it without copying its contents.
    #[must_use]
    pub fn from_bytes(bytes: impl Into<Bytes>) -> Self {
        let bytes = bytes.into();
        let hash = O256::from_bytes(&bytes);
        Self {
            assertion: CasAssertion {
                hash,
                range: ..,
                bytes,
            },
        }
    }
}

impl<R: BlobRange> CasRangeFact<R> {
    /// Introduces a fact. Every caller is a checking rule of this crate.
    pub(crate) const fn trust(assertion: CasRangeAssertion<R>) -> Self {
        Self { assertion }
    }

    /// Returns the hash of the complete blob.
    #[must_use]
    pub const fn hash(&self) -> O256 {
        self.assertion.hash
    }

    /// Borrows the position these bytes occupy in the blob.
    #[must_use]
    pub const fn range(&self) -> &R {
        &self.assertion.range
    }

    /// Borrows the known bytes.
    #[must_use]
    pub const fn bytes(&self) -> &Bytes {
        &self.assertion.bytes
    }

    /// Returns the byte range the known bytes occupy.
    ///
    /// For an open upper bound this resolves the end of the blob, since the
    /// fact's bytes run to it.
    #[must_use]
    pub fn extent(&self) -> Range<u64> {
        self.assertion.extent()
    }

    /// Returns the blob's length, when this fact's range reaches the end of it.
    ///
    /// Only an open upper bound reaches it. A fact about `3..9` knows nothing
    /// about how long the blob is, so this returns `None` rather than
    /// mistaking a range's end for the blob's.
    ///
    /// The data-free length claim is the empty case: a fact about `n..` whose
    /// bytes are empty says only that the blob is `n` bytes long. That is what
    /// a separate `CasLengthFact` would carry, so this crate has no such type.
    /// [`Self::slice`] derives one from any fact that reaches the end, which
    /// includes a fact checked from a proof of the blob's final range.
    ///
    /// ```
    /// use covalence_logic_cas::{Bytes, CasFact};
    ///
    /// let fact = CasFact::from_bytes(Bytes::from_static(b"0123456789"));
    /// assert_eq!(fact.blob_len(), Some(10));
    ///
    /// let length_only = fact.slice(10..).unwrap();
    /// assert!(length_only.bytes().is_empty());
    /// assert_eq!(length_only.blob_len(), Some(10));
    ///
    /// assert_eq!(fact.slice(3..9).unwrap().blob_len(), None);
    /// ```
    #[must_use]
    pub fn blob_len(&self) -> Option<u64> {
        self.assertion
            .range
            .end()
            .is_none()
            .then(|| self.extent().end)
    }

    pub(crate) const fn as_assertion(&self) -> &CasRangeAssertion<R> {
        &self.assertion
    }

    /// Forgets the checked invariant and returns the ordinary assertion.
    #[must_use]
    pub fn into_assertion(self) -> CasRangeAssertion<R> {
        self.assertion
    }

    /// Forgets this fact's static range shape, keeping the claim itself.
    ///
    /// The result says exactly what this fact says, in the one range type able
    /// to hold any shape. Use it at a boundary that cannot carry the type
    /// parameter, such as a collection of facts about different ranges or a
    /// dynamically typed language binding. Nothing is checked, because nothing
    /// can fail: a [`BlobSpan`] holds any bounds a `BlobRange` can report.
    ///
    /// What is given up is decided-by-type, not truth. A `0..` fact and a
    /// `..` fact erase to the same span, and both still know the blob's length
    /// through [`Self::blob_len`]; the difference is that recovering a
    /// whole-blob [`CasFact`] from the span now takes a checked
    /// [`Self::slice`].
    #[must_use]
    pub fn erase(&self) -> CasRangeFact<BlobSpan> {
        CasRangeFact::trust(CasRangeAssertion {
            hash: self.assertion.hash,
            range: self.assertion.range.span(),
            bytes: self.assertion.bytes.clone(),
        })
    }

    /// Narrows this fact to a sub-range of the bytes it already knows.
    ///
    /// The requested range is in blob coordinates, not relative to this fact,
    /// and the resulting bytes share this fact's buffer. Requesting an open
    /// upper bound needs one: a fact about `3..9` does not know where the blob
    /// ends, while a fact about `3..` does, so `..` narrows a `0..` fact into a
    /// whole-blob [`CasFact`].
    ///
    /// # Errors
    ///
    /// Returns [`SliceError`] when the request is not contained in the bytes
    /// this fact knows.
    pub fn slice<S: BlobRange>(&self, range: S) -> Result<CasRangeFact<S>, SliceError> {
        let known = self.extent();
        let start = range.start();
        // An open upper bound asks for the end of the blob, which only a fact
        // that already reaches it can answer.
        let end = match range.end() {
            Some(end) => end,
            None if self.assertion.range.end().is_some() => {
                return Err(SliceError::Bounded {
                    available: known.end,
                });
            }
            None => known.end,
        };
        if start < known.start {
            return Err(SliceError::Start {
                requested: start,
                available: known.start,
            });
        }
        if end > known.end {
            return Err(SliceError::End {
                requested: end,
                available: known.end,
            });
        }
        if end < start {
            return Err(SliceError::Backwards { start, end });
        }
        // `known.start <= start <= end <= known.end`, and the extent spans the
        // bytes themselves, so both offsets index them. The clamp keeps a
        // saturated extent from reaching `Bytes::slice` as an out-of-range one.
        let len = self.assertion.bytes.len();
        let from = usize::try_from(start - known.start).unwrap_or(len).min(len);
        let to = usize::try_from(end - known.start).unwrap_or(len).min(len);
        Ok(CasRangeFact::trust(CasRangeAssertion {
            hash: self.assertion.hash,
            range,
            bytes: self.assertion.bytes.slice(from..to),
        }))
    }

    /// Joins this fact with another about the same blob.
    ///
    /// The two ranges must overlap or touch; a gap between them would leave
    /// bytes the union claims to know but neither operand does. The result's
    /// shape comes from [`FuseRange`], so fusing a prefix with a suffix yields
    /// a whole-blob [`CasFact`].
    ///
    /// Both operands are checked facts about the same blob, so wherever they
    /// overlap they agree, and the join takes each byte from whichever operand
    /// covers it. When one range contains the other the wider operand's buffer
    /// is retained as is; otherwise the union is copied into a new buffer,
    /// because `Bytes` has no safe way to widen a shared view back over the
    /// buffer it was sliced from.
    ///
    /// # Errors
    ///
    /// Returns [`FuseError`] when the facts are about different blobs, when
    /// their ranges leave a gap, or when the joined bounds do not fit the
    /// output shape.
    pub fn fuse<S>(&self, other: &CasRangeFact<S>) -> Result<CasRangeFact<R::Output>, FuseError>
    where
        S: BlobRange,
        R: FuseRange<S>,
    {
        if self.assertion.hash != other.assertion.hash {
            return Err(FuseError::Hash {
                left: self.assertion.hash,
                right: other.assertion.hash,
            });
        }
        let left = self.extent();
        let right = other.extent();
        if left.start.max(right.start) > left.end.min(right.end) {
            return Err(FuseError::Disjoint { left, right });
        }
        let start = left.start.min(right.start);
        let end = left.end.max(right.end);
        let open = self.assertion.range.end().is_none() || other.assertion.range.end().is_none();
        let bound = (!open).then_some(end);
        let range =
            R::Output::from_bounds(start, bound).ok_or(FuseError::Shape { start, end: bound })?;

        let bytes = if left.start <= right.start && right.end <= left.end {
            self.assertion.bytes.clone()
        } else if right.start <= left.start && left.end <= right.end {
            other.assertion.bytes.clone()
        } else {
            let (head, tail, seam) = if left.start <= right.start {
                (
                    &self.assertion.bytes,
                    &other.assertion.bytes,
                    left.end - right.start,
                )
            } else {
                (
                    &other.assertion.bytes,
                    &self.assertion.bytes,
                    right.end - left.start,
                )
            };
            // `seam` counts bytes of `tail` that `head` already covers. Neither
            // range contains the other, so it is below `tail.len()`; the clamp
            // keeps a saturated extent from indexing past the end.
            let seam = usize::try_from(seam).unwrap_or(tail.len()).min(tail.len());
            let mut joined = BytesMut::with_capacity(head.len() + tail.len() - seam);
            joined.extend_from_slice(head);
            joined.extend_from_slice(&tail[seam..]);
            joined.freeze()
        };

        Ok(CasRangeFact::trust(CasRangeAssertion {
            hash: self.assertion.hash,
            range,
            bytes,
        }))
    }
}

impl<R: BlobRange> PartialEq for CasRangeFact<R> {
    fn eq(&self, other: &Self) -> bool {
        self.assertion == other.assertion
    }
}

impl<R: BlobRange> Eq for CasRangeFact<R> {}

impl<R: BlobRange> PartialOrd for CasRangeFact<R> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<R: BlobRange> Ord for CasRangeFact<R> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.assertion.cmp(&other.assertion)
    }
}

impl<R: BlobRange> Hash for CasRangeFact<R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.assertion.hash(state);
    }
}

impl TryFrom<CasAssertion> for CasFact {
    type Error = CasCheckError;

    fn try_from(assertion: CasAssertion) -> Result<Self, Self::Error> {
        assertion.check()
    }
}

impl From<CasFact> for CasRangeFact<RangeFrom<u64>> {
    fn from(fact: CasFact) -> Self {
        Self::trust(CasRangeAssertion {
            hash: fact.assertion.hash,
            range: 0..,
            bytes: fact.assertion.bytes,
        })
    }
}

impl TryFrom<CasRangeFact<RangeFrom<u64>>> for CasFact {
    type Error = SliceError;

    fn try_from(fact: CasRangeFact<RangeFrom<u64>>) -> Result<Self, Self::Error> {
        fact.slice(..)
    }
}

/// Failure to narrow a fact to a sub-range.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SliceError {
    /// The request starts before the first byte the fact knows.
    #[snafu(display("range start {requested} is outside known bytes from {available}"))]
    Start {
        /// Requested first byte.
        requested: u64,
        /// First byte the fact knows.
        available: u64,
    },
    /// The request ends after the last byte the fact knows.
    #[snafu(display("range end {requested} is past known bytes ending at {available}"))]
    End {
        /// Requested end.
        requested: u64,
        /// End of the bytes the fact knows.
        available: u64,
    },
    /// The requested range ends before it starts.
    #[snafu(display("range start {start} is after range end {end}"))]
    Backwards {
        /// Requested first byte.
        start: u64,
        /// Requested end.
        end: u64,
    },
    /// An open-ended range was requested of a fact that does not reach the
    /// end of the blob.
    #[snafu(display("bytes ending at {available} do not reach the end of the blob"))]
    Bounded {
        /// End of the bytes the fact knows.
        available: u64,
    },
}

/// Failure to join two facts.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum FuseError {
    /// The facts are about different blobs.
    #[snafu(display("cannot fuse facts about {left} and {right}"))]
    Hash {
        /// Address of the left fact.
        left: O256,
        /// Address of the right fact.
        right: O256,
    },
    /// The ranges leave a gap, so their union is not covered.
    #[snafu(display(
        "ranges {}..{} and {}..{} leave a gap",
        left.start,
        left.end,
        right.start,
        right.end
    ))]
    Disjoint {
        /// Bytes the left fact knows.
        left: Range<u64>,
        /// Bytes the right fact knows.
        right: Range<u64>,
    },
    /// The joined bounds do not fit the output shape.
    #[snafu(display("joined range {start}..{end:?} does not fit the requested shape"))]
    Shape {
        /// First byte of the union.
        start: u64,
        /// End of the union, or `None` for the end of the blob.
        end: Option<u64>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BlobSpan;

    fn whole() -> CasFact {
        CasFact::from_bytes(Bytes::from_static(b"0123456789"))
    }

    #[test]
    fn slicing_keeps_blob_coordinates_and_shares_the_buffer() {
        let fact = whole();
        let middle = fact.slice(3..7).unwrap();

        assert_eq!(middle.hash(), fact.hash());
        assert_eq!(middle.bytes(), &Bytes::from_static(b"3456"));
        assert_eq!(middle.range(), &(3..7));
        assert_eq!(middle.extent(), 3..7);
        assert_eq!(middle.bytes().as_ptr(), fact.bytes()[3..].as_ptr());

        // Sub-ranges are absolute, so a slice of a slice still names blob bytes.
        assert_eq!(
            middle.slice(4..6).unwrap().bytes(),
            &Bytes::from_static(b"45")
        );
        assert!(middle.slice(2..6).is_err());
    }

    #[test]
    fn open_ended_slices_need_a_fact_that_reaches_the_end() {
        let fact = whole();
        let suffix = fact.slice(4..).unwrap();
        assert_eq!(suffix.bytes(), &Bytes::from_static(b"456789"));
        assert_eq!(suffix.extent(), 4..10);

        // A suffix knows where the blob ends, so it can be narrowed further.
        assert_eq!(
            suffix.slice(6..).unwrap().bytes(),
            &Bytes::from_static(b"6789")
        );

        // A bounded range does not, so it cannot.
        let middle = fact.slice(3..7).unwrap();
        let error = middle.slice(4..).unwrap_err();
        assert_eq!(error, SliceError::Bounded { available: 7 });
    }

    #[test]
    fn a_suffix_from_zero_is_a_whole_blob_fact() {
        let fact = whole();
        let suffix: CasRangeFact<RangeFrom<u64>> = fact.clone().into();
        assert_eq!(suffix.range(), &(0..));

        let recovered = CasFact::try_from(suffix).unwrap();
        assert_eq!(recovered, fact);

        // A suffix that starts later is not the whole blob.
        let error = CasFact::try_from(fact.slice(1..).unwrap()).unwrap_err();
        assert_eq!(
            error,
            SliceError::Start {
                requested: 0,
                available: 1
            }
        );
    }

    #[test]
    fn slicing_refuses_bytes_the_fact_does_not_know() {
        let middle = whole().slice(3..7).unwrap();

        assert_eq!(
            middle.slice(2..5).unwrap_err(),
            SliceError::Start {
                requested: 2,
                available: 3
            }
        );
        assert_eq!(
            middle.slice(5..9).unwrap_err(),
            SliceError::End {
                requested: 9,
                available: 7
            }
        );
        #[allow(clippy::reversed_empty_ranges, reason = "the rule must reject this")]
        let backwards = middle.slice(6..4).unwrap_err();
        assert_eq!(backwards, SliceError::Backwards { start: 6, end: 4 });
        assert!(middle.slice(..5).is_err());
    }

    #[test]
    fn fusing_overlapping_ranges_covers_their_union() {
        let fact = whole();
        let left = fact.slice(1..5).unwrap();
        let right = fact.slice(3..8).unwrap();

        let fused = left.fuse(&right).unwrap();
        assert_eq!(fused.range(), &(1..8));
        assert_eq!(fused.bytes(), &Bytes::from_static(b"1234567"));

        // Fusing is order-insensitive.
        assert_eq!(right.fuse(&left).unwrap(), fused);
    }

    #[test]
    fn fusing_touching_ranges_covers_their_union() {
        let fact = whole();
        let fused = fact
            .slice(1..4)
            .unwrap()
            .fuse(&fact.slice(4..6).unwrap())
            .unwrap();
        assert_eq!(fused.range(), &(1..6));
        assert_eq!(fused.bytes(), &Bytes::from_static(b"12345"));
    }

    #[test]
    fn fusing_a_contained_range_retains_the_wider_buffer() {
        let fact = whole();
        let wide = fact.slice(1..8).unwrap();
        let narrow = fact.slice(3..5).unwrap();

        let fused = wide.fuse(&narrow).unwrap();
        assert_eq!(fused.range(), &(1..8));
        assert_eq!(fused.bytes().as_ptr(), wide.bytes().as_ptr());
        assert_eq!(
            narrow.fuse(&wide).unwrap().bytes().as_ptr(),
            wide.bytes().as_ptr()
        );
    }

    #[test]
    fn fusing_a_prefix_with_a_suffix_gives_the_whole_blob() {
        let fact = whole();
        let prefix = fact.slice(..6).unwrap();
        let suffix = fact.slice(4..).unwrap();

        let fused: CasFact = prefix.fuse(&suffix).unwrap();
        assert_eq!(fused, fact);
        assert_eq!(fused.bytes(), fact.bytes());

        // A prefix and a bounded middle stay a prefix.
        let bounded = prefix.fuse(&fact.slice(5..9).unwrap()).unwrap();
        assert_eq!(bounded.range(), &(..9));
        // A middle and a suffix stay a suffix.
        let tail = fact.slice(2..5).unwrap().fuse(&suffix).unwrap();
        assert_eq!(tail.range(), &(2..));
        assert_eq!(tail.bytes(), &Bytes::from_static(b"23456789"));
    }

    #[test]
    fn erasing_keeps_the_claim_and_gives_up_only_the_type() {
        let fact = whole();
        let middle = fact.slice(3..7).unwrap();
        let erased = middle.erase();

        assert_eq!(erased.hash(), middle.hash());
        assert_eq!(erased.bytes(), middle.bytes());
        assert_eq!(erased.extent(), middle.extent());
        assert_eq!(erased.range(), &BlobSpan::new(3, Some(7)).unwrap());
        // Erasure shares the buffer rather than copying it.
        assert_eq!(erased.bytes().as_ptr(), middle.bytes().as_ptr());

        // An open end still reports the length after erasure.
        assert_eq!(fact.slice(4..).unwrap().erase().blob_len(), Some(10));
        assert_eq!(fact.erase().blob_len(), Some(10));
        assert_eq!(erased.blob_len(), None);

        // `..` and `0..` erase alike; recovering the whole-blob type is a
        // checked slice rather than something the type still remembers.
        assert_eq!(fact.erase(), fact.slice(0..).unwrap().erase());
        assert_eq!(
            CasFact::try_from(fact.erase().slice(0..).unwrap()).unwrap(),
            fact
        );
        assert!(erased.slice(..).is_err());
    }

    #[test]
    fn fusing_an_erased_range_keeps_what_the_other_side_settles() {
        let fact = whole();
        let span = fact.slice(2..6).unwrap().erase();

        // A span is open above only dynamically, so it drags the output back
        // to a span.
        let dynamic = span.fuse(&fact.slice(5..8).unwrap()).unwrap();
        assert_eq!(dynamic.range(), &BlobSpan::new(2, Some(8)).unwrap());
        assert_eq!(dynamic.bytes(), &Bytes::from_static(b"234567"));

        // Unless the other side settles it: a suffix is open above whatever
        // the span turns out to be, and the whole blob swallows anything.
        let suffix: CasRangeFact<RangeFrom<u64>> = span.fuse(&fact.slice(5..).unwrap()).unwrap();
        assert_eq!(suffix.range(), &(2..));
        assert_eq!(suffix.blob_len(), Some(10));
        let all: CasFact = span.fuse(&fact).unwrap();
        assert_eq!(all, fact);
    }

    #[test]
    fn fusing_refuses_gaps_and_foreign_blobs() {
        let fact = whole();
        let error = fact
            .slice(1..3)
            .unwrap()
            .fuse(&fact.slice(5..7).unwrap())
            .unwrap_err();
        assert_eq!(
            error,
            FuseError::Disjoint {
                left: 1..3,
                right: 5..7
            }
        );

        let other = CasFact::from_bytes(Bytes::from_static(b"9876543210"));
        let error = fact
            .slice(1..5)
            .unwrap()
            .fuse(&other.slice(3..8).unwrap())
            .unwrap_err();
        assert_eq!(
            error,
            FuseError::Hash {
                left: fact.hash(),
                right: other.hash()
            }
        );
    }

    #[test]
    fn fusing_two_suffixes_keeps_the_earlier_one() {
        let fact = whole();
        let fused = fact
            .slice(6..)
            .unwrap()
            .fuse(&fact.slice(2..).unwrap())
            .unwrap();
        assert_eq!(fused.range(), &(2..));
        assert_eq!(fused.bytes(), &Bytes::from_static(b"23456789"));
        assert_eq!(fused.extent(), 2..10);
    }

    #[test]
    fn empty_facts_still_place_themselves() {
        let fact = whole();
        let empty = fact.slice(4..4).unwrap();
        assert!(empty.bytes().is_empty());
        assert_eq!(empty.extent(), 4..4);

        // An empty fact touches its neighbours and vanishes into them.
        let fused = fact.slice(1..4).unwrap().fuse(&empty).unwrap();
        assert_eq!(fused.range(), &(1..4));
        // A tail that knows the blob's end can be empty too. An empty tail
        // carries no bytes at all, so it is exactly a length claim: the blob
        // is ten bytes long, and here is none of it.
        let end = fact.slice(10..).unwrap();
        assert!(end.bytes().is_empty());
        assert_eq!(end.blob_len(), Some(10));
        assert_eq!(end.extent(), 10..10);
        // One byte earlier still pins the same length, but carries a byte.
        let last = fact.slice(9..).unwrap();
        assert_eq!(last.blob_len(), Some(10));
        assert_eq!(last.bytes(), &Bytes::from_static(b"9"));
        // A bounded range never claims a length.
        assert_eq!(fact.slice(0..10).unwrap().blob_len(), None);
        assert_eq!(CasFact::try_from(fact.slice(0..).unwrap()).unwrap(), fact);
        assert_eq!(end.fuse(&fact.slice(..10).unwrap()).unwrap(), fact);
    }
}
