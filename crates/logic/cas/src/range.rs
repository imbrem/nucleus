//! Byte ranges usable as the parameter of a CAS fact.
//!
//! [`BlobRange`] is the sealed interface the fact rules use to read a range's
//! bounds. Its four implementors are the standard `u64` range types, and the
//! distinction that matters is whether the upper bound is *closed* (a byte
//! offset) or *open* (the end of the blob, wherever that is):
//!
//! | Type              | Lower bound | Upper bound        |
//! | ----------------- | ----------- | ------------------ |
//! | `Range<u64>`      | `start`     | `end`              |
//! | `RangeFrom<u64>`  | `start`     | end of the blob    |
//! | `RangeTo<u64>`    | `0`         | `end`              |
//! | `RangeFull`       | `0`         | end of the blob    |
//!
//! An open upper bound is a stronger claim: a fact whose range is `start..`
//! also pins the blob's length at `start + bytes.len()`. `RangeFull` is
//! therefore exactly the whole-blob claim, which is why
//! [`CasFact`](crate::CasFact) is `CasRangeFact<RangeFull>`.
//!
//! Those four shapes differ only in what they pin *statically*. What they carry
//! at runtime is always a `u64` start and an optional end, because a blob
//! always starts at zero: there is no `..` distinct from `0..`, and `..e` is
//! `0..e`. [`BlobSpan`] is that erased shape, the one range type able to hold
//! any of the four, and the one a dynamically typed boundary can expose.
//!
//! Keeping the four static shapes as well is what lets a length claim be
//! decided by the type rather than checked at runtime: only an open upper
//! bound reaches the end of the blob, so only [`RangeFrom`] and [`RangeFull`]
//! pin a length, and [`CasRangeFact::fuse`](crate::CasRangeFact::fuse) can
//! promise a whole-blob fact from a prefix and a suffix before either is
//! examined.
//!
//! The trait is sealed because the fact invariant is stated in terms of
//! [`BlobRange::start`] and [`BlobRange::end`]. An outside implementor could
//! misreport its own bounds and so widen a checked fact.

use std::{
    fmt::{self, Debug},
    ops::{Range, RangeFrom, RangeFull, RangeTo},
};

mod sealed {
    pub trait BlobRange {}

    impl BlobRange for std::ops::Range<u64> {}
    impl BlobRange for std::ops::RangeFrom<u64> {}
    impl BlobRange for std::ops::RangeTo<u64> {}
    impl BlobRange for std::ops::RangeFull {}
    impl BlobRange for super::BlobSpan {}
}

/// A byte range within a blob.
///
/// `RangeInclusive<u64>` is deliberately absent: its upper bound cannot be
/// normalized to an exclusive one without overflowing at `u64::MAX`.
pub trait BlobRange: sealed::BlobRange + Clone + Debug {
    /// Returns the first byte offset the range covers.
    fn start(&self) -> u64;

    /// Returns one past the last byte, or `None` for the end of the blob.
    fn end(&self) -> Option<u64>;

    /// Rebuilds these bounds in this range's shape.
    ///
    /// Returns `None` when the shape cannot express them, such as a nonzero
    /// `start` for [`RangeTo`] or a closed `end` for [`RangeFrom`].
    #[must_use]
    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self>
    where
        Self: Sized;

    /// Erases this range's static shape, keeping the bounds it carries.
    #[must_use]
    fn span(&self) -> BlobSpan {
        BlobSpan {
            start: self.start(),
            end: self.end(),
        }
    }
}

impl BlobRange for Range<u64> {
    fn start(&self) -> u64 {
        self.start
    }

    fn end(&self) -> Option<u64> {
        Some(self.end)
    }

    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self> {
        Some(start..end?)
    }
}

impl BlobRange for RangeFrom<u64> {
    fn start(&self) -> u64 {
        self.start
    }

    fn end(&self) -> Option<u64> {
        None
    }

    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self> {
        end.is_none().then_some(start..)
    }
}

impl BlobRange for RangeTo<u64> {
    fn start(&self) -> u64 {
        0
    }

    fn end(&self) -> Option<u64> {
        Some(self.end)
    }

    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self> {
        (start == 0).then_some(..end?)
    }
}

impl BlobRange for RangeFull {
    fn start(&self) -> u64 {
        0
    }

    fn end(&self) -> Option<u64> {
        None
    }

    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self> {
        (start == 0 && end.is_none()).then_some(..)
    }
}

/// A byte range of any shape: a start, and an end that may run to the end of
/// the blob.
///
/// This is what the four static shapes erase to, and the shape to reach for at
/// a boundary that cannot carry a type parameter. It gives up what they decide
/// statically: whether a range pins the blob's length becomes
/// [`CasRangeFact::blob_len`](crate::CasRangeFact::blob_len) returning `None`
/// rather than a type that could not have claimed one.
///
/// A span never ends before it starts. It may be empty, since an empty range
/// is a derivable fact, and an empty span with an open end is exactly a length
/// claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlobSpan {
    start: u64,
    end: Option<u64>,
}

impl BlobSpan {
    /// The whole blob.
    pub const WHOLE: Self = Self {
        start: 0,
        end: None,
    };

    /// Constructs a span, or returns `None` when `end` precedes `start`.
    #[must_use]
    pub const fn new(start: u64, end: Option<u64>) -> Option<Self> {
        match end {
            Some(end) if end < start => None,
            _ => Some(Self { start, end }),
        }
    }

    /// Constructs the span running from `start` to the end of the blob.
    #[must_use]
    pub const fn from_start(start: u64) -> Self {
        Self { start, end: None }
    }

    /// Returns the first byte offset the span covers.
    #[must_use]
    pub const fn start(&self) -> u64 {
        self.start
    }

    /// Returns one past the last byte, or `None` for the end of the blob.
    #[must_use]
    pub const fn end(&self) -> Option<u64> {
        self.end
    }

    /// Reports whether the span runs to the end of the blob.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.end.is_none()
    }
}

impl fmt::Display for BlobSpan {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.end {
            Some(end) => write!(formatter, "{}..{end}", self.start),
            None => write!(formatter, "{}..", self.start),
        }
    }
}

impl BlobRange for BlobSpan {
    fn start(&self) -> u64 {
        self.start
    }

    fn end(&self) -> Option<u64> {
        self.end
    }

    fn from_bounds(start: u64, end: Option<u64>) -> Option<Self> {
        Self::new(start, end)
    }

    fn span(&self) -> Self {
        *self
    }
}

impl From<Range<u64>> for BlobSpan {
    fn from(range: Range<u64>) -> Self {
        range.span()
    }
}

impl From<RangeFrom<u64>> for BlobSpan {
    fn from(range: RangeFrom<u64>) -> Self {
        range.span()
    }
}

impl From<RangeTo<u64>> for BlobSpan {
    fn from(range: RangeTo<u64>) -> Self {
        range.span()
    }
}

impl From<RangeFull> for BlobSpan {
    fn from(range: RangeFull) -> Self {
        range.span()
    }
}

/// The shape of the union of two blob ranges.
///
/// The union is open below exactly when either side is, and open above
/// exactly when either side is, so fusing a prefix with a suffix yields
/// [`RangeFull`]: a whole-blob fact. The bounds still have to meet at runtime;
/// this only names the type that can hold the answer.
///
/// A [`BlobSpan`] operand is open above only dynamically, so it usually drags
/// the output back to `BlobSpan`. It does not when the other operand settles
/// the question on its own: fusing anything with a [`RangeFrom`] is open above
/// whatever the span turns out to be, and fusing anything with a
/// [`RangeFull`] is the whole blob.
pub trait FuseRange<Rhs: BlobRange>: BlobRange {
    /// The range covering both operands.
    type Output: BlobRange;
}

macro_rules! fuse_ranges {
    ($(($lhs:ty, $rhs:ty) => $output:ty,)*) => {
        $(
            impl FuseRange<$rhs> for $lhs {
                type Output = $output;
            }
        )*
    };
}

fuse_ranges! {
    (Range<u64>, Range<u64>) => Range<u64>,
    (Range<u64>, RangeFrom<u64>) => RangeFrom<u64>,
    (Range<u64>, RangeTo<u64>) => RangeTo<u64>,
    (Range<u64>, RangeFull) => RangeFull,
    (RangeFrom<u64>, Range<u64>) => RangeFrom<u64>,
    (RangeFrom<u64>, RangeFrom<u64>) => RangeFrom<u64>,
    (RangeFrom<u64>, RangeTo<u64>) => RangeFull,
    (RangeFrom<u64>, RangeFull) => RangeFull,
    (RangeTo<u64>, Range<u64>) => RangeTo<u64>,
    (RangeTo<u64>, RangeFrom<u64>) => RangeFull,
    (RangeTo<u64>, RangeTo<u64>) => RangeTo<u64>,
    (RangeTo<u64>, RangeFull) => RangeFull,
    (RangeFull, Range<u64>) => RangeFull,
    (RangeFull, RangeFrom<u64>) => RangeFull,
    (RangeFull, RangeTo<u64>) => RangeFull,
    (RangeFull, RangeFull) => RangeFull,
    (Range<u64>, BlobSpan) => BlobSpan,
    (RangeFrom<u64>, BlobSpan) => RangeFrom<u64>,
    (RangeTo<u64>, BlobSpan) => BlobSpan,
    (RangeFull, BlobSpan) => RangeFull,
    (BlobSpan, Range<u64>) => BlobSpan,
    (BlobSpan, RangeFrom<u64>) => RangeFrom<u64>,
    (BlobSpan, RangeTo<u64>) => BlobSpan,
    (BlobSpan, RangeFull) => RangeFull,
    (BlobSpan, BlobSpan) => BlobSpan,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_shapes_report_their_bounds() {
        assert_eq!((3..7).start(), 3);
        assert_eq!((3..7).end(), Some(7));
        assert_eq!((3..).start(), 3);
        assert_eq!((3..).end(), None);
        assert_eq!((..7).start(), 0);
        assert_eq!((..7).end(), Some(7));
        assert_eq!(BlobRange::start(&(..)), 0);
        assert_eq!(BlobRange::end(&(..)), None);
    }

    #[test]
    fn every_shape_erases_to_the_same_span() {
        assert_eq!((3..7).span(), BlobSpan::new(3, Some(7)).unwrap());
        assert_eq!((3..).span(), BlobSpan::from_start(3));
        assert_eq!((..7).span(), BlobSpan::new(0, Some(7)).unwrap());
        assert_eq!(BlobRange::span(&(..)), BlobSpan::WHOLE);

        // A blob always starts at zero, so `..` and `0..` erase alike, and so
        // do `..7` and `0..7`. The type is what told them apart.
        assert_eq!(BlobRange::span(&(..)), (0..).span());
        assert_eq!((..7).span(), (0..7).span());

        // Only an open end reaches the end of the blob.
        assert!(BlobSpan::WHOLE.is_open());
        assert!((3..).span().is_open());
        assert!(!(3..7).span().is_open());
    }

    #[test]
    fn spans_are_never_backwards_and_may_be_empty() {
        assert_eq!(BlobSpan::new(7, Some(3)), None);
        assert_eq!(
            BlobSpan::new(4, Some(4)).map(|span| span.end()),
            Some(Some(4))
        );
        assert_eq!(BlobSpan::from_start(u64::MAX).end(), None);
        assert_eq!(BlobSpan::WHOLE.start(), 0);
    }

    #[test]
    fn spans_display_as_their_bounds() {
        assert_eq!(BlobSpan::new(3, Some(7)).unwrap().to_string(), "3..7");
        assert_eq!(BlobSpan::from_start(3).to_string(), "3..");
        assert_eq!(BlobSpan::WHOLE.to_string(), "0..");
    }

    #[test]
    fn shapes_reject_bounds_they_cannot_express() {
        assert_eq!(Range::<u64>::from_bounds(3, Some(7)), Some(3..7));
        assert_eq!(Range::<u64>::from_bounds(3, None), None);
        assert_eq!(RangeFrom::<u64>::from_bounds(3, None), Some(3..));
        assert_eq!(RangeFrom::<u64>::from_bounds(3, Some(7)), None);
        assert_eq!(RangeTo::<u64>::from_bounds(0, Some(7)), Some(..7));
        assert_eq!(RangeTo::<u64>::from_bounds(3, Some(7)), None);
        assert_eq!(RangeFull::from_bounds(0, None), Some(..));
        assert_eq!(RangeFull::from_bounds(0, Some(7)), None);
        assert_eq!(RangeFull::from_bounds(3, None), None);
        // The erased shape is the one that turns nothing away but a backwards
        // range, which is what makes it the boundary type.
        assert_eq!(BlobSpan::from_bounds(3, Some(7)), BlobSpan::new(3, Some(7)));
        assert_eq!(
            BlobSpan::from_bounds(3, None),
            Some(BlobSpan::from_start(3))
        );
        assert_eq!(BlobSpan::from_bounds(7, Some(3)), None);
    }
}
