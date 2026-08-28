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
//! The trait is sealed because the fact invariant is stated in terms of
//! [`BlobRange::start`] and [`BlobRange::end`]. An outside implementor could
//! misreport its own bounds and so widen a checked fact.

use std::{
    fmt::Debug,
    ops::{Range, RangeFrom, RangeFull, RangeTo},
};

mod sealed {
    pub trait BlobRange {}

    impl BlobRange for std::ops::Range<u64> {}
    impl BlobRange for std::ops::RangeFrom<u64> {}
    impl BlobRange for std::ops::RangeTo<u64> {}
    impl BlobRange for std::ops::RangeFull {}
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

/// The shape of the union of two blob ranges.
///
/// The union is open below exactly when either side is, and open above
/// exactly when either side is, so fusing a prefix with a suffix yields
/// [`RangeFull`]: a whole-blob fact. The bounds still have to meet at runtime;
/// this only names the type that can hold the answer.
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
    }
}
