//! A total order on [`Json`], and the pointer shortcuts comparison starts
//! with.
//!
//! Trees in the owned families share subtrees aggressively — cloning is how a
//! subtree is extracted — so two values being compared are often literally the
//! same allocation. Every comparison therefore begins by asking whether the
//! two sides share storage, and answers without descending when they do. The
//! check is on the data pointer and length only: two live objects cannot
//! overlap, so matching addresses mean the same object even when the two
//! sides' index families differ.
//!
//! The order itself ranks variants — null, then booleans, numbers, strings,
//! arrays, objects — and compares contents within a variant: numerically for
//! numbers, lexicographically for strings, elementwise for arrays, and by
//! sorted `(key, value)` entries for objects. It is consistent with `Eq`,
//! which distinguishes `1` from `1.0` the way `serde_json` does; a numeric
//! tie between an integer and a float orders the integer first.

use std::cmp::Ordering;

use covalence_lib_json::Number;

use crate::{Index, Json, Map};

/// Whether two string slices are the same memory.
pub(crate) fn same_str(left: &str, right: &str) -> bool {
    std::ptr::eq(left, right)
}

/// Whether two slices are the same memory, however their elements are typed.
///
/// Address equality between live allocations implies the same object, so a
/// match across different index families implies the families' storage
/// coincides and the contents are one value.
pub(crate) fn same_slice<A, B>(left: &[A], right: &[B]) -> bool {
    left.len() == right.len() && std::ptr::eq(left.as_ptr().cast::<u8>(), right.as_ptr().cast())
}

/// `2^64`, the least float above every `u64`.
const ABOVE_INTS: f64 = 18_446_744_073_709_551_616.0;
/// `-2^63` exactly, the least integer either width represents.
const LEAST_INT: f64 = -9_223_372_036_854_775_808.0;

/// Where `int` stands relative to a finite `float`, exactly.
///
/// Comparing through `as f64` would be wrong twice over: distinct large
/// integers collapse onto one float, and a collapse to `Equal` would
/// contradict `Eq`. Instead the float's whole part is compared as an integer,
/// and its fraction breaks the tie. A numeric tie is broken toward the
/// integer, which is what keeps this consistent with `Eq` distinguishing `1`
/// from `1.0`.
fn int_versus_float(int: i128, float: f64) -> Ordering {
    if float >= ABOVE_INTS {
        return Ordering::Less;
    }
    if float < LEAST_INT {
        return Ordering::Greater;
    }
    let whole = float.trunc();
    // In `[-2^63, 2^64)` by the guards above, so the cast is exact.
    #[allow(clippy::cast_possible_truncation)]
    let whole_int = whole as i128;
    match int.cmp(&whole_int) {
        Ordering::Equal if float > whole => Ordering::Less,
        Ordering::Equal if float < whole => Ordering::Greater,
        Ordering::Equal => Ordering::Less,
        unequal => unequal,
    }
}

/// The integer a non-float [`Number`] holds, widened to compare exactly.
fn as_int(number: &Number) -> Option<i128> {
    if let Some(int) = number.as_i64() {
        Some(i128::from(int))
    } else {
        number.as_u64().map(i128::from)
    }
}

/// A total order on JSON numbers, consistent with their equality.
pub(crate) fn number_cmp(left: &Number, right: &Number) -> Ordering {
    match (as_int(left), as_int(right)) {
        (Some(left), Some(right)) => left.cmp(&right),
        (Some(int), None) => int_versus_float(int, right.as_f64().expect("not an integer")),
        (None, Some(int)) => int_versus_float(int, left.as_f64().expect("not an integer")).reverse(),
        (None, None) => {
            let (left, right) = (
                left.as_f64().expect("not an integer"),
                right.as_f64().expect("not an integer"),
            );
            // Finite by construction, so comparable; `==` treats zeros alike.
            left.partial_cmp(&right).expect("JSON floats are finite")
        }
    }
}

/// The rank a variant sorts at; contents only matter within a rank.
fn rank<I: Index>(value: &Json<I>) -> u8 {
    match value {
        Json::Null => 0,
        Json::Bool(_) => 1,
        Json::Number(_) => 2,
        Json::String(_) => 3,
        Json::Array(_) => 4,
        Json::Object(_) => 5,
    }
}

fn map_cmp<I: Index>(left: &Map<I>, right: &Map<I>) -> Ordering {
    if same_slice(left.entries(), right.entries()) {
        return Ordering::Equal;
    }
    for (left, right) in left.iter().zip(right.iter()) {
        let keys = if same_str(&left.key, &right.key) {
            Ordering::Equal
        } else {
            (*left.key).cmp(&right.key)
        };
        match keys.then_with(|| left.value.cmp(&right.value)) {
            Ordering::Equal => {}
            unequal => return unequal,
        }
    }
    left.len().cmp(&right.len())
}

impl<I: Index> Ord for Json<I> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Json::Bool(left), Json::Bool(right)) => left.cmp(right),
            (Json::Number(left), Json::Number(right)) => number_cmp(left, right),
            (Json::String(left), Json::String(right)) => {
                if same_str(left, right) {
                    Ordering::Equal
                } else {
                    (**left).cmp(right)
                }
            }
            (Json::Array(left), Json::Array(right)) => {
                if same_slice(left, right) {
                    Ordering::Equal
                } else {
                    left.iter().cmp(right.iter())
                }
            }
            (Json::Object(left), Json::Object(right)) => map_cmp(left, right),
            (left, right) => rank(left).cmp(&rank(right)),
        }
    }
}

impl<I: Index> PartialOrd for Json<I> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
