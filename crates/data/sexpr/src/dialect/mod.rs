//! Concrete textual dialects.
//!
//! Each dialect implements [`Dialect`](crate::text::Dialect) and nothing else:
//! the nesting, balance, and end-of-input rules live once in
//! [`Parser`](crate::text::Parser).
//!
//! [`Pose`] is the reference dialect. [`Wat`] exists to keep the abstraction
//! honest — it disagrees with POSE about comments, about which characters
//! continue an atom, and about whether a quoted literal denotes text or bytes,
//! which is exactly the range of disagreement the trait has to absorb.

mod pose;
mod wat;

pub use pose::{Pose, parse_pose};
pub use wat::{Wat, parse_wat};
