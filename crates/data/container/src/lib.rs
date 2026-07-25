//! Audited abstractions over standard container and indirection types.
//!
//! [`TrustedDeref`] identifies wrappers whose dereference target has stable
//! value semantics. [`TrustedListIndex`] provides uniform checked indexing for
//! trusted contiguous list containers and for trusted wrappers around them.
//! [`Proj`] provides const-indexed heterogeneous tuple and array projection.
//!
//! These traits are sealed intentionally. Supporting another smart pointer or
//! container is a trust decision made by this crate, not merely a structural
//! implementation choice.

#![deny(unsafe_code)]

mod projection;
mod trusted;

pub use projection::{Arity, Proj};
pub use trusted::{TrustedDeref, TrustedListIndex};
