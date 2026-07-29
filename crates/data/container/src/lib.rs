//! Audited abstractions over standard container types.
//!
//! [`Proj`] provides const-indexed tuple and array projection.
//!
//! The traits are sealed intentionally. Supporting another container is a trust
//! decision made by this crate, not merely a structural implementation choice.

#![deny(unsafe_code)]

mod projection;

pub use projection::{Arity, Proj};
