//! Small, shared syntax trees for the Nucleus HOL kernel.
//!
//! This crate starts with an enum-friendly expression layer. Logical checking
//! and theorem authority are deliberately added by higher layers.

mod expr;
mod tree;

pub use expr::{App, Arr, BoolTy, Bound, Eqn, Expr, Lam, Node};
pub use tree::Tree;
