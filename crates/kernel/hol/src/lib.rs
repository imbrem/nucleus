//! Small, shared syntax trees for the Nucleus HOL kernel.
//!
//! This crate starts with an enum-friendly expression layer. Logical checking
//! and theorem authority are deliberately added by higher layers.

mod check;
mod expr;
mod tree;

pub use check::{CheckError, check_closed, check_type};
pub use expr::{
    Abs, App, Arr, Base, BoolLit, BoolTy, Bound, Eps, Eqn, Expr, Free, IndTy, Lam, Node, Rep, Sub,
    Succ, Zero,
};
pub use tree::Tree;
