//! Untrusted Metamath parsing and proof validation.
//!
//! This crate is intentionally outside Nucleus's trusted computing base. Its
//! [`DatabaseSink`] interface is the boundary intended to drive a future HOL
//! replay: parsing may suggest kernel operations, but cannot establish them.

#![allow(clippy::pedantic, clippy::collapsible_if, clippy::type_complexity)]

mod database;
mod emit;
mod error;
mod expr;
mod parse;
mod subst;
mod verify;

pub use database::{
    Assertion, Database, DatabaseSink, FloatHyp, Frame, Hypothesis, Proof, Statement, SymbolKind,
};
pub use emit::to_mm_string;
pub use error::MmError;
pub use expr::{Expr, Symbol};
pub use parse::{
    FileResolver, MemoryResolver, SourceResolver, parse, parse_into, parse_into_with_resolver,
    parse_with_resolver,
};
pub use verify::{ProofStep, ReplayObserver, proof_steps, replay, verify_all, verify_assertion};
