//! Untrusted Metamath parsing and proof validation.
//!
//! This crate is intentionally outside Nucleus's trusted computing base. Its
//! [`DatabaseSink`] interface is the boundary intended to drive a future HOL
//! replay: parsing may suggest kernel operations, but cannot establish them.

pub mod axiom_sets;
mod database;
mod emit;
mod error;
mod expr;
mod parse;
mod subst;
pub mod trace;
mod verify;

pub use database::{
    Assertion, Database, DatabaseSink, FloatHyp, Frame, Hypothesis, Proof, Statement, SymbolKind,
};
pub use emit::to_mm_string;
pub use error::{LabelPosition, MmError};
pub use expr::{Expr, Symbol};
pub use parse::{
    FileResolver, MemoryResolver, SourceResolver, parse, parse_into, parse_into_with_resolver,
    parse_with_resolver,
};
// `ReplayObserver::assertion` takes a `&Subst`, so an out-of-crate observer
// needs to be able to name it.
pub use subst::Subst;
pub use verify::{ProofStep, ReplayObserver, proof_steps, replay, verify_all, verify_assertion};
