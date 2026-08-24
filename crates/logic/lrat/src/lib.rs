//! Typed LRAT parsing and proof-producing userspace loading.

mod loader;
#[cfg(test)]
#[path = "kernel.rs"]
mod oracle;
pub use covalence_logic_sat::cnf::{Clause, Formula, Literal};
pub use loader::{CnfBuilder, Error, LratProver, UnsatFormula, reconstruct};

/// A monotonically allocated LRAT clause identifier.
pub type ClauseId = u64;

/// One explicitly delimited RAT resolvent check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RatGroup {
    pub opposing_clause_id: ClauseId,
    pub resolvent_rup_hints: Vec<ClauseId>,
}

#[cfg(feature = "parse")]
pub mod parse;

#[cfg(feature = "parse")]
pub use parse::Step;
