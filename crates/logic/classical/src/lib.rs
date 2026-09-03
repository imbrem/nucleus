//! Checked classical logic.
//!
//! The runtime stores tagged formulas in 32-bit words. Validation, equality,
//! hashing, and decoding traverse that storage without recursion. The theorem
//! wrapper is sealed; validating syntax alone creates no theorem fact.

mod cnf;
mod tagged;

pub use cnf::{
    CheckedArena, ClassicalArena, ClassicalKernel, Error, Lit, LitError, LitVec, Matrix, RatGroup,
    Refutation, Refuter, RowId, ThmId, ThmRef,
};
pub use tagged::{Checked, EditError, Formula, RuntimeError, Sequent, Side, Theorem, pack};
