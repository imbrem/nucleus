//! Typed LRAT parsing and clause validation.

mod kernel;
pub use covalence_logic_sat::cnf::{Clause, Formula, Literal};
pub use kernel::{ClauseId, Error, Kernel, RatGroup};

#[cfg(feature = "parse")]
pub mod parse;
