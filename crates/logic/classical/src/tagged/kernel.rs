//! Sealed theorem authority for the tagged runtime.

use std::hash::{Hash, Hasher};

use covalence_lib_error::snafu::Snafu;

use super::{Checked, Formula, FormulaPath, RuntimeError, Sequent, Side, pack};

mod derive;
mod rewrite;
mod support;
mod types;

pub use types::{EditError, ModelWitness, Theorem};

use support::{concatenate, erase_first, evaluate, positive_roots, singleton};

#[cfg(test)]
#[allow(clippy::module_inception)]
mod tests;
