//! Untrusted derived constructions over the checked HOL kernel.
//!
//! This crate contains traversal, package assembly, and proof orchestration
//! which can be replaced without changing the trusted kernel. Every result is
//! admitted only through public checked [`Kernel`](covalence_logic_hol::Kernel)
//! operations.

mod model;
mod subtype;

pub use model::{ChosenModel, ModelError, ModelExt};
pub use subtype::{Subtype, SubtypeError, SubtypeExt};
