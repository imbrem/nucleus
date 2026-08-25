//! Untrusted derived constructions over the checked HOL kernel.
//!
//! This crate contains traversal, package assembly, and proof orchestration
//! which can be replaced without changing the trusted kernel. Every result is
//! admitted only through public checked [`Kernel`](covalence_logic_hol::Kernel)
//! operations.

mod exists;
mod infinity;
mod model;
mod natural;
mod subtype;

pub use exists::{ExistsError, OpenedExists, open_exists};
pub use infinity::{Infinity, InfinityError, InfinityExt};
pub use model::{ChosenModel, ModelError, ModelExt, Substitution, substitute};
pub use natural::{NaturalError, NaturalExt, Naturals};
pub use subtype::{Subtype, SubtypeError, SubtypeExt};
