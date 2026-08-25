//! Untrusted derived constructions over the checked HOL kernel.
//!
//! This crate contains traversal, package assembly, and proof orchestration
//! which can be replaced without changing the trusted kernel. Every result is
//! admitted only through public checked [`Kernel`](covalence_logic_hol::Kernel)
//! operations.

mod equality;
mod exists;
mod forall;
mod infinity;
mod model;
mod natural;
mod subtype;
mod syntax;

pub use equality::{EqualityError, ProvedEquality, equality_symmetry, equality_transitivity};
pub use exists::{ExistsError, OpenedExists, open_exists};
pub use forall::{ForallError, ProvedTerm, forall_elim};
pub use infinity::{Infinity, InfinityError, InfinityExt};
pub use model::{ChosenModel, ModelError, ModelExt, Substitution, eta_expand_at, substitute};
pub use natural::{NaturalError, NaturalExt, Naturals};
pub use subtype::{Subtype, SubtypeError, SubtypeExt};
pub use syntax::{SyntaxError, join_same_syntax};
