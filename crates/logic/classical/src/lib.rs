//! Tagged classical logic runtime and compatibility-facing matrix views.
//!
//! The selected runtime uses fixed 64-bit `LIT`/`AND`/`OR`/`SAT` references,
//! checked ownership, and an intrusive allocator. The former `Cnf`/`Dnf` API
//! remains as an untrusted builder and borrowed-view facade: every raw live
//! slot is actually backed by [`tagged::Checked`], and universal theorem slots
//! can only contain sealed [`tagged::Theorem`] values.
//!
//! External theorem IDs are stable handles with LIFO reuse. They are not part
//! of the packed authority-bearing representation.

mod compat;
pub mod tagged;

pub use compat::{
    CheckedArena, ClassicalArena, ClassicalKernel, Cnf, CnfId, CnfRef, Dnf, DnfId, DnfRef, Error,
    Lit, LitError, LitVec, RatGroup, Refutation, Refuter, ThmId, ThmRef,
};
