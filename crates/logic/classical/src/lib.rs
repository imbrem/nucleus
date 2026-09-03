//! Tagged classical logic runtime and compatibility-facing matrix views.
//!
//! The selected runtime is the [`tagged`] module: fixed 64-bit
//! `LIT`/`AND`/`OR`/`SAT` references, checked ownership, an intrusive
//! allocator, and a sealed [`tagged::Theorem`]. Validation, structural
//! equality, hashing and decoding are one flat pass over the words, and no
//! recursive syntax tree is stored for them. `Formula` is still a recursive
//! value, so building one, cloning it, hashing it, or packing it is bounded by
//! its depth; the flat pass is what removed that bound from validation,
//! comparison, and decoding.
//!
//! [`Matrix`] is the untrusted builder and projection the former `Cnf`/`Dnf`
//! pair became: which of AND/OR sits outermost is a property of the turnstile
//! [`Side`], not of the storage. [`ClassicalArena`] gates every slot through
//! canonical packing and keeps the matrix; only [`ClassicalKernel`] retains the
//! sealed theorem fact.
//!
//! External theorem IDs are stable handles with LIFO reuse. They are not part
//! of the packed authority-bearing representation.

mod compat;
pub mod tagged;

pub use compat::{
    CheckedArena, ClassicalArena, ClassicalKernel, Error, Lit, LitError, LitVec, Matrix, MatrixRef,
    RatGroup, Refutation, Refuter, RowId, ThmId, ThmRef,
};
pub use tagged::Side;
