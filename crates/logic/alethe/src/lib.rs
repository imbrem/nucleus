//! Typed Alethe parsing and proof-producing QF_UF replay.
//!
//! Like `covalence-logic-lrat`, this crate is the first-class Rust API. It
//! owns parser-independent command and replay types while treating proof bytes,
//! solver execution, names, and provenance as untrusted inputs. Every theorem
//! result is produced through checked HOL kernel operations.

mod parse;

pub use parse::{AletheCommand, AletheProof, ParseError, parse_alethe};
