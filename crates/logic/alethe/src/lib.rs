//! Typed Alethe parsing and proof-producing `QF_UF` replay.
//!
//! Like `covalence-logic-lrat`, this crate is the first-class Rust API. It
//! owns parser-independent command and replay types while treating proof bytes,
//! solver execution, names, and provenance as untrusted inputs. Every theorem
//! result is produced through checked HOL kernel operations.

mod parse;
mod replay;

pub use parse::{
    AletheCommand, AletheProof, ParseError, SmtCommand, SmtProblem, parse_alethe,
    parse_cvc5_output, parse_smtlib2,
};
pub use replay::{
    Error, Refutation, RuleHandler, RuleRequest, replay_qf_uf, replay_qf_uf_with_handler,
};
