//! Typed Alethe parsing and proof-producing `QF_UF` replay.
//!
//! Like `covalence-logic-lrat`, this crate is the first-class Rust API. It
//! owns parser-independent command and replay types while treating proof bytes,
//! solver execution, names, and provenance as untrusted inputs. Every theorem
//! result is produced through checked HOL kernel operations.
//!
//! [`replay_qf_uf`] is the only entry point that produces a [`Refutation`].
//! [`lower_qf_uflia`] reads `QF_UFLIA` input into the same checked rows but
//! produces no theorem, because no HOL theory in this tree states arithmetic;
//! it reports the first arithmetic rule that stops the proof instead. See the
//! `replay` module documentation for what that lowering does and does not
//! claim.

mod parse;
mod replay;

pub use parse::{
    AletheCommand, AletheProof, ParseError, SmtCommand, SmtProblem, parse_alethe,
    parse_cvc5_output, parse_smtlib2,
};
pub use replay::{
    ArithmeticGap, Error, Logic, Lowering, Refutation, RuleHandler, RuleRequest, lower_qf_uflia,
    replay_qf_uf, replay_qf_uf_with_handler,
};
