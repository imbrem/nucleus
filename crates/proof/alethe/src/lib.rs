//! Untrusted Alethe parsing and replay through the standard proof-component ABI.
//!
//! Parsing, names, rule dispatch, solver selection, and provenance are outside
//! the TCB. Only operations imported from `nucleus:proof/host` create checked
//! theorem facts.

pub use covalence_logic_alethe::{AletheCommand, AletheProof, ParseError, parse_alethe};

// `wit-bindgen` emits canonical-ABI glue only for the component build. The
// native build contains the parser and replay unit tests.
#[allow(
    unsafe_code,
    warnings,
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::restriction
)]
#[cfg(target_arch = "wasm32")]
mod bindings;
