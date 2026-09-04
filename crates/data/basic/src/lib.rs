//! Small, ubiquitous owned data types shared across Nucleus formats.
//!
//! Use [`Symbol`] for owned identifiers and tokens. It keeps the ordinary
//! short case inline while retaining string semantics and cheap cloning.

/// An owned identifier or token, stored inline when short.
pub type Symbol = smol_str::SmolStr;
