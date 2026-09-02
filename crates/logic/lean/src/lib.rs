//! Lean logic frontend and readers for Lean's exported logic.
//!
//! Parsing never creates a Nucleus theorem fact. [`stream`] contains the
//! logic-independent NDJSON and dense backward-table layer; [`lean4export`]
//! validates the pinned Lean-specific record vocabulary above it.

pub mod lean4export;
pub mod stream;
pub mod syntax;

mod decode;
pub mod direct;
pub mod import;

pub use import::{Artifacts, Backend, BackendArtifacts, ImportError, Imported, import};
pub use lean4export::{Error, Export, FORMAT_VERSION, Metadata, read};
