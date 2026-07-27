//! WebAssembly runtimes used by Nucleus.
//!
//! This crate is the dependency-policy boundary for executing WebAssembly.
//! Portable code can use [`wasmi`]; target-specific runtimes can be added
//! behind separate features without exposing them throughout the workspace.

#[cfg(feature = "wasmi")]
pub use wasmi;
