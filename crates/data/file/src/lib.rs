//! File byte stores with explicit pure-BLAKE3 authentication state.
//!
//! [`Blake3Mmap`] is a volatile, anonymous mapping whose mutations are all
//! mediated by this crate. [`Blake3File`] treats an ordinary file as untrusted
//! storage and rechecks every range before returning its bytes.

#![deny(unsafe_code)]

mod checked;
mod loader;
mod mapped;

pub use checked::{Blake3File, FileProofError, VerifiedRange};
pub use loader::{Blake3Bytes, LoadError, load_blake3_path, load_blake3_reader};
pub use mapped::{Blake3Mmap, RangeError, RangeRequirement, RangeState, StateSpan};
