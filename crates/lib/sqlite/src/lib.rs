//! `SQLite` binding used by Nucleus.

pub use rusqlite::*;

/// The minimal safe wrapper over the `SQLite` C API.
///
/// `SQLite` itself is shared: both wrappers bind the same `libsqlite3-sys`
/// (or `sqlite-wasm-rs`) crate, so there is one C library, one global VFS
/// registry, and one `sqlite3` type. See `tests/rusqlite_coexistence.rs`.
pub use covalence_lib_sqlite3 as raw;

#[cfg(feature = "vfs")]
pub mod vfs;
