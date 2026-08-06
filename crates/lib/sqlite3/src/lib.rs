//! Minimal safe wrapper over the `SQLite` C API.
//!
//! This crate is the unsafety-hiding layer and nothing else. It exposes the C
//! API with the same names, the same argument order, and the same result
//! codes; it does not decide how a database is used, how Rust values are
//! lowered into `SQLite` values, or when statements should be cached. Those
//! are policy questions and belong above this crate.
//!
//! # Statements do not borrow their connection
//!
//! [`Statement`] carries no `'conn` lifetime. `SQLite` does not require one:
//! [`sqlite3_close_v2`] leaves a connection with outstanding prepared
//! statements as an unusable "zombie" and deallocates it once the last
//! statement is finalized. A [`Statement`] therefore holds a refcounted
//! handle, and dropping the [`Connection`] first is safe. A struct may own a
//! connection and a fixed set of prepared statements side by side without a
//! self-referential borrow.
//!
//! [`sqlite3_close_v2`]: https://sqlite.org/c3ref/close.html
//!
//! # Bindings
//!
//! The raw declarations come from `libsqlite3-sys` (bundled amalgamation)
//! everywhere except `wasm32-unknown-unknown`, which uses `sqlite-wasm-rs`.
//! This is the split `rusqlite` itself uses, and reusing the same `-sys`
//! crates is what lets this crate coexist with `rusqlite` in one binary:
//! `libsqlite3-sys` declares `links = "sqlite3"`, so Cargo permits exactly one
//! copy of the C library in a build graph.

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub use libsqlite3_sys as ffi;
#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub use sqlite_wasm_rs as ffi;

mod connection;
mod error;
mod statement;

pub use connection::{Connection, OpenFlags};
pub use error::{Error, ResultCode};
pub use statement::Statement;

/// Result of a fallible `SQLite` call.
pub type Result<T, E = Error> = std::result::Result<T, E>;
