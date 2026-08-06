//! A minimal safe wrapper over the `SQLite` C API.
//!
//! This crate is the unsafety-hiding layer and nothing else. It exposes the C
//! API with the same names, the same argument order, and the same result
//! codes. It does not decide how a database is used, how Rust values are
//! lowered into `SQLite` values, or when statements should be cached — those
//! are policy questions, and they belong above this crate.
//!
//! It is deliberately small and deliberately unfinished. Growing it means
//! adding the next C function we actually need, not adopting a general-purpose
//! binding wholesale.
//!
//! # Every `unsafe` in the trusted path is here
//!
//! Nothing above this crate writes `unsafe`. The workspace denies it, and only
//! this crate's modules opt out, each call site carrying the argument for why
//! it is sound. That is the property worth having: auditing the FFI boundary
//! means reading one crate.
//!
//! # Statements do not borrow their connection
//!
//! [`Statement`] carries no `'conn` lifetime, because `SQLite` does not
//! require one. [`Connection`]'s `Drop` closes with `sqlite3_close_v2`, which
//! leaves a connection holding outstanding prepared statements as an unusable
//! "zombie" and deallocates it once the last statement is finalized. A
//! [`Statement`] holds a refcounted handle, so dropping the [`Connection`]
//! first is safe.
//!
//! This matters for what we are building. A prop table is a fixed set of
//! prepared statements — one insert for a fact, one per deduction rule — owned
//! alongside the connection they came from. With a `'conn` borrow that is a
//! self-referential struct; without one it is an ordinary one.
//!
//! `rusqlite` cannot offer this: `libsqlite3-sys` blocklists `sqlite3_close_v2`
//! (misclassified as deprecated, see its `build.rs`), so `rusqlite` closes with
//! `sqlite3_close` and must keep statements borrowing their connection.
//!
//! # Bindings
//!
//! Raw declarations come from `libsqlite3-sys` (bundled amalgamation)
//! everywhere except `wasm32-unknown-unknown`, which uses `sqlite-wasm-rs`.
//! This is the split `rusqlite` itself uses, and reusing the same `-sys`
//! crates is what lets this crate coexist with `rusqlite` in one binary:
//! `libsqlite3-sys` declares `links = "sqlite3"`, so Cargo permits exactly one
//! copy of the C library in a build graph.
//!
//! `rusqlite` is **not** re-exported here. Code outside the trusted core may
//! depend on it directly where that is convenient; nothing reaches it through
//! this crate.

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub use libsqlite3_sys as ffi;
#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub use sqlite_wasm_rs as ffi;

mod connection;
mod error;
mod statement;
mod value;

pub use connection::{Connection, OpenFlags};
pub use error::{Error, ResultCode};
pub use statement::{Statement, Step};
pub use value::{ValueRef, ValueType};

#[cfg(feature = "vfs")]
pub mod vfs;

/// Result of a fallible `SQLite` call.
pub type Result<T, E = Error> = std::result::Result<T, E>;
