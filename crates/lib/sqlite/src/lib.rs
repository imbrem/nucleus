//! `SQLite` binding used by Nucleus.

pub use rusqlite::*;

#[cfg(feature = "vfs")]
pub mod vfs;
