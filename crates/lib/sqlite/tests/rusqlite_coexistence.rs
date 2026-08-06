#![allow(unsafe_code)]
//! Evidence that this crate and `rusqlite` can live in one binary.
//!
//! `libsqlite3-sys` declares `links = "sqlite3"`, so Cargo admits at most one
//! copy of the C library into a build graph. Because this crate binds the same
//! `-sys` crate `rusqlite` does, the two wrappers share one `SQLite`: the same
//! symbols, the same global VFS registry, and the same `sqlite3` and
//! `sqlite3_stmt` Rust types. Nothing here would link if that were not so.

use std::path::PathBuf;
use std::process;

use covalence_lib_sqlite as rusqlite;
use covalence_lib_sqlite::raw as sqlite3;

/// A scratch database file removed when the test ends.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Self {
        let mut path = std::env::temp_dir();
        path.push(format!("covalence-sqlite3-{}-{name}.db", process::id()));
        let _ = std::fs::remove_file(&path);
        Self(path)
    }

    fn as_str(&self) -> &str {
        self.0.to_str().expect("temporary paths are UTF-8")
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

#[test]
fn both_wrappers_bind_the_same_c_library() {
    // Identical symbol, reached through two different crates.
    assert_eq!(
        // SAFETY: `sqlite3_libversion_number` takes no arguments and reads a
        // compile-time constant.
        unsafe { sqlite3::ffi::sqlite3_libversion_number() },
        // SAFETY: as above.
        unsafe { rusqlite::ffi::sqlite3_libversion_number() },
    );
}

#[test]
fn the_two_wrappers_agree_on_the_raw_handle_type() {
    let connection = rusqlite::Connection::open_in_memory().expect("open with rusqlite");
    // SAFETY: the handle is only read, and `connection` outlives this binding.
    let raw = unsafe { connection.handle() };
    // This assignment is the actual assertion: it only type-checks because
    // `rusqlite::ffi` and `covalence_lib_sqlite3::ffi` are the same crate.
    let raw: *mut sqlite3::ffi::sqlite3 = raw;
    assert!(!raw.is_null());
}

#[test]
fn each_wrapper_sees_the_others_writes() {
    let scratch = Scratch::new("handoff");

    let writer = rusqlite::Connection::open(scratch.as_str()).expect("open with rusqlite");
    writer
        .execute_batch("CREATE TABLE fact (subject INTEGER, object INTEGER)")
        .expect("create table with rusqlite");
    drop(writer);

    let reader = sqlite3::Connection::open(scratch.as_str()).expect("open with sqlite3");
    // Compiling this statement proves the schema written by rusqlite is
    // visible; SQLite resolves table names at prepare time.
    reader
        .prepare("SELECT subject, object FROM fact")
        .expect("prepare against the rusqlite-written schema")
        .finalize()
        .expect("finalize");
    reader
        .prepare("SELECT subject FROM absent")
        .expect_err("a table neither wrapper created");
}

#[test]
fn a_statement_outlives_a_connection_that_rusqlite_would_still_be_borrowing() {
    // The shape rusqlite cannot express: a plain struct owning a connection
    // and its prepared statements, with no lifetime parameter anywhere.
    struct PreparedSet {
        connection: sqlite3::Connection,
        statements: Vec<sqlite3::Statement>,
    }

    let set = {
        let connection = sqlite3::Connection::open_in_memory().expect("open");
        let statements = ["SELECT 1", "SELECT 2"]
            .into_iter()
            .map(|sql| connection.prepare(sql).expect("prepare"))
            .collect();
        PreparedSet {
            connection,
            statements,
        }
    };

    // Drop the connection first; the statements keep the handle alive.
    let PreparedSet {
        connection,
        statements,
    } = set;
    drop(connection);
    assert_eq!(statements.len(), 2);
    assert!(!statements[0].connection().is_closed());
    drop(statements);
}
