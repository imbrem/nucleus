//! Works out whether the `SQLite` being linked is thread-safe.
//!
//! `Connection` is `Send` and `Sync` only where `SQLite` was compiled in
//! serialized mode, and which mode that is depends on the target and on
//! `LIBSQLITE3_FLAGS`. Deciding it here, from the same inputs the C build
//! uses, is what keeps the two from drifting: a hand-maintained list of
//! targets in `#[cfg]` would go stale the first time a `-sys` crate changed
//! its mind, and the failure would be a data race rather than a build error.
//!
//! Emits `sqlite_serialized` when the answer is yes. `connection.rs` gates the
//! `unsafe impl`s on it, and a test asserts at runtime that
//! `sqlite3_threadsafe()` agrees.

use std::env;

/// `wasm32-unknown-unknown` has no libc, so `sqlite-wasm-rs` supplies its own
/// build. It hardcodes `SQLITE_THREADSAFE=0` with no way to override.
const NO_LIBC: &str = "wasm32-unknown-unknown";

fn main() {
    println!("cargo::rustc-check-cfg=cfg(sqlite_serialized)");
    println!("cargo::rerun-if-env-changed=LIBSQLITE3_FLAGS");
    println!("cargo::rerun-if-changed=build.rs");

    let target = env::var("TARGET").unwrap_or_default();
    if threadsafe(&target) != 0 {
        println!("cargo::rustc-cfg=sqlite_serialized");
    }
}

/// Returns the `SQLITE_THREADSAFE` the linked library was built with.
fn threadsafe(target: &str) -> u8 {
    // Not negotiable: `sqlite-wasm-rs` ignores `LIBSQLITE3_FLAGS` entirely.
    if target == NO_LIBC {
        return 0;
    }

    // `libsqlite3-sys` applies `LIBSQLITE3_FLAGS` after its own defaults, and
    // a later `-D` of the same macro wins, so the last one is what the
    // compiler sees.
    let flags = env::var("LIBSQLITE3_FLAGS").unwrap_or_default();
    if let Some(mode) = flags
        .split_whitespace()
        .filter_map(|flag| flag.strip_prefix("-DSQLITE_THREADSAFE="))
        .next_back()
    {
        return mode.parse().unwrap_or(0);
    }

    // Defaults, from `libsqlite3-sys`'s own build script: serialized
    // everywhere except WASI, which it forces to single-threaded.
    u8::from(!target.starts_with("wasm32-wasi"))
}
