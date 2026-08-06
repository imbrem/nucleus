//! The shell sees VFSes registered by the host.
//!
//! This mirrors `crates/lib/sqlite-shell/tests/mounted_cas.rs`, which asserts
//! the same property of the vendored upstream shell. The point of doing it
//! twice is that the property is about the *binding*, not about which shell
//! sits on top: `SQLite`'s VFS registry is process-global, so a CAS mounted
//! from Rust is reachable from anything holding a connection.
//!
//! Unlike the vendored shell, nothing here runs in C and nothing here needs a
//! `setjmp` trampoline to survive a failed open.

#![allow(
    unsafe_code,
    reason = "registers VFS names private to this test binary"
)]

use std::sync::Arc;

use covalence_data_cas::MemoryCas;
use covalence_lib_sql_shell::{SharedBuffer, Shell};
use covalence_lib_sqlite::Connection;
use covalence_lib_sqlite::vfs::register_cas;

/// Builds a real database and returns its complete bytes.
fn database_image(stem: &str) -> Vec<u8> {
    let path = std::env::temp_dir().join(format!("covalence-sql-shell-{stem}.sqlite"));
    let _ = std::fs::remove_file(&path);
    {
        let connection = Connection::open(&path).unwrap();
        connection
            .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
            .unwrap();
    }
    let bytes = std::fs::read(&path).unwrap();
    std::fs::remove_file(&path).unwrap();
    bytes
}

/// Runs a script against a fresh in-memory shell and returns what it printed.
fn shell_output(script: &str) -> (String, String, usize) {
    let out = SharedBuffer::new();
    let err = SharedBuffer::new();
    let mut shell = Shell::new(
        Connection::open_in_memory().unwrap(),
        Box::new(out.clone()),
        Box::new(err.clone()),
    );
    shell.run(&mut script.as_bytes()).unwrap();
    (out.take_string(), err.take_string(), shell.errors())
}

#[test]
fn the_shell_queries_a_database_mounted_in_the_cas() {
    let cas = Arc::new(MemoryCas::new());
    let address = cas.insert(database_image("mounted")).unwrap();
    // SAFETY: this name is private to this test binary.
    let mounted = unsafe { register_cas(Arc::clone(&cas), "covalence-test-sql-shell-cas", false) }
        .expect("mounting the CAS");

    // Exactly what a user would type at a prompt.
    let script = format!(
        ".open file:{}?mode=ro&immutable=1&vfs={}\nSELECT n FROM value;\n",
        address.hex(),
        mounted.name().as_str()
    );
    let (output, errors, count) = shell_output(&script);

    assert_eq!(count, 0, "shell reported errors: {errors}");
    assert_eq!(output.trim(), "42");
}

#[test]
fn the_mount_is_visible_to_dot_commands() {
    let cas = Arc::new(MemoryCas::new());
    let address = cas.insert(database_image("dotcmds")).unwrap();
    // SAFETY: this name is private to this test binary.
    let mounted =
        unsafe { register_cas(Arc::clone(&cas), "covalence-test-sql-shell-cas-dot", false) }
            .expect("mounting the CAS");

    let script = format!(
        ".open file:{}?mode=ro&immutable=1&vfs={}\n.tables\n.schema\n.mode box\nSELECT n FROM value;\n",
        address.hex(),
        mounted.name().as_str()
    );
    let (output, errors, count) = shell_output(&script);

    assert_eq!(count, 0, "shell reported errors: {errors}");
    assert!(output.contains("value"), "{output}");
    assert!(
        output.contains("CREATE TABLE value (n INTEGER);"),
        "{output}"
    );
    assert!(output.contains("42"), "{output}");
}

#[test]
fn the_shell_cannot_write_through_the_mount() {
    let cas = Arc::new(MemoryCas::new());
    let address = cas.insert(database_image("readonly")).unwrap();
    // SAFETY: this name is private to this test binary.
    let mounted =
        unsafe { register_cas(Arc::clone(&cas), "covalence-test-sql-shell-cas-ro", false) }
            .expect("mounting the CAS");

    let script = format!(
        ".open file:{}?mode=ro&immutable=1&vfs={}\nINSERT INTO value VALUES (7);\n",
        address.hex(),
        mounted.name().as_str()
    );
    let (_, errors, count) = shell_output(&script);

    assert_eq!(count, 1, "the mount must reject writes");
    assert!(errors.contains("Error: "), "{errors}");
}

#[test]
fn the_shell_reports_an_address_which_is_not_resident() {
    let cas = Arc::new(MemoryCas::new());
    // Admitted, then dropped: a well-formed address that no longer resolves.
    let address = cas.insert(database_image("absent")).unwrap();
    assert!(cas.remove(address));

    // SAFETY: this name is private to this test binary.
    let mounted = unsafe {
        register_cas(
            Arc::clone(&cas),
            "covalence-test-sql-shell-cas-absent",
            false,
        )
    }
    .expect("mounting the CAS");

    let script = format!(
        ".open file:{}?mode=ro&immutable=1&vfs={}\nSELECT n FROM value;\n",
        address.hex(),
        mounted.name().as_str()
    );
    let (_, errors, count) = shell_output(&script);

    // Both the open and the query fail: the shell keeps the previous
    // connection, which is an empty in-memory database with no `value` table.
    assert!(count >= 1, "a removed object must not resolve");
    assert!(errors.contains("Error: "), "{errors}");
}

#[test]
fn a_failed_open_leaves_the_shell_usable() {
    let cas = Arc::new(MemoryCas::new());
    // SAFETY: this name is private to this test binary.
    let mounted = unsafe {
        register_cas(
            Arc::clone(&cas),
            "covalence-test-sql-shell-cas-usable",
            false,
        )
    }
    .expect("mounting the CAS");

    // The equivalent path in the vendored shell reaches `exit()` and needs a
    // `setjmp` landing pad to avoid taking the host process down with it.
    let script = format!(
        ".open file:not-an-address?vfs={}\nSELECT 'still here';\n",
        mounted.name().as_str()
    );
    let (output, _, count) = shell_output(&script);

    assert_eq!(count, 1);
    assert_eq!(output.trim(), "still here");
}
