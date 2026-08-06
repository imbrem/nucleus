//! The embedded shell sees VFSes registered by the host.
//!
//! This is the property the whole embedding exists for. `SQLite`'s VFS
//! registry is process-global, and the shell links the same `SQLite` as the
//! host, so a CAS mounted from Rust is reachable from a shell command line
//! with no bridge, no export, and no copy of the bytes.

#![allow(
    unsafe_code,
    reason = "registers VFS names private to this test binary"
)]

use std::sync::{Arc, Mutex, MutexGuard};

use covalence_data_cas::MemoryCas;
use covalence_lib_sqlite::Connection;
use covalence_lib_sqlite::vfs::register_cas;

/// `shell.c` keeps its state in file-scope variables. One invocation at a time.
static SHELL: Mutex<()> = Mutex::new(());

fn exclusive() -> MutexGuard<'static, ()> {
    SHELL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Builds a real database and returns its complete bytes.
fn database_image(stem: &str) -> Vec<u8> {
    let path = std::env::temp_dir().join(format!("covalence-shell-{stem}.sqlite"));
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

/// Runs the shell with its output redirected to a fresh file, and returns it.
fn shell_output(stem: &str, arguments: &[&str]) -> (i32, String) {
    let path = std::env::temp_dir().join(format!("covalence-shell-out-{stem}.txt"));
    let _ = std::fs::remove_file(&path);

    let mut argv = vec![
        "-batch".to_owned(),
        "-cmd".to_owned(),
        format!(".output {}", path.display()),
    ];
    argv.extend(arguments.iter().map(|argument| (*argument).to_owned()));

    let status = covalence_lib_sqlite_shell::run(&argv).unwrap();
    let output = std::fs::read_to_string(&path).unwrap_or_default();
    let _ = std::fs::remove_file(&path);
    (status, output)
}

#[test]
fn the_shell_queries_a_database_mounted_in_the_cas() {
    let _guard = exclusive();
    let cas = Arc::new(MemoryCas::new());
    let address = cas.insert(database_image("mounted")).unwrap();
    // SAFETY: this name is private to this test binary.
    let mounted = unsafe { register_cas(Arc::clone(&cas), "covalence-test-shell-cas", false) }
        .expect("mounting the CAS");

    // Exactly what a user would type at a shell prompt.
    let uri = format!(
        "file:{}?mode=ro&immutable=1&vfs={}",
        address.hex(),
        mounted.name().as_str()
    );
    let (status, output) = shell_output("mounted", &[&uri, "SELECT n FROM value;"]);

    assert_eq!(status, 0, "shell exited non-zero; output: {output}");
    assert_eq!(output.trim(), "42");
}

#[test]
fn the_shell_cannot_write_through_the_mount() {
    let _guard = exclusive();
    let cas = Arc::new(MemoryCas::new());
    let address = cas.insert(database_image("readonly")).unwrap();
    // SAFETY: this name is private to this test binary.
    let mounted = unsafe { register_cas(Arc::clone(&cas), "covalence-test-shell-cas-ro", false) }
        .expect("mounting the CAS");

    let uri = format!(
        "file:{}?mode=ro&immutable=1&vfs={}",
        address.hex(),
        mounted.name().as_str()
    );
    let (status, _) = shell_output("readonly", &[&uri, "INSERT INTO value VALUES (7);"]);

    assert_ne!(status, 0, "the mount must reject writes");
}

#[test]
fn the_shell_reports_an_address_which_is_not_resident() {
    let _guard = exclusive();
    let cas = Arc::new(MemoryCas::new());
    // Admitted, then dropped: a well-formed address that no longer resolves.
    let address = cas.insert(database_image("absent")).unwrap();
    assert!(cas.remove(address));

    // SAFETY: this name is private to this test binary.
    let mounted =
        unsafe { register_cas(Arc::clone(&cas), "covalence-test-shell-cas-absent", false) }
            .expect("mounting the CAS");

    let uri = format!(
        "file:{}?mode=ro&immutable=1&vfs={}",
        address.hex(),
        mounted.name().as_str()
    );
    let (status, _) = shell_output("absent", &[&uri, "SELECT n FROM value;"]);

    assert_ne!(status, 0, "a removed object must not resolve");
}
