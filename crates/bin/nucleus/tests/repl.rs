//! The terminal REPL, driven the way a script would drive it.
//!
//! These run the real binary against the real shell binary, because the thing
//! worth testing is the wiring: a session says [`Response::Shell`], the host
//! serves its store over a socket, and a separate process reads it. Unit tests
//! on the session cannot see any of that.
//!
//! # What is not covered here
//!
//! A bare `(sqlite)` with nothing after it — the interactive case. Handing a
//! *pipe* to the shell means the shell reads ahead and discards whatever it
//! buffered when it exits, so anything after `.quit` is lost; at a terminal
//! there is nothing to read ahead and Ctrl-D returns to this prompt cleanly.
//! Testing that needs a pty, which is a heavier dependency than the property
//! is worth. Every `(sqlite …)` form *with* arguments is covered, and that is
//! the same code path up to who is holding the keyboard.

use std::io::Write;
use std::process::{Command, Stdio};

/// Where the shell binary is, if it has been built.
///
/// `CARGO_BIN_EXE_*` only names binaries of the package under test, and the
/// shell belongs to another one. Both land in the same directory, so the
/// sibling path is the answer -- and checking that it exists is what keeps a
/// single-package `cargo test -p covalence-bin-nucleus` from failing for a
/// reason that has nothing to do with this crate.
fn shell_binary() -> Option<std::path::PathBuf> {
    let path = std::path::Path::new(env!("CARGO_BIN_EXE_nucleus"))
        .parent()?
        .join("covalence-cas-shell");
    path.is_file().then_some(path)
}

/// Runs `script` through the REPL, returning everything it printed.
///
/// Both streams, combined: the REPL writes to stdout and the shell it runs
/// writes its errors to stderr, and a test that only read one of them would
/// call a failed statement a success.
fn repl(script: &str) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_nucleus"));
    if let Some(shell) = shell_binary() {
        command.env("COVALENCE_CAS_SHELL", shell);
    }
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the REPL");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write the script");
    let output = child.wait_with_output().expect("run the REPL");
    let mut combined = String::from_utf8_lossy(&output.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&output.stderr));
    combined
}

/// Returns the first content address printed.
///
/// Split on delimiters as well as whitespace: an address inside a list comes
/// back as `…)`, and a token that is 64 hex digits plus a paren is not 64 hex
/// digits.
fn address_in(output: &str) -> String {
    output
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .find(|token| token.len() == 64 && token.bytes().all(|b| b.is_ascii_hexdigit()))
        .unwrap_or_else(|| panic!("no address in output:\n{output}"))
        .to_owned()
}

/// Writes a small database and returns its path.
fn database(name: &str) -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!("covalence-repl-test-{name}.sqlite"));
    let _ = std::fs::remove_file(&path);
    let connection = covalence_lib_sqlite::Connection::open(
        &std::ffi::CString::new(path.to_str().expect("utf-8 path")).expect("no NUL"),
    )
    .expect("create");
    covalence_lib_sqlite::Statement::execute_batch(
        &connection,
        "CREATE TABLE planets (name TEXT, moons INTEGER) STRICT;
         INSERT INTO planets VALUES ('Earth', 1), ('Mars', 2), ('Jupiter', 95);",
    )
    .expect("populate");
    drop(connection);
    path
}

#[test]
fn an_empty_store_reports_nothing() {
    let output = repl("(stats)\n(objects)\n");
    assert!(output.contains("(objects 0)"), "{output}");
    assert!(output.contains("()"), "{output}");
}

#[test]
fn unbound_names_are_reported_without_stopping() {
    let output = repl("(nope)\n(stats)\n");
    assert!(output.contains("unbound: nope"), "{output}");
    assert!(output.contains("(objects 0)"), "{output}");
}

#[test]
fn a_missing_file_is_reported_without_stopping() {
    let output = repl("(put \"/nonexistent/nope\")\n(stats)\n");
    assert!(output.contains("error:"), "{output}");
    assert!(output.contains("(objects 0)"), "{output}");
}

#[test]
fn a_file_admits_and_then_lists() {
    let path = database("admit");
    let output = repl(&format!("(put {:?})\n(objects)\n(stats)\n", path.display()));
    // The address is printed once by `put` and again inside the list.
    let address = address_in(&output);
    assert!(output.contains(&format!("({address})")), "{output}");
    assert!(output.contains("(objects 1)"), "{output}");
}

#[test]
fn an_admitted_database_is_queryable_through_the_shell() {
    let Some(_) = shell_binary() else {
        eprintln!(
            "skipping an_admitted_database_is_queryable_through_the_shell: build the workspace to run it"
        );
        return;
    };
    let path = database("query");
    let output = repl(&format!("(put {:?})\n(objects)\n", path.display()));
    let address = address_in(&output);

    // A bare address becomes the URI that opens it, so this is all it takes.
    // The first argument is the database and the rest is SQL, exactly as
    // `sqlite3` takes them.
    let output = repl(&format!(
        "(put {:?})\n(sqlite {address} \"SELECT name FROM planets ORDER BY moons DESC LIMIT 1\")\n",
        path.display()
    ));
    assert!(output.contains("Jupiter"), "{output}");
}

#[test]
fn the_whole_store_is_reachable_by_attach() {
    let Some(_) = shell_binary() else {
        eprintln!("skipping the_whole_store_is_reachable_by_attach: build the workspace to run it");
        return;
    };
    let path = database("attach");
    let output = repl(&format!("(put {:?})\n", path.display()));
    let address = address_in(&output);

    // A scratch database, and then the store reached from inside it. No
    // `mode=ro`, no `immutable=1`: the mount answers every open read-only, so
    // the URI a person would guess is the URI that works. This is the whole
    // point of mounting a store rather than opening one file.
    let output = repl(&format!(
        "(put {:?})\n(sqlite \":memory:\" \"ATTACH 'file:{address}?vfs=cas' AS obj; SELECT 'moons=' || sum(moons) FROM obj.planets;\")\n",
        path.display()
    ));
    assert!(output.contains("moons=98"), "{output}");
}

#[test]
fn an_attached_object_cannot_be_written() {
    let Some(_) = shell_binary() else {
        eprintln!("skipping an_attached_object_cannot_be_written: build the workspace to run it");
        return;
    };
    let path = database("readonly");
    let output = repl(&format!("(put {:?})\n", path.display()));
    let address = address_in(&output);

    let output = repl(&format!(
        "(put {:?})\n(sqlite \":memory:\" \"ATTACH 'file:{address}?vfs=cas' AS obj; INSERT INTO obj.planets VALUES ('Pluto', 5);\")\n",
        path.display()
    ));
    assert!(output.contains("readonly"), "{output}");
}

#[test]
fn samples_give_an_empty_store_something_to_query() {
    let Some(_) = shell_binary() else {
        eprintln!("skipping samples_give_an_empty_store_something_to_query: build the workspace");
        return;
    };
    // No file, no fixture: the databases are built by SQLite in-process.
    let output = repl("(samples)\n");
    let address = address_in(&output);
    assert!(output.contains("(planets "), "{output}");
    assert!(output.contains("(moons "), "{output}");

    // And they are real databases the shell can read by address.
    let output = repl(&format!(
        "(samples)\n(sqlite {address} \"-batch\" \"SELECT name FROM planets ORDER BY moons DESC LIMIT 1\")\n"
    ));
    assert!(output.contains("Saturn"), "{output}");
}

#[test]
fn several_forms_on_one_line_all_run() {
    let output = repl("(open) (open) (connections)\n");
    assert!(output.contains("(1 \":memory:\" #f)"), "{output}");
    assert!(output.contains("(2 \":memory:\" #t)"), "{output}");
}
