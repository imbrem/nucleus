//! The terminal REPL, driven the way a script would drive it.
//!
//! These run the real binary the way a script would.

use std::io::Write;
use std::process::{Command, Stdio};

/// Runs `script` through the REPL, returning everything it printed.
fn repl(script: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_nucleus"))
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
fn several_forms_on_one_line_all_run() {
    let output = repl("(open) (open) (connections)\n");
    assert!(output.contains("(1 \":memory:\" #f)"), "{output}");
    assert!(output.contains("(2 \":memory:\" #t)"), "{output}");
}
