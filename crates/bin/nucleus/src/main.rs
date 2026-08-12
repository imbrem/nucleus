//! Terminal front end for the content-addressed REPL.

use covalence_repl::{Response, Session};
use std::io::{self, BufRead, Write};

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("nucleus: {error}");
            std::process::ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut session = Session::new()?;
    let stdin = io::stdin();
    let mut input = stdin.lock();
    let mut stdout = io::stdout();

    writeln!(
        stdout,
        "nucleus: content-addressed SQLite. Store mounted as vfs={}. (help) for commands.",
        session.repl().mount().name()
    )?;

    let mut line = String::new();
    loop {
        write!(stdout, "nucleus> ")?;
        stdout.flush()?;

        line.clear();
        if input.read_line(&mut line)? == 0 {
            writeln!(stdout)?;
            return Ok(());
        }
        if line.trim().is_empty() {
            continue;
        }

        // A command failing is ordinary. Report it and keep the prompt.
        match step(&mut session, &line, &mut stdout) {
            Ok(true) => return Ok(()),
            Ok(false) => {}
            Err(error) => writeln!(stdout, "error: {error}")?,
        }
    }
}

/// Runs one line, returning whether the REPL should stop.
fn step(
    session: &mut Session,
    line: &str,
    out: &mut impl Write,
) -> Result<bool, Box<dyn std::error::Error>> {
    match session.eval(line)? {
        Response::Quit => return Ok(true),
        Response::Value(value) => {
            // A form done for its effect has no result to show. `()` is not
            // that: an empty `(objects)` prints `()`, because that is what it
            // returned.
            if value != covalence_repl::Value::Unspecified {
                writeln!(out, "{}", value.display())?;
            }
        }
        Response::ReadFile(path) => {
            let bytes = std::fs::read(&path)?;
            writeln!(out, "{}", session.admit(bytes)?)?;
        }
        Response::Fetch { url, address } => {
            let bytes = fetch(&url)?;
            writeln!(out, "{}", session.admit_verified(address, bytes)?)?;
        }
        Response::Shell(arguments) => {
            let _ = arguments;
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "the SQLite component is currently available in the browser REPL",
            )
            .into());
        }
    }
    Ok(false)
}

/// Fetches a URL with `curl`.
///
/// Shelling out rather than linking an HTTP client keeps a TLS stack and an
/// async runtime out of the binary that owns the store. The bytes are
/// untrusted either way — they are checked against their address before being
/// admitted — so what fetches them is a dependency question, not a trust one.
fn fetch(url: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let output = std::process::Command::new("curl")
        .args(["--silent", "--show-error", "--fail", "--location", url])
        .output()
        .map_err(|error| format!("could not run curl: {error}"))?;
    if !output.status.success() {
        let message = String::from_utf8_lossy(&output.stderr);
        return Err(format!("fetch failed: {}", message.trim()).into());
    }
    Ok(output.stdout)
}
