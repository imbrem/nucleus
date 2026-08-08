//! Terminal front end for the content-addressed `SQLite` REPL.
//!
//! There is almost nothing here, and that is the point. Every command lives in
//! [`covalence_repl::Session`], which knows nothing about terminals; this
//! binary reads lines, hands them over, and does the three things a session
//! cannot do for itself — read a file, fetch a URL, and run the shell.
//!
//! There is no SQL at this prompt. `(sqlite)` is not a fallback for a missing
//! feature: it hands you the real thing.
//!
//! # The same binary, compiled for WASI
//!
//! Built for `wasm32-wasip1` this *is* the REPL — same session, same forms,
//! same output — but a guest cannot open a socket or spawn a process, so
//! fetching and running the shell become imports the embedder supplies. The
//! two `#[cfg]` pairs below are the whole difference.

/// The capabilities a WASI guest cannot supply for itself.
#[cfg(target_os = "wasi")]
mod host;

use std::fs::File;
use std::io::{self, Read, Write};
use std::os::fd::AsFd;

use covalence_repl::{Response, Session};

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
    let mut stdin = unbuffered_stdin()?;
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
        if read_line(&mut stdin, &mut line)? == 0 {
            writeln!(stdout)?;
            return Ok(());
        }
        if line.trim().is_empty() {
            continue;
        }

        // A form failing is ordinary. Report it and keep the prompt.
        match step(&mut session, &line, &mut stdout) {
            Ok(true) => return Ok(()),
            Ok(false) => {}
            Err(error) => writeln!(stdout, "error: {error}")?,
        }
    }
}

/// A handle on standard input that does no buffering of its own.
///
/// [`io::Stdin`] is a `BufReader`, and that buffer is the problem: it belongs
/// to this process, a child cannot inherit it, and it is filled eagerly. So
/// `(sqlite)` with anything queued behind it would hand the shell an
/// already-drained stdin, and the queued lines would come back here as
/// nonsense. It happens to work at a terminal — a tty read returns one typed
/// line and no more — which is exactly the kind of bug that survives.
///
/// `try_clone_to_owned` is `dup(2)`: a second descriptor onto the *same* open
/// file description, so reading from it advances the same stream, and dropping
/// it closes only the duplicate. Nothing here is `unsafe`.
fn unbuffered_stdin() -> io::Result<File> {
    Ok(File::from(io::stdin().as_fd().try_clone_to_owned()?))
}

/// Reads one line, consuming not one byte more.
///
/// A byte at a time is a syscall per byte, which costs nothing at typing speed
/// and is what makes the handoff to the shell exact: it resumes reading
/// precisely where this stopped. That is also what makes `nucleus < script`
/// work, which is how the demo and the tests drive it.
fn read_line(input: &mut impl Read, line: &mut String) -> io::Result<usize> {
    let mut read = 0;
    let mut byte = [0u8; 1];
    while input.read(&mut byte)? == 1 {
        read += 1;
        line.push(char::from(byte[0]));
        if byte[0] == b'\n' {
            break;
        }
    }
    Ok(read)
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
        Response::Shell(arguments) => run_shell(session, &arguments, out)?,
    }
    Ok(false)
}

/// Runs the shell, in whatever way this host can.
///
/// Natively that is a subprocess over a Unix socket, sharing this terminal —
/// which is what makes a bare `(sqlite)` an interactive `sqlite3` that owns
/// the screen until you leave it. Under WASI it is an import, because a guest
/// cannot spawn anything: the embedder runs the shell module and hands back
/// what it printed.
#[cfg(unix)]
fn run_shell(
    session: &Session,
    arguments: &[String],
    out: &mut impl Write,
) -> Result<(), Box<dyn std::error::Error>> {
    let status = covalence_repl::shell::run(session.store(), arguments)?;
    if status != 0 {
        writeln!(out, "shell exited with status {status}")?;
    }
    Ok(())
}

#[cfg(target_os = "wasi")]
fn run_shell(
    _session: &Session,
    arguments: &[String],
    out: &mut impl Write,
) -> Result<(), Box<dyn std::error::Error>> {
    let (output, status) = host::shell(arguments)?;
    let output = output.trim_end();
    if !output.is_empty() {
        writeln!(out, "{output}")?;
    }
    if status != 0 {
        writeln!(out, "shell exited with status {status}")?;
    }
    Ok(())
}

/// Fetches a URL through the host.
#[cfg(target_os = "wasi")]
fn fetch(url: &str) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    Ok(host::fetch(url)?)
}

/// Fetches a URL with `curl`.
///
/// Shelling out rather than linking an HTTP client keeps a TLS stack and an
/// async runtime out of the binary that owns the store. The bytes are
/// untrusted either way — they are checked against their address before being
/// admitted — so what fetches them is a dependency question, not a trust one.
#[cfg(unix)]
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
