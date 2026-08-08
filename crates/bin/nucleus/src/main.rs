//! Terminal front end for the content-addressed `SQLite` REPL.
//!
//! There is almost nothing here, and that is the point. Every command lives in
//! [`covalence_repl::Session`], which knows nothing about terminals; this
//! binary reads lines, hands them over, and does the two things a session
//! cannot do for itself — read a file, and run the shell.
//!
//! There is no SQL at this prompt. `(sqlite)` is not a fallback for a missing
//! feature: it hands you the real thing.

#[cfg(not(target_os = "wasi"))]
use std::fs::File;
use std::io::{self, Read, Write};
#[cfg(not(target_os = "wasi"))]
use std::os::fd::AsFd;

#[cfg(unix)]
use covalence_repl::shell;
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
    let mut input = stdin()?;
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
        if read_line(&mut input, &mut line)? == 0 {
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

/// Standard input, unbuffered where that is possible.
///
/// [`io::Stdin`] is a `BufReader`, and that buffer is the problem: it belongs
/// to this process, a child cannot inherit it, and it is filled eagerly. So
/// `(sqlite)` with anything queued behind it would hand the shell an
/// already-drained stdin, and the queued lines would come back here as
/// nonsense. It happens to work at a terminal — a tty read returns one typed
/// line and no more — which is exactly the kind of bug that survives.
///
/// `try_clone_to_owned` is `dup(2)`: a second descriptor onto the *same* open
/// file description, so reading advances the same stream and dropping it
/// closes only the duplicate. Nothing here is `unsafe`.
///
/// WASI has neither `dup` nor a way to spawn anything, so there is nobody to
/// hand the stream to and buffering costs nothing. It gets ordinary stdin.
#[cfg_attr(target_os = "wasi", allow(clippy::unnecessary_wraps))]
fn stdin() -> io::Result<Box<dyn Read>> {
    #[cfg(target_os = "wasi")]
    {
        Ok(Box::new(io::stdin()))
    }
    #[cfg(not(target_os = "wasi"))]
    {
        Ok(Box::new(File::from(
            io::stdin().as_fd().try_clone_to_owned()?,
        )))
    }
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
        Response::Shell(arguments) => {
            #[cfg(not(unix))]
            let _ = arguments;
            #[cfg(not(unix))]
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "the SQLite subprocess shell is unavailable on this platform",
            )
            .into());

            // The shell inherits this terminal, so a bare `(sqlite)` is a real
            // sqlite3 owning the screen until the user leaves it -- which is
            // what running a shell means.
            #[cfg(unix)]
            let status = shell::run(session.store(), &arguments)?;
            #[cfg(unix)]
            if status != 0 {
                writeln!(out, "shell exited with status {status}")?;
            }
        }
    }
    Ok(false)
}
