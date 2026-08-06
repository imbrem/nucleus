//! Terminal front end for the content-addressed `SQLite` REPL.
//!
//! There is almost nothing here, and that is the point. Every command lives in
//! [`covalence_repl::Session`], which knows nothing about terminals; this
//! binary reads lines, hands them over, and does the one thing a session
//! cannot do for itself — read a file.

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

        // A command failing is ordinary. Report it and keep the prompt.
        match step(&mut session, &line, &mut stdout) {
            Ok(true) => return Ok(()),
            Ok(false) => {}
            Err(error) => writeln!(stdout, "error: {error}")?,
        }
    }
}

/// A handle on standard input that does no buffering of its own.
///
/// [`io::Stdin`] is a `BufReader`, and reading ahead into a buffer this
/// process owns is exactly wrong for a REPL that will later hand its input
/// stream to a child. `try_clone_to_owned` is `dup(2)`: a second descriptor
/// onto the *same* open file description, so reading advances the same stream
/// and dropping it closes only the duplicate. Nothing here is `unsafe`.
fn unbuffered_stdin() -> io::Result<File> {
    Ok(File::from(io::stdin().as_fd().try_clone_to_owned()?))
}

/// Reads one line, consuming not one byte more.
///
/// A byte at a time is a syscall per byte, which costs nothing at typing
/// speed. What it buys is that nothing is read that was not asked for, which
/// is what makes `nucleus < script` behave and what the shell handoff will
/// need.
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
            // `()` is what a form returns when it has nothing to say, and
            // printing it every time would be noise.
            if value != covalence_repl::Value::Nil {
                writeln!(out, "{}", value.display())?;
            }
        }
        Response::ReadFile(path) => {
            let bytes = std::fs::read(&path)?;
            writeln!(out, "{}", session.admit(bytes)?)?;
        }
    }
    Ok(false)
}
