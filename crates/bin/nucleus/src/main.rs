//! Terminal front end for the content-addressed `SQLite` REPL.
//!
//! The command surface is small on purpose: put bytes in the store, look at
//! the store, manage connections, and hand off to the real `SQLite` shell.
//! There is no SQL here. `.shell` is not a fallback for a missing feature — it
//! is the feature.

use std::io::{self, BufRead, Write};
use std::str::FromStr;

use covalence_lib_hash::O256;
use covalence_repl::{ConnectionId, Repl};

const HELP: &str = "\
.put PATH          admit a file into the store, printing its address
.forget ADDRESS    drop an address from the store
.cas               summarise what the store holds
.objects           list every resident address
.open [URI]        open a connection (default: private in-memory)
.mount ADDRESS     open a resident object read-only through the mount
.connections       list open connections
.select N          select a connection
.close N           close a connection
.shell [ARG...]    run the real SQLite shell, in its own process, with
                   the store mounted; a bare ADDRESS expands to its URI
.help              show this
.quit              leave
";

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
    let mut repl = Repl::new()?;
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    writeln!(
        stdout,
        "nucleus: content-addressed SQLite. Store mounted as vfs={}. `.help` for commands.",
        repl.mount().name()
    )?;

    let mut line = String::new();
    loop {
        write!(stdout, "nucleus> ")?;
        stdout.flush()?;

        line.clear();
        if stdin.lock().read_line(&mut line)? == 0 {
            writeln!(stdout)?;
            return Ok(());
        }

        let trimmed = line.trim().to_owned();
        if trimmed.is_empty() {
            continue;
        }
        match dispatch(&mut repl, &trimmed, &mut stdout) {
            Ok(Control::Continue) => {}
            Ok(Control::Quit) => return Ok(()),
            // A command failing is ordinary. Report it and keep the prompt.
            Err(error) => writeln!(stdout, "error: {error}")?,
        }
    }
}

enum Control {
    Continue,
    Quit,
}

fn dispatch(
    repl: &mut Repl,
    line: &str,
    out: &mut impl Write,
) -> Result<Control, Box<dyn std::error::Error>> {
    let (command, rest) = line
        .split_once(char::is_whitespace)
        .map_or((line, ""), |(command, rest)| (command, rest.trim()));

    match command {
        ".quit" | ".exit" => return Ok(Control::Quit),
        ".help" => write!(out, "{HELP}")?,

        ".put" => {
            if rest.is_empty() {
                return Err("usage: .put PATH".into());
            }
            let bytes = std::fs::read(rest)?;
            let len = bytes.len();
            let address = repl.put(bytes)?;
            writeln!(out, "{} ({len} bytes)", address.hex())?;
        }
        ".forget" => {
            let address = parse_address(rest)?;
            if repl.forget(address) {
                writeln!(out, "dropped {}", address.hex())?;
            } else {
                writeln!(out, "{} was not resident", address.hex())?;
            }
        }
        ".cas" => {
            let stats = repl.stats();
            writeln!(
                out,
                "{} object(s), {} byte(s), largest {} byte(s)",
                stats.objects, stats.bytes, stats.largest
            )?;
        }
        ".objects" => {
            for address in repl.addresses() {
                writeln!(out, "{}", address.hex())?;
            }
        }

        ".open" => {
            let id = if rest.is_empty() {
                repl.open_memory()?
            } else {
                repl.open_uri(rest)?
            };
            writeln!(out, "connection {id}")?;
        }
        ".mount" => {
            let id = repl.open_address(parse_address(rest)?)?;
            writeln!(out, "connection {id}")?;
        }
        ".connections" => {
            for info in repl.connections() {
                let marker = if info.selected { '*' } else { ' ' };
                writeln!(out, "{marker} {} {}", info.id, info.origin)?;
            }
        }
        ".select" => repl.select(parse_connection(rest)?)?,
        ".close" => repl.close(parse_connection(rest)?)?,

        ".shell" => {
            let status = shell(repl, rest)?;
            if status != 0 {
                writeln!(out, "shell exited with status {status}")?;
            }
        }

        other => return Err(format!("unknown command {other}; try .help").into()),
    }
    Ok(Control::Continue)
}

/// Runs the real `SQLite` shell in its own process.
///
/// The shell reaches the store over a socket rather than by sharing this
/// process's memory, so nothing it does can touch the REPL. A bare address is
/// expanded to the URI which opens it, because typing the full
/// `file:...?vfs=cas` form every time is friction with no upside.
fn shell(repl: &Repl, rest: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let arguments: Vec<String> = split_arguments(rest)?
        .into_iter()
        .map(|argument| O256::from_str(&argument).map_or(argument, |address| repl.uri(address)))
        .collect();
    Ok(covalence_repl::shell::run(repl.cas(), &arguments)?)
}

/// Splits a `.shell` argument line the way a shell would.
///
/// Whitespace separates arguments, and single or double quotes group them. SQL
/// contains spaces, so splitting on whitespace alone would make the most
/// obvious use — `.shell ADDRESS 'SELECT * FROM t'` — impossible.
///
/// This is not a full shell parser and does not try to be: there is no
/// expansion, substitution, or escaping beyond a backslash inside double
/// quotes. Anything more belongs to the shell itself.
fn split_arguments(line: &str) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let mut arguments = Vec::new();
    let mut current = String::new();
    let mut started = false;
    let mut quote: Option<char> = None;
    let mut characters = line.chars();

    while let Some(character) = characters.next() {
        match (quote, character) {
            (Some(open), c) if c == open => quote = None,
            (Some('"'), '\\') => match characters.next() {
                Some(escaped) => current.push(escaped),
                None => return Err("unterminated escape".into()),
            },
            (Some(_), c) => current.push(c),
            (None, '\'' | '"') => {
                quote = Some(character);
                // An empty quoted string is still an argument.
                started = true;
            }
            (None, c) if c.is_whitespace() => {
                if started {
                    arguments.push(std::mem::take(&mut current));
                    started = false;
                }
            }
            (None, c) => {
                current.push(c);
                started = true;
            }
        }
    }

    if quote.is_some() {
        return Err("unterminated quote".into());
    }
    if started {
        arguments.push(current);
    }
    Ok(arguments)
}

fn parse_address(text: &str) -> Result<O256, Box<dyn std::error::Error>> {
    O256::from_str(text.trim())
        .map_err(|error| format!("{text:?} is not an address: {error}").into())
}

fn parse_connection(text: &str) -> Result<ConnectionId, Box<dyn std::error::Error>> {
    text.trim()
        .parse::<u64>()
        .map(ConnectionId::from_raw)
        .map_err(|_| format!("{text:?} is not a connection handle").into())
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;

    static NEXT: AtomicU64 = AtomicU64::new(0);

    /// Drives the dispatcher directly, which is where all the behaviour is.
    ///
    /// Each session needs a distinct mount name: registration is
    /// process-global and permanent.
    fn session(commands: &[&str]) -> String {
        let name = format!(
            "covalence-test-cli-{}",
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        let mut repl = Repl::with_mount_name(&name, false).unwrap();
        let mut out = Vec::new();
        for command in commands {
            match dispatch(&mut repl, command, &mut out) {
                Ok(Control::Continue) => {}
                Ok(Control::Quit) => break,
                Err(error) => writeln!(out, "error: {error}").unwrap(),
            }
        }
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn an_empty_store_reports_nothing() {
        assert_eq!(
            session(&[".cas"]),
            "0 object(s), 0 byte(s), largest 0 byte(s)\n"
        );
    }

    #[test]
    fn unknown_commands_are_reported_without_stopping() {
        let output = session(&[".nope", ".cas"]);
        assert!(output.contains("unknown command .nope"), "{output}");
        assert!(
            output.contains("1 object(s)") || output.contains("0 object(s)"),
            "{output}"
        );
    }

    #[test]
    fn a_missing_file_is_reported_without_stopping() {
        let output = session(&[".put /nonexistent/nope", ".cas"]);
        assert!(output.contains("error:"), "{output}");
        assert!(output.contains("0 object(s)"), "{output}");
    }

    #[test]
    fn a_bad_address_is_rejected() {
        let output = session(&[".forget not-an-address"]);
        assert!(output.contains("is not an address"), "{output}");
    }

    #[test]
    fn shell_arguments_split_on_whitespace_and_respect_quotes() {
        assert_eq!(split_arguments("").unwrap(), Vec::<String>::new());
        assert_eq!(split_arguments("  a   b ").unwrap(), ["a", "b"]);
        assert_eq!(
            split_arguments("db -batch 'SELECT * FROM t'").unwrap(),
            ["db", "-batch", "SELECT * FROM t"]
        );
        assert_eq!(
            split_arguments(r#"db "a b" 'c d'"#).unwrap(),
            ["db", "a b", "c d"]
        );
        // An empty quoted string is an argument, not nothing.
        assert_eq!(split_arguments("a '' b").unwrap(), ["a", "", "b"]);
        // Quotes may open mid-argument, as in a shell.
        assert_eq!(split_arguments("pre'fix ed'").unwrap(), ["prefix ed"]);
        assert_eq!(split_arguments(r#""say \"hi\"""#).unwrap(), [r#"say "hi""#]);
        assert!(split_arguments("'unterminated").is_err());
    }

    #[test]
    fn connections_open_select_and_close() {
        let output = session(&[
            ".open",
            ".open",
            ".connections",
            ".select 1",
            ".connections",
            ".close 1",
            ".connections",
        ]);
        assert!(output.contains("connection 1"), "{output}");
        assert!(output.contains("connection 2"), "{output}");
        // After `.select 1` the marker moves; after `.close 1` it is gone.
        assert!(output.contains("* 1 :memory:"), "{output}");
        assert!(
            !output.lines().last().unwrap_or_default().contains(" 1 "),
            "{output}"
        );
    }
}
