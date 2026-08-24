//! Terminal front end for the content-addressed REPL.

use covalence_lib_error::miette::{self, Context, IntoDiagnostic, miette};
use covalence_repl::{Response, Session};
use std::io::{self, BufRead, Write};

fn main() -> miette::Result<()> {
    let mut session = Session::new()
        .into_diagnostic()
        .context("could not open the REPL session")?;
    let stdin = io::stdin();
    let mut input = stdin.lock();
    let mut stdout = io::stdout();

    writeln!(
        stdout,
        "nucleus: content-addressed SQLite. Store mounted as vfs={}. (help) for commands.",
        session.repl().mount().name()
    )
    .into_diagnostic()?;

    let mut line = String::new();
    loop {
        write!(stdout, "nucleus> ").into_diagnostic()?;
        stdout.flush().into_diagnostic()?;

        line.clear();
        if input.read_line(&mut line).into_diagnostic()? == 0 {
            writeln!(stdout).into_diagnostic()?;
            return Ok(());
        }
        if line.trim().is_empty() {
            continue;
        }

        // A command failing is ordinary. Report it on one line and keep the
        // prompt: only a failure that ends the session is worth a full report.
        match step(&mut session, &line, &mut stdout) {
            Ok(true) => return Ok(()),
            Ok(false) => {}
            Err(error) => writeln!(stdout, "error: {error}").into_diagnostic()?,
        }
    }
}

/// Runs one line, returning whether the REPL should stop.
fn step(session: &mut Session, line: &str, out: &mut impl Write) -> miette::Result<bool> {
    match session.eval(line).into_diagnostic()? {
        Response::Quit => return Ok(true),
        Response::Value(value) => {
            // A form done for its effect has no result to show. `()` is not
            // that: an empty `(objects)` prints `()`, because that is what it
            // returned.
            if value != covalence_repl::Value::Unspecified {
                writeln!(out, "{}", value.display()).into_diagnostic()?;
            }
        }
        Response::ReadFile(path) => {
            let bytes = std::fs::read(&path)
                .into_diagnostic()
                .with_context(|| format!("could not read `{path}`"))?;
            let address = session.admit(bytes).into_diagnostic()?;
            writeln!(out, "{address}").into_diagnostic()?;
        }
        Response::Fetch { url, address } => {
            let bytes = fetch(&url)?;
            let admitted = session
                .admit_verified(address, bytes)
                .into_diagnostic()
                .context("the fetched bytes do not match the requested address")?;
            writeln!(out, "{admitted}").into_diagnostic()?;
        }
        Response::RunProof { url, address } => {
            run_proof(session, url.as_deref(), address, out)?;
        }
        Response::Shell(arguments) => {
            let _ = arguments;
            return Err(miette!(
                "the SQLite component is currently available in the browser REPL"
            ));
        }
    }
    Ok(false)
}

#[cfg(not(target_os = "wasi"))]
fn run_proof(
    session: &Session,
    url: Option<&str>,
    address: covalence_lib_hash::O256,
    out: &mut impl Write,
) -> miette::Result<()> {
    if session.store().fact_at(address).is_none()
        && let Some(url) = url
    {
        let bytes = fetch(url)?;
        session
            .admit_verified(address, bytes)
            .into_diagnostic()
            .context("the fetched proof does not match the requested address")?;
    }
    let component = session
        .store()
        .fact_at(address)
        .ok_or_else(|| miette!("proof component {address} is not resident"))?;
    let kernel = covalence_nucleus::load_standard_proof(component.bytes())
        .map_err(|error| miette!("proof failed: {error}"))?;
    writeln!(out, "{}", kernel.addr()).into_diagnostic()
}

#[cfg(target_os = "wasi")]
fn run_proof(
    _session: &Session,
    _url: Option<&str>,
    _address: covalence_lib_hash::O256,
    _out: &mut impl Write,
) -> miette::Result<()> {
    Err(miette!(
        "nested proof components are not available in the WASI CLI"
    ))
}

/// Fetches a URL with `curl`.
///
/// Shelling out rather than linking an HTTP client keeps a TLS stack and an
/// async runtime out of the binary that owns the store. The bytes are
/// untrusted either way — they are checked against their address before being
/// admitted — so what fetches them is a dependency question, not a trust one.
fn fetch(url: &str) -> miette::Result<Vec<u8>> {
    let output = std::process::Command::new("curl")
        .args(["--silent", "--show-error", "--fail", "--location", url])
        .output()
        .into_diagnostic()
        .context("could not run curl")?;
    if !output.status.success() {
        let message = String::from_utf8_lossy(&output.stderr);
        return Err(miette!("could not fetch `{url}`: {}", message.trim()));
    }
    Ok(output.stdout)
}
