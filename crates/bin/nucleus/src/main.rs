//! Terminal front end for the content-addressed REPL.

use covalence_repl::{Response, Session, SolveRequest, SolveResult};
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
    let mut sat = NoSatProvider;
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
        match step(&mut session, &line, &mut stdout, &mut sat) {
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
    sat: &mut impl SatProvider,
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
        Response::Solve(request) => {
            let job = request.job();
            let result = match sat.solve(&request) {
                Ok(result) => result,
                Err(error) => {
                    session.reject_sat_provider(&error.to_string())?;
                    return Err(error);
                }
            };
            writeln!(out, "{}", session.complete_sat(job, result)?.display())?;
        }
    }
    Ok(false)
}

/// An untrusted SAT provider selected by the terminal host.
trait SatProvider {
    fn solve(&mut self, request: &SolveRequest) -> Result<SolveResult, Box<dyn std::error::Error>>;
}

/// Native SAT process and HTTP adapters are intentionally supplied by a host.
struct NoSatProvider;

impl SatProvider for NoSatProvider {
    fn solve(
        &mut self,
        _request: &SolveRequest,
    ) -> Result<SolveResult, Box<dyn std::error::Error>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "no native SAT provider is configured; use a browser or HTTP SAT host",
        )
        .into())
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    struct OneModel;

    impl SatProvider for OneModel {
        fn solve(
            &mut self,
            request: &SolveRequest,
        ) -> Result<SolveResult, Box<dyn std::error::Error>> {
            let text = std::str::from_utf8(request.dimacs())?;
            let mut clauses = Vec::new();
            let mut clause = Vec::new();
            let mut variables = 0_u32;
            for line in text.lines() {
                if line.starts_with('c') || line.starts_with('p') {
                    continue;
                }
                for word in line.split_whitespace() {
                    let literal = word.parse::<i64>()?;
                    if literal == 0 {
                        clauses.push(std::mem::take(&mut clause));
                    } else {
                        variables = variables.max(literal.unsigned_abs().try_into()?);
                        clause.push(literal);
                    }
                }
            }
            let assignment = (0_u64..(1_u64 << variables))
                .find(|bits| {
                    clauses.iter().all(|clause| {
                        clause.iter().any(|literal| {
                            let bit = 1_u64 << (literal.unsigned_abs() - 1);
                            (*bits & bit != 0) == (*literal > 0)
                        })
                    })
                })
                .ok_or("test formula must be satisfiable")?;
            let model = (1..=variables)
                .map(|variable| {
                    let literal = i64::from(variable);
                    if assignment & (1_u64 << (variable - 1)) == 0 {
                        -literal
                    } else {
                        literal
                    }
                })
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Ok(SolveResult::Sat {
                problem: request.problem(),
                model,
            })
        }
    }

    fn eval_text(session: &mut Session, form: &str) -> String {
        let Response::Value(value) = session.eval(form).expect("evaluate") else {
            panic!("expected a value response");
        };
        value.to_string()
    }

    #[test]
    fn solve_is_handed_to_the_host_then_checked() {
        let mut session = Session::new().expect("session");
        session
            .eval("(sat-select and-sat)")
            .expect("select problem");
        let error = step(
            &mut session,
            "(sat-solve)",
            &mut Vec::new(),
            &mut NoSatProvider,
        )
        .expect_err("provider required");
        assert!(error.to_string().contains("no native SAT provider"));
        assert!(eval_text(&mut session, "(sat-status)").contains("rejected"));

        session
            .eval("(sat-set \"p cnf 1 1\\n1 0\\n\")")
            .expect("select problem");
        let mut output = Vec::new();

        assert!(!step(&mut session, "(sat-solve)", &mut output, &mut OneModel).expect("solve"));

        let output = String::from_utf8(output).expect("utf8");
        assert!(output.contains("checked-model"), "{output}");
        assert!(eval_text(&mut session, "(sat-verify)").contains("checked-model"));
    }
}
