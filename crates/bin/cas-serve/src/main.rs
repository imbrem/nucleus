//! Serves files from a content-addressed store over HTTP.
//!
//! ```text
//! covalence-cas-serve [--port PORT] FILE...
//! ```
//!
//! Each file is admitted and its address printed, one per line, so a caller
//! can pipe the output somewhere useful. The last line is the base URL.
//!
//! This is a **read capability on a port**. It binds loopback and nothing
//! else, because anything that can reach it can read everything it holds.

use std::process::ExitCode;
use std::sync::Arc;

use covalence_data_cas::MemoryCas;
use covalence_data_cas_http::serve;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("cas-serve: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut port = 0u16;
    let mut paths = Vec::new();

    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        if argument == "--port" {
            port = arguments
                .next()
                .ok_or("--port requires a number")?
                .parse()?;
        } else {
            paths.push(argument);
        }
    }

    let cas = Arc::new(MemoryCas::new());
    for path in &paths {
        let bytes = std::fs::read(path)?;
        let address = cas.insert(bytes)?;
        println!("{} {path}", address.hex());
    }

    let serving = serve(Arc::clone(&cas), format!("127.0.0.1:{port}").parse()?)?;
    println!("{}", serving.base_url());

    // Serving happens on its own threads; park until killed.
    loop {
        std::thread::park();
    }
}
