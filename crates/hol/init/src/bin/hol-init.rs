//! Generates the propositional init image and reports its content hash.

use std::env;
use std::error::Error;
use std::fs::OpenOptions;
use std::io::{self, Write as _};
use std::process::ExitCode;

use covalence_lib_hash::O256;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn usage(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(output, "usage: hol-init PATH")?;
    writeln!(output, "       hol-init --help")?;
    writeln!(
        output,
        "writes the propositional init image to a new file at PATH"
    )
}

fn generate(path: &str) -> Result<()> {
    let bytes = covalence_hol_init::init_image()?;
    let hash = O256::from_bytes(&bytes);
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(&bytes)?;
    file.sync_all()?;
    println!("wrote {} bytes to {path}", bytes.len());
    println!("{hash}");
    Ok(())
}

fn run() -> Result<()> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        Some("-h" | "--help") => {
            usage(&mut io::stdout().lock())?;
            Ok(())
        }
        Some(path) if arguments.next().is_none() => generate(path),
        _ => {
            usage(&mut io::stderr().lock())?;
            Err("expected exactly one output path".into())
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}
