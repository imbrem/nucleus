//! Runs one component implementing the standard portable proof world.

use std::{env, fs, process::ExitCode};

fn main() -> ExitCode {
    let Some(path) = env::args_os().nth(1) else {
        eprintln!("usage: load-proof COMPONENT.wasm");
        return ExitCode::FAILURE;
    };
    let component = match fs::read(path) {
        Ok(component) => component,
        Err(error) => {
            eprintln!("could not read proof component: {error}");
            return ExitCode::FAILURE;
        }
    };
    match covalence_nucleus::load_standard_proof(&component) {
        Ok(kernel) => {
            println!("{}", kernel.addr());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("proof failed: {error}");
            ExitCode::FAILURE
        }
    }
}
