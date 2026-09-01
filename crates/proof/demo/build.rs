mod compiler;

use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=program.tactic");
    println!("cargo:rerun-if-changed=compiler.rs");
    let source = fs::read_to_string("program.tactic").expect("read tactic source");
    let instruction = compiler::parse(&source).expect("compile tactic source");
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR")).join("tactic_program.rs");
    fs::write(output, compiler::generate(instruction)).expect("write generated tactic program");
}
