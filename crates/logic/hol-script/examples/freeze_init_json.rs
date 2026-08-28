//! Regenerate the editable named JSON source for the canonical init slice.

use std::{fs, path::PathBuf};

use covalence_lib_json::serde_json;
use covalence_logic_hol::init;
use covalence_logic_hol_script::{compile_init_slice, dag_json};

const LOGICAL_INIT: &str = include_str!("../../../../theories/init-boolean.checked.json");

fn main() {
    let destination = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .expect("usage: freeze_init_json PATH");
    let manifest: init::Manifest =
        serde_json::from_str(LOGICAL_INIT).expect("logical init manifest must parse");
    let logical = init::compile(&manifest).expect("logical init manifest must check");
    let slice = compile_init_slice(&logical).expect("standard init slice must compile");
    let value = dag_json::render(slice.prefix().arena(), slice.symbols())
        .expect("standard init slice must have an unambiguous name index");
    let mut output = serde_json::to_string_pretty(&value).expect("arena JSON must render");
    output.push('\n');
    fs::write(&destination, output).expect("fixture destination must be writable");
}
