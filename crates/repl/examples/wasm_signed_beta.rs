//! Runs the untrusted closed-beta component and writes its signed HOL snapshot.

use std::{env, error::Error, fmt::Write as _, fs, path::PathBuf};

use covalence_nucleus::{Kernel, schema_valid_snapshot_statement};
use covalence_proton::WasmtimeComponentLimits;
use covalence_repl::run_hol_proof_component;

fn main() -> Result<(), Box<dyn Error>> {
    let component = env::args_os()
        .nth(1)
        .ok_or("usage: wasm_signed_beta COMPONENT OUTPUT-DIRECTORY")?;
    let output = env::args_os()
        .nth(2)
        .ok_or("usage: wasm_signed_beta COMPONENT OUTPUT-DIRECTORY")?;
    let output = PathBuf::from(output);
    let component = fs::read(component)?;
    let kernel = Kernel::ephemeral();
    let artifact =
        run_hol_proof_component(&kernel, &component, WasmtimeComponentLimits::default())?;
    let statement = schema_valid_snapshot_statement(artifact.schema(), artifact.image_hash());

    fs::create_dir_all(&output)?;
    fs::write(output.join("proof.sqlite"), artifact.image())?;
    let mut manifest = String::new();
    writeln!(manifest, "schema {}", artifact.schema())?;
    writeln!(manifest, "image {}", artifact.image_hash())?;
    writeln!(manifest, "signer {}", artifact.signer())?;
    writeln!(manifest, "public-key {}", hex(artifact.public_key()))?;
    writeln!(manifest, "signature {}", hex(artifact.signature()))?;
    writeln!(manifest, "statement {statement}")?;
    writeln!(manifest, "namespace {}", artifact.namespace_id())?;
    writeln!(manifest, "context-export 0")?;
    writeln!(manifest, "theorem-export 1")?;
    fs::write(output.join("attestation.txt"), manifest)?;
    println!("wrote signed beta snapshot to {}", output.display());
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}
