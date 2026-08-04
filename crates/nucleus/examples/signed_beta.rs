use std::{env, error::Error, fmt::Write as _, fs, path::PathBuf};

use covalence_nucleus::{AllowAll, Kernel, schema_valid_snapshot_statement};

#[path = "support/closed_beta.rs"]
mod closed_beta;

fn main() -> Result<(), Box<dyn Error>> {
    let output = env::args_os()
        .nth(1)
        .map_or_else(|| PathBuf::from("signed-beta-artifact"), PathBuf::from);
    fs::create_dir_all(&output)?;

    let kernel = Kernel::ephemeral();
    let mut database = kernel.open_hol(AllowAll)?;
    let proof = closed_beta::build(&mut database)?;

    let snapshot = kernel.export_hol(&mut database)?;
    let attestation = snapshot.attestation();
    let statement = schema_valid_snapshot_statement(attestation.schema(), attestation.image());
    fs::write(output.join("proof.sqlite"), snapshot.image().bytes())?;
    fs::write(output.join("schema.covhol"), snapshot.descriptor().encode())?;

    let mut manifest = String::new();
    writeln!(manifest, "schema {}", attestation.schema())?;
    writeln!(manifest, "image {}", attestation.image())?;
    writeln!(manifest, "signer {}", attestation.signer())?;
    writeln!(manifest, "public-key {}", hex(attestation.public_key()))?;
    writeln!(manifest, "signature {}", hex(attestation.signature()))?;
    writeln!(manifest, "statement {statement}")?;
    writeln!(manifest, "namespace {}", proof.namespace.get())?;
    writeln!(manifest, "theorem-export 0")?;
    writeln!(manifest, "context-export 1")?;
    writeln!(manifest, "theorem-context {}", proof.context.get())?;
    writeln!(manifest, "theorem-term {}", proof.conclusion.get())?;
    fs::write(output.join("attestation.txt"), manifest)?;

    println!("wrote signed beta theorem to {}", output.display());
    println!("image {}", attestation.image());
    println!("signer {}", attestation.signer());
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}
