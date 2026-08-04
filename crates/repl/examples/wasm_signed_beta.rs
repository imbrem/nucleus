use std::{env, error::Error, fmt::Write as _, fs, path::PathBuf, sync::Arc};

use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, HolDatabaseRef, ImportedExport, Kernel, NamespaceId,
    SignedSnapshotAttestation, SignedSnapshotEnvelope, schema_valid_snapshot_statement,
};
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
    let snapshot =
        run_hol_proof_component(&kernel, &component, WasmtimeComponentLimits::default())?;
    let attestation = snapshot.attestation();
    let statement = schema_valid_snapshot_statement(attestation.schema(), attestation.image());

    // Exercise the receiving side before writing the transport-neutral files.
    let claim = SignedSnapshotAttestation::new(
        attestation.schema(),
        attestation.image(),
        attestation.signer(),
        *attestation.public_key(),
        attestation.signature(),
    )
    .authenticate()?;
    let receiving_kernel = Kernel::ephemeral();
    let mut receiving = receiving_kernel.open_hol(AllowAll)?;
    assert!(matches!(
        receiving.accept_authenticated_snapshot(&claim),
        Err(covalence_nucleus::SnapshotTrustError::UntrustedSigner(signer))
            if signer == attestation.signer()
    ));
    receiving.trust_snapshot_signer(&claim)?;
    receiving.accept_authenticated_snapshot(&claim)?;
    let import = receiving.register_import(HolDatabaseRef::new(
        attestation.schema(),
        attestation.image(),
    ))?;
    let trusted = receiving.accept_trusted_import(import, &claim)?;
    let imported_namespace = receiving.create_imported_namespace(
        Some(NamespaceId::root()),
        Some("wasm-beta"),
        import,
        1,
    )?;
    let authenticated = SignedSnapshotEnvelope::new(
        snapshot.image().bytes(),
        attestation.schema(),
        attestation.image(),
        attestation.signer(),
        *attestation.public_key(),
        attestation.signature(),
    )
    .authenticate()?;
    let validated = AuthenticatedValidatedHolImage::validate_with_descriptor(
        authenticated,
        snapshot.descriptor(),
    )?;
    let mounted =
        covalence_neutron::ImmutableImage::register(Arc::from(validated.image().bytes()))?;
    let matched = receiving.match_trusted_import_image(trusted, validated)?;
    matched.with_mounted_reader(imported_namespace, &mounted, |mut reader| {
        let ImportedExport::Term(equality) = reader
            .namespace_export(0)?
            .ok_or("theorem export 0 is absent")?
        else {
            return Err("export 0 is not a term".into());
        };
        let ImportedExport::Context(context) = reader
            .namespace_export(1)?
            .ok_or("context export 1 is absent")?
        else {
            return Err("export 1 is not a context".into());
        };
        reader
            .theorem(context, equality)?
            .ok_or("exported signed judgement is absent")?;
        Ok::<_, Box<dyn Error>>(())
    })??;

    fs::create_dir_all(&output)?;
    fs::write(output.join("proof.sqlite"), snapshot.image().bytes())?;
    fs::write(output.join("schema.covhol"), snapshot.descriptor().encode())?;
    let mut manifest = String::new();
    writeln!(manifest, "schema {}", attestation.schema())?;
    writeln!(manifest, "image {}", attestation.image())?;
    writeln!(manifest, "signer {}", attestation.signer())?;
    writeln!(manifest, "public-key {}", hex(attestation.public_key()))?;
    writeln!(manifest, "signature {}", hex(attestation.signature()))?;
    writeln!(manifest, "statement {statement}")?;
    writeln!(manifest, "namespace 1")?;
    writeln!(manifest, "theorem-export 0")?;
    writeln!(manifest, "context-export 1")?;
    fs::write(output.join("attestation.txt"), manifest)?;
    println!(
        "wrote guest-produced signed beta theorem to {}",
        output.display()
    );
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}
