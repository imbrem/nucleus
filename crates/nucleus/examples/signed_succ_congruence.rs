use std::{env, error::Error, fmt::Write as _, fs, io, path::PathBuf, sync::Arc};

use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, HolDatabaseRef, ImportedExport, ImportedTermView,
    Kernel, NamespaceId, SignedSnapshotAttestation, SignedSnapshotEnvelope, SnapshotTrustError,
    schema_valid_snapshot_statement,
};

#[path = "support/succ_congruence.rs"]
mod succ_congruence;

type AnyError = Box<dyn Error>;

fn main() -> Result<(), AnyError> {
    let output = env::args_os().nth(1).map_or_else(
        || PathBuf::from("signed-succ-congruence-artifact"),
        PathBuf::from,
    );
    let source_kernel = Kernel::ephemeral();
    let mut source = source_kernel.open_hol(AllowAll)?;
    let proof = succ_congruence::build(&mut source)?;
    let snapshot = source_kernel.export_hol(&mut source)?;
    write_artifact(&output, &snapshot, &proof)?;

    let attestation = snapshot.attestation();
    let claim = SignedSnapshotAttestation::new(
        attestation.schema(),
        attestation.image(),
        attestation.signer(),
        *attestation.public_key(),
        attestation.signature(),
    )
    .authenticate()?;
    let target_kernel = Kernel::ephemeral();
    let mut target = target_kernel.open_hol(AllowAll)?;
    assert!(matches!(
        target.accept_authenticated_snapshot(&claim),
        Err(SnapshotTrustError::UntrustedSigner(signer)) if signer == attestation.signer()
    ));
    target.trust_snapshot_signer(&claim)?;
    target.accept_authenticated_snapshot(&claim)?;
    let import = target.register_import(HolDatabaseRef::new(
        attestation.schema(),
        attestation.image(),
    ))?;
    let trusted = target.accept_trusted_import(import, &claim)?;
    let namespace = target.create_imported_namespace(
        Some(NamespaceId::root()),
        Some("signed-succ-congruence"),
        import,
        proof.namespace.get(),
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
    let matched = target.match_trusted_import_image(trusted, validated)?;
    matched.with_mounted_reader(namespace, &mounted, |mut reader| {
        let ImportedExport::Term(conclusion) = reader
            .namespace_export(0)?
            .ok_or_else(|| io::Error::other("theorem export 0 is absent"))?
        else {
            return Err(io::Error::other("export 0 is not a term").into());
        };
        let ImportedExport::Context(context) = reader
            .namespace_export(1)?
            .ok_or_else(|| io::Error::other("context export 1 is absent"))?
        else {
            return Err(io::Error::other("export 1 is not a context").into());
        };
        let imported = reader
            .theorem(context, conclusion)?
            .ok_or_else(|| io::Error::other("signed succ-congruence judgement is absent"))?;
        assert_eq!(imported.context(), context);
        assert_eq!(imported.conclusion(), conclusion);
        inspect_succ_congruence(&mut reader, conclusion)?;
        Ok::<_, AnyError>(())
    })??;

    println!("wrote, trusted, and inspected {}", output.display());
    println!("image {}", attestation.image());
    println!("source signer {}", attestation.signer());
    Ok(())
}

fn inspect_succ_congruence<'reader>(
    reader: &mut covalence_nucleus::ImportedHolReader<'reader, '_, AllowAll>,
    conclusion: covalence_nucleus::ImportedTermId<'reader>,
) -> Result<(), AnyError> {
    let ImportedTermView::Equality { left, right, .. } = reader.term(conclusion)? else {
        return Err(io::Error::other("conclusion is not equality").into());
    };
    let ImportedTermView::Application {
        function: left_succ,
        argument: x,
        ..
    } = reader.term(left)?
    else {
        return Err(io::Error::other("left side is not succ application").into());
    };
    let ImportedTermView::Application {
        function: right_succ,
        argument: y,
        ..
    } = reader.term(right)?
    else {
        return Err(io::Error::other("right side is not succ application").into());
    };
    assert_eq!(left_succ, right_succ);
    assert!(matches!(
        reader.term(left_succ)?,
        ImportedTermView::Constant { symbol: 202, .. }
    ));
    assert!(matches!(
        reader.term(x)?,
        ImportedTermView::Constant { symbol: 200, .. }
    ));
    assert!(matches!(
        reader.term(y)?,
        ImportedTermView::Constant { symbol: 201, .. }
    ));
    Ok(())
}

fn write_artifact(
    output: &PathBuf,
    snapshot: &covalence_nucleus::SignedHolSnapshot,
    proof: &succ_congruence::SuccCongruence,
) -> Result<(), AnyError> {
    fs::create_dir_all(output)?;
    let attestation = snapshot.attestation();
    fs::write(output.join("proof.sqlite"), snapshot.image().bytes())?;
    fs::write(output.join("schema.covhol"), snapshot.descriptor().encode())?;
    let mut manifest = String::new();
    writeln!(manifest, "schema {}", attestation.schema())?;
    writeln!(manifest, "image {}", attestation.image())?;
    writeln!(manifest, "signer {}", attestation.signer())?;
    writeln!(manifest, "public-key {}", hex(attestation.public_key()))?;
    writeln!(manifest, "signature {}", hex(attestation.signature()))?;
    writeln!(
        manifest,
        "statement {}",
        schema_valid_snapshot_statement(attestation.schema(), attestation.image())
    )?;
    writeln!(manifest, "namespace {}", proof.namespace.get())?;
    writeln!(manifest, "theorem-export 0")?;
    writeln!(manifest, "context-export 1")?;
    writeln!(manifest, "theorem-context {}", proof.context.get())?;
    writeln!(manifest, "theorem-term {}", proof.conclusion.get())?;
    fs::write(output.join("attestation.txt"), manifest)?;
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}
