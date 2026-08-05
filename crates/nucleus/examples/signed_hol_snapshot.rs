//! Minimal end-to-end signed HOL snapshot demonstration.
//!
//! The proof recipe lives here, above the Nucleus trusted core.  The imported
//! judgement remains reader-scoped evidence: importing it does not manufacture
//! a local theorem capability.

use std::error::Error;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::Arc;

use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, ContextId, ExportId, HolDatabaseRef, ImportedExport,
    ImportedTermView, Kernel, NamespaceExport, SignedSnapshotEnvelope,
};

fn main() -> Result<(), Box<dyn Error>> {
    let output = std::env::args_os()
        .nth(1)
        .map_or_else(|| PathBuf::from("target/signed-hol-demo"), PathBuf::from);
    std::fs::create_dir_all(&output)?;

    // Producer: construct (\x:bool. x) true = true using only an existing HOL rule.
    let producer = Kernel::ephemeral();
    let mut source = producer.open_hol(AllowAll)?;
    let bool_type = source.insert_bool_type()?;
    let bound = source.insert_bound_term(0, bool_type)?;
    let identity = source.insert_lambda(bool_type, bound)?;
    let truth = source.insert_bool_term(true)?;
    let conclusion = source.with_proof_session(|mut proof| {
        let theorem = proof.prove_beta(ContextId::empty(), identity, truth)?;
        let conclusion = theorem.conclusion();
        // Proof recipes are deliberately not stored.  Only kernel state is persisted.
        proof.persist_theorem(&theorem)?;
        Ok::<_, covalence_nucleus::ProofError>(conclusion)
    })?;

    let namespace = source.create_namespace(None, Some("beta-demo"))?;
    source.export_value(
        namespace,
        ExportId::from_i64(0),
        NamespaceExport::Context(ContextId::empty()),
        Some("empty-context"),
    )?;
    source.export_value(
        namespace,
        ExportId::from_i64(1),
        NamespaceExport::Term(conclusion),
        Some("beta-conclusion"),
    )?;

    // Export exact SQLite bytes and a signature over (HOL schema, byte hash).
    let signed = producer.export_hol(&mut source)?;
    let attestation = signed.attestation();
    let database_path = output.join("beta.sqlite3");
    let attestation_path = output.join("beta.attestation.txt");
    std::fs::write(&database_path, signed.image().bytes())?;
    std::fs::write(
        &attestation_path,
        render_attestation(
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            attestation.public_key(),
            attestation.signature(),
        ),
    )?;

    // Receiver phase 1 — authentication: verify byte hash, key ID, and signature.
    // This does not validate SQLite/HOL and does not trust the signing key.
    let received = std::fs::read(&database_path)?;
    let authenticated = SignedSnapshotEnvelope::new(
        &received,
        attestation.schema(),
        attestation.image(),
        attestation.signer(),
        *attestation.public_key(),
        attestation.signature(),
    )
    .authenticate()?;

    // Receiver phase 2 — detached validation: parse the bytes in a disposable
    // connection and independently check the one current HOL schema.
    let validated = AuthenticatedValidatedHolImage::validate_default(authenticated)?;

    let importer_kernel = Kernel::ephemeral();
    let mut target = importer_kernel.open_hol(AllowAll)?;
    let claim = validated.claim();

    // Receiver phase 3 — explicit trust and acceptance.  Signer trust and exact
    // snapshot acceptance are separate, connection-local decisions.
    target.trust_snapshot_signer(claim)?;
    target.accept_authenticated_snapshot(claim)?;

    // Receiver phase 4 — inert import registration, persistent audit evidence,
    // and a complete namespace alias.  None of these steps fetches the image.
    let import = target.register_import(HolDatabaseRef::new(claim.schema(), claim.image()))?;
    let trusted = target.accept_trusted_import(import, claim)?;
    let imported_namespace = target.create_imported_namespace(
        None,
        Some("received-beta-demo"),
        import,
        namespace.get(),
    )?;

    // Receiver phase 5 — mount the exact validated bytes and obtain structural,
    // reader-scoped evidence.  ImportedTheorem cannot be used as a local Theorem.
    let mounted = covalence_neutron::ImmutableImage::register(Arc::from(received))?;
    target
        .match_trusted_import_image(trusted, validated)?
        .with_mounted_reader(imported_namespace, &mounted, |mut reader| {
            let ImportedExport::Context(context) =
                reader.namespace_export(0)?.expect("context export")
            else {
                panic!("export 0 must be a context")
            };
            let ImportedExport::Term(conclusion) =
                reader.namespace_export(1)?.expect("term export")
            else {
                panic!("export 1 must be a term")
            };
            let theorem = reader
                .theorem(context, conclusion)?
                .expect("persisted beta theorem");
            assert_eq!(theorem.context(), context);
            assert_eq!(theorem.conclusion(), conclusion);
            assert!(matches!(
                reader.term(conclusion)?,
                ImportedTermView::Equality { .. }
            ));
            Ok::<_, covalence_nucleus::ImportedReaderError>(())
        })??;

    println!("database: {}", database_path.display());
    println!("attestation: {}", attestation_path.display());
    println!("schema: {}", attestation.schema());
    println!("image: {}", attestation.image());
    println!("signer: {}", attestation.signer());
    println!("verified imported theorem: empty |- (\\x:bool. x) true = true");
    Ok(())
}

fn render_attestation(
    schema: covalence_lib_hash::O256,
    image: covalence_lib_hash::O256,
    signer: covalence_lib_hash::O256,
    public_key: &[u8; 32],
    signature: &[u8],
) -> String {
    let mut text = String::new();
    writeln!(text, "format=covalence-signed-snapshot-v0").unwrap();
    writeln!(text, "schema={schema}").unwrap();
    writeln!(text, "image={image}").unwrap();
    writeln!(text, "signer={signer}").unwrap();
    writeln!(text, "public_key={}", hex(public_key)).unwrap();
    writeln!(text, "signature={}", hex(signature)).unwrap();
    text
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}
