use std::{error::Error, io, sync::Arc, sync::mpsc, thread};

use covalence_lib_hash::O256;
use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, HolDatabaseRef, HolSchemaDescriptor, ImportedExport,
    ImportedTermView, Kernel, NamespaceId, SignedSnapshotAttestation, SignedSnapshotEnvelope,
    SnapshotTrustError,
};

#[path = "support/closed_beta.rs"]
mod closed_beta;

type AnyError = Box<dyn Error>;

struct WireSnapshot {
    bytes: Vec<u8>,
    descriptor: Vec<u8>,
    schema: O256,
    image: O256,
    signer: O256,
    public_key: [u8; 32],
    signature: Vec<u8>,
    namespace: i64,
}

fn main() -> Result<(), AnyError> {
    let (sender, receiver) = mpsc::sync_channel(1);
    let source = thread::spawn(move || {
        let result = build_source().map_err(|error| error.to_string());
        let _ = sender.send(result);
    });
    let wire = receiver.recv()?.map_err(io::Error::other)?;
    source
        .join()
        .map_err(|_| io::Error::other("source kernel thread panicked"))?;

    let target_kernel = Kernel::ephemeral();
    let mut target = target_kernel.open_hol(AllowAll)?;
    let claim = SignedSnapshotAttestation::new(
        wire.schema,
        wire.image,
        wire.signer,
        wire.public_key,
        &wire.signature,
    )
    .authenticate()?;
    assert!(matches!(
        target.accept_authenticated_snapshot(&claim),
        Err(SnapshotTrustError::UntrustedSigner(signer)) if signer == wire.signer
    ));

    target.trust_snapshot_signer(&claim)?;
    target.accept_authenticated_snapshot(&claim)?;
    let import = target.register_import(HolDatabaseRef::new(wire.schema, wire.image))?;
    let trusted = target.accept_trusted_import(import, &claim)?;
    let namespace = target.create_imported_namespace(
        Some(NamespaceId::root()),
        Some("signed-beta"),
        import,
        wire.namespace,
    )?;

    let authenticated = SignedSnapshotEnvelope::new(
        &wire.bytes,
        wire.schema,
        wire.image,
        wire.signer,
        wire.public_key,
        &wire.signature,
    )
    .authenticate()?;
    let descriptor = HolSchemaDescriptor::decode(&wire.descriptor)?;
    let validated =
        AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
    let mounted =
        covalence_neutron::ImmutableImage::register(Arc::from(validated.image().bytes()))?;
    let matched = target.match_trusted_import_image(trusted, validated)?;
    matched.with_mounted_reader(namespace, &mounted, |mut reader| {
        let ImportedExport::Term(equality) = reader
            .namespace_export(0)?
            .ok_or_else(|| io::Error::other("signed beta namespace does not export theorem 0"))?
        else {
            return Err(io::Error::other("signed beta export is not a term").into());
        };
        let ImportedTermView::Equality { left, right, .. } = reader.term(equality)? else {
            return Err(io::Error::other("exported theorem is not an equality").into());
        };
        assert_eq!(reader.term(right)?, ImportedTermView::Bool(true));
        let ImportedTermView::Application {
            function, argument, ..
        } = reader.term(left)?
        else {
            return Err(io::Error::other("beta left side is not an application").into());
        };
        assert_eq!(reader.term(argument)?, ImportedTermView::Bool(true));
        let ImportedTermView::Lambda { body, .. } = reader.term(function)? else {
            return Err(io::Error::other("beta function is not a lambda").into());
        };
        assert!(matches!(
            reader.term(body)?,
            ImportedTermView::Bound { index: 0, .. }
        ));
        let ImportedExport::Context(context) = reader
            .namespace_export(1)?
            .ok_or_else(|| io::Error::other("signed beta namespace does not export context 1"))?
        else {
            return Err(io::Error::other("signed beta context export is not a context").into());
        };
        let imported_theorem = reader
            .theorem(context, equality)?
            .ok_or_else(|| io::Error::other("signed beta judgement is absent"))?;
        assert_eq!(imported_theorem.context(), context);
        assert_eq!(imported_theorem.conclusion(), equality);
        Ok::<_, AnyError>(())
    })??;

    let target_snapshot = target_kernel.export_hol(&mut target)?;
    assert_ne!(target_snapshot.attestation().signer(), wire.signer);
    assert_eq!(target_snapshot.image().counts().import_references, 1);
    assert_eq!(
        target_snapshot
            .image()
            .counts()
            .untrusted_trusted_import_rows,
        1
    );
    println!("trusted and inspected signed beta image {}", wire.image);
    println!("source signer {}", wire.signer);
    println!("target signer {}", target_snapshot.attestation().signer());
    Ok(())
}

fn build_source() -> Result<WireSnapshot, AnyError> {
    let kernel = Kernel::ephemeral();
    let mut database = kernel.open_hol(AllowAll)?;
    let proof = closed_beta::build(&mut database)?;
    assert!(database.with_proof_session(|mut session| {
        Ok::<_, covalence_nucleus::ProofError>(
            session
                .load_theorem(proof.context, proof.conclusion)?
                .is_some(),
        )
    })?);
    let snapshot = kernel.export_hol(&mut database)?;
    let attestation = snapshot.attestation();
    Ok(WireSnapshot {
        bytes: snapshot.image().bytes().to_vec(),
        descriptor: snapshot.descriptor().encode().to_vec(),
        schema: attestation.schema(),
        image: attestation.image(),
        signer: attestation.signer(),
        public_key: *attestation.public_key(),
        signature: attestation.signature().to_vec(),
        namespace: proof.namespace.get(),
    })
}
