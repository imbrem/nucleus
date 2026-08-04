//! Produces, signs, imports, and structurally inspects the explicit infinity-assumption demo.

use std::collections::HashSet;
use std::env;
use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use covalence_hol_library::{InfinityDemo, prove_infinity_successor_nonzero};
use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, ExportId, HolDatabaseRef, HolSchemaDescriptor,
    ImportedExport, ImportedHolReader, ImportedTermId, ImportedTermView, Kernel, NamespaceExport,
    NamespaceId, SignedSnapshotAttestation, SignedSnapshotEnvelope, SnapshotTrustError,
    schema_valid_snapshot_statement,
};

type AnyError = Box<dyn Error>;

const IND_SYMBOL: i64 = 10;
const ZERO_SYMBOL: i64 = 20;
const SUCCESSOR_SYMBOL: i64 = 30;

fn main() -> Result<(), AnyError> {
    let output = env::args_os()
        .nth(1)
        .map_or_else(|| PathBuf::from("signed-infinity-artifact"), PathBuf::from);

    let source_kernel = Kernel::ephemeral();
    let mut source = source_kernel.open_hol(AllowAll)?;
    let proof =
        prove_infinity_successor_nonzero(&mut source, IND_SYMBOL, ZERO_SYMBOL, SUCCESSOR_SYMBOL)?;
    assert_eq!(
        source.context_members(proof.context)?,
        sorted_assumptions(&proof)
    );
    let namespace = publish(&mut source, &proof)?;
    let snapshot = source_kernel.export_hol(&mut source)?;
    write_artifact(&output, &snapshot, namespace, &proof)?;

    // Treat the files as the wire format. Authentication and schema/image validation below use
    // these freshly read bytes, not the live source connection or an assumed SQLite layout.
    let image_bytes = fs::read(output.join("proof.sqlite"))?;
    let descriptor_bytes = fs::read(output.join("schema.covhol"))?;
    let descriptor = HolSchemaDescriptor::decode(&descriptor_bytes)?;
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
    let imported_namespace = target.create_imported_namespace(
        Some(NamespaceId::root()),
        Some("signed-infinity"),
        import,
        namespace.get(),
    )?;

    let authenticated = SignedSnapshotEnvelope::new(
        &image_bytes,
        attestation.schema(),
        attestation.image(),
        attestation.signer(),
        *attestation.public_key(),
        attestation.signature(),
    )
    .authenticate()?;
    let validated =
        AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
    let mounted =
        covalence_neutron::ImmutableImage::register(Arc::from(validated.image().bytes()))?;
    let matched = target.match_trusted_import_image(trusted, validated)?;
    matched.with_mounted_reader(imported_namespace, &mounted, |mut reader| {
        inspect_import(&mut reader)
    })??;

    println!("wrote, trusted, and inspected {}", output.display());
    println!("image {}", attestation.image());
    println!("source signer {}", attestation.signer());
    println!("context assumptions H0 and Hinj were exported and structurally inspected");
    Ok(())
}

fn publish(
    source: &mut covalence_nucleus::Connection<covalence_nucleus::Hol<AllowAll>>,
    proof: &InfinityDemo,
) -> Result<NamespaceId, AnyError> {
    let namespace =
        source.create_namespace(Some(NamespaceId::root()), Some("infinity-assumptions"))?;
    for (export, value, name) in [
        (
            0,
            NamespaceExport::Term(proof.conclusion),
            "successor_zero_nonzero",
        ),
        (1, NamespaceExport::Context(proof.context), "Gamma_inf"),
        (
            2,
            NamespaceExport::Term(proof.successor_nonzero_assumption),
            "H0_successor_nonzero",
        ),
        (
            3,
            NamespaceExport::Term(proof.successor_injective_assumption),
            "Hinj_successor_injective",
        ),
        (4, NamespaceExport::Term(proof.zero), "zero"),
        (5, NamespaceExport::Term(proof.successor), "successor"),
    ] {
        source.export_value(namespace, ExportId::from_i64(export), value, Some(name))?;
    }
    Ok(namespace)
}

fn inspect_import(reader: &mut ImportedHolReader<'_, '_, AllowAll>) -> Result<(), AnyError> {
    let conclusion = require_term_export(reader, 0)?;
    let ImportedExport::Context(context) = reader
        .namespace_export(1)?
        .ok_or_else(|| io::Error::other("Gamma_inf export 1 is absent"))?
    else {
        return Err(io::Error::other("Gamma_inf export 1 is not a context").into());
    };
    let h0 = require_term_export(reader, 2)?;
    let hinj = require_term_export(reader, 3)?;
    let zero = require_term_export(reader, 4)?;
    let successor = require_term_export(reader, 5)?;

    let theorem = reader
        .theorem(context, conclusion)?
        .ok_or_else(|| io::Error::other("trusted imported infinity judgement is absent"))?;
    assert_eq!(theorem.context(), context);
    assert_eq!(theorem.conclusion(), conclusion);
    assert!(matches!(
        reader.term(zero)?,
        ImportedTermView::Constant {
            symbol: ZERO_SYMBOL,
            ..
        }
    ));
    assert!(matches!(
        reader.term(successor)?,
        ImportedTermView::Constant {
            symbol: SUCCESSOR_SYMBOL,
            ..
        }
    ));

    let conclusion_shape = summarize(reader, conclusion)?;
    assert!(conclusion_shape.equalities >= 2);
    assert_eq!(conclusion_shape.epsilons, 0);
    assert_eq!(
        conclusion_shape.symbols,
        HashSet::from([ZERO_SYMBOL, SUCCESSOR_SYMBOL])
    );

    // The imported-reader API deliberately does not expose raw context-member SQL. The exact
    // source context was checked before signing; detached validation checks all context rows; the
    // theorem capability names the exported context; and these two separately exported members
    // are structurally inspected through the pointer-verified immutable reader.
    let h0_shape = summarize(reader, h0)?;
    assert!(h0_shape.lambdas >= 3);
    assert!(h0_shape.equalities >= 4);
    assert_eq!(h0_shape.epsilons, 0);
    assert_eq!(
        h0_shape.symbols,
        HashSet::from([ZERO_SYMBOL, SUCCESSOR_SYMBOL])
    );
    let hinj_shape = summarize(reader, hinj)?;
    assert!(hinj_shape.lambdas >= 5);
    assert!(hinj_shape.equalities >= 5);
    assert_eq!(hinj_shape.epsilons, 0);
    assert_eq!(hinj_shape.symbols, HashSet::from([SUCCESSOR_SYMBOL]));
    Ok(())
}

fn require_term_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedTermId<'reader>, AnyError> {
    match reader
        .namespace_export(export)?
        .ok_or_else(|| io::Error::other(format!("term export {export} is absent")))?
    {
        ImportedExport::Term(term) => Ok(term),
        _ => Err(io::Error::other(format!("export {export} is not a term")).into()),
    }
}

#[derive(Default)]
struct Shape {
    applications: usize,
    bounds: usize,
    equalities: usize,
    epsilons: usize,
    lambdas: usize,
    symbols: HashSet<i64>,
}

fn summarize<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    root: ImportedTermId<'reader>,
) -> Result<Shape, AnyError> {
    fn visit<'reader>(
        reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
        term: ImportedTermId<'reader>,
        shape: &mut Shape,
    ) -> Result<(), AnyError> {
        match reader.term(term)? {
            ImportedTermView::Bool(_) | ImportedTermView::Free { .. } => {}
            ImportedTermView::Constant { symbol, .. } => {
                shape.symbols.insert(symbol);
            }
            ImportedTermView::Bound { .. } => shape.bounds += 1,
            ImportedTermView::Application {
                function, argument, ..
            } => {
                shape.applications += 1;
                visit(reader, function, shape)?;
                visit(reader, argument, shape)?;
            }
            ImportedTermView::Lambda { body, .. } => {
                shape.lambdas += 1;
                visit(reader, body, shape)?;
            }
            ImportedTermView::Equality { left, right, .. } => {
                shape.equalities += 1;
                visit(reader, left, shape)?;
                visit(reader, right, shape)?;
            }
            ImportedTermView::Epsilon { predicate, .. } => {
                shape.epsilons += 1;
                visit(reader, predicate, shape)?;
            }
        }
        Ok(())
    }

    let mut shape = Shape::default();
    visit(reader, root, &mut shape)?;
    Ok(shape)
}

fn sorted_assumptions(proof: &InfinityDemo) -> Vec<covalence_nucleus::TermId> {
    let mut assumptions = vec![
        proof.successor_nonzero_assumption,
        proof.successor_injective_assumption,
    ];
    assumptions.sort_unstable();
    assumptions
}

fn write_artifact(
    output: &Path,
    snapshot: &covalence_nucleus::SignedHolSnapshot,
    namespace: NamespaceId,
    proof: &InfinityDemo,
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
    writeln!(manifest, "namespace {}", namespace.get())?;
    writeln!(manifest, "theorem-export 0")?;
    writeln!(manifest, "context-export 1")?;
    writeln!(manifest, "H0-export 2")?;
    writeln!(manifest, "Hinj-export 3")?;
    writeln!(manifest, "zero-export 4")?;
    writeln!(manifest, "successor-export 5")?;
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
