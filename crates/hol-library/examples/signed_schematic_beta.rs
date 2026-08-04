//! Proves schematic beta, signs its database, then trusts and inspects the immutable import.

use std::env;
use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use covalence_hol_library::{SchematicBetaDemo, prove_schematic_beta};
use covalence_nucleus::{
    AllowAll, AuthenticatedValidatedHolImage, ExportId, HolDatabaseRef, HolSchemaDescriptor,
    ImportedContextId, ImportedExport, ImportedHolReader, ImportedTermId, ImportedTermView,
    ImportedTypeId, ImportedTypeView, Kernel, NamespaceExport, NamespaceId,
    SignedSnapshotAttestation, SignedSnapshotEnvelope, SnapshotTrustError,
    schema_valid_snapshot_statement,
};

type AnyError = Box<dyn Error>;

const ALPHA_SYMBOL: i64 = 700;
const Y_SYMBOL: i64 = 701;

fn main() -> Result<(), AnyError> {
    let output = env::args_os().nth(1).map_or_else(
        || PathBuf::from("signed-schematic-beta-artifact"),
        PathBuf::from,
    );

    let source_kernel = Kernel::ephemeral();
    let mut source = source_kernel.open_hol(AllowAll)?;
    let proof = prove_schematic_beta(&mut source, ALPHA_SYMBOL, Y_SYMBOL)?;
    assert!(source.context_members(proof.context)?.is_empty());
    for conclusion in [
        proof.generic_conclusion,
        proof.bool_conclusion,
        proof.concrete_conclusion,
    ] {
        assert!(source.proved_judgement(proof.context, conclusion)?);
    }

    let namespace = publish(&mut source, &proof)?;
    let snapshot = source_kernel.export_hol(&mut source)?;
    write_artifact(&output, &snapshot, namespace, &proof)?;

    // Read the artifact back as its wire representation. Authentication and validation below do
    // not retain authority from the live source connection.
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
        Some("signed-schematic-beta"),
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
    println!("generic beta, its bool instance, and its true instance were inspected");
    Ok(())
}

fn publish(
    source: &mut covalence_nucleus::Connection<covalence_nucleus::Hol<AllowAll>>,
    proof: &SchematicBetaDemo,
) -> Result<NamespaceId, AnyError> {
    let namespace = source.create_namespace(Some(NamespaceId::root()), Some("schematic-beta"))?;
    for (export, value, name) in [
        (0, NamespaceExport::Context(proof.context), "empty_context"),
        (1, NamespaceExport::Type(proof.alpha), "alpha"),
        (2, NamespaceExport::Type(proof.bool_type), "bool"),
        (
            3,
            NamespaceExport::Type(proof.alpha_identity_type),
            "alpha_to_alpha",
        ),
        (
            4,
            NamespaceExport::Type(proof.bool_identity_type),
            "bool_to_bool",
        ),
        (10, NamespaceExport::Term(proof.y_alpha), "y_alpha"),
        (
            11,
            NamespaceExport::Term(proof.identity_alpha),
            "identity_alpha",
        ),
        (
            12,
            NamespaceExport::Term(proof.generic_conclusion),
            "generic_beta",
        ),
        (20, NamespaceExport::Term(proof.y_bool), "y_bool"),
        (
            21,
            NamespaceExport::Term(proof.identity_bool),
            "identity_bool",
        ),
        (
            22,
            NamespaceExport::Term(proof.bool_conclusion),
            "bool_beta",
        ),
        (30, NamespaceExport::Term(proof.truth), "true"),
        (
            31,
            NamespaceExport::Term(proof.concrete_conclusion),
            "true_beta",
        ),
    ] {
        source.export_value(namespace, ExportId::from_i64(export), value, Some(name))?;
    }
    Ok(namespace)
}

fn inspect_import(reader: &mut ImportedHolReader<'_, '_, AllowAll>) -> Result<(), AnyError> {
    let context = require_context_export(reader, 0)?;
    let alpha = require_type_export(reader, 1)?;
    let bool_type = require_type_export(reader, 2)?;
    let alpha_arrow = require_type_export(reader, 3)?;
    let bool_arrow = require_type_export(reader, 4)?;
    let y_alpha = require_term_export(reader, 10)?;
    let identity_alpha = require_term_export(reader, 11)?;
    let generic = require_term_export(reader, 12)?;
    let y_bool = require_term_export(reader, 20)?;
    let identity_bool = require_term_export(reader, 21)?;
    let bool_instance = require_term_export(reader, 22)?;
    let truth = require_term_export(reader, 30)?;
    let concrete = require_term_export(reader, 31)?;

    assert_eq!(
        reader.type_view(alpha)?,
        ImportedTypeView::Free {
            symbol: ALPHA_SYMBOL
        }
    );
    assert_eq!(reader.type_view(bool_type)?, ImportedTypeView::Bool);
    assert_eq!(
        reader.type_view(alpha_arrow)?,
        ImportedTypeView::Arrow {
            domain: alpha,
            codomain: alpha,
        }
    );
    assert_eq!(
        reader.type_view(bool_arrow)?,
        ImportedTypeView::Arrow {
            domain: bool_type,
            codomain: bool_type,
        }
    );

    assert_eq!(
        reader.term(y_alpha)?,
        ImportedTermView::Free {
            symbol: u64::try_from(Y_SYMBOL)?,
            ty: alpha,
        }
    );
    assert_identity(reader, identity_alpha, alpha, alpha_arrow)?;
    assert_beta(reader, generic, identity_alpha, y_alpha, alpha, bool_type)?;

    assert_eq!(
        reader.term(y_bool)?,
        ImportedTermView::Free {
            symbol: u64::try_from(Y_SYMBOL)?,
            ty: bool_type,
        }
    );
    assert_identity(reader, identity_bool, bool_type, bool_arrow)?;
    assert_beta(
        reader,
        bool_instance,
        identity_bool,
        y_bool,
        bool_type,
        bool_type,
    )?;

    assert_eq!(reader.term(truth)?, ImportedTermView::Bool(true));
    assert_beta(reader, concrete, identity_bool, truth, bool_type, bool_type)?;

    for conclusion in [generic, bool_instance, concrete] {
        let theorem = reader
            .theorem(context, conclusion)?
            .ok_or_else(|| io::Error::other("trusted imported beta judgement is absent"))?;
        assert_eq!(theorem.context(), context);
        assert_eq!(theorem.conclusion(), conclusion);
    }
    Ok(())
}

fn assert_identity<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    identity: ImportedTermId<'reader>,
    parameter_type: ImportedTypeId<'reader>,
    function_type: ImportedTypeId<'reader>,
) -> Result<(), AnyError> {
    let ImportedTermView::Lambda {
        parameter_type: actual_parameter_type,
        body,
        ty,
    } = reader.term(identity)?
    else {
        return Err(io::Error::other("exported identity is not a lambda").into());
    };
    assert_eq!(actual_parameter_type, parameter_type);
    assert_eq!(ty, function_type);
    assert_eq!(
        reader.term(body)?,
        ImportedTermView::Bound {
            index: 0,
            ty: parameter_type,
        }
    );
    Ok(())
}

fn assert_beta<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    conclusion: ImportedTermId<'reader>,
    identity: ImportedTermId<'reader>,
    argument: ImportedTermId<'reader>,
    result_type: ImportedTypeId<'reader>,
    bool_type: ImportedTypeId<'reader>,
) -> Result<(), AnyError> {
    let ImportedTermView::Equality { left, right, ty } = reader.term(conclusion)? else {
        return Err(io::Error::other("beta conclusion is not an equality").into());
    };
    assert_eq!(right, argument);
    assert_eq!(ty, bool_type);
    assert_eq!(
        reader.term(left)?,
        ImportedTermView::Application {
            function: identity,
            argument,
            ty: result_type,
        }
    );
    Ok(())
}

fn require_context_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedContextId<'reader>, AnyError> {
    match require_export(reader, export)? {
        ImportedExport::Context(context) => Ok(context),
        _ => Err(io::Error::other(format!("export {export} is not a context")).into()),
    }
}

fn require_type_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedTypeId<'reader>, AnyError> {
    match require_export(reader, export)? {
        ImportedExport::Type(ty) => Ok(ty),
        _ => Err(io::Error::other(format!("export {export} is not a type")).into()),
    }
}

fn require_term_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedTermId<'reader>, AnyError> {
    match require_export(reader, export)? {
        ImportedExport::Term(term) => Ok(term),
        _ => Err(io::Error::other(format!("export {export} is not a term")).into()),
    }
}

fn require_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedExport<'reader>, AnyError> {
    reader
        .namespace_export(export)?
        .ok_or_else(|| io::Error::other(format!("export {export} is absent")).into())
}

fn write_artifact(
    output: &Path,
    snapshot: &covalence_nucleus::SignedHolSnapshot,
    namespace: NamespaceId,
    proof: &SchematicBetaDemo,
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
    writeln!(manifest, "context-export 0")?;
    writeln!(manifest, "alpha-type-export 1")?;
    writeln!(manifest, "bool-type-export 2")?;
    writeln!(manifest, "alpha-arrow-export 3")?;
    writeln!(manifest, "bool-arrow-export 4")?;
    writeln!(manifest, "y-alpha-export 10")?;
    writeln!(manifest, "identity-alpha-export 11")?;
    writeln!(manifest, "generic-theorem-export 12")?;
    writeln!(manifest, "y-bool-export 20")?;
    writeln!(manifest, "identity-bool-export 21")?;
    writeln!(manifest, "bool-theorem-export 22")?;
    writeln!(manifest, "true-export 30")?;
    writeln!(manifest, "concrete-theorem-export 31")?;
    writeln!(manifest, "theorem-context {}", proof.context.get())?;
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
