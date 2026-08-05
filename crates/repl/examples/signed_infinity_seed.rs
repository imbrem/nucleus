//! Builds, signs, reloads, trusts, imports, and reads the first HOL stdlib seed.

use std::env;
use std::error::Error;
use std::fmt::Write as _;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use covalence_lib_hash::O256;
use covalence_nucleus::{
    AllowAll, AuthenticatedSnapshot, AuthenticatedValidatedHolImage, ExportId, HolDatabaseRef,
    ImportedExport, ImportedHolReader, ImportedTermId, ImportedTermView, ImportedTypeId,
    ImportedTypeView, Kernel, NamespaceExport, NamespaceId, SignedSnapshotEnvelope,
    SnapshotTrustError, schema_valid_snapshot_statement,
};
use covalence_repl::MAX_IMAGE_BYTES;
use covalence_repl::hol_recipes::{InfinitySeed, prove_infinity_seed};

type AnyError = Box<dyn Error>;

const IND_SYMBOL: i64 = 10;
const ZERO_SYMBOL: i64 = 20;
const SUCCESSOR_SYMBOL: i64 = 30;
const ATTESTATION_FORMAT: &str = "covalence-hol-stdlib-seed-v0";
const MAX_ATTESTATION_BYTES: usize = 4 * 1024;

fn main() -> Result<(), AnyError> {
    let output = env::args_os()
        .nth(1)
        .map_or_else(|| PathBuf::from("signed-infinity-seed"), PathBuf::from);
    // Reserve the user-visible destination before mutating even the disposable
    // producer. The guard removes only the two files it may create.
    let mut artifact_directory = FreshArtifactDirectory::create(&output)?;

    let source_kernel = Kernel::ephemeral();
    // This pin is established from the selected endpoint, outside the artifact
    // transport. A self-consistent signature by any other key remains untrusted.
    let expected_signer = ExpectedSigner {
        signer: source_kernel.key_id(),
        public_key: *source_kernel.verifying_key().as_bytes(),
    };
    let mut source = source_kernel.open_hol(AllowAll)?;
    let seed = prove_infinity_seed(&mut source, IND_SYMBOL, ZERO_SYMBOL, SUCCESSOR_SYMBOL)?;
    let namespace = publish(&mut source, &seed)?;
    let snapshot = source_kernel.export_hol(&mut source)?;
    write_artifact(&mut artifact_directory, &snapshot, namespace)?;
    artifact_directory.commit();

    // Everything below is a file-level receiver. It uses neither the source
    // connection nor any coordinate retained from `snapshot`.
    let image = read_bounded(&output.join("proof.sqlite"), MAX_IMAGE_BYTES)?;
    let attestation_bytes = read_bounded(&output.join("attestation.txt"), MAX_ATTESTATION_BYTES)?;
    let attestation = parse_attestation(&attestation_bytes)?;
    let expected_statement = schema_valid_snapshot_statement(attestation.schema, attestation.image);
    if attestation.statement != expected_statement {
        return Err(io::Error::other("serialized snapshot statement is incoherent").into());
    }
    let authenticated = SignedSnapshotEnvelope::new(
        &image,
        attestation.schema,
        attestation.image,
        attestation.signer,
        attestation.public_key,
        &attestation.signature,
    )
    .authenticate()?;
    require_expected_signer(&authenticated, expected_signer)?;
    let validated = AuthenticatedValidatedHolImage::validate_default(authenticated)?;

    // A raw, read-only audit demonstrates the serialized state contains the
    // canonical judgement and no proof-event/proof-step relation.
    let mounted = covalence_neutron::ImmutableImage::register(Arc::from(image.as_slice()))?;
    let raw = covalence_neutron::Connection::open_in_memory()?;
    mounted.attach(&raw, "artifact")?;
    let judgement_count: i64 =
        raw.sqlite()
            .query_row("SELECT count(*) FROM artifact.hol_judgement", [], |row| {
                row.get(0)
            })?;
    let proof_trace_tables: i64 = raw.sqlite().query_row(
        "SELECT count(*) FROM artifact.sqlite_schema
         WHERE type = 'table' AND (name LIKE '%proof%step%' OR name LIKE '%proof%event%')",
        [],
        |row| row.get(0),
    )?;
    if judgement_count != 2 || proof_trace_tables != 0 {
        return Err(io::Error::other("artifact is not kernel-state-only").into());
    }
    verify_exact_context_members(&raw, attestation.namespace)?;

    let target_kernel = Kernel::ephemeral();
    let mut target = target_kernel.open_hol(AllowAll)?;
    let claim = validated.claim();
    assert!(matches!(
        target.accept_authenticated_snapshot(claim),
        Err(SnapshotTrustError::UntrustedSigner(signer)) if signer == attestation.signer
    ));
    target.trust_snapshot_signer(claim)?;
    target.accept_authenticated_snapshot(claim)?;
    let import = target.register_import(HolDatabaseRef::new(claim.schema(), claim.image()))?;
    let trusted = target.accept_trusted_import(import, claim)?;
    let imported_namespace = target.create_imported_namespace(
        Some(NamespaceId::root()),
        Some("signed-infinity-seed"),
        import,
        attestation.namespace,
    )?;
    target
        .match_trusted_import_image(trusted, validated)?
        .with_mounted_reader(imported_namespace, &mounted, |mut reader| {
            inspect_import(&mut reader)
        })??;

    println!(
        "wrote, authenticated, trusted, and inspected {}",
        output.display()
    );
    println!("theorem Gamma_inf |- not (successor zero = zero)");
    println!("image {}", attestation.image);
    println!("signer {}", attestation.signer);
    println!("persisted judgements {judgement_count}; persisted proof traces {proof_trace_tables}");
    Ok(())
}

fn publish(
    source: &mut covalence_nucleus::Connection<covalence_nucleus::Hol<AllowAll>>,
    seed: &InfinitySeed,
) -> Result<NamespaceId, AnyError> {
    let namespace = source.create_namespace(Some(NamespaceId::root()), Some("stdlib-seed"))?;
    for (export, value, name) in [
        (0, NamespaceExport::Context(seed.context), "Gamma_inf"),
        (
            1,
            NamespaceExport::Term(seed.conclusion),
            "successor_zero_nonzero",
        ),
        (
            2,
            NamespaceExport::Term(seed.successor_nonzero_assumption),
            "H0_successor_nonzero",
        ),
        (
            3,
            NamespaceExport::Term(seed.successor_injective_assumption),
            "Hinj_successor_injective",
        ),
        (4, NamespaceExport::Type(seed.ind_type), "ind"),
        (5, NamespaceExport::Term(seed.zero), "zero"),
        (6, NamespaceExport::Term(seed.successor), "successor"),
        (
            7,
            NamespaceExport::Term(seed.injectivity_instance),
            "successor_injectivity_instance",
        ),
    ] {
        source.export_value(namespace, ExportId::from_i64(export), value, Some(name))?;
    }
    Ok(namespace)
}

fn inspect_import(reader: &mut ImportedHolReader<'_, '_, AllowAll>) -> Result<(), AnyError> {
    let Some(ImportedExport::Context(context)) = reader.namespace_export(0)? else {
        return Err(io::Error::other("export 0 is not Gamma_inf").into());
    };
    let conclusion = require_term_export(reader, 1)?;
    let h0 = require_term_export(reader, 2)?;
    let hinj = require_term_export(reader, 3)?;
    let Some(ImportedExport::Type(ind)) = reader.namespace_export(4)? else {
        return Err(io::Error::other("export 4 is not ind").into());
    };
    let zero = require_term_export(reader, 5)?;
    let successor = require_term_export(reader, 6)?;
    let injectivity_instance = require_term_export(reader, 7)?;

    let theorem = reader
        .theorem(context, conclusion)?
        .ok_or_else(|| io::Error::other("persisted imported judgement is absent"))?;
    assert_eq!(theorem.context(), context);
    assert_eq!(theorem.conclusion(), conclusion);
    let injectivity_theorem = reader
        .theorem(context, injectivity_instance)?
        .ok_or_else(|| io::Error::other("persisted injectivity instance is absent"))?;
    assert_eq!(injectivity_theorem.context(), context);
    assert_eq!(injectivity_theorem.conclusion(), injectivity_instance);
    if !matches!(
        reader.type_view(ind)?,
        ImportedTypeView::Base { symbol: IND_SYMBOL }
    ) {
        return Err(io::Error::other("exported ind has the wrong declaration").into());
    }
    let ImportedTermView::Constant {
        symbol: ZERO_SYMBOL,
        ty: zero_type,
    } = reader.term(zero)?
    else {
        return Err(io::Error::other("exported zero has the wrong declaration").into());
    };
    if zero_type != ind {
        return Err(io::Error::other("zero does not have type ind").into());
    }
    let ImportedTermView::Constant {
        symbol: SUCCESSOR_SYMBOL,
        ty: successor_type,
    } = reader.term(successor)?
    else {
        return Err(io::Error::other("exported successor has the wrong declaration").into());
    };
    if !matches!(
        reader.type_view(successor_type)?,
        ImportedTypeView::Arrow { domain, codomain } if domain == ind && codomain == ind
    ) {
        return Err(io::Error::other("successor is not ind -> ind").into());
    }
    let ImportedTermView::Equality { ty: bool_type, .. } = reader.term(conclusion)? else {
        return Err(io::Error::other("first theorem is not an equality").into());
    };
    if !matches!(reader.type_view(bool_type)?, ImportedTypeView::Bool) {
        return Err(io::Error::other("theorem does not have Boolean type").into());
    }

    verify_imported_formulas(
        reader,
        ImportedSeed {
            ind,
            bool_type,
            zero,
            successor,
            h0,
            hinj,
            conclusion,
            injectivity_instance,
        },
    )
}

#[derive(Clone, Copy)]
struct ImportedSeed<'reader> {
    ind: ImportedTypeId<'reader>,
    bool_type: ImportedTypeId<'reader>,
    zero: ImportedTermId<'reader>,
    successor: ImportedTermId<'reader>,
    h0: ImportedTermId<'reader>,
    hinj: ImportedTermId<'reader>,
    conclusion: ImportedTermId<'reader>,
    injectivity_instance: ImportedTermId<'reader>,
}

fn verify_imported_formulas<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    seed: ImportedSeed<'reader>,
) -> Result<(), AnyError> {
    let ImportedSeed {
        ind,
        bool_type,
        zero,
        successor,
        h0,
        hinj,
        conclusion,
        injectivity_instance,
    } = seed;
    let identity = ExpectedTerm::lambda(bool_type, ExpectedTerm::bound(0, bool_type));
    let truth = ExpectedTerm::equality(identity.clone(), identity.clone());
    let falsehood = ExpectedTerm::equality(
        ExpectedTerm::lambda(
            bool_type,
            ExpectedTerm::application(identity.clone(), ExpectedTerm::bound(0, bool_type)),
        ),
        ExpectedTerm::lambda(bool_type, truth.clone()),
    );
    let successor_zero =
        ExpectedTerm::application(ExpectedTerm::exact(successor), ExpectedTerm::exact(zero));

    let expected_conclusion = ExpectedTerm::equality(
        ExpectedTerm::equality(successor_zero.clone(), ExpectedTerm::exact(zero)),
        falsehood.clone(),
    );
    verify_term(reader, conclusion, &expected_conclusion, bool_type)?;

    let nonzero_body = ExpectedTerm::equality(
        ExpectedTerm::equality(
            ExpectedTerm::application(ExpectedTerm::exact(successor), ExpectedTerm::bound(0, ind)),
            ExpectedTerm::exact(zero),
        ),
        falsehood,
    );
    let nonzero_predicate = ExpectedTerm::lambda(ind, nonzero_body);
    let expected_h0 = ExpectedTerm::equality(
        ExpectedTerm::lambda(
            ind,
            ExpectedTerm::application(nonzero_predicate, ExpectedTerm::bound(0, ind)),
        ),
        ExpectedTerm::lambda(ind, truth.clone()),
    );
    verify_term(reader, h0, &expected_h0, bool_type)?;

    let injectivity_body = ExpectedTerm::equality(
        ExpectedTerm::equality(
            ExpectedTerm::application(ExpectedTerm::exact(successor), ExpectedTerm::bound(1, ind)),
            ExpectedTerm::application(ExpectedTerm::exact(successor), ExpectedTerm::bound(0, ind)),
        ),
        ExpectedTerm::equality(ExpectedTerm::bound(1, ind), ExpectedTerm::bound(0, ind)),
    );
    let forall_y = ExpectedTerm::equality(
        ExpectedTerm::lambda(ind, injectivity_body),
        ExpectedTerm::lambda(ind, truth.clone()),
    );
    let injectivity_predicate = ExpectedTerm::lambda(ind, forall_y);
    let expected_hinj = ExpectedTerm::equality(
        ExpectedTerm::lambda(
            ind,
            ExpectedTerm::application(injectivity_predicate, ExpectedTerm::bound(0, ind)),
        ),
        ExpectedTerm::lambda(ind, truth),
    );
    verify_term(reader, hinj, &expected_hinj, bool_type)?;

    let expected_instance = ExpectedTerm::equality(
        ExpectedTerm::equality(
            successor_zero.clone(),
            ExpectedTerm::application(ExpectedTerm::exact(successor), successor_zero.clone()),
        ),
        ExpectedTerm::equality(ExpectedTerm::exact(zero), successor_zero),
    );
    verify_term(reader, injectivity_instance, &expected_instance, bool_type)?;
    Ok(())
}

fn require_term_export<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    export: i64,
) -> Result<ImportedTermId<'reader>, AnyError> {
    match reader.namespace_export(export)? {
        Some(ImportedExport::Term(term)) => Ok(term),
        _ => Err(io::Error::other(format!("export {export} is not a term")).into()),
    }
}

#[derive(Clone)]
enum ExpectedTerm<'reader> {
    Exact(ImportedTermId<'reader>),
    Bound {
        index: u64,
        ty: ImportedTypeId<'reader>,
    },
    Application(Box<Self>, Box<Self>),
    Lambda {
        parameter_type: ImportedTypeId<'reader>,
        body: Box<Self>,
    },
    Equality(Box<Self>, Box<Self>),
}

impl<'reader> ExpectedTerm<'reader> {
    fn exact(term: ImportedTermId<'reader>) -> Self {
        Self::Exact(term)
    }

    fn bound(index: u64, ty: ImportedTypeId<'reader>) -> Self {
        Self::Bound { index, ty }
    }

    fn application(function: Self, argument: Self) -> Self {
        Self::Application(Box::new(function), Box::new(argument))
    }

    fn lambda(parameter_type: ImportedTypeId<'reader>, body: Self) -> Self {
        Self::Lambda {
            parameter_type,
            body: Box::new(body),
        }
    }

    fn equality(left: Self, right: Self) -> Self {
        Self::Equality(Box::new(left), Box::new(right))
    }
}

fn verify_term<'reader>(
    reader: &mut ImportedHolReader<'reader, '_, AllowAll>,
    actual: ImportedTermId<'reader>,
    expected: &ExpectedTerm<'reader>,
    bool_type: ImportedTypeId<'reader>,
) -> Result<(), AnyError> {
    match expected {
        ExpectedTerm::Exact(expected) if actual == *expected => Ok(()),
        ExpectedTerm::Bound {
            index: expected_index,
            ty: expected_type,
        } => match reader.term(actual)? {
            ImportedTermView::Bound { index, ty }
                if index == *expected_index && ty == *expected_type =>
            {
                Ok(())
            }
            _ => Err(io::Error::other("unexpected bound-variable structure").into()),
        },
        ExpectedTerm::Application(expected_function, expected_argument) => {
            let ImportedTermView::Application {
                function, argument, ..
            } = reader.term(actual)?
            else {
                return Err(io::Error::other("unexpected application structure").into());
            };
            verify_term(reader, function, expected_function, bool_type)?;
            verify_term(reader, argument, expected_argument, bool_type)
        }
        ExpectedTerm::Lambda {
            parameter_type: expected_parameter_type,
            body: expected_body,
        } => {
            let ImportedTermView::Lambda {
                parameter_type,
                body,
                ..
            } = reader.term(actual)?
            else {
                return Err(io::Error::other("unexpected lambda structure").into());
            };
            if parameter_type != *expected_parameter_type {
                return Err(io::Error::other("unexpected lambda parameter type").into());
            }
            verify_term(reader, body, expected_body, bool_type)
        }
        ExpectedTerm::Equality(expected_left, expected_right) => {
            let ImportedTermView::Equality {
                left, right, ty, ..
            } = reader.term(actual)?
            else {
                return Err(io::Error::other("unexpected equality structure").into());
            };
            if ty != bool_type {
                return Err(io::Error::other("equality has non-Boolean result").into());
            }
            verify_term(reader, left, expected_left, bool_type)?;
            verify_term(reader, right, expected_right, bool_type)
        }
        ExpectedTerm::Exact(_) => Err(io::Error::other("unexpected exact term coordinate").into()),
    }
}

fn write_artifact(
    output: &mut FreshArtifactDirectory,
    snapshot: &covalence_nucleus::SignedHolSnapshot,
    namespace: NamespaceId,
) -> Result<(), AnyError> {
    output.write(ArtifactFile::Database, snapshot.image().bytes())?;
    let attestation = snapshot.attestation();
    let mut manifest = String::new();
    writeln!(manifest, "format {ATTESTATION_FORMAT}")?;
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
    output.write(ArtifactFile::Attestation, manifest.as_bytes())?;
    Ok(())
}

struct FreshArtifactDirectory {
    path: PathBuf,
    keep: bool,
    database_owned: bool,
    attestation_owned: bool,
}

#[derive(Clone, Copy)]
enum ArtifactFile {
    Database,
    Attestation,
}

impl ArtifactFile {
    const fn name(self) -> &'static str {
        match self {
            Self::Database => "proof.sqlite",
            Self::Attestation => "attestation.txt",
        }
    }
}

impl FreshArtifactDirectory {
    fn create(path: &Path) -> io::Result<Self> {
        fs::create_dir(path)?;
        Ok(Self {
            path: path.to_owned(),
            keep: false,
            database_owned: false,
            attestation_owned: false,
        })
    }

    fn write(&mut self, artifact: ArtifactFile, bytes: &[u8]) -> io::Result<()> {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(self.path.join(artifact.name()))?;
        // Ownership begins only after this invocation's create_new succeeds.
        match artifact {
            ArtifactFile::Database => self.database_owned = true,
            ArtifactFile::Attestation => self.attestation_owned = true,
        }
        file.write_all(bytes)?;
        file.sync_all()
    }

    fn commit(&mut self) {
        self.keep = true;
    }
}

impl Drop for FreshArtifactDirectory {
    fn drop(&mut self) {
        if !self.keep {
            if self.attestation_owned {
                let _ = fs::remove_file(self.path.join(ArtifactFile::Attestation.name()));
            }
            if self.database_owned {
                let _ = fs::remove_file(self.path.join(ArtifactFile::Database.name()));
            }
            let _ = fs::remove_dir(&self.path);
        }
    }
}

#[derive(Clone, Copy)]
struct ExpectedSigner {
    signer: O256,
    public_key: [u8; 32],
}

fn require_expected_signer(
    authenticated: &AuthenticatedSnapshot,
    expected: ExpectedSigner,
) -> io::Result<()> {
    if authenticated.signer() != expected.signer
        || authenticated.public_key() != &expected.public_key
    {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "authenticated artifact signer does not match the independently selected producer",
        ));
    }
    Ok(())
}

struct SerializedAttestation {
    schema: O256,
    image: O256,
    signer: O256,
    public_key: [u8; 32],
    signature: [u8; 64],
    statement: O256,
    namespace: i64,
}

fn parse_attestation(bytes: &[u8]) -> io::Result<SerializedAttestation> {
    let text = std::str::from_utf8(bytes)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "attestation is not UTF-8"))?;
    let mut format = None;
    let mut schema = None;
    let mut image = None;
    let mut signer = None;
    let mut public_key = None;
    let mut signature = None;
    let mut statement = None;
    let mut namespace = None;
    for line in text.lines() {
        let (key, value) = line.split_once(' ').ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "malformed attestation line")
        })?;
        match key {
            "format" => set_once(&mut format, value.to_owned(), key)?,
            "schema" => set_once(&mut schema, parse_o256(value, key)?, key)?,
            "image" => set_once(&mut image, parse_o256(value, key)?, key)?,
            "signer" => set_once(&mut signer, parse_o256(value, key)?, key)?,
            "public-key" => set_once(&mut public_key, parse_hex(value, key)?, key)?,
            "signature" => set_once(&mut signature, parse_hex(value, key)?, key)?,
            "statement" => set_once(&mut statement, parse_o256(value, key)?, key)?,
            "namespace" => {
                let value = value
                    .parse::<i64>()
                    .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid namespace"))?;
                if value < 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "negative namespace",
                    ));
                }
                set_once(&mut namespace, value, key)?;
            }
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "unknown attestation field",
                ));
            }
        }
    }
    if format.as_deref() != Some(ATTESTATION_FORMAT) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unsupported attestation format",
        ));
    }
    Ok(SerializedAttestation {
        schema: required(schema, "schema")?,
        image: required(image, "image")?,
        signer: required(signer, "signer")?,
        public_key: required(public_key, "public-key")?,
        signature: required(signature, "signature")?,
        statement: required(statement, "statement")?,
        namespace: required(namespace, "namespace")?,
    })
}

fn set_once<T>(slot: &mut Option<T>, value: T, name: &str) -> io::Result<()> {
    if slot.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("duplicate {name}"),
        ));
    }
    *slot = Some(value);
    Ok(())
}

fn required<T>(value: Option<T>, name: &str) -> io::Result<T> {
    value.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, format!("missing {name}")))
}

fn parse_o256(value: &str, name: &str) -> io::Result<O256> {
    O256::from_hex(value)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, format!("invalid {name}")))
}

fn parse_hex<const N: usize>(value: &str, name: &str) -> io::Result<[u8; N]> {
    if value.len() != N * 2 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid {name} length"),
        ));
    }
    let mut bytes = [0; N];
    for (index, byte) in bytes.iter_mut().enumerate() {
        let pair = value
            .get(index * 2..index * 2 + 2)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, format!("invalid {name}")))?;
        *byte = u8::from_str_radix(pair, 16)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, format!("invalid {name}")))?;
    }
    Ok(bytes)
}

fn read_bounded(path: &Path, limit: usize) -> io::Result<Vec<u8>> {
    let read_limit = u64::try_from(limit)
        .ok()
        .and_then(|limit| limit.checked_add(1))
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "image limit overflow"))?;
    let mut bytes = Vec::new();
    File::open(path)?.take(read_limit).read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("database image exceeds {limit} bytes"),
        ));
    }
    Ok(bytes)
}

fn verify_exact_context_members(
    raw: &covalence_neutron::Connection,
    namespace: i64,
) -> Result<(), AnyError> {
    let context = raw_export_id(raw, namespace, 0, "context")?;
    let mut expected = vec![
        raw_export_id(raw, namespace, 2, "term")?,
        raw_export_id(raw, namespace, 3, "term")?,
    ];
    expected.sort_unstable();
    let mut statement = raw.sqlite().prepare(
        "SELECT term_id FROM artifact.hol_context_member
         WHERE ctx_id = ?1 ORDER BY term_id",
    )?;
    let actual = statement
        .query_map([context], |row| row.get::<_, i64>(0))?
        .collect::<Result<Vec<_>, _>>()?;
    if actual != expected {
        return Err(io::Error::other("Gamma_inf does not contain exactly H0 and Hinj").into());
    }
    Ok(())
}

fn raw_export_id(
    raw: &covalence_neutron::Connection,
    namespace: i64,
    export: i64,
    sort: &str,
) -> Result<i64, AnyError> {
    Ok(raw.sqlite().query_row(
        "SELECT local_id FROM artifact.hol_namespace_export
         WHERE namespace_id = ?1 AND export_id = ?2 AND sort = ?3",
        (namespace, export, sort),
        |row| row.get(0),
    )?)
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> PathBuf {
        env::temp_dir().join(format!(
            "covalence-{name}-{}-{}",
            std::process::id(),
            Kernel::ephemeral().key_id()
        ))
    }

    fn valid_attestation() -> String {
        format!(
            "format {ATTESTATION_FORMAT}\nschema {zero}\nimage {zero}\nsigner {zero}\npublic-key {key}\nsignature {signature}\nstatement {zero}\nnamespace 7\n",
            zero = "00".repeat(32),
            key = "11".repeat(32),
            signature = "22".repeat(64),
        )
    }

    #[test]
    fn serialized_attestation_round_trips_all_untrusted_fields() {
        let parsed = parse_attestation(valid_attestation().as_bytes()).unwrap();
        assert_eq!(parsed.namespace, 7);
        assert_eq!(parsed.public_key, [0x11; 32]);
        assert_eq!(parsed.signature, [0x22; 64]);
    }

    #[test]
    fn serialized_attestation_rejects_duplicate_unknown_and_corrupt_fields() {
        let valid = valid_attestation();
        assert!(
            parse_attestation(format!("{valid}schema {}\n", "00".repeat(32)).as_bytes()).is_err()
        );
        assert!(parse_attestation(valid.replace("namespace 7", "mystery 7").as_bytes()).is_err());
        assert!(parse_attestation(valid.replace(&"22".repeat(64), "not-hex").as_bytes()).is_err());
    }

    #[test]
    fn valid_signature_from_the_wrong_pinned_kernel_is_rejected() {
        let producer = Kernel::ephemeral();
        let wrong_endpoint = Kernel::ephemeral();
        let mut connection = producer.open_hol(AllowAll).unwrap();
        let snapshot = producer.export_hol(&mut connection).unwrap();
        let attestation = snapshot.attestation();
        let authenticated = SignedSnapshotEnvelope::new(
            snapshot.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap();
        require_expected_signer(
            &authenticated,
            ExpectedSigner {
                signer: producer.key_id(),
                public_key: *producer.verifying_key().as_bytes(),
            },
        )
        .unwrap();
        assert!(
            require_expected_signer(
                &authenticated,
                ExpectedSigner {
                    signer: wrong_endpoint.key_id(),
                    public_key: *wrong_endpoint.verifying_key().as_bytes(),
                },
            )
            .is_err()
        );
    }

    #[test]
    fn bounded_read_rejects_the_sentinel_byte() {
        let path = scratch("bounded-read");
        fs::write(&path, b"four").unwrap();
        assert!(read_bounded(&path, 3).is_err());
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn rollback_removes_only_files_created_by_this_guard() {
        let path = scratch("owned-artifacts");
        let mut directory = FreshArtifactDirectory::create(&path).unwrap();
        directory.write(ArtifactFile::Database, b"ours").unwrap();
        fs::write(path.join("attestation.txt"), b"concurrent").unwrap();
        assert!(
            directory
                .write(ArtifactFile::Attestation, b"replacement")
                .is_err()
        );
        drop(directory);
        assert!(!path.join("proof.sqlite").exists());
        assert_eq!(
            fs::read(path.join("attestation.txt")).unwrap(),
            b"concurrent"
        );
        fs::remove_file(path.join("attestation.txt")).unwrap();
        fs::remove_dir(path).unwrap();
    }
}
