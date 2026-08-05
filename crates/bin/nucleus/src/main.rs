use std::collections::HashMap;
use std::env;
use std::error::Error;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use covalence_repl::{
    AllowAll, ConnectionId, ExpectedKernelIdentity, HolRecipe, HolRecipeResult, Kernel, KernelId,
    LocalConnection, MAX_IMAGE_BYTES, MAX_SEALED_HOL_RECIPE_BYTES,
    MAX_SIGNED_HOL_ARTIFACT_SIDECAR_BYTES, Outcome, Repl, RetainedReceivedHolSnapshot,
    SignedHolRoundTripResult, Value, authenticate_pinned_signed_hol_artifact,
    open_retained_trusted_hol_as_managed_state, parse_signed_hol_artifact_sidecar,
    produce_signed_dedekind_infinity_assumption, produce_signed_hol_artifact,
    produce_signed_natlike_missing_zero, replay_sealed_hol_proof_recipe,
    retain_replayed_hol_proof_recipe, retain_signed_dedekind_infinity_assumption,
    retain_signed_natlike_missing_zero, run_managed_signed_hol_round_trip,
    trust_and_receive_pinned_signed_hol_artifact,
    trust_receive_and_retain_selected_managed_hol_artifact,
};
#[cfg(not(target_arch = "wasm32"))]
use covalence_repl::{
    ManagedHolGuestResult, O256, PrecompiledHolProofComponentExecutor, PreparedHolProofComponent,
    ReceivedHolSnapshot, ServiceOperation, ServiceResult, SessionInitiator, SignedHolArtifact,
    SignedKernelService, WasmtimeComponentLimits, retain_signed_hol_guest_artifact,
    run_hol_proof_component,
};
#[cfg(not(target_arch = "wasm32"))]
use covalence_repl::{NativeHttpKernelServer, SIGNED_KERNEL_HTTP_PATH};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
type LocalRepl = Repl<LocalConnection>;

fn open_sql_connection(kernel: &Kernel, repl: &mut LocalRepl) -> Result<ConnectionId> {
    let connection = LocalConnection::Sql(kernel.open_sql()?);
    let id = repl.insert(connection.protocol(), connection)?;
    repl.select(id)?;
    Ok(id)
}

fn open_hol_connection(kernel: &Kernel, repl: &mut LocalRepl) -> Result<ConnectionId> {
    let connection = LocalConnection::Hol(kernel.open_hol(AllowAll)?);
    let id = repl.insert(connection.protocol(), connection)?;
    repl.select(id)?;
    Ok(id)
}

fn print_outcome(output: &mut impl io::Write, outcome: &Outcome) -> io::Result<()> {
    match outcome {
        Outcome::Changed(count) => writeln!(output, "changed {count}"),
        Outcome::Rows(result) => {
            writeln!(
                output,
                "{}",
                result
                    .columns
                    .iter()
                    .map(|column| column.escape_default().to_string())
                    .collect::<Vec<_>>()
                    .join("\t")
            )?;
            for row in &result.rows {
                writeln!(
                    output,
                    "{}",
                    row.iter().map(format_value).collect::<Vec<_>>().join("\t")
                )?;
            }
            Ok(())
        }
    }
}

fn format_value(value: &Value) -> String {
    match value {
        Value::Null => "NULL".to_owned(),
        Value::Integer(value) => value.to_string(),
        Value::Real(value) => value.to_string(),
        Value::Text(value) => format!("\"{}\"", value.escape_default()),
        Value::Blob(value) => {
            let mut encoded = String::with_capacity(3 + value.len() * 2);
            encoded.push_str("x'");
            for byte in value {
                use std::fmt::Write as _;
                write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
            }
            encoded.push('\'');
            encoded
        }
    }
}

fn print_hol_outcome(output: &mut impl io::Write, outcome: &HolRecipeResult) -> io::Result<()> {
    writeln!(output, "kind\t{}", outcome.kind())?;
    writeln!(output, "recipe\t{}", outcome.recipe())?;
    writeln!(output, "context\t{}", outcome.context_id())?;
    writeln!(output, "conclusion\t{}", outcome.conclusion_id())?;
    writeln!(output, "statement\t{}", outcome.statement())
}

fn print_signed_hol_outcome(
    output: &mut impl io::Write,
    outcome: &SignedHolRoundTripResult,
) -> io::Result<()> {
    writeln!(output, "kind\t{}", outcome.kind())?;
    writeln!(output, "phases\t{}", outcome.phases().join(","))?;
    writeln!(output, "statement\t{}", outcome.proof().statement())?;
    writeln!(output, "conclusion\t{}", outcome.proof().conclusion_id())?;
    writeln!(output, "namespace\t{}", outcome.namespace_id())?;
    writeln!(output, "schema\t{}", outcome.schema())?;
    writeln!(output, "image\t{}", outcome.image_hash())?;
    writeln!(output, "signer\t{}", outcome.signer())?;
    writeln!(output, "import\t{}", outcome.import_id())?;
    writeln!(
        output,
        "imported_namespace\t{}",
        outcome.imported_namespace_id()
    )?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        outcome.imported_context_id(),
        outcome.imported_conclusion_id()
    )
}

fn write_signed_hol_artifacts(
    output: &mut impl io::Write,
    mut fresh: FreshArtifactDirectory,
    outcome: &SignedHolRoundTripResult,
) -> Result<()> {
    let attestation = outcome.attestation_text();
    fresh.write_pair(outcome.image(), attestation.as_bytes())?;
    let path = fresh.path().to_owned();
    fresh.commit();
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    Ok(())
}

/// Exact fresh directory owned by this invocation until both artifacts exist.
///
/// Rollback removes only files whose `create_new` call succeeded in this
/// invocation. A concurrent file which made a later `create_new` fail is never
/// marked as owned and is therefore never a cleanup target.
struct FreshArtifactDirectory {
    path: PathBuf,
    proof_owned: bool,
    attestation_owned: bool,
    committed: bool,
}

impl FreshArtifactDirectory {
    fn create(path: &Path) -> io::Result<Self> {
        let name = path.file_name().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "artifact output must name a fresh directory",
            )
        })?;
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let path = fs::canonicalize(parent)?.join(name);
        fs::create_dir(&path)?;
        Ok(Self {
            path,
            proof_owned: false,
            attestation_owned: false,
            committed: false,
        })
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn write_pair(&mut self, image: &[u8], attestation: &[u8]) -> io::Result<()> {
        self.write_owned("proof.sqlite", image)?;
        self.write_owned("attestation.txt", attestation)
    }

    fn write_owned(&mut self, name: &'static str, bytes: &[u8]) -> io::Result<()> {
        let path = self.path.join(name);
        let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
        match name {
            "proof.sqlite" => self.proof_owned = true,
            "attestation.txt" => self.attestation_owned = true,
            _ => unreachable!("artifact writer uses only fixed names"),
        }
        file.write_all(bytes)?;
        file.sync_all()
    }

    fn commit(mut self) {
        self.committed = true;
    }
}

impl Drop for FreshArtifactDirectory {
    fn drop(&mut self) {
        if self.committed {
            return;
        }
        if self.proof_owned {
            let _ = fs::remove_file(self.path.join("proof.sqlite"));
        }
        if self.attestation_owned {
            let _ = fs::remove_file(self.path.join("attestation.txt"));
        }
        let _ = fs::remove_dir(&self.path);
    }
}

fn run_interkernel_hol(output: &mut impl io::Write) -> Result<()> {
    let producer_kernel = Kernel::ephemeral();
    let receiver_kernel = Kernel::ephemeral();
    let mut directory = Repl::empty()?;
    let producer_endpoint = directory.register_kernel(
        "local",
        Some("producer"),
        producer_kernel.verifying_key().as_bytes(),
    )?;
    let receiver_endpoint = directory.register_kernel(
        "local",
        Some("receiver"),
        receiver_kernel.verifying_key().as_bytes(),
    )?;
    let source = LocalConnection::Hol(producer_kernel.open_hol(AllowAll)?);
    let source_id = directory.insert_at(producer_endpoint, source.protocol(), Some("1"), source)?;
    let target = LocalConnection::Hol(receiver_kernel.open_hol(AllowAll)?);
    let target_id = directory.insert_at(receiver_endpoint, target.protocol(), Some("1"), target)?;

    let artifact_bundle =
        produce_signed_hol_artifact(&producer_kernel, directory.get_mut(source_id)?.hol_mut()?)?;
    let expected = directory.expected_kernel_identity(producer_endpoint)?;
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact_bundle.artifact())?;
    let imported = trust_and_receive_pinned_signed_hol_artifact(
        directory.get_mut(target_id)?.hol_mut()?,
        pinned,
    )?;

    writeln!(output, "producer_kernel\t{producer_endpoint}")?;
    writeln!(output, "receiver_kernel\t{receiver_endpoint}")?;
    writeln!(
        output,
        "producer_signer\t{}",
        artifact_bundle.artifact().signer()
    )?;
    writeln!(output, "receiver_signer\t{}", receiver_kernel.key_id())?;
    writeln!(output, "connections\t{}", directory.connections()?.len())?;
    writeln!(
        output,
        "receiver_phases\t{}",
        covalence_repl::SIGNED_HOL_PHASES[3..].join(",")
    )?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        imported.context_id(),
        imported.conclusion_id()
    )?;
    Ok(())
}

fn load_image(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    schema: &str,
    path: &str,
) -> Result<()> {
    let bytes = read_bounded_image(File::open(path)?)?;
    let connection = repl.active_mut()?.sql_mut()?;
    let hash = connection.put_image(&bytes)?;
    connection.attach_immutable_image(hash, schema)?;
    writeln!(output, "attached {schema} {hash}")?;
    Ok(())
}

fn read_bounded_image(mut input: impl io::Read) -> Result<Vec<u8>> {
    let sentinel_limit = u64::try_from(MAX_IMAGE_BYTES)? + 1;
    let mut bytes = Vec::new();
    input
        .by_ref()
        .take(sentinel_limit)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_IMAGE_BYTES {
        return Err(format!("image exceeds the {MAX_IMAGE_BYTES}-byte limit").into());
    }
    Ok(bytes)
}

#[cfg(not(target_arch = "wasm32"))]
fn read_bounded_component(path: &Path, maximum: usize) -> Result<Vec<u8>> {
    read_bounded_component_from(File::open(path)?, maximum)
}

#[cfg(not(target_arch = "wasm32"))]
fn read_bounded_component_from(mut input: impl io::Read, maximum: usize) -> Result<Vec<u8>> {
    let sentinel_limit = maximum
        .checked_add(1)
        .ok_or("component byte limit cannot be represented")?;
    let mut bytes = Vec::new();
    input
        .by_ref()
        .take(u64::try_from(sentinel_limit)?)
        .read_to_end(&mut bytes)?;
    if bytes.len() > maximum {
        return Err(format!("component exceeds the {maximum}-byte pre-compilation limit").into());
    }
    Ok(bytes)
}

#[cfg(not(target_arch = "wasm32"))]
fn run_managed_wasm_hol(
    output: &mut impl io::Write,
    directory: &mut LocalRepl,
    kernel: &Kernel,
    component_path: &Path,
    artifact_directory: &Path,
) -> Result<ManagedHolGuestResult> {
    let limits = WasmtimeComponentLimits::default();
    let component = read_bounded_component(component_path, limits.component_bytes)?;
    let mut fresh = FreshArtifactDirectory::create(artifact_directory)?;
    let artifact = run_hol_proof_component(kernel, &component, limits)?;
    let attestation = artifact.attestation_text();
    fresh.write_pair(artifact.image(), attestation.as_bytes())?;
    let managed = retain_signed_hol_guest_artifact(kernel, directory, artifact)?;
    let path = fresh.path().to_owned();
    fresh.commit();

    writeln!(output, "kind\tmanaged-wasm-hol")?;
    writeln!(output, "connection\t{}", managed.connection())?;
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    writeln!(output, "namespace\t{}", managed.artifact().namespace_id())?;
    writeln!(output, "schema\t{}", managed.artifact().schema())?;
    writeln!(output, "image\t{}", managed.artifact().image_hash())?;
    writeln!(output, "signer\t{}", managed.artifact().signer())?;
    writeln!(output, "import\t{}", managed.received().import_id())?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        managed.received().context_id(),
        managed.received().conclusion_id()
    )?;
    Ok(managed)
}

#[cfg(not(target_arch = "wasm32"))]
fn run_hash_selected_wasm_hol(
    output: &mut impl io::Write,
    receiver_kernel: &Kernel,
    directory: &mut LocalRepl,
    expected_component: O256,
    component_path: &Path,
    artifact_directory: &Path,
) -> Result<(
    ConnectionId,
    ExpectedKernelIdentity,
    SignedHolArtifact,
    ReceivedHolSnapshot,
    RetainedReceivedHolSnapshot,
)> {
    let limits = WasmtimeComponentLimits::default();
    let component = read_bounded_component(component_path, limits.component_bytes)?;
    // Hash agreement, byte bounds, validation, and compilation all complete
    // before a signing service or session exists.
    let prepared = PreparedHolProofComponent::prepare(expected_component, &component, limits)?;
    let mut executor = PrecompiledHolProofComponentExecutor::new();
    executor.insert(prepared)?;
    let mut fresh = FreshArtifactDirectory::create(artifact_directory)?;

    let mut service = SignedKernelService::new()?;
    service.install_hol_proof_component_executor(executor)?;
    let description = service.description().clone();
    let endpoint = description.identity();
    let expected_endpoint =
        ExpectedKernelIdentity::from_public_key(KernelId::from_u32(1), &endpoint.public_key())?;
    let initiator = SessionInitiator::begin(endpoint, &description)?;
    let accepted = service.open_session(initiator.request())?;
    let mut session = initiator.accept(&accepted)?;
    let command = session.command(ServiceOperation::RunHolProofComponent(expected_component))?;
    let reply = service.execute(&command)?;
    let ServiceResult::ProducedByComponent(produced) = session.accept_reply(&command, reply)?
    else {
        return Err("hash-selected HOL component did not produce an artifact".into());
    };
    if produced.component() != expected_component {
        return Err("signed component result changed the selected digest".into());
    }
    let artifact = produced.into_artifact();
    let attestation = artifact.attestation_text();
    fresh.write_pair(artifact.image(), attestation.as_bytes())?;

    let pinned = authenticate_pinned_signed_hol_artifact(&expected_endpoint, &artifact)?;
    let receiver = receiver_kernel.open_hol(AllowAll)?;
    let (connection, retained) =
        covalence_repl::trust_receive_and_retain_managed_hol_artifact(directory, receiver, pinned)?;
    let first_read = retained.received();

    let path = fresh.path().to_owned();
    fresh.commit();
    writeln!(output, "kind\thash-selected-wasm-hol")?;
    writeln!(output, "component\t{expected_component}")?;
    writeln!(output, "endpoint\t{}", endpoint.signer())?;
    writeln!(output, "connection\t{connection}")?;
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        first_read.context_id(),
        first_read.conclusion_id()
    )?;
    Ok((
        connection,
        expected_endpoint,
        artifact,
        first_read,
        retained,
    ))
}

fn write_new_file(path: &Path, write: impl FnOnce(&mut File) -> io::Result<()>) -> io::Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    if let Err(write_error) = write(&mut file) {
        drop(file);
        return match fs::remove_file(path) {
            Ok(()) => Err(write_error),
            Err(cleanup_error) if cleanup_error.kind() == io::ErrorKind::NotFound => {
                Err(write_error)
            }
            Err(cleanup_error) => Err(io::Error::other(format!(
                "could not remove partial snapshot after {write_error}: {cleanup_error}"
            ))),
        };
    }
    Ok(())
}

fn export_snapshot(path: &Path, bytes: &[u8]) -> io::Result<()> {
    write_new_file(path, |file| {
        file.write_all(bytes)?;
        file.sync_all()
    })
}

fn parse_load(command: &str) -> Option<(&str, &str)> {
    let arguments = command.strip_prefix(".load")?.trim();
    let split = arguments.find(char::is_whitespace)?;
    let schema = arguments[..split].trim();
    let path = arguments[split..].trim();
    (!schema.is_empty() && !path.is_empty()).then_some((schema, path))
}

#[cfg(not(target_arch = "wasm32"))]
fn run_interactive_hash_selected_wasm_hol(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    arguments: &str,
) -> Result<()> {
    let mut arguments = arguments.split_whitespace();
    let expected = arguments
        .next()
        .ok_or("usage: .hol hash-wasm O256 COMPONENT DIRECTORY")?;
    let component = arguments
        .next()
        .ok_or("usage: .hol hash-wasm O256 COMPONENT DIRECTORY")?;
    let directory = arguments
        .next()
        .ok_or("usage: .hol hash-wasm O256 COMPONENT DIRECTORY")?;
    if arguments.next().is_some() {
        return Err("usage: .hol hash-wasm O256 COMPONENT DIRECTORY".into());
    }
    let (receiver, _, _, _, retained) = run_hash_selected_wasm_hol(
        output,
        kernel,
        repl,
        O256::from_hex(expected)?,
        Path::new(component),
        Path::new(directory),
    )?;
    received_artifacts.insert(receiver, retained);
    repl.select(receiver)?;
    writeln!(output, "using receiver connection {receiver}")?;
    writeln!(output, "trusted_import_receipt\tretained")?;
    Ok(())
}

fn print_connections(repl: &mut LocalRepl, output: &mut impl io::Write) -> Result<()> {
    let active = repl.active()?;
    let mut statement = repl
        .state()
        .sqlite()
        .prepare("SELECT connection_id, protocol FROM repl_connection ORDER BY connection_id")?;
    let rows = statement.query_map((), |row| {
        Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?))
    })?;
    for row in rows {
        let (id, protocol) = row?;
        let marker = if active.is_some_and(|active| active.get() == id) {
            '*'
        } else {
            ' '
        };
        writeln!(output, "{marker} {id}\t{protocol}")?;
    }
    Ok(())
}

fn print_help(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(
        output,
        ".load SCHEMA PATH  attach a complete immutable SQLite image"
    )?;
    writeln!(output, ".open [sql|hol]    open and select a connection")?;
    writeln!(
        output,
        ".hol RECIPE        run truth, reflexivity BOOL, or beta BOOL"
    )?;
    writeln!(
        output,
        ".hol signed-roundtrip DIRECTORY  prove, sign, import, verify, and export artifacts"
    )?;
    #[cfg(not(target_arch = "wasm32"))]
    writeln!(
        output,
        ".hol hash-wasm O256 COMPONENT DIRECTORY  pin and run a component, then select its receiver"
    )?;
    writeln!(
        output,
        ".hol open-state [RECEIVER_ID]  reopen a retained trusted receiver as writable HOL state"
    )?;
    writeln!(
        output,
        ".hol assume-infinity DIRECTORY  create, dump, and retain the signed Dedekind-infinity assumption"
    )?;
    writeln!(
        output,
        ".hol natlike-missing-zero DIRECTORY  derive, dump, and retain signed missing zero"
    )?;
    writeln!(
        output,
        ".hol recipe FILE DIRECTORY  replay canonical bytes, dump, and retain the signed result"
    )?;
    writeln!(
        output,
        ".hol receive-signed DIRECTORY EXPECTED_PUBLIC_KEY_HEX  verify and retain signed files"
    )?;
    writeln!(output, ".use ID            select a connection")?;
    writeln!(output, ".close [ID]        close a connection")?;
    writeln!(output, ".connections       list open connections")?;
    writeln!(
        output,
        ".kernel identity   print this kernel's public identity"
    )?;
    writeln!(
        output,
        ".export PATH       write the active main snapshot to a file"
    )?;
    writeln!(
        output,
        ".state SQL         query the REPL state database read-only"
    )?;
    writeln!(output, ".quit              exit")
}

fn open_interactive_trusted_state(
    repl: &mut LocalRepl,
    received_artifacts: &HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    argument: Option<&str>,
) -> Result<()> {
    let owner = match argument {
        Some(argument) => ConnectionId::from_u32(argument.trim().parse()?),
        None => repl.active()?.ok_or("no active connection")?,
    };
    let retained = received_artifacts
        .get(&owner)
        .ok_or("connection has no retained trusted HOL snapshot")?;
    let opened = open_retained_trusted_hol_as_managed_state(repl, owner, retained, AllowAll)?;
    writeln!(output, "kind\ttrusted-hol-state")?;
    writeln!(output, "connection\t{}", opened.connection())?;
    writeln!(output, "source_namespace\t{}", opened.source_namespace_id())?;
    writeln!(
        output,
        "trusted_theorem\t{}\t{}",
        opened.context_id(),
        opened.conclusion_id()
    )?;
    Ok(())
}

fn run_info_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    if line == ".connections" {
        print_connections(repl, output)?;
        return Ok(true);
    }
    if line != ".kernel identity" {
        return Ok(false);
    }
    let public_key = kernel.verifying_key();
    let mut public_key_hex = String::with_capacity(64);
    for byte in public_key.as_bytes() {
        use std::fmt::Write as _;
        write!(public_key_hex, "{byte:02x}")?;
    }
    writeln!(output, "kind\tkernel-identity")?;
    writeln!(output, "signer\t{}", kernel.key_id())?;
    writeln!(output, "public_key\t{public_key_hex}")?;
    Ok(true)
}

fn assume_interactive_infinity(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    artifact_directory: &Path,
) -> Result<()> {
    let mut fresh = FreshArtifactDirectory::create(artifact_directory)?;
    let assumption = produce_signed_dedekind_infinity_assumption(kernel)?;
    let attestation = assumption.attestation_text();
    fresh.write_pair(assumption.artifact().image(), attestation.as_bytes())?;
    let (receiver, retained) =
        retain_signed_dedekind_infinity_assumption(kernel, repl, &assumption)?;
    received_artifacts.insert(receiver, retained);
    let path = fresh.path().to_owned();
    fresh.commit();
    writeln!(output, "kind\t{}", assumption.kind())?;
    writeln!(output, "authority\tsigned-assumption")?;
    writeln!(output, "assumption\tdedekind-infinity")?;
    writeln!(output, "falsehood\tall-bool-identity")?;
    writeln!(output, "connection\t{receiver}")?;
    writeln!(
        output,
        "source_namespace\t{}",
        assumption.artifact().namespace_id()
    )?;
    writeln!(output, "schema\t{}", assumption.artifact().schema())?;
    writeln!(output, "image\t{}", assumption.artifact().image_hash())?;
    writeln!(output, "signer\t{}", assumption.artifact().signer())?;
    writeln!(
        output,
        "assumed_judgement\t{}\t{}",
        assumption.context().get(),
        assumption.conclusion().get()
    )?;
    writeln!(output, "trusted_import_receipt\tretained")?;
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    Ok(())
}

fn run_interactive_infinity_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    if line == ".hol assume-infinity" {
        return Err("usage: .hol assume-infinity DIRECTORY".into());
    }
    let Some(path) = line.strip_prefix(".hol assume-infinity ") else {
        return Ok(false);
    };
    let path = path.trim();
    if path.is_empty() {
        return Err("usage: .hol assume-infinity DIRECTORY".into());
    }
    assume_interactive_infinity(kernel, repl, received_artifacts, output, Path::new(path))?;
    Ok(true)
}

fn derive_interactive_natlike_missing_zero(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    artifact_directory: &Path,
) -> Result<()> {
    let mut fresh = FreshArtifactDirectory::create(artifact_directory)?;
    let derivation = produce_signed_natlike_missing_zero(kernel)?;
    let attestation = derivation.attestation_text();
    fresh.write_pair(derivation.artifact().image(), attestation.as_bytes())?;
    let (receiver, retained) = retain_signed_natlike_missing_zero(kernel, repl, &derivation)?;
    received_artifacts.insert(receiver, retained);
    let path = fresh.path().to_owned();
    fresh.commit();

    writeln!(output, "kind\t{}", derivation.kind())?;
    writeln!(output, "authority\tkernel-derived-theorem")?;
    writeln!(output, "theorem\tnatlike-missing-zero")?;
    writeln!(output, "falsehood\tall-bool-identity")?;
    writeln!(output, "connection\t{receiver}")?;
    writeln!(
        output,
        "source_namespace\t{}",
        derivation.artifact().namespace_id()
    )?;
    writeln!(output, "schema\t{}", derivation.artifact().schema())?;
    writeln!(output, "image\t{}", derivation.artifact().image_hash())?;
    writeln!(output, "signer\t{}", derivation.artifact().signer())?;
    writeln!(
        output,
        "inherited_assumption\t{}\t{}",
        derivation.context().get(),
        derivation.inherited_infinity().get()
    )?;
    writeln!(
        output,
        "derived_judgement\t{}\t{}",
        derivation.context().get(),
        derivation.conclusion().get()
    )?;
    writeln!(output, "trusted_import_receipt\tretained")?;
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    Ok(())
}

fn run_interactive_natlike_missing_zero_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    if line == ".hol natlike-missing-zero" {
        return Err("usage: .hol natlike-missing-zero DIRECTORY".into());
    }
    let Some(path) = line.strip_prefix(".hol natlike-missing-zero ") else {
        return Ok(false);
    };
    let path = path.trim();
    if path.is_empty() {
        return Err("usage: .hol natlike-missing-zero DIRECTORY".into());
    }
    derive_interactive_natlike_missing_zero(
        kernel,
        repl,
        received_artifacts,
        output,
        Path::new(path),
    )?;
    Ok(true)
}

fn decode_expected_public_key(value: &str) -> Result<[u8; 32]> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("expected public key must be exactly 64 lowercase hex digits".into());
    }
    let mut decoded = [0; 32];
    for (target, pair) in decoded.iter_mut().zip(value.as_bytes().chunks_exact(2)) {
        let high = if pair[0].is_ascii_digit() {
            pair[0] - b'0'
        } else {
            pair[0] - b'a' + 10
        };
        let low = if pair[1].is_ascii_digit() {
            pair[1] - b'0'
        } else {
            pair[1] - b'a' + 10
        };
        *target = high * 16 + low;
    }
    Ok(decoded)
}

fn read_bounded_signed_artifact_sidecar(mut input: impl io::Read) -> Result<Vec<u8>> {
    let sentinel_limit = u64::try_from(MAX_SIGNED_HOL_ARTIFACT_SIDECAR_BYTES)? + 1;
    let mut bytes = Vec::new();
    input
        .by_ref()
        .take(sentinel_limit)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_SIGNED_HOL_ARTIFACT_SIDECAR_BYTES {
        return Err(format!(
            "attestation exceeds the {MAX_SIGNED_HOL_ARTIFACT_SIDECAR_BYTES}-byte limit"
        )
        .into());
    }
    Ok(bytes)
}

fn read_bounded_hol_proof_recipe(mut input: impl io::Read) -> Result<Vec<u8>> {
    let sentinel_limit = u64::try_from(MAX_SEALED_HOL_RECIPE_BYTES)? + 1;
    let mut bytes = Vec::new();
    input
        .by_ref()
        .take(sentinel_limit)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_SEALED_HOL_RECIPE_BYTES {
        return Err(format!(
            "sealed HOL recipe exceeds the {MAX_SEALED_HOL_RECIPE_BYTES}-byte limit"
        )
        .into());
    }
    Ok(bytes)
}

fn replay_interactive_hol_proof_recipe(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    recipe_file: &Path,
    artifact_directory: &Path,
) -> Result<()> {
    // Refuse a colliding destination before replaying, signing, or admitting a
    // receiver. Until commit, every file created below is rollback-owned.
    let mut fresh = FreshArtifactDirectory::create(artifact_directory)?;
    let recipe = read_bounded_hol_proof_recipe(File::open(recipe_file)?)?;
    let artifact = replay_sealed_hol_proof_recipe(kernel, &recipe)?;
    let attestation = artifact.attestation_text();
    fresh.write_pair(artifact.image(), attestation.as_bytes())?;
    let managed = retain_replayed_hol_proof_recipe(kernel, repl, artifact)?;
    let (artifact, receiver, retained) = managed.into_parts();
    let imported = retained.received();
    received_artifacts.insert(receiver, retained);
    let path = fresh.path().to_owned();
    fresh.commit();

    writeln!(output, "kind\tsigned-hol-proof-recipe")?;
    writeln!(output, "authority\tkernel-checked-replay")?;
    writeln!(output, "connection\t{receiver}")?;
    writeln!(output, "source_namespace\t{}", artifact.namespace_id())?;
    writeln!(output, "schema\t{}", artifact.schema())?;
    writeln!(output, "image\t{}", artifact.image_hash())?;
    writeln!(output, "signer\t{}", artifact.signer())?;
    writeln!(output, "import\t{}", imported.import_id())?;
    writeln!(output, "imported_namespace\t{}", imported.namespace_id())?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        imported.context_id(),
        imported.conclusion_id()
    )?;
    writeln!(output, "trusted_import_receipt\tretained")?;
    writeln!(output, "database\t{}", path.join("proof.sqlite").display())?;
    writeln!(
        output,
        "attestation\t{}",
        path.join("attestation.txt").display()
    )?;
    Ok(())
}

fn run_interactive_hol_proof_recipe_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    const USAGE: &str = "usage: .hol recipe FILE DIRECTORY";
    if line == ".hol recipe" {
        return Err(USAGE.into());
    }
    let Some(arguments) = line.strip_prefix(".hol recipe ") else {
        return Ok(false);
    };
    let arguments = arguments.trim();
    let split = arguments.find(char::is_whitespace).ok_or(USAGE)?;
    let recipe_file = &arguments[..split];
    let artifact_directory = arguments[split..].trim();
    if recipe_file.is_empty() || artifact_directory.is_empty() {
        return Err(USAGE.into());
    }
    replay_interactive_hol_proof_recipe(
        kernel,
        repl,
        received_artifacts,
        output,
        Path::new(recipe_file),
        Path::new(artifact_directory),
    )?;
    Ok(true)
}

fn receive_interactive_signed_artifact(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    artifact_directory: &Path,
    expected_public_key: &str,
) -> Result<()> {
    let expected_public_key = decode_expected_public_key(expected_public_key)?;
    let image = read_bounded_image(File::open(artifact_directory.join("proof.sqlite"))?)?;
    let sidecar = read_bounded_signed_artifact_sidecar(File::open(
        artifact_directory.join("attestation.txt"),
    )?)?;
    let artifact = parse_signed_hol_artifact_sidecar(image, &sidecar)?;
    // `LOCAL` is only this adapter's diagnostic routing label. Authority comes
    // exclusively from the independently supplied public key.
    let expected = ExpectedKernelIdentity::from_public_key(KernelId::LOCAL, &expected_public_key)?;
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, &artifact)?;
    let receiver = kernel.open_hol(AllowAll)?;
    let (receiver, retained) =
        trust_receive_and_retain_selected_managed_hol_artifact(repl, receiver, pinned)?;
    let imported = retained.received();
    received_artifacts.insert(receiver, retained);

    writeln!(output, "kind\treceived-signed-hol")?;
    writeln!(output, "connection\t{receiver}")?;
    writeln!(output, "source_namespace\t{}", artifact.namespace_id())?;
    writeln!(output, "schema\t{}", artifact.schema())?;
    writeln!(output, "image\t{}", artifact.image_hash())?;
    writeln!(output, "signer\t{}", artifact.signer())?;
    writeln!(output, "import\t{}", imported.import_id())?;
    writeln!(output, "imported_namespace\t{}", imported.namespace_id())?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        imported.context_id(),
        imported.conclusion_id()
    )?;
    writeln!(output, "trusted_import_receipt\tretained")?;
    Ok(())
}

fn run_interactive_receive_signed_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    const USAGE: &str = "usage: .hol receive-signed DIRECTORY EXPECTED_PUBLIC_KEY_HEX";
    if line == ".hol receive-signed" {
        return Err(USAGE.into());
    }
    let Some(arguments) = line.strip_prefix(".hol receive-signed ") else {
        return Ok(false);
    };
    let arguments = arguments.trim();
    let split = arguments.rfind(char::is_whitespace).ok_or(USAGE)?;
    let artifact_directory = arguments[..split].trim_end();
    let expected_public_key = arguments[split..].trim();
    if artifact_directory.is_empty()
        || expected_public_key.is_empty()
        || expected_public_key.contains(char::is_whitespace)
    {
        return Err(USAGE.into());
    }
    receive_interactive_signed_artifact(
        kernel,
        repl,
        received_artifacts,
        output,
        Path::new(artifact_directory),
        expected_public_key,
    )?;
    Ok(true)
}

fn run_interactive_hol_artifact_command(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    if run_interactive_hol_proof_recipe_command(kernel, repl, received_artifacts, output, line)? {
        return Ok(true);
    }
    if run_interactive_infinity_command(kernel, repl, received_artifacts, output, line)? {
        return Ok(true);
    }
    if run_interactive_natlike_missing_zero_command(kernel, repl, received_artifacts, output, line)?
    {
        return Ok(true);
    }
    run_interactive_receive_signed_command(kernel, repl, received_artifacts, output, line)
}

fn close_interactive_connection(
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    argument: Option<&str>,
) -> Result<()> {
    let id = match argument {
        Some(argument) => ConnectionId::from_u32(argument.trim().parse()?),
        None => repl.active()?.ok_or("no active connection")?,
    };
    repl.remove(id)?;
    received_artifacts.remove(&id);
    writeln!(output, "closed connection {id}")?;
    Ok(())
}

fn run_interactive_signed_round_trip(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    path: &str,
) -> Result<()> {
    let path = path.trim();
    if path.is_empty() {
        return Err("usage: .hol signed-roundtrip DIRECTORY".into());
    }
    let fresh = FreshArtifactDirectory::create(Path::new(path))?;
    let source = repl.active()?.ok_or("no active connection")?;
    let (outcome, receiver) = run_managed_signed_hol_round_trip(kernel, repl, source)?;
    print_signed_hol_outcome(output, &outcome)?;
    writeln!(output, "receiver_connection\t{receiver}")?;
    write_signed_hol_artifacts(output, fresh, &outcome)
}

fn run_line(
    kernel: &Kernel,
    repl: &mut LocalRepl,
    received_artifacts: &mut HashMap<ConnectionId, RetainedReceivedHolSnapshot>,
    output: &mut impl io::Write,
    line: &str,
) -> Result<bool> {
    let line = line.trim();
    if line.is_empty() {
        return Ok(true);
    }
    if line == ".quit" || line == ".exit" {
        return Ok(false);
    }
    if line == ".help" {
        print_help(output)?;
        return Ok(true);
    }
    if line == ".open" || line == ".open sql" {
        let id = open_sql_connection(kernel, repl)?;
        writeln!(output, "opened SQL connection {id}")?;
        return Ok(true);
    }
    if line == ".open hol" {
        let id = open_hol_connection(kernel, repl)?;
        writeln!(output, "opened HOL connection {id}")?;
        return Ok(true);
    }
    if let Some(argument) = line.strip_prefix(".use ") {
        let id = ConnectionId::from_u32(argument.trim().parse()?);
        repl.select(id)?;
        writeln!(output, "using connection {id}")?;
        return Ok(true);
    }
    if run_info_command(kernel, repl, output, line)? {
        return Ok(true);
    }
    if line == ".close" || line.starts_with(".close ") {
        close_interactive_connection(
            repl,
            received_artifacts,
            output,
            line.strip_prefix(".close "),
        )?;
        return Ok(true);
    }
    if let Some(path) = line.strip_prefix(".export ") {
        let path = path.trim();
        if path.is_empty() {
            return Err("usage: .export PATH".into());
        }
        let bytes = repl.active_mut()?.sql_mut()?.serialize_main()?;
        export_snapshot(Path::new(path), &bytes)?;
        writeln!(output, "exported {} bytes to {path}", bytes.len())?;
        return Ok(true);
    }
    if let Some(sql) = line.strip_prefix(".state ") {
        let result = repl.inspect_state(sql.trim())?;
        print_outcome(output, &Outcome::Rows(result))?;
        return Ok(true);
    }
    if line.starts_with(".load") {
        let (schema, path) = parse_load(line).ok_or("usage: .load SCHEMA PATH")?;
        load_image(repl, output, schema, path)?;
        return Ok(true);
    }
    if let Some(path) = line.strip_prefix(".hol signed-roundtrip ") {
        run_interactive_signed_round_trip(kernel, repl, output, path)?;
        return Ok(true);
    }
    #[cfg(not(target_arch = "wasm32"))]
    if let Some(arguments) = line.strip_prefix(".hol hash-wasm ") {
        run_interactive_hash_selected_wasm_hol(
            kernel,
            repl,
            received_artifacts,
            output,
            arguments,
        )?;
        return Ok(true);
    }
    if line == ".hol open-state" || line.starts_with(".hol open-state ") {
        open_interactive_trusted_state(
            repl,
            received_artifacts,
            output,
            line.strip_prefix(".hol open-state "),
        )?;
        return Ok(true);
    }
    if run_interactive_hol_artifact_command(kernel, repl, received_artifacts, output, line)? {
        return Ok(true);
    }
    if let Some(source) = line.strip_prefix(".hol ") {
        let recipe = source.parse::<HolRecipe>()?;
        let outcome = recipe.execute(repl.active_mut()?.hol_mut()?)?;
        print_hol_outcome(output, &outcome)?;
        return Ok(true);
    }
    if line.starts_with('.') {
        return Err(format!("unknown command: {line}").into());
    }

    let outcome = repl.active_mut()?.sql_mut()?.run(line, &[])?;
    print_outcome(output, &outcome)?;
    Ok(true)
}

fn run_repl(
    input: &mut impl io::BufRead,
    output: &mut impl io::Write,
    errors: &mut impl io::Write,
    prompt: bool,
) -> Result<()> {
    let kernel = Kernel::ephemeral();
    let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
    let mut received_artifacts = HashMap::new();
    open_sql_connection(&kernel, &mut repl)?;
    let mut line = String::new();
    loop {
        if prompt {
            write!(output, "nucleus> ")?;
            output.flush()?;
        }
        line.clear();
        if input.read_line(&mut line)? == 0 {
            break;
        }
        match run_line(&kernel, &mut repl, &mut received_artifacts, output, &line) {
            Ok(true) => {}
            Ok(false) => break,
            Err(error) => writeln!(errors, "error: {error}")?,
        }
    }
    Ok(())
}

fn usage(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(output, "usage: nucleus [-c SQL]")?;
    writeln!(output, "       nucleus --hol RECIPE")?;
    writeln!(output, "       nucleus --signed-hol OUTPUT-DIRECTORY")?;
    #[cfg(not(target_arch = "wasm32"))]
    writeln!(
        output,
        "       nucleus --wasm-hol COMPONENT OUTPUT-DIRECTORY"
    )?;
    #[cfg(not(target_arch = "wasm32"))]
    writeln!(
        output,
        "       nucleus --hash-wasm-hol O256 COMPONENT OUTPUT-DIRECTORY"
    )?;
    writeln!(output, "       nucleus --interkernel-hol")?;
    #[cfg(not(target_arch = "wasm32"))]
    writeln!(
        output,
        "       nucleus --kernel-http ADDRESS ALLOWED_ORIGIN"
    )?;
    #[cfg(not(target_arch = "wasm32"))]
    writeln!(
        output,
        "       nucleus --hash-wasm-hol-http O256 COMPONENT ADDRESS ALLOWED_ORIGIN"
    )?;
    writeln!(output, "       nucleus --help")?;
    writeln!(
        output,
        "O256 is: b3sum --no-names COMPONENT (64 lowercase hex characters)."
    )?;
    writeln!(
        output,
        "Hash-selected output directories must not exist; HTTP mode prints URL, key, and component coordinates."
    )?;
    writeln!(
        output,
        "ALLOWED_ORIGIN must exactly match the browser page origin; native HTTP binds loopback only."
    )
}

#[cfg(not(target_arch = "wasm32"))]
fn run_wasm_arguments(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<()> {
    let component = arguments
        .next()
        .ok_or("--wasm-hol requires COMPONENT OUTPUT-DIRECTORY")?;
    let output = arguments
        .next()
        .ok_or("--wasm-hol requires COMPONENT OUTPUT-DIRECTORY")?;
    if arguments.next().is_some() {
        return Err("unexpected arguments after --wasm-hol COMPONENT OUTPUT-DIRECTORY".into());
    }
    let kernel = Kernel::ephemeral();
    let mut directory = Repl::new(kernel.verifying_key().as_bytes())?;
    run_managed_wasm_hol(
        &mut io::stdout().lock(),
        &mut directory,
        &kernel,
        Path::new(&component),
        Path::new(&output),
    )?;
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn run_hash_selected_wasm_arguments(
    arguments: &mut impl Iterator<Item = std::ffi::OsString>,
) -> Result<()> {
    let expected = arguments
        .next()
        .ok_or("--hash-wasm-hol requires O256 COMPONENT OUTPUT-DIRECTORY")?
        .into_string()
        .map_err(|_| "component O256 must be valid UTF-8")?;
    let component = arguments
        .next()
        .ok_or("--hash-wasm-hol requires O256 COMPONENT OUTPUT-DIRECTORY")?;
    let output = arguments
        .next()
        .ok_or("--hash-wasm-hol requires O256 COMPONENT OUTPUT-DIRECTORY")?;
    if arguments.next().is_some() {
        return Err(
            "unexpected arguments after --hash-wasm-hol O256 COMPONENT OUTPUT-DIRECTORY".into(),
        );
    }
    let expected = O256::from_hex(&expected)?;
    let receiver_kernel = Kernel::ephemeral();
    let mut directory = Repl::new(receiver_kernel.verifying_key().as_bytes())?;
    run_hash_selected_wasm_hol(
        &mut io::stdout().lock(),
        &receiver_kernel,
        &mut directory,
        expected,
        Path::new(&component),
        Path::new(&output),
    )?;
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn run_kernel_http_arguments(
    arguments: &mut impl Iterator<Item = std::ffi::OsString>,
) -> Result<()> {
    let address = arguments
        .next()
        .ok_or("--kernel-http requires ADDRESS ALLOWED_ORIGIN")?
        .into_string()
        .map_err(|_| "native HTTP address must be valid UTF-8")?;
    let allowed_origin = arguments
        .next()
        .ok_or("--kernel-http requires ADDRESS ALLOWED_ORIGIN")?
        .into_string()
        .map_err(|_| "allowed origin must be valid UTF-8")?;
    if arguments.next().is_some() {
        return Err("unexpected arguments after --kernel-http ADDRESS ALLOWED_ORIGIN".into());
    }
    let server = NativeHttpKernelServer::bind(address, allowed_origin)?;
    let address = server.local_addr()?;
    let mut public_key = String::with_capacity(64);
    for byte in server.identity().public_key() {
        use std::fmt::Write as _;
        write!(public_key, "{byte:02x}")?;
    }
    let mut output = io::stdout().lock();
    writeln!(output, "url\thttp://{address}{SIGNED_KERNEL_HTTP_PATH}")?;
    writeln!(output, "public_key\t{public_key}")?;
    output.flush()?;
    drop(output);
    server.serve().map_err(Into::into)
}

#[cfg(not(target_arch = "wasm32"))]
fn run_hash_selected_wasm_http_arguments(
    arguments: &mut impl Iterator<Item = std::ffi::OsString>,
) -> Result<()> {
    let expected = arguments
        .next()
        .ok_or("--hash-wasm-hol-http requires O256 COMPONENT ADDRESS ALLOWED_ORIGIN")?
        .into_string()
        .map_err(|_| "component O256 must be valid UTF-8")?;
    let component = arguments
        .next()
        .ok_or("--hash-wasm-hol-http requires O256 COMPONENT ADDRESS ALLOWED_ORIGIN")?;
    let address = arguments
        .next()
        .ok_or("--hash-wasm-hol-http requires O256 COMPONENT ADDRESS ALLOWED_ORIGIN")?
        .into_string()
        .map_err(|_| "native HTTP address must be valid UTF-8")?;
    let allowed_origin = arguments
        .next()
        .ok_or("--hash-wasm-hol-http requires O256 COMPONENT ADDRESS ALLOWED_ORIGIN")?
        .into_string()
        .map_err(|_| "allowed origin must be valid UTF-8")?;
    if arguments.next().is_some() {
        return Err(
            "unexpected arguments after --hash-wasm-hol-http O256 COMPONENT ADDRESS ALLOWED_ORIGIN"
                .into(),
        );
    }

    // The allowlist is fully bounded, hash-checked, validated, and compiled
    // before the signed service or any session exists. This remains the
    // same-process Wasmtime/JIT prototype tracked in #320.
    let expected = O256::from_hex(&expected)?;
    let limits = WasmtimeComponentLimits::default();
    let bytes = read_bounded_component(Path::new(&component), limits.component_bytes)?;
    let prepared = PreparedHolProofComponent::prepare(expected, &bytes, limits)?;
    let mut executor = PrecompiledHolProofComponentExecutor::new();
    executor.insert(prepared)?;
    let server =
        NativeHttpKernelServer::bind_with_hol_proof_components(address, allowed_origin, executor)?;
    let address = server.local_addr()?;
    let mut public_key = String::with_capacity(64);
    for byte in server.identity().public_key() {
        use std::fmt::Write as _;
        write!(public_key, "{byte:02x}")?;
    }
    let mut output = io::stdout().lock();
    writeln!(output, "url\thttp://{address}{SIGNED_KERNEL_HTTP_PATH}")?;
    writeln!(output, "public_key\t{public_key}")?;
    writeln!(output, "component\t{expected}")?;
    output.flush()?;
    drop(output);
    server.serve().map_err(Into::into)
}

fn run() -> Result<()> {
    let mut arguments = env::args_os().skip(1);
    match arguments.next() {
        None => run_repl(
            &mut io::stdin().lock(),
            &mut io::stdout().lock(),
            &mut io::stderr().lock(),
            true,
        ),
        Some(flag) if flag == "-c" => {
            let sql = arguments
                .next()
                .ok_or("-c requires one SQL statement")?
                .into_string()
                .map_err(|_| "SQL statement must be valid UTF-8")?;
            if arguments.next().is_some() {
                return Err("unexpected arguments after SQL statement".into());
            }
            let kernel = Kernel::ephemeral();
            let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
            open_sql_connection(&kernel, &mut repl)?;
            let outcome = repl.active_mut()?.sql_mut()?.run(&sql, &[])?;
            print_outcome(&mut io::stdout().lock(), &outcome)?;
            Ok(())
        }
        Some(flag) if flag == "--hol" => {
            let source = arguments
                .next()
                .ok_or("--hol requires one recipe")?
                .into_string()
                .map_err(|_| "HOL recipe must be valid UTF-8")?;
            if arguments.next().is_some() {
                return Err("unexpected arguments after HOL recipe".into());
            }
            let kernel = Kernel::ephemeral();
            let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
            open_hol_connection(&kernel, &mut repl)?;
            let outcome = source
                .parse::<HolRecipe>()?
                .execute(repl.active_mut()?.hol_mut()?)?;
            print_hol_outcome(&mut io::stdout().lock(), &outcome)?;
            Ok(())
        }
        Some(flag) if flag == "--signed-hol" => {
            let path = arguments
                .next()
                .ok_or("--signed-hol requires OUTPUT-DIRECTORY")?;
            if arguments.next().is_some() {
                return Err("unexpected arguments after signed HOL path".into());
            }
            let kernel = Kernel::ephemeral();
            let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
            open_hol_connection(&kernel, &mut repl)?;
            let fresh = FreshArtifactDirectory::create(Path::new(&path))?;
            let source = repl.active()?.ok_or("no active connection")?;
            let (outcome, receiver) =
                run_managed_signed_hol_round_trip(&kernel, &mut repl, source)?;
            print_signed_hol_outcome(&mut io::stdout().lock(), &outcome)?;
            writeln!(io::stdout().lock(), "receiver_connection\t{receiver}")?;
            write_signed_hol_artifacts(&mut io::stdout().lock(), fresh, &outcome)
        }
        #[cfg(not(target_arch = "wasm32"))]
        Some(flag) if flag == "--wasm-hol" => run_wasm_arguments(&mut arguments),
        #[cfg(not(target_arch = "wasm32"))]
        Some(flag) if flag == "--hash-wasm-hol" => run_hash_selected_wasm_arguments(&mut arguments),
        Some(flag) if flag == "--interkernel-hol" => {
            if arguments.next().is_some() {
                return Err("unexpected arguments after --interkernel-hol".into());
            }
            run_interkernel_hol(&mut io::stdout().lock())
        }
        #[cfg(not(target_arch = "wasm32"))]
        Some(flag) if flag == "--kernel-http" => run_kernel_http_arguments(&mut arguments),
        #[cfg(not(target_arch = "wasm32"))]
        Some(flag) if flag == "--hash-wasm-hol-http" => {
            run_hash_selected_wasm_http_arguments(&mut arguments)
        }
        Some(flag) if flag == "-h" || flag == "--help" => {
            usage(&mut io::stdout().lock())?;
            Ok(())
        }
        Some(argument) => {
            Err(format!("unexpected argument: {}", argument.to_string_lossy()).into())
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, ErrorKind};
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use covalence_repl::{Connection, Sql};

    const CLOSED_BETA_RECIPE: &[u8] = &[
        6, 0, 11, 0, 8, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 1, 4, 53, 0, 2, 0, 3, 56, 0, 4,
        0, 5, 6, 0, 6, 7, 1, 0, 4, 100, 101, 109, 111, 9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 8,
        0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0,
    ];

    static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

    fn temporary_file(stem: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "nucleus-{stem}-{}",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ))
    }

    fn contains_imported_theorem(output: &str) -> bool {
        output.lines().any(|line| {
            line.strip_prefix("imported_theorem\t")
                .and_then(|coordinates| coordinates.split_once('\t'))
                .is_some_and(|(context, conclusion)| {
                    context.parse::<i64>().is_ok_and(|id| id >= 0)
                        && conclusion.parse::<i64>().is_ok_and(|id| id > 0)
                })
        })
    }

    fn bytes_hex(bytes: &[u8]) -> String {
        use std::fmt::Write as _;
        let mut encoded = String::with_capacity(bytes.len() * 2);
        for byte in bytes {
            write!(encoded, "{byte:02x}").unwrap();
        }
        encoded
    }

    fn signed_hol_directory(stem: &str) -> (PathBuf, String, Vec<u8>, String) {
        let producer = Kernel::ephemeral();
        let mut source = producer.open_hol(AllowAll).unwrap();
        let bundle = produce_signed_hol_artifact(&producer, &mut source).unwrap();
        let image = bundle.artifact().image().to_vec();
        let sidecar = bundle.artifact().attestation_text();
        let public_key = bytes_hex(producer.verifying_key().as_bytes());
        let path = temporary_file(stem);
        fs::create_dir(&path).unwrap();
        fs::write(path.join("proof.sqlite"), &image).unwrap();
        fs::write(path.join("attestation.txt"), &sidecar).unwrap();
        (path, public_key, image, sidecar)
    }

    fn signed_missing_zero_directory(stem: &str) -> (PathBuf, String, i64, i64) {
        let producer = Kernel::ephemeral();
        let theorem = produce_signed_natlike_missing_zero(&producer).unwrap();
        let public_key = bytes_hex(producer.verifying_key().as_bytes());
        let path = temporary_file(stem);
        fs::create_dir(&path).unwrap();
        fs::write(path.join("proof.sqlite"), theorem.artifact().image()).unwrap();
        fs::write(path.join("attestation.txt"), theorem.attestation_text()).unwrap();
        (
            path,
            public_key,
            theorem.context().get(),
            theorem.conclusion().get(),
        )
    }

    fn remove_signed_hol_directory(path: &Path) {
        fs::remove_file(path.join("proof.sqlite")).unwrap();
        fs::remove_file(path.join("attestation.txt")).unwrap();
        fs::remove_dir(path).unwrap();
    }

    struct GrowingImage {
        remaining: usize,
    }

    impl io::Read for GrowingImage {
        fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
            let count = buffer.len().min(self.remaining);
            buffer[..count].fill(0);
            self.remaining -= count;
            Ok(count)
        }
    }

    #[test]
    fn runs_sql_until_quit() {
        let mut input = Cursor::new(
            "CREATE TABLE t(x INTEGER)\nINSERT INTO t VALUES (42)\nSELECT x AS answer FROM t\n.quit\nSELECT 0\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("changed 0\n"));
        assert!(output.contains("changed 1\n"));
        assert!(output.contains("answer\n42\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn manages_independent_connections_like_the_browser_repl() {
        let mut input = Cursor::new(
            "CREATE TABLE first(value INTEGER)\nINSERT INTO first VALUES (42)\n.open\nSELECT count(*) AS absent FROM sqlite_schema WHERE name = 'first'\n.use 1\nSELECT value FROM first\n.connections\n.close 2\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("opened SQL connection 2\n"));
        assert!(output.contains("absent\n0\n"));
        assert!(output.contains("using connection 1\n"));
        assert!(output.contains("value\n42\n"));
        assert!(output.contains("* 1\tnucleus/sql\n"));
        assert!(output.contains("  2\tnucleus/sql\n"));
        assert!(output.contains("closed connection 2\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn signed_infinity_command_dumps_then_opens_assumed_state() {
        let path = temporary_file("signed-infinity");
        let script = format!(
            ".hol assume-infinity {}\n.hol open-state\n.hol assume-infinity {}\n.hol truth\n.quit\n",
            path.display(),
            path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let image = fs::read(path.join("proof.sqlite")).unwrap();
        assert!(!image.is_empty());
        let attestation = fs::read_to_string(path.join("attestation.txt")).unwrap();
        assert!(attestation.starts_with("authority=signed-assumption\n"));
        assert!(attestation.contains("assumption=dedekind-infinity\n"));
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\tsigned-assumption\n"));
        assert!(output.contains("authority\tsigned-assumption\n"));
        assert!(output.contains("falsehood\tall-bool-identity\n"));
        assert!(output.contains("kind\ttrusted-hol-state\n"));
        assert!(output.contains("statement\ttrue\n"));
        let errors = String::from_utf8(errors).unwrap();
        assert!(errors.contains("File exists"));

        fs::remove_file(path.join("proof.sqlite")).unwrap();
        fs::remove_file(path.join("attestation.txt")).unwrap();
        fs::remove_dir(path).unwrap();
    }

    #[test]
    fn signed_natlike_missing_zero_command_dumps_retains_and_opens_state() {
        let path = temporary_file("signed-natlike-missing-zero");
        let script = format!(
            ".hol natlike-missing-zero {}\n.hol open-state\n.hol truth\n.quit\n",
            path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let image = fs::read(path.join("proof.sqlite")).unwrap();
        assert!(!image.is_empty());
        let attestation = fs::read_to_string(path.join("attestation.txt")).unwrap();
        assert!(attestation.starts_with("authority=kernel-derived-theorem\n"));
        assert!(attestation.contains("theorem=natlike-missing-zero\n"));
        assert!(attestation.contains("theorem-oracle=(APP missing zero)\n"));
        assert!(attestation.contains("intermediate-persistence=none\n"));
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\tsigned-natlike-missing-zero\n"));
        assert!(output.contains("authority\tkernel-derived-theorem\n"));
        assert!(output.contains("theorem\tnatlike-missing-zero\n"));
        assert!(output.contains("trusted_import_receipt\tretained\n"));
        assert!(output.contains("kind\ttrusted-hol-state\n"));
        assert!(output.contains("statement\ttrue\n"));
        assert!(errors.is_empty());

        fs::remove_file(path.join("proof.sqlite")).unwrap();
        fs::remove_file(path.join("attestation.txt")).unwrap();
        fs::remove_dir(path).unwrap();
    }

    #[test]
    fn sealed_recipe_command_replays_dumps_retains_and_opens_state() {
        let recipe_path = temporary_file("closed-beta-recipe");
        let output_path = temporary_file("closed-beta-recipe-artifact");
        fs::write(&recipe_path, CLOSED_BETA_RECIPE).unwrap();
        let script = format!(
            ".hol recipe {} {}\n.hol open-state\n.hol truth\n.quit\n",
            recipe_path.display(),
            output_path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let image = fs::read(output_path.join("proof.sqlite")).unwrap();
        let sidecar = fs::read(output_path.join("attestation.txt")).unwrap();
        let artifact = parse_signed_hol_artifact_sidecar(image, &sidecar).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\tsigned-hol-proof-recipe\n"));
        assert!(output.contains("authority\tkernel-checked-replay\n"));
        assert!(output.contains("trusted_import_receipt\tretained\n"));
        assert!(contains_imported_theorem(&output));
        assert!(output.contains("kind\ttrusted-hol-state\n"));
        assert!(output.contains("statement\ttrue\n"));
        assert_eq!(artifact.namespace_id().to_string(), "1");
        assert!(errors.is_empty());

        fs::remove_file(recipe_path).unwrap();
        remove_signed_hol_directory(&output_path);
    }

    #[test]
    fn sealed_recipe_rejections_preserve_selection_receipts_and_output() {
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let original = open_sql_connection(&kernel, &mut repl).unwrap();
        let mut retained = HashMap::new();
        let mut output = Vec::new();
        let canonical = CLOSED_BETA_RECIPE.to_vec();

        for (name, bytes) in [
            ("malformed", vec![0xff]),
            ("trailing", {
                let mut bytes = canonical.clone();
                bytes.push(0);
                bytes
            }),
            ("policy-denied-version", {
                let mut bytes = canonical.clone();
                bytes[0] = bytes[0].wrapping_sub(1);
                bytes
            }),
        ] {
            let recipe_path = temporary_file(name);
            let artifact_path = temporary_file(&format!("{name}-artifact"));
            fs::write(&recipe_path, bytes).unwrap();
            assert!(
                replay_interactive_hol_proof_recipe(
                    &kernel,
                    &mut repl,
                    &mut retained,
                    &mut output,
                    &recipe_path,
                    &artifact_path,
                )
                .is_err()
            );
            assert!(!artifact_path.exists());
            fs::remove_file(recipe_path).unwrap();
        }

        let recipe_path = temporary_file("existing-output-recipe");
        let artifact_path = temporary_file("existing-output-artifact");
        fs::write(&recipe_path, &canonical).unwrap();
        fs::create_dir(&artifact_path).unwrap();
        assert!(
            replay_interactive_hol_proof_recipe(
                &kernel,
                &mut repl,
                &mut retained,
                &mut output,
                &recipe_path,
                &artifact_path,
            )
            .is_err()
        );

        assert_eq!(repl.active().unwrap(), Some(original));
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        assert!(retained.is_empty());
        assert!(output.is_empty());

        fs::remove_file(recipe_path).unwrap();
        fs::remove_dir(artifact_path).unwrap();
    }

    #[test]
    fn sealed_recipe_reader_refuses_oversized_input() {
        let error = read_bounded_hol_proof_recipe(GrowingImage {
            remaining: MAX_SEALED_HOL_RECIPE_BYTES + 1,
        })
        .unwrap_err();
        assert!(error.to_string().contains("exceeds"));
    }

    #[test]
    fn kernel_identity_is_the_public_key_which_signs_same_session_export() {
        let path = temporary_file("kernel-identity-signed-natlike-missing-zero");
        let script = format!(
            ".kernel identity\n.hol natlike-missing-zero {}\n.quit\n",
            path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        let mut identity_record = output
            .lines()
            .skip_while(|line| *line != "kind\tkernel-identity");
        assert_eq!(identity_record.next(), Some("kind\tkernel-identity"));
        let signer_line = identity_record.next().expect("public identity signer");
        let public_key_hex = identity_record
            .next()
            .and_then(|line| line.strip_prefix("public_key\t"))
            .expect("public identity key");
        let public_key = decode_expected_public_key(public_key_hex).unwrap();
        let expected =
            ExpectedKernelIdentity::from_public_key(KernelId::LOCAL, &public_key).unwrap();
        assert_eq!(signer_line, format!("signer\t{}", expected.signer()));
        assert!(!output.contains("secret"));
        assert!(!output.contains("private_key"));

        let image = fs::read(path.join("proof.sqlite")).unwrap();
        let sidecar = fs::read(path.join("attestation.txt")).unwrap();
        let artifact = parse_signed_hol_artifact_sidecar(image, &sidecar).unwrap();
        assert_eq!(artifact.public_key(), public_key);
        authenticate_pinned_signed_hol_artifact(&expected, &artifact)
            .expect("same-session identity authenticates export");
        assert!(errors.is_empty());

        fs::remove_file(path.join("proof.sqlite")).unwrap();
        fs::remove_file(path.join("attestation.txt")).unwrap();
        fs::remove_dir(path).unwrap();
    }

    #[test]
    fn receive_signed_command_pins_retains_selects_and_opens_state() {
        let (path, expected_public_key, context, conclusion) =
            signed_missing_zero_directory("receive-signed-missing-zero");
        let script = format!(
            ".hol receive-signed {} {}\n.hol open-state\n.hol truth\n.quit\n",
            path.display(),
            expected_public_key
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\treceived-signed-hol\n"));
        assert!(output.contains("trusted_import_receipt\tretained\n"));
        assert!(output.contains(&format!("imported_theorem\t{context}\t{conclusion}\n")));
        assert!(output.contains("kind\ttrusted-hol-state\n"));
        assert!(output.contains(&format!("trusted_theorem\t{context}\t{conclusion}\n")));
        assert!(output.contains("statement\ttrue\n"));
        assert!(errors.is_empty());
        remove_signed_hol_directory(&path);
    }

    #[test]
    fn receive_signed_rejections_leave_directory_state_unchanged() {
        let (path, expected_public_key, image, sidecar) =
            signed_hol_directory("receive-signed-rejections");
        let receiver = Kernel::ephemeral();
        let wrong_public_key = bytes_hex(receiver.verifying_key().as_bytes());
        let mut repl = Repl::new(receiver.verifying_key().as_bytes()).unwrap();
        let original = open_sql_connection(&receiver, &mut repl).unwrap();
        let mut retained = HashMap::new();
        let mut output = Vec::new();
        let command = |key: &str| format!(".hol receive-signed {} {key}", path.display());

        assert!(
            run_line(
                &receiver,
                &mut repl,
                &mut retained,
                &mut output,
                &command(&wrong_public_key),
            )
            .is_err()
        );

        let mut tampered = image.clone();
        tampered[0] ^= 1;
        fs::write(path.join("proof.sqlite"), tampered).unwrap();
        assert!(
            run_line(
                &receiver,
                &mut repl,
                &mut retained,
                &mut output,
                &command(&expected_public_key),
            )
            .is_err()
        );
        fs::write(path.join("proof.sqlite"), &image).unwrap();

        let duplicate = format!("schema={}\n{sidecar}", "00".repeat(32));
        fs::write(path.join("attestation.txt"), duplicate).unwrap();
        assert!(
            run_line(
                &receiver,
                &mut repl,
                &mut retained,
                &mut output,
                &command(&expected_public_key),
            )
            .is_err()
        );

        fs::write(path.join("attestation.txt"), sidecar.trim_end_matches('\n')).unwrap();
        assert!(
            run_line(
                &receiver,
                &mut repl,
                &mut retained,
                &mut output,
                &command(&expected_public_key),
            )
            .is_err()
        );

        let untrusted_key = sidecar.replace(
            &format!("public_key={expected_public_key}"),
            &format!("public_key={wrong_public_key}"),
        );
        fs::write(path.join("attestation.txt"), untrusted_key).unwrap();
        assert!(
            run_line(
                &receiver,
                &mut repl,
                &mut retained,
                &mut output,
                &command(&expected_public_key),
            )
            .is_err()
        );

        assert_eq!(repl.active().unwrap(), Some(original));
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        assert!(retained.is_empty());
        assert!(output.is_empty());
        fs::write(path.join("attestation.txt"), sidecar).unwrap();
        remove_signed_hol_directory(&path);
    }

    #[test]
    fn missing_zero_write_failure_leaves_no_receiver_or_receipt() {
        let path = temporary_file("signed-natlike-missing-zero-write-failure");
        let blocker_path = path.clone();
        let blocker = std::thread::spawn(move || {
            while !blocker_path.is_dir() {
                std::thread::yield_now();
            }
            fs::create_dir(blocker_path.join("proof.sqlite")).unwrap();
        });
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let original = open_sql_connection(&kernel, &mut repl).unwrap();
        let mut retained = HashMap::new();
        let mut output = Vec::new();

        let error = derive_interactive_natlike_missing_zero(
            &kernel,
            &mut repl,
            &mut retained,
            &mut output,
            &path,
        )
        .unwrap_err();
        blocker.join().unwrap();

        let error = error.downcast::<io::Error>().unwrap();
        assert!(matches!(
            error.kind(),
            ErrorKind::AlreadyExists | ErrorKind::IsADirectory
        ));
        assert_eq!(repl.active().unwrap(), Some(original));
        assert!(retained.is_empty());
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        assert!(output.is_empty());
        assert!(path.join("proof.sqlite").is_dir());
        assert!(!path.join("attestation.txt").exists());

        fs::remove_dir(path.join("proof.sqlite")).unwrap();
        fs::remove_dir(path).unwrap();
    }

    #[test]
    fn exports_and_reloads_the_main_snapshot() {
        let path = temporary_file("export.sqlite");

        let script = format!(
            "CREATE TABLE example(value TEXT)\nINSERT INTO example VALUES ('roundtrip')\n.export {path}\n.open\n.load library {path}\nSELECT value FROM library.example\n.quit\n",
            path = path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();
        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");
        fs::remove_file(path).expect("remove exported snapshot");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("exported "));
        assert!(output.contains("attached library"));
        assert!(output.contains("value\n\"roundtrip\"\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn rejects_a_stream_which_grows_past_the_image_bound() {
        let error = read_bounded_image(GrowingImage {
            remaining: MAX_IMAGE_BYTES + 1,
        })
        .expect_err("reject sentinel byte");
        assert!(error.to_string().contains("exceeds"));
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn bounded_component_reader_consumes_only_one_sentinel_byte() {
        let error = read_bounded_component_from(GrowingImage { remaining: 17 }, 16)
            .expect_err("reject sentinel byte");
        assert!(error.to_string().contains("16-byte pre-compilation limit"));
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn configured_real_component_uses_caller_state_and_refuses_overwrite() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_GUEST_COMPONENT") else {
            return;
        };
        let output_path = std::env::temp_dir().join(format!(
            "nucleus-managed-guest-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let mut output = Vec::new();
        let managed = run_managed_wasm_hol(
            &mut output,
            &mut directory,
            &kernel,
            Path::new(&component),
            &output_path,
        )
        .unwrap();

        let image_path = output_path.join("proof.sqlite");
        let attestation_path = output_path.join("attestation.txt");
        let image = fs::read(&image_path).unwrap();
        let attestation = fs::read_to_string(&attestation_path).unwrap();
        assert!(!image.is_empty());
        assert!(attestation.contains("format=covalence-repl-signed-snapshot-demo-v0"));
        assert!(
            directory
                .get_mut(managed.connection())
                .unwrap()
                .hol_mut()
                .is_ok()
        );
        assert_eq!(
            directory
                .inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );

        let mut second_output = Vec::new();
        assert!(
            run_managed_wasm_hol(
                &mut second_output,
                &mut directory,
                &kernel,
                Path::new(&component),
                &output_path,
            )
            .is_err()
        );
        assert_eq!(fs::read(&image_path).unwrap(), image);
        assert_eq!(
            directory
                .inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        fs::remove_file(image_path).unwrap();
        fs::remove_file(attestation_path).unwrap();
        fs::remove_dir(output_path).unwrap();

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\tmanaged-wasm-hol\n"));
        assert!(contains_imported_theorem(&output));
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn configured_real_component_runs_through_hash_selected_signed_service() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_GUEST_COMPONENT") else {
            return;
        };
        let bytes = fs::read(&component).unwrap();
        let digest = O256::from_bytes(&bytes);
        let output_path = std::env::temp_dir().join(format!(
            "nucleus-hash-guest-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let mut output = Vec::new();
        let receiver_kernel = Kernel::ephemeral();
        let mut directory = Repl::new(receiver_kernel.verifying_key().as_bytes()).unwrap();
        let (connection, expected_endpoint, artifact, first_read, _retained) =
            run_hash_selected_wasm_hol(
                &mut output,
                &receiver_kernel,
                &mut directory,
                digest,
                Path::new(&component),
                &output_path,
            )
            .unwrap();
        assert_eq!(connection, ConnectionId::from_u32(1));
        let pinned =
            authenticate_pinned_signed_hol_artifact(&expected_endpoint, &artifact).unwrap();
        let reread = trust_and_receive_pinned_signed_hol_artifact(
            directory.get_mut(connection).unwrap().hol_mut().unwrap(),
            pinned,
        )
        .unwrap();
        assert_eq!(
            (reread.context_id(), reread.conclusion_id()),
            (first_read.context_id(), first_read.conclusion_id())
        );
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\thash-selected-wasm-hol\n"));
        assert!(output.contains(&format!("component\t{digest}\n")));
        assert!(contains_imported_theorem(&output));
        fs::remove_file(output_path.join("proof.sqlite")).unwrap();
        fs::remove_file(output_path.join("attestation.txt")).unwrap();
        fs::remove_dir(output_path).unwrap();
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn interactive_hash_selected_command_retains_and_selects_receiver() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_GUEST_COMPONENT") else {
            return;
        };
        let digest = O256::from_bytes(fs::read(&component).unwrap());
        let output_path = std::env::temp_dir().join(format!(
            "nucleus-interactive-hash-guest-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let mut output = Vec::new();
        let command = format!(
            ".hol hash-wasm {digest} {} {}",
            Path::new(&component).display(),
            output_path.display()
        );

        let mut received_artifacts = HashMap::new();
        assert!(
            run_line(
                &kernel,
                &mut repl,
                &mut received_artifacts,
                &mut output,
                &command,
            )
            .unwrap()
        );
        let receiver = repl.active().unwrap().expect("selected receiver");
        assert!(repl.get_mut(receiver).unwrap().hol_mut().is_ok());
        assert_eq!(
            repl.inspect_state(
                "SELECT protocol, remote_connection_id FROM repl_connection WHERE connection_id = 1"
            )
            .unwrap()
            .rows,
            [[Value::Text("nucleus/hol".to_owned()), Value::Null]]
        );
        let open_command = format!(".hol open-state {receiver}");
        assert!(
            run_line(
                &kernel,
                &mut repl,
                &mut received_artifacts,
                &mut output,
                &open_command,
            )
            .unwrap()
        );
        let child = repl.active().unwrap().expect("selected trusted child");
        assert_ne!(child, receiver);
        assert!(repl.get_mut(child).unwrap().hol_mut().is_ok());
        assert!(
            run_line(
                &kernel,
                &mut repl,
                &mut received_artifacts,
                &mut output,
                &format!(".close {receiver}"),
            )
            .unwrap()
        );
        assert!(
            run_line(
                &kernel,
                &mut repl,
                &mut received_artifacts,
                &mut output,
                ".hol truth",
            )
            .unwrap()
        );
        assert!(
            run_line(
                &kernel,
                &mut repl,
                &mut received_artifacts,
                &mut output,
                &format!(".hol open-state {receiver}"),
            )
            .is_err()
        );
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains(&format!("component\t{digest}\n")));
        assert!(contains_imported_theorem(&output));
        assert!(output.contains(&format!("using receiver connection {receiver}\n")));
        assert!(output.contains("kind\ttrusted-hol-state\n"));

        fs::remove_file(output_path.join("proof.sqlite")).unwrap();
        fs::remove_file(output_path.join("attestation.txt")).unwrap();
        fs::remove_dir(output_path).unwrap();
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn hash_selected_cli_rejects_hash_and_compile_before_output_reservation() {
        let component = temporary_file("invalid-component.wasm");
        let output_path = temporary_file("invalid-component-output");
        let bytes = b"not a WebAssembly component";
        fs::write(&component, bytes).unwrap();

        let mut output = Vec::new();
        let receiver_kernel = Kernel::ephemeral();
        let mut directory = Repl::new(receiver_kernel.verifying_key().as_bytes()).unwrap();
        assert!(
            run_hash_selected_wasm_hol(
                &mut output,
                &receiver_kernel,
                &mut directory,
                O256::from_bytes(b"different bytes"),
                &component,
                &output_path,
            )
            .is_err()
        );
        assert!(!output_path.exists());

        assert!(
            run_hash_selected_wasm_hol(
                &mut output,
                &receiver_kernel,
                &mut directory,
                O256::from_bytes(bytes),
                &component,
                &output_path,
            )
            .is_err()
        );
        assert!(!output_path.exists());
        assert!(output.is_empty());
        fs::remove_file(component).unwrap();
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn hash_selected_http_rejects_wrong_bytes_before_service_or_socket() {
        let Some(component) = std::env::var_os("COVALENCE_HOL_GUEST_COMPONENT") else {
            return;
        };
        let arguments = [
            std::ffi::OsString::from(O256::from_bytes(b"wrong component").to_string()),
            component,
            std::ffi::OsString::from("127.0.0.1:0"),
            std::ffi::OsString::from("https://repl.example"),
        ];
        let error = run_hash_selected_wasm_http_arguments(&mut arguments.into_iter()).unwrap_err();
        assert!(error.to_string().contains("hash"));
    }

    #[test]
    fn export_never_replaces_an_existing_file() {
        let path = temporary_file("existing.sqlite");
        fs::write(&path, b"keep me").expect("create existing file");

        let error = export_snapshot(&path, b"replacement").expect_err("reject existing target");

        assert_eq!(error.kind(), ErrorKind::AlreadyExists);
        assert_eq!(fs::read(&path).expect("read existing file"), b"keep me");
        fs::remove_file(path).expect("remove existing file");
    }

    #[test]
    fn failed_export_removes_only_the_file_it_created() {
        let path = temporary_file("partial.sqlite");
        let error = write_new_file(&path, |file| {
            file.write_all(b"partial")?;
            Err(io::Error::other("simulated write failure"))
        })
        .expect_err("surface write failure");

        assert_eq!(error.to_string(), "simulated write failure");
        assert!(!path.exists());
    }

    #[test]
    fn shares_hol_recipes_across_multiple_protocol_connections() {
        let mut input = Cursor::new(
            ".open hol\n.hol beta true\n.open sql\nSELECT 7 AS sql_only\n.use 2\n.hol reflexivity false\n.connections\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("opened HOL connection 2\n"));
        assert!(output.contains("recipe\tbeta\n"));
        assert!(output.contains("statement\t(lambda x:bool. x) true = true\n"));
        assert!(output.contains("opened SQL connection 3\n"));
        assert!(output.contains("sql_only\n7\n"));
        assert!(output.contains("recipe\treflexivity\n"));
        assert!(output.contains("statement\tfalse = false\n"));
        assert!(output.contains("  1\tnucleus/sql\n"));
        assert!(output.contains("* 2\tnucleus/hol\n"));
        assert!(output.contains("  3\tnucleus/sql\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn exports_the_same_signed_round_trip_available_to_the_browser() {
        let directory = std::env::temp_dir().join(format!(
            "nucleus-signed-hol-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let mut input = Cursor::new(format!(
            ".open hol\n.hol signed-roundtrip {}\n.quit\n",
            directory.display()
        ));
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let image_path = directory.join("proof.sqlite");
        let attestation_path = directory.join("attestation.txt");
        let image = fs::read(&image_path).expect("read signed image");
        let sidecar = fs::read_to_string(&attestation_path).expect("read attestation");
        fs::remove_file(image_path).expect("remove signed image");
        fs::remove_file(attestation_path).expect("remove attestation");
        fs::remove_dir(directory).expect("remove artifact directory");
        let output = String::from_utf8(output).unwrap();
        assert!(!image.is_empty());
        assert!(sidecar.contains("format=covalence-repl-signed-snapshot-demo-v0"));
        assert!(sidecar.contains("namespace=1\n"));
        assert!(output.contains("kind\tsigned-hol-round-trip\n"));
        assert!(output.contains("proof-persisted"));
        assert!(output.contains("theorem-read"));
        assert!(output.contains("statement\t(lambda x:bool. x) true = true\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn signed_artifact_pair_is_fresh_and_rolls_back_second_file_failure() {
        let output_path = std::env::temp_dir().join(format!(
            "nucleus-artifact-rollback-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let mut fresh = FreshArtifactDirectory::create(&output_path).unwrap();
        fresh.write_owned("proof.sqlite", b"image").unwrap();
        fs::write(output_path.join("attestation.txt"), b"concurrent owner").unwrap();
        assert_eq!(
            fresh
                .write_owned("attestation.txt", b"attestation")
                .unwrap_err()
                .kind(),
            io::ErrorKind::AlreadyExists
        );
        drop(fresh);
        assert!(!output_path.join("proof.sqlite").exists());
        assert_eq!(
            fs::read(output_path.join("attestation.txt")).unwrap(),
            b"concurrent owner"
        );
        fs::remove_file(output_path.join("attestation.txt")).unwrap();
        fs::remove_dir(&output_path).unwrap();

        fs::create_dir(&output_path).unwrap();
        fs::write(output_path.join("user-data"), b"keep").unwrap();
        assert!(FreshArtifactDirectory::create(&output_path).is_err());
        assert_eq!(fs::read(output_path.join("user-data")).unwrap(), b"keep");
        fs::remove_file(output_path.join("user-data")).unwrap();
        fs::remove_dir(output_path).unwrap();
    }

    #[test]
    fn signed_command_rejects_an_existing_directory_before_mutating_kernel_state() {
        let output_path = std::env::temp_dir().join(format!(
            "nucleus-existing-artifact-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&output_path).unwrap();
        fs::write(output_path.join("user-data"), b"keep").unwrap();
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let source = open_hol_connection(&kernel, &mut repl).unwrap();
        let mut output = Vec::new();
        let mut received_artifacts = HashMap::new();

        let error = run_line(
            &kernel,
            &mut repl,
            &mut received_artifacts,
            &mut output,
            &format!(".hol signed-roundtrip {}", output_path.display()),
        )
        .unwrap_err();

        assert!(error.to_string().contains("File exists"));
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        assert!(
            !repl
                .get_mut(source)
                .unwrap()
                .hol_mut()
                .unwrap()
                .proved_judgement(
                    covalence_repl::ContextId::empty(),
                    covalence_repl::TermId::from_i64(8),
                )
                .unwrap_or(false)
        );
        assert_eq!(fs::read(output_path.join("user-data")).unwrap(), b"keep");
        fs::remove_file(output_path.join("user-data")).unwrap();
        fs::remove_dir(output_path).unwrap();
    }

    #[test]
    fn transfers_a_signed_theorem_between_registered_local_kernels() {
        let mut output = Vec::new();
        run_interkernel_hol(&mut output).expect("run inter-kernel demo");
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("producer_kernel\t1\n"));
        assert!(output.contains("receiver_kernel\t2\n"));
        assert!(output.contains("connections\t2\n"));
        assert!(output.contains(
            "receiver_phases\timage-size-checked,signature-authenticated,signer-pinned,image-detached-validated,signer-trusted,snapshot-accepted,namespace-imported,theorem-read\n"
        ));
        assert!(output.contains("imported_theorem\t0\t8\n"));
    }

    #[test]
    fn inspects_the_directory_as_sqlite() {
        let mut input = Cursor::new(
            ".open\n.state SELECT connection_id, protocol FROM repl_connection ORDER BY connection_id\n.state DELETE FROM repl_connection\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();
        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(
            output.contains("connection_id\tprotocol\n1\t\"nucleus/sql\"\n2\t\"nucleus/sql\"\n")
        );
        assert!(
            String::from_utf8(errors)
                .unwrap()
                .contains("state inspection statements must return rows")
        );
    }

    #[test]
    fn loads_a_complete_immutable_image() {
        let mut source = Connection::<Sql>::open_in_memory().expect("open source");
        source
            .execute_batch("CREATE TABLE example(value TEXT); INSERT INTO example VALUES ('ok');")
            .expect("populate source");
        let image = source.serialize_main().expect("serialize source");
        let path = temporary_file("repl.sqlite");
        fs::write(&path, image).expect("write image");

        let script = format!(
            ".load library {}\nSELECT value FROM library.example\nINSERT INTO library.example VALUES ('no')\n.quit\n",
            path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();
        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");
        fs::remove_file(path).expect("remove image");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("attached library"));
        assert!(output.contains("value\n\"ok\"\n"));
        assert!(
            String::from_utf8(errors)
                .unwrap()
                .contains("attempt to write a readonly database")
        );
    }
}
