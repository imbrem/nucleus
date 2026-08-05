use std::env;
use std::error::Error;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use covalence_repl::{
    AllowAll, ConnectionId, HolRecipe, HolRecipeResult, Kernel, LocalConnection, MAX_IMAGE_BYTES,
    Outcome, Repl, SignedHolRoundTripResult, Value, authenticate_pinned_signed_hol_artifact,
    produce_signed_hol_artifact, run_managed_signed_hol_round_trip,
    trust_and_receive_pinned_signed_hol_artifact,
};
#[cfg(not(target_arch = "wasm32"))]
use covalence_repl::{
    ExpectedKernelIdentity, KernelId, ManagedHolGuestResult, O256,
    PrecompiledHolProofComponentExecutor, PreparedHolProofComponent, ReceivedHolSnapshot,
    ServiceOperation, ServiceResult, SessionInitiator, SignedHolArtifact, SignedKernelService,
    WasmtimeComponentLimits, retain_signed_hol_guest_artifact, run_hol_proof_component,
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
    let mut receiver = receiver_kernel.open_hol(AllowAll)?;
    let first_read = trust_and_receive_pinned_signed_hol_artifact(&mut receiver, pinned)?;
    let retained = LocalConnection::Hol(receiver);
    let connection = directory.insert(retained.protocol(), retained)?;

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
    Ok((connection, expected_endpoint, artifact, first_read))
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
    let (receiver, _, _, _) = run_hash_selected_wasm_hol(
        output,
        kernel,
        repl,
        O256::from_hex(expected)?,
        Path::new(component),
        Path::new(directory),
    )?;
    repl.select(receiver)?;
    writeln!(output, "using receiver connection {receiver}")?;
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
    writeln!(output, ".use ID            select a connection")?;
    writeln!(output, ".close [ID]        close a connection")?;
    writeln!(output, ".connections       list open connections")?;
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

fn run_line(
    kernel: &Kernel,
    repl: &mut LocalRepl,
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
    if line == ".connections" {
        print_connections(repl, output)?;
        return Ok(true);
    }
    if line == ".close" || line.starts_with(".close ") {
        let id = match line.strip_prefix(".close ") {
            Some(argument) => ConnectionId::from_u32(argument.trim().parse()?),
            None => repl.active()?.ok_or("no active connection")?,
        };
        repl.remove(id)?;
        writeln!(output, "closed connection {id}")?;
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
        let path = path.trim();
        if path.is_empty() {
            return Err("usage: .hol signed-roundtrip DIRECTORY".into());
        }
        let fresh = FreshArtifactDirectory::create(Path::new(path))?;
        let source = repl.active()?.ok_or("no active connection")?;
        let (outcome, receiver) = run_managed_signed_hol_round_trip(kernel, repl, source)?;
        print_signed_hol_outcome(output, &outcome)?;
        writeln!(output, "receiver_connection\t{receiver}")?;
        write_signed_hol_artifacts(output, fresh, &outcome)?;
        return Ok(true);
    }
    #[cfg(not(target_arch = "wasm32"))]
    if let Some(arguments) = line.strip_prefix(".hol hash-wasm ") {
        run_interactive_hash_selected_wasm_hol(kernel, repl, output, arguments)?;
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
        match run_line(&kernel, &mut repl, output, &line) {
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
        let (connection, expected_endpoint, artifact, first_read) = run_hash_selected_wasm_hol(
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

        assert!(run_line(&kernel, &mut repl, &mut output, &command).unwrap());
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
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains(&format!("component\t{digest}\n")));
        assert!(contains_imported_theorem(&output));
        assert!(output.contains(&format!("using receiver connection {receiver}\n")));

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

        let error = run_line(
            &kernel,
            &mut repl,
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
