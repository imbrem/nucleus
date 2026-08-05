use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::io::Read as _;
use std::io::Write as _;
use std::process::ExitCode;

use covalence_repl::{
    AllowAll, ConnectionId, HolRecipe, HolRecipeResult, Kernel, LocalConnection, MAX_IMAGE_BYTES,
    Outcome, Repl, SignedHolRoundTripResult, Value, authenticate_pinned_signed_hol_artifact,
    produce_signed_hol_artifact, trust_and_receive_pinned_signed_hol_artifact,
};
#[cfg(not(target_arch = "wasm32"))]
use covalence_repl::{
    MAX_HOL_PROOF_COMPONENT_BYTES, NativeHttpClientError, NativeHttpKernelClient,
    NativeHttpKernelServer, PreparedHolProofComponent, RemoteSessionState, SIGNED_KERNEL_HTTP_PATH,
    ServiceOperation, ServiceProducedHol, ServiceResult,
};

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
    path: &str,
    outcome: &SignedHolRoundTripResult,
) -> Result<()> {
    fs::write(path, outcome.image())?;
    let attestation_path = format!("{path}.attestation.txt");
    fs::write(&attestation_path, outcome.attestation_text())?;
    writeln!(output, "database\t{path}")?;
    writeln!(output, "attestation\t{attestation_path}")?;
    Ok(())
}

fn run_managed_signed_hol_round_trip(
    kernel: &Kernel,
    repl: &mut LocalRepl,
) -> Result<(SignedHolRoundTripResult, ConnectionId)> {
    let produced = produce_signed_hol_artifact(kernel, repl.active_mut()?.hol_mut()?)?;
    let receiver = LocalConnection::Hol(kernel.open_hol(AllowAll)?);
    let receiver_id = repl.insert(receiver.protocol(), receiver)?;
    let expected = repl.expected_kernel_identity(covalence_repl::KernelId::LOCAL)?;
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, produced.artifact())?;
    let imported = trust_and_receive_pinned_signed_hol_artifact(
        repl.get_mut(receiver_id)?.hol_mut()?,
        pinned,
    )?;
    Ok((
        SignedHolRoundTripResult::from_parts(produced, imported),
        receiver_id,
    ))
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

#[cfg(not(target_arch = "wasm32"))]
fn parse_public_key(source: &str) -> Result<[u8; 32]> {
    if source.len() != 64 || !source.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("public key must be exactly 64 hexadecimal characters".into());
    }
    let mut key = [0_u8; 32];
    for (index, byte) in key.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&source[index * 2..index * 2 + 2], 16)?;
    }
    Ok(key)
}

#[cfg(not(target_arch = "wasm32"))]
fn fail_remote_session(
    directory: &Repl<()>,
    session: covalence_repl::RemoteSessionId,
    error: &NativeHttpClientError,
    ambiguous: RemoteSessionState,
) -> Result<()> {
    if error.outcome_unknown() {
        directory.transition_remote_session(session, ambiguous)?;
    }
    directory.transition_remote_session(session, RemoteSessionState::Failed)?;
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn execute_remote_operation(
    directory: &Repl<()>,
    session: covalence_repl::RemoteSessionId,
    client: &mut NativeHttpKernelClient,
    operation: ServiceOperation,
    ambiguous: RemoteSessionState,
) -> Result<ServiceResult> {
    client.execute(operation).map_err(|error| {
        let transition = fail_remote_session(directory, session, &error, ambiguous);
        transition.map_or_else(|state_error| state_error, |()| error.into())
    })
}

#[cfg(not(target_arch = "wasm32"))]
fn record_local_operation<T>(
    directory: &mut Repl<()>,
    session: covalence_repl::RemoteSessionId,
    operation: impl FnOnce(&mut Repl<()>) -> Result<T>,
) -> Result<T> {
    operation(directory).map_err(|error| {
        let transition = directory.transition_remote_session(session, RemoteSessionState::Failed);
        transition.map_or_else(Into::into, |()| error)
    })
}

#[cfg(not(target_arch = "wasm32"))]
fn import_remote_artifact(
    directory: &mut Repl<()>,
    session: covalence_repl::RemoteSessionId,
    endpoint: covalence_repl::KernelId,
    produced: &ServiceProducedHol,
) -> Result<covalence_repl::ReceivedHolSnapshot> {
    record_local_operation(directory, session, |directory| {
        let expected = directory.expected_kernel_identity(endpoint)?;
        let pinned = authenticate_pinned_signed_hol_artifact(&expected, produced.artifact())?;
        let receiver_kernel = Kernel::ephemeral();
        let mut receiver = receiver_kernel.open_hol(AllowAll)?;
        trust_and_receive_pinned_signed_hol_artifact(&mut receiver, pinned).map_err(Into::into)
    })
}

#[cfg(not(target_arch = "wasm32"))]
fn print_remote_lifecycle(
    output: &mut impl io::Write,
    directory: &Repl<()>,
    session: covalence_repl::RemoteSessionId,
) -> Result<()> {
    let lifecycle = directory.inspect_state(&format!(
        "SELECT state FROM repl_lifecycle_event
         WHERE resource = 'session' AND resource_id = {} ORDER BY event_id",
        session.get()
    ))?;
    for row in lifecycle.rows {
        if let [Value::Text(state)] = row.as_slice() {
            writeln!(output, "session_state\t{state}")?;
        }
    }
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn run_managed_native_http_hol(
    output: &mut impl io::Write,
    directory: &mut Repl<()>,
    address: std::net::SocketAddr,
    public_key: [u8; 32],
) -> Result<()> {
    let endpoint = directory.register_kernel(
        "native-http",
        Some(&format!("http://{address}{SIGNED_KERNEL_HTTP_PATH}")),
        &public_key,
    )?;
    let session = directory.begin_remote_session(endpoint)?;
    let mut client = match NativeHttpKernelClient::connect(address, public_key) {
        Ok(client) => client,
        Err(error) => {
            fail_remote_session(
                directory,
                session,
                &error,
                RemoteSessionState::OpeningUnknown,
            )?;
            return Err(error.into());
        }
    };
    directory.transition_remote_session(session, RemoteSessionState::Established)?;

    let ServiceResult::Opened(opened) = execute_remote_operation(
        directory,
        session,
        &mut client,
        ServiceOperation::OpenHol,
        RemoteSessionState::CommandUnknown,
    )?
    else {
        directory.transition_remote_session(session, RemoteSessionState::Failed)?;
        return Err("native endpoint returned the wrong OpenHol result".into());
    };
    let managed = record_local_operation(directory, session, |directory| {
        directory
            .insert_at(endpoint, "nucleus/hol", Some(&opened.to_string()), ())
            .map_err(Into::into)
    })?;

    let ServiceResult::Produced(produced) = execute_remote_operation(
        directory,
        session,
        &mut client,
        ServiceOperation::ProduceSignedHol(opened),
        RemoteSessionState::CommandUnknown,
    )?
    else {
        directory.transition_remote_session(session, RemoteSessionState::Failed)?;
        return Err("native endpoint returned the wrong ProduceSignedHol result".into());
    };
    let statement = produced.statement().to_owned();
    let imported = import_remote_artifact(directory, session, endpoint, &produced)?;

    if !matches!(
        execute_remote_operation(
            directory,
            session,
            &mut client,
            ServiceOperation::CloseHol(opened),
            RemoteSessionState::CommandUnknown,
        )?,
        ServiceResult::Closed
    ) {
        directory.transition_remote_session(session, RemoteSessionState::Failed)?;
        return Err("native endpoint returned the wrong CloseHol result".into());
    }
    record_local_operation(directory, session, |directory| {
        directory.remove(managed).map(drop).map_err(Into::into)
    })?;
    directory.transition_remote_session(session, RemoteSessionState::Closing)?;
    if !matches!(
        execute_remote_operation(
            directory,
            session,
            &mut client,
            ServiceOperation::Shutdown,
            RemoteSessionState::ClosingUnknown,
        )?,
        ServiceResult::Goodbye
    ) {
        directory.transition_remote_session(session, RemoteSessionState::Failed)?;
        return Err("native endpoint returned the wrong Shutdown result".into());
    }
    directory.transition_remote_session(session, RemoteSessionState::Closed)?;

    writeln!(output, "kind\tmanaged-native-http-hol")?;
    writeln!(output, "kernel\t{endpoint}")?;
    writeln!(output, "session\t{session}")?;
    writeln!(output, "remote_connection\t{opened}")?;
    writeln!(output, "statement\t{statement}")?;
    writeln!(
        output,
        "imported_theorem\t{}\t{}",
        imported.context_id(),
        imported.conclusion_id()
    )?;
    print_remote_lifecycle(output, directory, session)?;
    writeln!(
        output,
        "directory_retention\tcaller-owned-until-explicit-cleanup"
    )?;
    Ok(())
}

fn load_image(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    schema: &str,
    path: &str,
) -> Result<()> {
    let size = fs::metadata(path)?.len();
    if size > MAX_IMAGE_BYTES as u64 {
        return Err(format!("image is {size} bytes; the limit is {MAX_IMAGE_BYTES} bytes").into());
    }
    let bytes = fs::read(path)?;
    let connection = repl.active_mut()?.sql_mut()?;
    let hash = connection.put_image(&bytes)?;
    connection.attach_immutable_image(hash, schema)?;
    writeln!(output, "attached {schema} {hash}")?;
    Ok(())
}

fn parse_load(command: &str) -> Option<(&str, &str)> {
    let arguments = command.strip_prefix(".load")?.trim();
    let split = arguments.find(char::is_whitespace)?;
    let schema = arguments[..split].trim();
    let path = arguments[split..].trim();
    (!schema.is_empty() && !path.is_empty()).then_some((schema, path))
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
        ".hol signed-roundtrip PATH  prove, sign, import, verify, and export artifacts"
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
        let active = repl.active()?;
        let mut statement = repl.state().sqlite().prepare(
            "SELECT connection_id, protocol FROM repl_connection ORDER BY connection_id",
        )?;
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
        fs::write(path, &bytes)?;
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
            return Err("usage: .hol signed-roundtrip PATH".into());
        }
        let (outcome, receiver) = run_managed_signed_hol_round_trip(kernel, repl)?;
        print_signed_hol_outcome(output, &outcome)?;
        writeln!(output, "receiver_connection\t{receiver}")?;
        write_signed_hol_artifacts(output, path, &outcome)?;
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
    writeln!(output, "       nucleus --signed-hol PATH")?;
    writeln!(output, "       nucleus --interkernel-hol")?;
    writeln!(
        output,
        "       nucleus --kernel-http ADDRESS ALLOWED_ORIGIN"
    )?;
    writeln!(
        output,
        "       nucleus --kernel-http-hol-component ADDRESS ALLOWED_ORIGIN COMPONENT"
    )?;
    writeln!(
        output,
        "       nucleus --managed-http-hol ADDRESS PUBLIC_KEY_HEX"
    )?;
    writeln!(output, "       nucleus --help")
}

#[cfg(not(target_arch = "wasm32"))]
fn run_hol_component_server_arguments(arguments: &mut impl Iterator<Item = String>) -> Result<()> {
    let address = arguments
        .next()
        .ok_or("--kernel-http-hol-component requires ADDRESS ALLOWED_ORIGIN COMPONENT")?;
    let allowed_origin = arguments
        .next()
        .ok_or("--kernel-http-hol-component requires ADDRESS ALLOWED_ORIGIN COMPONENT")?;
    let path = arguments
        .next()
        .ok_or("--kernel-http-hol-component requires ADDRESS ALLOWED_ORIGIN COMPONENT")?;
    if arguments.next().is_some() {
        return Err(
            "unexpected arguments after --kernel-http-hol-component ADDRESS ALLOWED_ORIGIN COMPONENT"
                .into(),
        );
    }
    let source = fs::File::open(path)?;
    let mut bytes = Vec::new();
    source
        .take(MAX_HOL_PROOF_COMPONENT_BYTES as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > MAX_HOL_PROOF_COMPONENT_BYTES {
        return Err(
            format!("component exceeds the {MAX_HOL_PROOF_COMPONENT_BYTES}-byte limit").into(),
        );
    }
    let component = PreparedHolProofComponent::prepare_default(&bytes)?;
    let component_digest = component.digest();
    let server =
        NativeHttpKernelServer::bind_hol_proof_component(address, allowed_origin, component)?;
    let address = server.local_addr()?;
    let mut public_key = String::with_capacity(64);
    for byte in server.identity().public_key() {
        use std::fmt::Write as _;
        write!(public_key, "{byte:02x}")?;
    }
    let mut output = io::stdout().lock();
    writeln!(output, "url\thttp://{address}{SIGNED_KERNEL_HTTP_PATH}")?;
    writeln!(output, "public_key\t{public_key}")?;
    writeln!(output, "component\t{component_digest}")?;
    output.flush()?;
    drop(output);
    server.serve()?;
    Ok(())
}

#[cfg(not(target_arch = "wasm32"))]
fn run_managed_http_arguments(arguments: &mut impl Iterator<Item = String>) -> Result<()> {
    let address = arguments
        .next()
        .ok_or("--managed-http-hol requires ADDRESS PUBLIC_KEY_HEX")?
        .parse()?;
    let public_key = parse_public_key(
        &arguments
            .next()
            .ok_or("--managed-http-hol requires ADDRESS PUBLIC_KEY_HEX")?,
    )?;
    if arguments.next().is_some() {
        return Err("unexpected arguments after --managed-http-hol ADDRESS PUBLIC_KEY_HEX".into());
    }
    let mut directory = Repl::empty()?;
    run_managed_native_http_hol(
        &mut io::stdout().lock(),
        &mut directory,
        address,
        public_key,
    )
}

fn run() -> Result<()> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        None => run_repl(
            &mut io::stdin().lock(),
            &mut io::stdout().lock(),
            &mut io::stderr().lock(),
            true,
        ),
        Some("-c") => {
            let sql = arguments.next().ok_or("-c requires one SQL statement")?;
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
        Some("--hol") => {
            let source = arguments.next().ok_or("--hol requires one recipe")?;
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
        Some("--signed-hol") => {
            let path = arguments.next().ok_or("--signed-hol requires PATH")?;
            if arguments.next().is_some() {
                return Err("unexpected arguments after signed HOL path".into());
            }
            let kernel = Kernel::ephemeral();
            let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
            open_hol_connection(&kernel, &mut repl)?;
            let (outcome, receiver) = run_managed_signed_hol_round_trip(&kernel, &mut repl)?;
            print_signed_hol_outcome(&mut io::stdout().lock(), &outcome)?;
            writeln!(io::stdout().lock(), "receiver_connection\t{receiver}")?;
            write_signed_hol_artifacts(&mut io::stdout().lock(), &path, &outcome)
        }
        Some("--interkernel-hol") => {
            if arguments.next().is_some() {
                return Err("unexpected arguments after --interkernel-hol".into());
            }
            run_interkernel_hol(&mut io::stdout().lock())
        }
        #[cfg(not(target_arch = "wasm32"))]
        Some("--kernel-http") => {
            let address = arguments
                .next()
                .ok_or("--kernel-http requires ADDRESS ALLOWED_ORIGIN")?;
            let allowed_origin = arguments
                .next()
                .ok_or("--kernel-http requires ADDRESS ALLOWED_ORIGIN")?;
            if arguments.next().is_some() {
                return Err(
                    "unexpected arguments after --kernel-http ADDRESS ALLOWED_ORIGIN".into(),
                );
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
            server.serve()?;
            Ok(())
        }
        #[cfg(not(target_arch = "wasm32"))]
        Some("--kernel-http-hol-component") => run_hol_component_server_arguments(&mut arguments),
        #[cfg(not(target_arch = "wasm32"))]
        Some("--managed-http-hol") => run_managed_http_arguments(&mut arguments),
        Some("-h" | "--help") => {
            usage(&mut io::stdout().lock())?;
            Ok(())
        }
        Some(argument) => Err(format!("unexpected argument: {argument}").into()),
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
    use std::io::Cursor;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use covalence_repl::{Connection, Sql};

    static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

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
        let temporary = std::env::temp_dir();
        fs::create_dir_all(&temporary).expect("create temporary directory");
        let path = temporary.join(format!(
            "nucleus-export-{}.sqlite",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));

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
        let path = std::env::temp_dir().join(format!(
            "nucleus-signed-hol-{}.sqlite",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let attestation = format!("{}.attestation.txt", path.display());
        let mut input = Cursor::new(format!(
            ".open hol\n.hol signed-roundtrip {}\n.quit\n",
            path.display()
        ));
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let image = fs::read(&path).expect("read signed image");
        let sidecar = fs::read_to_string(&attestation).expect("read attestation");
        fs::remove_file(&path).expect("remove signed image");
        fs::remove_file(&attestation).expect("remove attestation");
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
    fn terminal_manages_a_native_http_session_in_raw_sqlite_state() {
        let server =
            NativeHttpKernelServer::bind((std::net::Ipv4Addr::LOCALHOST, 0), "http://127.0.0.1:1")
                .unwrap();
        let address = server.local_addr().unwrap();
        let public_key = server.identity().public_key();
        let handle = std::thread::spawn(move || server.serve());
        let mut output = Vec::new();
        let mut directory = Repl::empty().unwrap();
        run_managed_native_http_hol(&mut output, &mut directory, address, public_key).unwrap();
        handle.join().unwrap().unwrap();

        let kernels = directory.kernels().unwrap();
        assert_eq!(kernels.len(), 1);
        assert!(directory.connections().unwrap().is_empty());
        let session = directory
            .inspect_state("SELECT session_id, state FROM repl_remote_session")
            .unwrap();
        assert_eq!(
            session.rows,
            [[Value::Integer(1), Value::Text("closed".to_owned())]]
        );
        directory
            .forget_remote_session("1".parse().unwrap())
            .unwrap();
        directory.unregister_kernel(kernels[0].id).unwrap();
        assert!(directory.kernels().unwrap().is_empty());

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("kind\tmanaged-native-http-hol\n"));
        assert!(output.contains("remote_connection\t1\n"));
        assert!(output.contains("statement\t(lambda x:bool. x) true = true\n"));
        assert!(output.contains("imported_theorem\t0\t8\n"));
        assert!(output.contains(
            "session_state\topening\nsession_state\testablished\nsession_state\tclosing\nsession_state\tclosed\n"
        ));
        assert!(output.contains("directory_retention\tcaller-owned-until-explicit-cleanup\n"));
    }

    #[test]
    fn terminal_records_failed_before_returning_a_local_post_handshake_error() {
        let mut directory = Repl::empty().unwrap();
        let endpoint = directory
            .register_kernel("native-http", None, &[8; 32])
            .unwrap();
        let session = directory.begin_remote_session(endpoint).unwrap();
        directory
            .transition_remote_session(session, RemoteSessionState::Established)
            .unwrap();
        let result = record_local_operation::<()>(&mut directory, session, |_| {
            Err("local artifact authentication failed".into())
        });
        assert!(result.is_err());
        assert_eq!(
            directory.remote_session(session).unwrap().state,
            RemoteSessionState::Failed
        );
        assert!(directory.connections().unwrap().is_empty());
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
        let temporary = std::env::temp_dir();
        fs::create_dir_all(&temporary).expect("create temporary directory");
        let path = temporary.join(format!(
            "nucleus-repl-{}.sqlite",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
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
