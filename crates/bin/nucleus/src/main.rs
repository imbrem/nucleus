use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::io::Write as _;
use std::process::ExitCode;

use covalence_repl::{
    AllowAll, ConnectionId, HolRecipe, HolRecipeResult, Kernel, LocalConnection, MAX_IMAGE_BYTES,
    Outcome, Repl, SignedHolRoundTripResult, Value, authenticate_pinned_signed_hol_artifact,
    produce_signed_hol_artifact, trust_and_receive_pinned_signed_hol_artifact,
};
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use covalence_repl::{
    NativeKernelProcess, SIGNED_HOL_PHASES, ServiceIdentity, ServiceOperation, ServiceResult,
    SessionInitiator, SignedServiceSession, serve_kernel_stdio,
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

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
fn native_command(
    remote: &mut NativeKernelProcess,
    session: &mut SignedServiceSession,
    operation: ServiceOperation,
) -> Result<ServiceResult> {
    let command = session.command(operation)?;
    let reply = remote.execute(&command)?;
    Ok(session.accept_reply(&command, reply)?)
}

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
fn run_native_hol(
    program: &std::path::Path,
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
) -> Result<()> {
    let mut remote = NativeKernelProcess::spawn(program)?;
    let description = remote.describe()?;
    let identity = description.identity();
    let endpoint = repl.register_kernel(
        "stdio",
        Some(&program.display().to_string()),
        &identity.public_key(),
    )?;
    let result: Result<()> = (|| {
        let expected = repl.expected_kernel_identity(endpoint)?;
        let pinned_identity = ServiceIdentity::new(expected.signer(), *expected.public_key())?;
        let initiator = SessionInitiator::begin(pinned_identity, &description)?;
        let accepted = remote.open_session(initiator.request())?;
        let mut session = initiator.accept(&accepted)?;
        let ServiceResult::Opened(remote_connection) =
            native_command(&mut remote, &mut session, ServiceOperation::OpenHol)?
        else {
            return Err("native kernel did not open a HOL connection".into());
        };
        let ServiceResult::Produced(produced) = native_command(
            &mut remote,
            &mut session,
            ServiceOperation::ProduceSignedHol(remote_connection),
        )?
        else {
            return Err("native kernel did not produce a signed HOL artifact".into());
        };
        let pinned = authenticate_pinned_signed_hol_artifact(&expected, produced.artifact())?;
        let received =
            trust_and_receive_pinned_signed_hol_artifact(repl.active_mut()?.hol_mut()?, pinned)?;
        if !matches!(
            native_command(
                &mut remote,
                &mut session,
                ServiceOperation::CloseHol(remote_connection)
            )?,
            ServiceResult::Closed
        ) {
            return Err("native kernel did not close its HOL connection".into());
        }
        if !matches!(
            native_command(&mut remote, &mut session, ServiceOperation::Shutdown)?,
            ServiceResult::Goodbye
        ) {
            return Err("native kernel did not accept signed shutdown".into());
        }
        remote.wait_for_exit()?;

        writeln!(output, "kind\tnative-signed-hol-round-trip")?;
        writeln!(output, "native_kernel\t{endpoint}")?;
        writeln!(output, "native_signer\t{}", identity.signer())?;
        writeln!(output, "native_connection\t{remote_connection}")?;
        writeln!(output, "statement\t{}", produced.statement())?;
        writeln!(output, "phases\t{}", SIGNED_HOL_PHASES.join(","))?;
        writeln!(output, "import\t{}", received.import_id())?;
        writeln!(
            output,
            "imported_theorem\t{}\t{}",
            received.context_id(),
            received.conclusion_id()
        )?;
        writeln!(output, "native_exit\tsuccess")?;
        Ok(())
    })();
    let cleanup = repl.unregister_kernel(endpoint);
    match (result, cleanup) {
        (Ok(()), Ok(())) => {
            writeln!(output, "native_endpoint_cleanup\tremoved")?;
            Ok(())
        }
        (Err(error), Ok(())) => Err(error),
        (Ok(()), Err(error)) => Err(error.into()),
        (Err(error), Err(cleanup)) => {
            Err(format!("{error}; failed to unregister native endpoint: {cleanup}").into())
        }
    }
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
    writeln!(
        output,
        ".hol native-roundtrip  drive a separate native kernel over stdio"
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
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    if line.trim() == ".hol native-roundtrip" {
        return run_native_hol(&env::current_exe()?, repl, output).map(|()| true);
    }
    run_local_line(kernel, repl, output, line)
}

fn run_local_line(
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
    writeln!(output, "       nucleus --native-hol [PROGRAM]")?;
    writeln!(output, "       nucleus --help")
}

fn run() -> Result<()> {
    let mut arguments = env::args().skip(1);
    match arguments.next().as_deref() {
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        Some("--kernel-stdio") => {
            if arguments.next().is_some() {
                return Err("unexpected arguments after --kernel-stdio".into());
            }
            serve_kernel_stdio(io::stdin().lock(), io::stdout().lock()).map_err(Into::into)
        }
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
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        Some("--native-hol") => {
            let program = match arguments.next() {
                Some(program) => program.into(),
                None => env::current_exe()?,
            };
            if arguments.next().is_some() {
                return Err("unexpected arguments after native kernel program".into());
            }
            let kernel = Kernel::ephemeral();
            let mut repl = Repl::new(kernel.verifying_key().as_bytes())?;
            open_hol_connection(&kernel, &mut repl)?;
            run_native_hol(&program, &mut repl, &mut io::stdout().lock())
        }
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
