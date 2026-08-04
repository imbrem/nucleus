use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::io::Write as _;
use std::net::SocketAddr;
use std::process::ExitCode;

use covalence_repl::{
    ConnectionId, ContextId, ExportId, KernelId, KindId, KindView, LocalRepl, NamespaceExport,
    NamespaceId, NativeKernelServerConfig, O256, Outcome, ProofError, TermId, TermView,
    TrustedImportId, TypeId, TypeView, Value, compile_hol_schema_json, random_bootstrap_token,
    spawn_native_kernel_server,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
fn open_connection(repl: &mut LocalRepl, protocol: &str) -> Result<ConnectionId> {
    open_connection_on(repl, KernelId::local(), protocol)
}

fn open_connection_on(
    repl: &mut LocalRepl,
    kernel: KernelId,
    protocol: &str,
) -> Result<ConnectionId> {
    match protocol {
        "sql" => Ok(repl.open_sql_on(kernel)?),
        "hol" => Ok(repl.open_hol_on(kernel)?),
        _ => Err(format!("unknown connection protocol: {protocol}").into()),
    }
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

fn load_image(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    schema: &str,
    path: &str,
) -> Result<()> {
    let bytes = fs::read(path)?;
    let id = repl.active()?.ok_or("no active connection")?;
    let hash = repl.put_image_for_connection(id, &bytes)?;
    repl.attach_image(id, hash, schema)?;
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

fn run_line(repl: &mut LocalRepl, output: &mut impl io::Write, line: &str) -> Result<bool> {
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
    if line == ".open" || line.starts_with(".open ") {
        open_repl_connection(repl, output, line)?;
        return Ok(true);
    }
    if line == ".kernel new" {
        let id = repl.create_local_kernel()?;
        writeln!(output, "created local kernel {id}")?;
        return Ok(true);
    }
    if let Some(arguments) = line.strip_prefix(".kernel connect-http ") {
        connect_http_kernel(repl, output, arguments)?;
        return Ok(true);
    }
    if line == ".kernels" {
        for (id, kernel) in repl.kernels() {
            writeln!(
                output,
                "{id}\t{transport}\t{}\t{}",
                kernel.endpoint.as_deref().unwrap_or("-"),
                hex(&kernel.public_key),
                transport = kernel.transport,
            )?;
        }
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
            "SELECT connection_id, kernel_id, protocol FROM repl_connection ORDER BY connection_id",
        )?;
        let rows = statement.query_map((), |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, String>(2)?,
            ))
        })?;
        for row in rows {
            let (id, kernel, protocol) = row?;
            let marker = if active.is_some_and(|active| active.get() == id) {
                '*'
            } else {
                ' '
            };
            writeln!(output, "{marker} {id}\t@{kernel}\t{protocol}")?;
        }
        return Ok(true);
    }
    if line == ".close" || line.starts_with(".close ") {
        let id = match line.strip_prefix(".close ") {
            Some(argument) => ConnectionId::from_u32(argument.trim().parse()?),
            None => repl.active()?.ok_or("no active connection")?,
        };
        repl.close(id)?;
        writeln!(output, "closed connection {id}")?;
        return Ok(true);
    }
    if line.starts_with(".load") {
        let (schema, path) = parse_load(line).ok_or("usage: .load SCHEMA PATH")?;
        load_image(repl, output, schema, path)?;
        return Ok(true);
    }
    if let Some(arguments) = line.strip_prefix(".hol-schema ") {
        compile_hol_schema(output, arguments)?;
        return Ok(true);
    }
    if let Some(arguments) = line.strip_prefix(".hol-snapshot ") {
        put_hol_snapshot(repl, output, arguments)?;
        return Ok(true);
    }
    if let Some(arguments) = line.strip_prefix(".hol ") {
        run_hol(repl, output, arguments)?;
        return Ok(true);
    }
    if line.starts_with('.') {
        return Err(format!("unknown command: {line}").into());
    }

    let id = repl.active()?.ok_or("no active connection")?;
    let outcome = repl.run_sql(id, line)?;
    print_outcome(output, &outcome)?;
    Ok(true)
}

fn connect_http_kernel(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    arguments: &str,
) -> Result<()> {
    let mut arguments = arguments.split_whitespace();
    let address = arguments
        .next()
        .ok_or("missing native kernel address")?
        .parse::<SocketAddr>()?;
    let public_key = parse_fixed_hex::<32>(arguments.next(), "kernel public key")?;
    let bootstrap = match arguments.next() {
        None | Some("-") => None,
        token => Some(parse_fixed_hex::<32>(token, "bootstrap token")?),
    };
    if arguments.next().is_some() {
        return Err("usage: .kernel connect-http ADDRESS PUBLIC_KEY [BOOTSTRAP_TOKEN|-]".into());
    }
    let kernel = repl.connect_native_http(address, public_key, bootstrap)?;
    writeln!(output, "connected native HTTP kernel {kernel}")?;
    Ok(())
}

fn open_repl_connection(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    line: &str,
) -> Result<()> {
    let arguments = line
        .strip_prefix(".open")
        .expect("matched prefix")
        .split_whitespace()
        .collect::<Vec<_>>();
    let (kernel, arguments) = match arguments.first() {
        Some(value) if value.starts_with('@') => {
            (KernelId::from_u32(value[1..].parse()?), &arguments[1..])
        }
        _ => (KernelId::local(), arguments.as_slice()),
    };
    let (protocol, id) = match arguments {
        [] | ["sql"] => ("sql", open_connection_on(repl, kernel, "sql")?),
        ["hol"] => ("hol", open_connection_on(repl, kernel, "hol")?),
        ["hol", "--descriptor", path] => (
            "hol",
            repl.open_hol_with_descriptor_on(kernel, &fs::read(path)?)?,
        ),
        ["hol", "--schema-json", path] => (
            "hol",
            repl.open_hol_with_schema_json_on(kernel, &fs::read_to_string(path)?)?,
        ),
        _ => {
            return Err(
                "usage: .open [@KERNEL] [sql|hol [--descriptor PATH|--schema-json PATH]]".into(),
            );
        }
    };
    writeln!(
        output,
        "opened {protocol} connection {id} on kernel {kernel}"
    )?;
    Ok(())
}

fn print_help(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(
        output,
        ".load SCHEMA PATH  attach a complete immutable SQLite image"
    )?;
    writeln!(
        output,
        ".open [@KERNEL] hol [--descriptor PATH|--schema-json PATH]  open a HOL connection"
    )?;
    writeln!(output, ".open [@KERNEL] [sql]  open a raw SQL connection")?;
    writeln!(
        output,
        ".kernel new        create an independently keyed local kernel"
    )?;
    writeln!(
        output,
        ".kernel connect-http ADDRESS PUBLIC_KEY [BOOTSTRAP_TOKEN|-]  connect a pinned loopback kernel"
    )?;
    writeln!(
        output,
        ".kernels           list kernel identities and transports"
    )?;
    writeln!(output, ".use ID            select a connection")?;
    writeln!(output, ".close [ID]        close a connection")?;
    writeln!(output, ".connections       list open connections")?;
    writeln!(output, ".hol star          intern the star kind")?;
    writeln!(output, ".hol arrow D C     intern the kind D -> C")?;
    writeln!(output, ".hol show ID       inspect a kind")?;
    writeln!(output, ".hol rank ID       derive a kind's order rank")?;
    writeln!(
        output,
        ".hol type ...      admit/inspect Bool and arrow types"
    )?;
    writeln!(
        output,
        ".hol term ...      admit/inspect simply typed terms and binders"
    )?;
    writeln!(output, ".hol ctx ...       define/inspect Boolean contexts")?;
    writeln!(
        output,
        ".hol metadata get|set JSON  read/write declared metadata columns"
    )?;
    writeln!(
        output,
        ".hol namespace ... define/inspect export namespaces"
    )?;
    writeln!(output, ".hol export ...    bind/inspect namespace exports")?;
    writeln!(
        output,
        ".hol snapshot export PATH  write a signed HOL image and descriptor sidecar"
    )?;
    writeln!(
        output,
        ".hol import trust ...      trust and persist a hash-first signed import"
    )?;
    writeln!(
        output,
        ".hol import show ID        inspect a trusted import"
    )?;
    writeln!(
        output,
        ".hol import namespace ...   alias a complete imported namespace"
    )?;
    writeln!(
        output,
        ".hol import inspect ...     read a downloaded trusted export"
    )?;
    writeln!(
        output,
        ".hol import inspect-resident ...  read an already-admitted trusted export"
    )?;
    writeln!(output, ".hol prove ...     apply an explicit HOL rule")?;
    writeln!(
        output,
        ".hol script JSON   replay one strict bounded proof recipe"
    )?;
    writeln!(
        output,
        ".hol-schema compile JSON OUT  compile editable schema JSON"
    )?;
    writeln!(
        output,
        ".hol-snapshot put ...  admit one signed resident image"
    )?;
    writeln!(output, ".quit              exit")
}

fn compile_hol_schema(output: &mut impl io::Write, arguments: &str) -> Result<()> {
    let mut arguments = arguments.split_whitespace();
    if arguments.next() != Some("compile") {
        return Err("usage: .hol-schema compile JSON_PATH DESCRIPTOR_PATH".into());
    }
    let json_path = arguments.next().ok_or("missing schema JSON path")?;
    let descriptor_path = arguments.next().ok_or("missing descriptor path")?;
    if arguments.next().is_some() {
        return Err("usage: .hol-schema compile JSON_PATH DESCRIPTOR_PATH".into());
    }
    let descriptor = compile_hol_schema_json(&fs::read_to_string(json_path)?)?;
    fs::write(descriptor_path, descriptor.encode())?;
    writeln!(output, "descriptor {descriptor_path}")?;
    writeln!(output, "schema {}", descriptor.schema_id())?;
    Ok(())
}

fn put_hol_snapshot(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    arguments: &str,
) -> Result<()> {
    let mut arguments = arguments.split_whitespace();
    if arguments.next() != Some("put") {
        return Err("usage: .hol-snapshot put PATH DESCRIPTOR_PATH SCHEMA IMAGE SIGNER PUBLIC_KEY SIGNATURE".into());
    }
    let path = arguments.next().ok_or("missing snapshot path")?;
    let descriptor_path = arguments.next().ok_or("missing descriptor path")?;
    let schema = parse_o256(arguments.next(), "schema")?;
    let image = parse_o256(arguments.next(), "image")?;
    let signer = parse_o256(arguments.next(), "signer")?;
    let public_key = parse_fixed_hex::<32>(arguments.next(), "public key")?;
    let signature = parse_hex(arguments.next(), "signature")?;
    if arguments.next().is_some() {
        return Err("usage: .hol-snapshot put PATH DESCRIPTOR_PATH SCHEMA IMAGE SIGNER PUBLIC_KEY SIGNATURE".into());
    }
    let admitted = repl.put_signed_hol_snapshot_with_descriptor(
        &fs::read(path)?,
        &fs::read(descriptor_path)?,
        schema,
        image,
        signer,
        public_key,
        &signature,
    )?;
    writeln!(output, "resident-hol {admitted} schema={schema}")?;
    Ok(())
}

fn run_hol(repl: &mut LocalRepl, output: &mut impl io::Write, arguments: &str) -> Result<()> {
    let connection = repl.active()?.ok_or("no active connection")?;
    if let Some(arguments) = arguments.strip_prefix("metadata ") {
        return run_hol_metadata(repl, output, connection, arguments);
    }
    if let Some(request) = arguments.strip_prefix("script ") {
        let response = repl.run_hol_proof_script_json(connection, request)?;
        writeln!(output, "{response}")?;
        return Ok(());
    }
    let mut arguments = arguments.split_whitespace();
    match arguments.next() {
        Some("star") if arguments.next().is_none() => {
            let kind = repl
                .hol_mut(connection)?
                .insert_kind(&covalence_repl::Kind::Star)?;
            writeln!(output, "kind {} = star", kind.get())?;
        }
        Some("arrow") => {
            let domain = parse_kind_id(arguments.next(), "domain")?;
            let codomain = parse_kind_id(arguments.next(), "codomain")?;
            if arguments.next().is_some() {
                return Err("usage: .hol arrow DOMAIN CODOMAIN".into());
            }
            let kind = repl
                .hol_mut(connection)?
                .insert_kind_arrow(domain, codomain)?;
            writeln!(
                output,
                "kind {} = {} -> {}",
                kind.get(),
                domain.get(),
                codomain.get()
            )?;
        }
        Some("show") => {
            let kind = parse_kind_id(arguments.next(), "kind")?;
            if arguments.next().is_some() {
                return Err("usage: .hol show ID".into());
            }
            match repl.hol_mut(connection)?.kind(kind)? {
                KindView::Star => writeln!(output, "kind {} = star", kind.get())?,
                KindView::Arrow { domain, codomain } => writeln!(
                    output,
                    "kind {} = {} -> {}",
                    kind.get(),
                    domain.get(),
                    codomain.get()
                )?,
            }
        }
        Some("rank") => {
            let kind = parse_kind_id(arguments.next(), "kind")?;
            if arguments.next().is_some() {
                return Err("usage: .hol rank ID".into());
            }
            let rank = repl.hol_mut(connection)?.kind_rank(kind)?;
            writeln!(output, "rank {} = {rank}", kind.get())?;
        }
        Some("type") => run_hol_type(repl, output, connection, arguments)?,
        Some("term") => run_hol_term(repl, output, connection, arguments)?,
        Some("ctx") => run_hol_context(repl, output, connection, arguments)?,
        Some("namespace") => run_hol_namespace(repl, output, connection, arguments)?,
        Some("export") => run_hol_export(repl, output, connection, arguments)?,
        Some("snapshot") => run_hol_snapshot(repl, output, connection, arguments)?,
        Some("import") => run_hol_import(repl, output, connection, arguments)?,
        Some("prove") => run_hol_proof(repl, output, connection, arguments)?,
        Some("proved") => {
            let context = parse_context_id(arguments.next(), "context")?;
            let term = parse_term_id(arguments.next(), "term")?;
            if arguments.next().is_some() {
                return Err("usage: .hol proved CONTEXT TERM".into());
            }
            let proved = repl.hol_mut(connection)?.proved_judgement(context, term)?;
            writeln!(output, "proved {} {} = {proved}", context.get(), term.get())?;
        }
        _ => {
            return Err(
                "usage: .hol star|arrow|show|rank|type|term|ctx|namespace|export|snapshot|import|metadata|script|prove|proved ..."
                    .into(),
            );
        }
    }
    Ok(())
}

fn run_hol_metadata(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    arguments: &str,
) -> Result<()> {
    if let Some(request) = arguments.strip_prefix("get ") {
        let values = repl.hol_metadata_json(connection, request)?;
        writeln!(output, "metadata {values}")?;
        return Ok(());
    }
    if let Some(request) = arguments.strip_prefix("set ") {
        repl.set_hol_metadata_json(connection, request)?;
        writeln!(output, "metadata updated")?;
        return Ok(());
    }
    Err("usage: .hol metadata get|set JSON".into())
}

fn run_hol_import<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("trust") => {
            let schema = parse_o256(arguments.next(), "schema")?;
            let image = parse_o256(arguments.next(), "image")?;
            let signer = parse_o256(arguments.next(), "signer")?;
            let public_key = parse_fixed_hex::<32>(arguments.next(), "public key")?;
            let signature = parse_hex(arguments.next(), "signature")?;
            if arguments.next().is_some() {
                return Err(
                    "usage: .hol import trust SCHEMA IMAGE SIGNER PUBLIC_KEY SIGNATURE".into(),
                );
            }
            let trusted =
                repl.trust_hol_import(connection, schema, image, signer, public_key, &signature)?;
            writeln!(
                output,
                "trusted-import {} import={} schema={} image={} signer={}",
                trusted.trusted_import().get(),
                trusted.import().get(),
                trusted.database().schema(),
                trusted.database().image(),
                trusted.signer()
            )?;
        }
        Some("show") => {
            let trusted_import = TrustedImportId::from_i64(
                arguments
                    .next()
                    .ok_or("missing trusted-import ID")?
                    .parse()?,
            );
            if arguments.next().is_some() {
                return Err("usage: .hol import show TRUSTED_IMPORT_ID".into());
            }
            let trusted = repl.hol_trusted_import(connection, trusted_import)?;
            writeln!(
                output,
                "trusted-import {} import={} schema={} image={} signer={}",
                trusted.trusted_import().get(),
                trusted.import().get(),
                trusted.database().schema(),
                trusted.database().image(),
                trusted.signer()
            )?;
        }
        Some("namespace") => run_hol_import_namespace(repl, output, connection, arguments)?,
        Some("inspect") => run_hol_import_inspect(repl, output, connection, arguments)?,
        Some("inspect-resident") => {
            run_hol_import_inspect_resident(repl, output, connection, arguments)?;
        }
        _ => {
            return Err("usage: .hol import trust ...|show ID|namespace ...|inspect ...|inspect-resident ...".into());
        }
    }
    Ok(())
}

fn run_hol_import_namespace<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    let import =
        covalence_repl::ImportId::from_i64(arguments.next().ok_or("missing import ID")?.parse()?);
    let source_namespace = arguments
        .next()
        .ok_or("missing source namespace ID")?
        .parse()?;
    let parent =
        parse_optional_id(arguments.next(), "parent namespace")?.map(NamespaceId::from_i64);
    let name = arguments.next().ok_or("missing namespace name")?;
    let name = (name != "-").then_some(name);
    if arguments.next().is_some() {
        return Err("usage: .hol import namespace IMPORT SOURCE_NAMESPACE PARENT|- NAME|-".into());
    }
    let namespace =
        repl.create_hol_imported_namespace(connection, parent, name, import, source_namespace)?;
    writeln!(output, "imported-namespace {}", namespace.get())?;
    Ok(())
}

fn run_hol_import_inspect<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    let trusted = TrustedImportId::from_i64(
        arguments
            .next()
            .ok_or("missing trusted-import ID")?
            .parse()?,
    );
    let namespace = NamespaceId::from_i64(
        arguments
            .next()
            .ok_or("missing imported namespace ID")?
            .parse()?,
    );
    let export = ExportId::from_i64(arguments.next().ok_or("missing export ID")?.parse()?);
    let path = arguments.next().ok_or("missing snapshot path")?;
    let descriptor_path = arguments.next().ok_or("missing descriptor path")?;
    let schema = parse_o256(arguments.next(), "schema")?;
    let image = parse_o256(arguments.next(), "image")?;
    let signer = parse_o256(arguments.next(), "signer")?;
    let public_key = parse_fixed_hex::<32>(arguments.next(), "public key")?;
    let signature = parse_hex(arguments.next(), "signature")?;
    if arguments.next().is_some() {
        return Err("usage: .hol import inspect TRUSTED_IMPORT NAMESPACE EXPORT PATH DESCRIPTOR_PATH SCHEMA IMAGE SIGNER PUBLIC_KEY SIGNATURE".into());
    }
    let bytes = fs::read(path)?;
    let descriptor = fs::read(descriptor_path)?;
    let value = repl.inspect_trusted_hol_export_with_descriptor(
        connection,
        trusted,
        &bytes,
        &descriptor,
        schema,
        image,
        signer,
        public_key,
        &signature,
        namespace,
        export,
    )?;
    writeln!(output, "imported-export {value:?}")?;
    Ok(())
}

fn run_hol_import_inspect_resident<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    let trusted = TrustedImportId::from_i64(
        arguments
            .next()
            .ok_or("missing trusted-import ID")?
            .parse()?,
    );
    let namespace = NamespaceId::from_i64(
        arguments
            .next()
            .ok_or("missing imported namespace ID")?
            .parse()?,
    );
    let export = ExportId::from_i64(arguments.next().ok_or("missing export ID")?.parse()?);
    let image = parse_o256(arguments.next(), "image")?;
    if arguments.next().is_some() {
        return Err(
            "usage: .hol import inspect-resident TRUSTED_IMPORT NAMESPACE EXPORT IMAGE".into(),
        );
    }
    let value =
        repl.inspect_resident_trusted_hol_export(connection, trusted, image, namespace, export)?;
    writeln!(output, "imported-export {value:?}")?;
    Ok(())
}

fn parse_o256(value: Option<&str>, label: &str) -> Result<O256> {
    O256::from_hex(value.ok_or_else(|| format!("missing {label}"))?).map_err(Into::into)
}

fn parse_hex(value: Option<&str>, label: &str) -> Result<Vec<u8>> {
    let value = value.ok_or_else(|| format!("missing {label}"))?;
    if !value.is_ascii() || value.len() % 2 != 0 {
        return Err(format!("{label} must contain an even number of hex digits").into());
    }
    (0..value.len())
        .step_by(2)
        .map(|offset| u8::from_str_radix(&value[offset..offset + 2], 16).map_err(Into::into))
        .collect()
}

fn parse_fixed_hex<const N: usize>(value: Option<&str>, label: &str) -> Result<[u8; N]> {
    let decoded = parse_hex(value, label)?;
    decoded
        .try_into()
        .map_err(|_: Vec<u8>| format!("{label} must be exactly {N} bytes").into())
}

fn run_hol_namespace<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("create") => {
            let parent = parse_optional_id(arguments.next(), "parent")?.map(NamespaceId::from_i64);
            let name = parse_optional_text(arguments.next());
            if arguments.next().is_some() {
                return Err("usage: .hol namespace create PARENT|- NAME|-".into());
            }
            let namespace = repl.create_hol_namespace(connection, parent, name)?;
            writeln!(output, "namespace {} defined", namespace.get())?;
        }
        Some("show") => {
            let namespace = parse_namespace_id(arguments.next(), "namespace")?;
            if arguments.next().is_some() {
                return Err("usage: .hol namespace show ID".into());
            }
            let view = repl.hol_namespace(connection, namespace)?;
            writeln!(
                output,
                "namespace {} parent={} name={}",
                namespace.get(),
                view.parent
                    .map_or_else(|| "-".to_owned(), |id| id.get().to_string()),
                view.name.as_deref().unwrap_or("-")
            )?;
        }
        _ => return Err("usage: .hol namespace create PARENT|- NAME|-|show ID".into()),
    }
    Ok(())
}

fn run_hol_export<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("bind") => {
            let namespace = parse_namespace_id(arguments.next(), "namespace")?;
            let export = parse_export_id(arguments.next(), "export")?;
            let sort = arguments.next().ok_or("missing export sort")?;
            let local: i64 = arguments.next().ok_or("missing local ID")?.parse()?;
            let name = parse_optional_text(arguments.next());
            if arguments.next().is_some() {
                return Err(
                    "usage: .hol export bind NAMESPACE EXPORT KIND|TYPE|TERM|CONTEXT LOCAL [NAME|-]"
                        .into(),
                );
            }
            let value = parse_namespace_export(sort, local)?;
            repl.bind_hol_export(connection, namespace, export, value, name)?;
            writeln!(
                output,
                "export {}:{} = {} {}",
                namespace.get(),
                export.get(),
                sort,
                local
            )?;
        }
        Some("show") => {
            let namespace = parse_namespace_id(arguments.next(), "namespace")?;
            let export = parse_export_id(arguments.next(), "export")?;
            if arguments.next().is_some() {
                return Err("usage: .hol export show NAMESPACE EXPORT".into());
            }
            let view = repl
                .hol_export(connection, namespace, export)?
                .ok_or("unknown export")?;
            let (sort, local) = format_namespace_export(view.value);
            writeln!(
                output,
                "export {}:{} = {} {} name={}",
                namespace.get(),
                export.get(),
                sort,
                local,
                view.name.as_deref().unwrap_or("-")
            )?;
        }
        Some("resolve") => {
            let namespace = parse_namespace_id(arguments.next(), "namespace")?;
            let name = arguments.next().ok_or("missing export name")?;
            if arguments.next().is_some() {
                return Err("usage: .hol export resolve NAMESPACE NAME".into());
            }
            let (export, _) = repl
                .resolve_hol_export_name(connection, namespace, name)?
                .ok_or("unknown export name")?;
            writeln!(output, "export {}:{}", namespace.get(), export.get())?;
        }
        _ => {
            return Err(
                "usage: .hol export bind NAMESPACE EXPORT SORT LOCAL [NAME|-]|show NAMESPACE EXPORT|resolve NAMESPACE NAME"
                    .into(),
            );
        }
    }
    Ok(())
}

fn run_hol_snapshot<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    if arguments.next() != Some("export") {
        return Err("usage: .hol snapshot export PATH".into());
    }
    let path = arguments.next().ok_or("missing snapshot path")?;
    if arguments.next().is_some() {
        return Err("usage: .hol snapshot export PATH".into());
    }
    let snapshot = repl.export_hol_snapshot(connection)?;
    fs::write(path, snapshot.bytes())?;
    let descriptor_path = format!("{path}.hol-schema");
    fs::write(&descriptor_path, snapshot.descriptor())?;
    writeln!(output, "descriptor {descriptor_path}")?;
    writeln!(output, "schema {}", snapshot.schema())?;
    writeln!(output, "image {}", snapshot.image())?;
    writeln!(output, "signer {}", snapshot.signer())?;
    writeln!(output, "public-key {}", hex(snapshot.public_key()))?;
    writeln!(output, "signature {}", hex(snapshot.signature()))?;
    Ok(())
}

fn parse_optional_id(value: Option<&str>, label: &str) -> Result<Option<i64>> {
    match value {
        Some("-") => Ok(None),
        Some(value) => Ok(Some(value.parse()?)),
        None => Err(format!("missing {label}").into()),
    }
}

fn parse_optional_text(value: Option<&str>) -> Option<&str> {
    value.filter(|value| *value != "-")
}

fn parse_namespace_id(value: Option<&str>, label: &str) -> Result<NamespaceId> {
    value
        .ok_or_else(|| format!("missing {label}"))?
        .parse()
        .map(NamespaceId::from_i64)
        .map_err(Into::into)
}

fn parse_export_id(value: Option<&str>, label: &str) -> Result<ExportId> {
    value
        .ok_or_else(|| format!("missing {label}"))?
        .parse()
        .map(ExportId::from_i64)
        .map_err(Into::into)
}

fn parse_namespace_export(sort: &str, local: i64) -> Result<NamespaceExport> {
    match sort {
        "kind" => Ok(NamespaceExport::Kind(KindId::from_i64(local))),
        "type" => Ok(NamespaceExport::Type(TypeId::from_i64(local))),
        "term" => Ok(NamespaceExport::Term(TermId::from_i64(local))),
        "context" => Ok(NamespaceExport::Context(ContextId::from_i64(local))),
        _ => Err(format!("unknown export sort: {sort}").into()),
    }
}

fn format_namespace_export(value: NamespaceExport) -> (&'static str, i64) {
    match value {
        NamespaceExport::Kind(id) => ("kind", id.get()),
        NamespaceExport::Type(id) => ("type", id.get()),
        NamespaceExport::Term(id) => ("term", id.get()),
        NamespaceExport::Context(id) => ("context", id.get()),
    }
}

fn hex(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

fn run_hol_context<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("define") => {
            let members = arguments
                .map(|value| value.parse().map(TermId::from_i64))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            let context = repl.hol_mut(connection)?.define_context(members)?;
            writeln!(output, "context {} defined", context.get())?;
        }
        Some("show") => {
            let context = parse_context_id(arguments.next(), "context")?;
            if arguments.next().is_some() {
                return Err("usage: .hol ctx show ID".into());
            }
            let members = repl.hol_mut(connection)?.context_members(context)?;
            writeln!(
                output,
                "context {} = {}",
                context.get(),
                members
                    .iter()
                    .map(|term| term.get().to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            )?;
        }
        _ => return Err("usage: .hol ctx define [TERM...]|show ID".into()),
    }
    Ok(())
}

fn run_hol_proof<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    let (theorem_context, theorem_conclusion) = match arguments.next() {
        Some("hyp") => {
            let context = parse_context_id(arguments.next(), "context")?;
            let term = parse_term_id(arguments.next(), "term")?;
            if arguments.next().is_some() {
                return Err("usage: .hol prove hyp CONTEXT TERM".into());
            }
            repl.hol_mut(connection)?.with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, term)?;
                let result = (theorem.context(), theorem.conclusion());
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(result)
            })?
        }
        Some("truth") => {
            let context = parse_context_id(arguments.next(), "context")?;
            if arguments.next().is_some() {
                return Err("usage: .hol prove truth CONTEXT".into());
            }
            repl.hol_mut(connection)?.with_proof_session(|mut proof| {
                let theorem = proof.prove_truth(context)?;
                let result = (theorem.context(), theorem.conclusion());
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(result)
            })?
        }
        Some("refl") => {
            let context = parse_context_id(arguments.next(), "context")?;
            let term = parse_term_id(arguments.next(), "term")?;
            if arguments.next().is_some() {
                return Err("usage: .hol prove refl CONTEXT TERM".into());
            }
            repl.hol_mut(connection)?.with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(context, term)?;
                let result = (theorem.context(), theorem.conclusion());
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(result)
            })?
        }
        Some("beta") => {
            let context = parse_context_id(arguments.next(), "context")?;
            let abstraction = parse_term_id(arguments.next(), "abstraction")?;
            let argument = parse_term_id(arguments.next(), "argument")?;
            if arguments.next().is_some() {
                return Err("usage: .hol prove beta CONTEXT ABSTRACTION ARGUMENT".into());
            }
            repl.hol_mut(connection)?.with_proof_session(|mut proof| {
                let theorem = proof.prove_beta(context, abstraction, argument)?;
                let result = (theorem.context(), theorem.conclusion());
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(result)
            })?
        }
        Some("eqmp") => run_hol_eqmp(repl, connection, &mut arguments)?,
        Some("implies") => {
            let antecedent = parse_context_id(arguments.next(), "antecedent")?;
            let consequent = parse_context_id(arguments.next(), "consequent")?;
            let witnesses = arguments
                .map(|value| value.parse().map(TermId::from_i64))
                .collect::<std::result::Result<Vec<_>, _>>()?;
            repl.prove_context_implication(connection, antecedent, consequent, &witnesses)?;
            writeln!(
                output,
                "context implication {} => {}",
                antecedent.get(),
                consequent.get()
            )?;
            return Ok(());
        }
        Some("weaken") => {
            let antecedent = parse_context_id(arguments.next(), "antecedent")?;
            let consequent = parse_context_id(arguments.next(), "consequent")?;
            let conclusion = parse_term_id(arguments.next(), "conclusion")?;
            if arguments.next().is_some() {
                return Err("usage: .hol prove weaken ANTECEDENT CONSEQUENT CONCLUSION".into());
            }
            let conclusion = repl.weaken(connection, antecedent, consequent, conclusion)?;
            (antecedent, conclusion)
        }
        _ => {
            return Err(
                "usage: .hol prove hyp CONTEXT TERM|truth CONTEXT|refl CONTEXT TERM|beta CONTEXT ABSTRACTION ARGUMENT|eqmp CONTEXT EQUALITY PREMISE|implies ANTECEDENT CONSEQUENT WITNESS_TERM...|weaken ANTECEDENT CONSEQUENT CONCLUSION".into(),
            );
        }
    };
    writeln!(
        output,
        "theorem {} |- {}",
        theorem_context.get(),
        theorem_conclusion.get()
    )?;
    Ok(())
}

fn run_hol_eqmp<'a>(
    repl: &mut LocalRepl,
    connection: ConnectionId,
    arguments: &mut impl Iterator<Item = &'a str>,
) -> Result<(ContextId, TermId)> {
    let context = parse_context_id(arguments.next(), "context")?;
    let equality = parse_term_id(arguments.next(), "equality")?;
    let premise = parse_term_id(arguments.next(), "premise")?;
    if arguments.next().is_some() {
        return Err("usage: .hol prove eqmp CONTEXT EQUALITY PREMISE".into());
    }
    Ok((
        context,
        repl.equality_modus_ponens(connection, context, equality, premise)?,
    ))
}

fn run_hol_type<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("bool") if arguments.next().is_none() => {
            let ty = repl.hol_mut(connection)?.insert_bool_type()?;
            writeln!(output, "type {} = Bool", ty.get())?;
        }
        Some("base") => {
            let symbol: i64 = arguments
                .next()
                .ok_or("missing base type symbol")?
                .parse()?;
            if arguments.next().is_some() {
                return Err("usage: .hol type base SYMBOL".into());
            }
            let ty = repl.hol_mut(connection)?.insert_base_type(symbol)?;
            writeln!(output, "type {} = base {symbol}", ty.get())?;
        }
        Some("arrow") => {
            let domain = parse_type_id(arguments.next(), "domain")?;
            let codomain = parse_type_id(arguments.next(), "codomain")?;
            if arguments.next().is_some() {
                return Err("usage: .hol type arrow DOMAIN CODOMAIN".into());
            }
            let ty = repl
                .hol_mut(connection)?
                .insert_arrow_type(domain, codomain)?;
            writeln!(
                output,
                "type {} = {} -> {}",
                ty.get(),
                domain.get(),
                codomain.get()
            )?;
        }
        Some("show") => {
            let ty = parse_type_id(arguments.next(), "type")?;
            if arguments.next().is_some() {
                return Err("usage: .hol type show ID".into());
            }
            match repl.hol_mut(connection)?.type_view(ty)? {
                TypeView::Bool => writeln!(output, "type {} = Bool", ty.get())?,
                TypeView::Base { symbol } => {
                    writeln!(output, "type {} = base {symbol}", ty.get())?;
                }
                TypeView::Free { symbol } => {
                    writeln!(output, "type {} = free {symbol}", ty.get())?;
                }
                TypeView::Arrow { domain, codomain } => writeln!(
                    output,
                    "type {} = {} -> {}",
                    ty.get(),
                    domain.get(),
                    codomain.get()
                )?,
            }
        }
        _ => return Err("usage: .hol type bool|base SYMBOL|arrow D C|show ID".into()),
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn run_hol_term<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    match arguments.next() {
        Some("bool") => {
            let value = match arguments.next() {
                Some("true") => true,
                Some("false") => false,
                _ => return Err("usage: .hol term bool true|false".into()),
            };
            if arguments.next().is_some() {
                return Err("usage: .hol term bool true|false".into());
            }
            let term = repl.hol_mut(connection)?.insert_bool_term(value)?;
            writeln!(output, "term {} = {value}", term.get())?;
        }
        Some("free") => {
            let symbol: i64 = arguments.next().ok_or("missing symbol ID")?.parse()?;
            let ty = parse_type_id(arguments.next(), "type")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term free SYMBOL TYPE".into());
            }
            let term = repl.hol_mut(connection)?.insert_free_term(symbol, ty)?;
            writeln!(output, "term {} = free {symbol} : {}", term.get(), ty.get())?;
        }
        Some("constant") => {
            let symbol: i64 = arguments.next().ok_or("missing constant symbol")?.parse()?;
            let ty = parse_type_id(arguments.next(), "type")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term constant SYMBOL TYPE".into());
            }
            let term = repl.hol_mut(connection)?.insert_constant(symbol, ty)?;
            writeln!(
                output,
                "term {} = constant {symbol} : {}",
                term.get(),
                ty.get()
            )?;
        }
        Some("bound") => {
            let index: u32 = arguments.next().ok_or("missing de Bruijn index")?.parse()?;
            let ty = parse_type_id(arguments.next(), "type")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term bound INDEX TYPE".into());
            }
            let term = repl.hol_mut(connection)?.insert_bound_term(index, ty)?;
            writeln!(output, "term {} = bound {index} : {}", term.get(), ty.get())?;
        }
        Some("app") => {
            let function = parse_term_id(arguments.next(), "function")?;
            let argument = parse_term_id(arguments.next(), "argument")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term app FUNCTION ARGUMENT".into());
            }
            let term = repl
                .hol_mut(connection)?
                .insert_application(function, argument)?;
            writeln!(
                output,
                "term {} = app {} {}",
                term.get(),
                function.get(),
                argument.get()
            )?;
        }
        Some("lam") => {
            let parameter_type = parse_type_id(arguments.next(), "parameter")?;
            let body = parse_term_id(arguments.next(), "body")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term lam TYPE BODY".into());
            }
            let term = repl
                .hol_mut(connection)?
                .insert_lambda(parameter_type, body)?;
            writeln!(
                output,
                "term {} = lam {} {}",
                term.get(),
                parameter_type.get(),
                body.get()
            )?;
        }
        Some("eq") => {
            let left = parse_term_id(arguments.next(), "left")?;
            let right = parse_term_id(arguments.next(), "right")?;
            if arguments.next().is_some() {
                return Err("usage: .hol term eq LEFT RIGHT".into());
            }
            let term = repl.hol_mut(connection)?.insert_equality(left, right)?;
            writeln!(
                output,
                "term {} = eq {} {}",
                term.get(),
                left.get(),
                right.get()
            )?;
        }
        Some(operation @ ("show" | "type" | "freevars" | "closed" | "unbound")) => {
            run_hol_term_query(repl, output, connection, operation, arguments)?;
        }
        _ => {
            return Err(
                "usage: .hol term bool|constant|free|bound|app|lam|eq|show|type|freevars|closed|unbound ..."
                    .into(),
            );
        }
    }
    Ok(())
}

fn run_hol_term_query<'a>(
    repl: &mut LocalRepl,
    output: &mut impl io::Write,
    connection: ConnectionId,
    operation: &str,
    mut arguments: impl Iterator<Item = &'a str>,
) -> Result<()> {
    let term = parse_term_id(arguments.next(), "term")?;
    if arguments.next().is_some() {
        return Err(format!("usage: .hol term {operation} ID").into());
    }
    match operation {
        "show" => match repl.hol_mut(connection)?.term(term)? {
            TermView::Bool(value) => writeln!(output, "term {} = {value}", term.get())?,
            TermView::Constant { symbol } => {
                writeln!(output, "term {} = constant {symbol}", term.get())?;
            }
            TermView::Free { symbol } => writeln!(output, "term {} = free {symbol}", term.get())?,
            TermView::Bound { index } => writeln!(output, "term {} = bound {index}", term.get())?,
            TermView::Application { function, argument } => writeln!(
                output,
                "term {} = app {} {}",
                term.get(),
                function.get(),
                argument.get()
            )?,
            TermView::Lambda {
                parameter_type,
                body,
            } => writeln!(
                output,
                "term {} = lam {} {}",
                term.get(),
                parameter_type.get(),
                body.get()
            )?,
            TermView::Equality { left, right } => writeln!(
                output,
                "term {} = eq {} {}",
                term.get(),
                left.get(),
                right.get()
            )?,
            TermView::Epsilon { predicate } => {
                writeln!(output, "term {} = epsilon {}", term.get(), predicate.get())?;
            }
        },
        "type" => {
            let ty = repl.hol_mut(connection)?.term_type(term)?;
            writeln!(output, "term {} : {}", term.get(), ty.get())?;
        }
        "freevars" => {
            let variables = repl.hol_mut(connection)?.term_free_variables(term)?;
            writeln!(
                output,
                "freevars {} = {}",
                term.get(),
                variables
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            )?;
        }
        "closed" => {
            let closed = repl.hol_mut(connection)?.term_is_locally_closed(term)?;
            writeln!(output, "closed {} = {closed}", term.get())?;
        }
        "unbound" => {
            let variables = repl.hol_mut(connection)?.term_unbound_variables(term)?;
            writeln!(
                output,
                "unbound {} = {}",
                term.get(),
                variables
                    .iter()
                    .map(|variable| format!("{}:{}", variable.index, variable.ty.get()))
                    .collect::<Vec<_>>()
                    .join(",")
            )?;
        }
        _ => unreachable!("caller filters term query operations"),
    }
    Ok(())
}

fn parse_kind_id(value: Option<&str>, name: &str) -> Result<KindId> {
    let value = value.ok_or_else(|| format!("missing {name} kind ID"))?;
    Ok(KindId::from_i64(value.parse()?))
}

fn parse_type_id(value: Option<&str>, name: &str) -> Result<TypeId> {
    let value = value.ok_or_else(|| format!("missing {name} type ID"))?;
    Ok(TypeId::from_i64(value.parse()?))
}

fn parse_term_id(value: Option<&str>, name: &str) -> Result<TermId> {
    let value = value.ok_or_else(|| format!("missing {name} term ID"))?;
    Ok(TermId::from_i64(value.parse()?))
}

fn parse_context_id(value: Option<&str>, name: &str) -> Result<ContextId> {
    let value = value.ok_or_else(|| format!("missing {name} context ID"))?;
    Ok(ContextId::from_i64(value.parse()?))
}

fn run_repl(
    input: &mut impl io::BufRead,
    output: &mut impl io::Write,
    errors: &mut impl io::Write,
    prompt: bool,
) -> Result<()> {
    let mut repl = LocalRepl::new()?;
    open_connection(&mut repl, "sql")?;
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
        match run_line(&mut repl, output, &line) {
            Ok(true) => {}
            Ok(false) => break,
            Err(error) => writeln!(errors, "error: {error}")?,
        }
    }
    Ok(())
}

fn usage(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(output, "usage: nucleus [-c SQL]")?;
    writeln!(
        output,
        "       nucleus serve [--listen ADDRESS] [--allow-key PUBLIC_KEY]... [--bootstrap]"
    )?;
    writeln!(output, "       nucleus --help")
}

fn run_native_server(mut arguments: impl Iterator<Item = String>) -> Result<()> {
    let mut listen = "127.0.0.1:0".parse::<SocketAddr>()?;
    let mut allowed_callers = Vec::new();
    let mut bootstrap = None;
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--listen" => {
                listen = arguments
                    .next()
                    .ok_or("--listen requires a numeric loopback address")?
                    .parse()?;
            }
            "--allow-key" => allowed_callers.push(parse_fixed_hex::<32>(
                arguments.next().as_deref(),
                "allowed caller public key",
            )?),
            "--bootstrap" if bootstrap.is_none() => bootstrap = Some(random_bootstrap_token()),
            "--bootstrap" => return Err("--bootstrap may be supplied only once".into()),
            _ => return Err(format!("unexpected serve argument: {argument}").into()),
        }
    }
    let mut config = NativeKernelServerConfig::new(listen, allowed_callers);
    if let Some(token) = bootstrap {
        config = config.with_bootstrap_token(token);
    }
    let server = spawn_native_kernel_server(config)?;
    let mut output = io::stdout().lock();
    writeln!(output, "listen {}", server.address())?;
    writeln!(output, "kernel-key {}", hex(&server.public_key()))?;
    if let Some(token) = bootstrap {
        writeln!(output, "bootstrap-token {}", hex(&token))?;
    }
    output.flush()?;
    loop {
        std::thread::park();
    }
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
            let mut repl = LocalRepl::new()?;
            let id = open_connection(&mut repl, "sql")?;
            let outcome = repl.run_sql(id, &sql)?;
            print_outcome(&mut io::stdout().lock(), &outcome)?;
            Ok(())
        }
        Some("-h" | "--help") => {
            usage(&mut io::stdout().lock())?;
            Ok(())
        }
        Some("serve") => run_native_server(arguments),
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
    use covalence_repl::{Connection, NativeKernelServerError, Sql};

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
        assert!(output.contains("opened sql connection 2 on kernel 0\n"));
        assert!(output.contains("absent\n0\n"));
        assert!(output.contains("using connection 1\n"));
        assert!(output.contains("value\n42\n"));
        assert!(output.contains("* 1\t@0\tnucleus/sql\n"));
        assert!(output.contains("  2\t@0\tnucleus/sql\n"));
        assert!(output.contains("closed connection 2\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn routes_terminal_connections_to_independently_keyed_kernels() {
        let mut input = Cursor::new(
            ".kernel new\n.kernels\n.open @1 sql\nSELECT 42 AS remote_local\n.open @1 hol\n.hol star\n.connections\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("created local kernel 1\n"));
        let kernel_rows = output
            .lines()
            .filter(|line| line.starts_with("0\tlocal\t-") || line.starts_with("1\tlocal\t-"))
            .collect::<Vec<_>>();
        assert_eq!(kernel_rows.len(), 2);
        assert_ne!(
            kernel_rows[0].split('\t').nth(3),
            kernel_rows[1].split('\t').nth(3)
        );
        assert!(output.contains("opened sql connection 2 on kernel 1\n"));
        assert!(output.contains("remote_local\n42\n"));
        assert!(output.contains("opened hol connection 3 on kernel 1\n"));
        assert!(output.contains("kind 1 = star\n"));
        assert!(output.contains("  2\t@1\tnucleus/sql\n"));
        assert!(output.contains("* 3\t@1\tnucleus/hol-common-v2\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn connects_the_terminal_repl_to_a_native_http_kernel() {
        let bootstrap = [0x6b; 32];
        let server = match spawn_native_kernel_server(
            NativeKernelServerConfig::new("127.0.0.1:0".parse().unwrap(), [])
                .with_bootstrap_token(bootstrap),
        ) {
            Ok(server) => server,
            Err(NativeKernelServerError::Io(error))
                if error.kind() == io::ErrorKind::PermissionDenied =>
            {
                return;
            }
            Err(error) => panic!("could not start loopback kernel: {error}"),
        };
        let mut repl = LocalRepl::new().unwrap();
        let mut output = Vec::new();
        let connect = format!(
            ".kernel connect-http {} {} {}",
            server.address(),
            hex(&server.public_key()),
            hex(&bootstrap)
        );

        assert!(run_line(&mut repl, &mut output, &connect).unwrap());
        assert!(run_line(&mut repl, &mut output, ".open @1 sql").unwrap());
        assert!(run_line(&mut repl, &mut output, "SELECT 42 AS native_http_answer").unwrap());
        assert!(run_line(&mut repl, &mut output, ".kernels").unwrap());

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("connected native HTTP kernel 1\n"));
        assert!(output.contains("opened sql connection 1 on kernel 1\n"));
        assert!(output.contains("native_http_answer\n42\n"));
        assert!(output.contains(&format!(
            "1\tnative-http\t{}\t{}",
            server.address(),
            hex(&server.public_key())
        )));
        drop(repl);
        server.shutdown().unwrap();
    }

    #[test]
    fn manages_sql_and_hol_connections_in_one_repl() {
        let mut input = Cursor::new(
            ".open hol\n.hol star\n.hol arrow 1 1\n.hol show 3\n.hol rank 3\n.hol type bool\n.hol type arrow 2 2\n.hol term free 100 4\n.hol term free 101 2\n.hol term app 5 6\n.hol term type 7\n.hol term freevars 7\n.hol ctx define 7\n.hol ctx show 1\n.hol prove hyp 1 7\n.hol prove truth 0\n.hol proved 1 7\n.hol proved 0 8\n.hol term bound 0 2\n.hol term unbound 9\n.hol term closed 9\n.hol term lam 2 9\n.hol term show 10\n.hol term closed 10\n.hol prove refl 0 10\n.hol term show 11\n.hol proved 0 11\n.hol prove beta 0 10 8\n.hol term show 13\n.hol proved 0 13\n.hol ctx define 6\n.hol ctx define 6 8\n.hol prove refl 2 6\n.hol prove hyp 3 6\n.hol prove implies 3 2 6\n.hol proved 3 14\n.hol prove weaken 3 2 14\n.hol proved 3 14\n.connections\n.use 1\nSELECT 42 AS sql_still_live\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("opened hol connection 2 on kernel 0\n"));
        assert!(output.contains("kind 1 = star\n"));
        assert!(output.contains("kind 3 = 1 -> 1\n"));
        assert!(output.contains("rank 3 = 1\n"));
        assert!(output.contains("type 2 = Bool\n"));
        assert!(output.contains("type 4 = 2 -> 2\n"));
        assert!(output.contains("term 7 = app 5 6\n"));
        assert!(output.contains("term 7 : 2\n"));
        assert!(output.contains("freevars 7 = 100,101\n"));
        assert!(output.contains("context 1 defined\n"));
        assert!(output.contains("context 1 = 7\n"));
        assert!(output.contains("theorem 1 |- 7\n"));
        assert!(output.contains("theorem 0 |- 8\n"));
        assert!(output.contains("proved 1 7 = true\n"));
        assert!(output.contains("proved 0 8 = true\n"));
        assert!(output.contains("term 9 = bound 0 : 2\n"));
        assert!(output.contains("unbound 9 = 0:2\n"));
        assert!(output.contains("closed 9 = false\n"));
        assert!(output.contains("term 10 = lam 2 9\n"));
        assert!(output.contains("closed 10 = true\n"));
        assert!(output.contains("theorem 0 |- 11\n"));
        assert!(output.contains("term 11 = eq 10 10\n"));
        assert!(output.contains("proved 0 11 = true\n"));
        assert!(output.contains("theorem 0 |- 13\n"));
        assert!(output.contains("term 13 = eq 12 8\n"));
        assert!(output.contains("proved 0 13 = true\n"));
        assert!(output.contains("context implication 3 => 2\n"));
        assert!(output.contains("proved 3 14 = false\n"));
        assert!(output.contains("theorem 3 |- 14\n"));
        assert!(output.contains("proved 3 14 = true\n"));
        assert!(output.contains("  1\t@0\tnucleus/sql\n"));
        assert!(output.contains("* 2\t@0\tnucleus/hol-common-v2\n"));
        assert!(output.contains("sql_still_live\n42\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn terminal_replays_the_shared_strict_json_proof_recipe() {
        let mut input = Cursor::new(
            ".open hol\n.hol script {\"version\":1,\"steps\":[{\"op\":\"truth\",\"context\":0},{\"op\":\"persist_theorem\",\"theorem\":0}]}\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        assert!(String::from_utf8(output).unwrap().contains(
            "{\"version\":1,\"outputs\":[{\"kind\":\"theorem\",\"context\":0,\"conclusion\":3},{\"kind\":\"unit\"}]}\n"
        ));
        assert!(errors.is_empty());
    }

    #[test]
    fn terminal_trusts_and_inspects_a_hash_first_hol_import() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let truth = repl
            .hol_mut(source)
            .unwrap()
            .insert_bool_term(true)
            .unwrap();
        repl.bind_hol_export(
            source,
            NamespaceId::root(),
            ExportId::from_i64(7),
            NamespaceExport::Term(truth),
            Some("truth"),
        )
        .unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        let path = std::env::temp_dir().join(format!(
            "nucleus-hol-import-{}.sqlite",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let descriptor_path = path.with_extension("hol-schema");
        fs::write(&path, snapshot.bytes()).unwrap();
        fs::write(&descriptor_path, snapshot.descriptor()).unwrap();
        repl.select(target).unwrap();
        let command = format!(
            ".hol import trust {} {} {} {} {}",
            snapshot.schema(),
            snapshot.image(),
            snapshot.signer(),
            hex(snapshot.public_key()),
            hex(snapshot.signature())
        );
        let mut output = Vec::new();

        assert!(run_line(&mut repl, &mut output, &command).unwrap());
        assert!(run_line(&mut repl, &mut output, ".hol import show 0").unwrap());
        assert!(
            run_line(
                &mut repl,
                &mut output,
                ".hol import namespace 0 0 - downloaded"
            )
            .unwrap()
        );
        let put = format!(
            ".hol-snapshot put {} {} {} {} {} {} {}",
            path.display(),
            descriptor_path.display(),
            snapshot.schema(),
            snapshot.image(),
            snapshot.signer(),
            hex(snapshot.public_key()),
            hex(snapshot.signature())
        );
        assert!(run_line(&mut repl, &mut output, &put).unwrap());
        fs::remove_file(path).unwrap();
        fs::remove_file(descriptor_path).unwrap();
        let inspect = format!(".hol import inspect-resident 0 1 7 {}", snapshot.image());
        assert!(run_line(&mut repl, &mut output, &inspect).unwrap());

        let output = String::from_utf8(output).unwrap();
        let expected = format!(
            "trusted-import 0 import=0 schema={} image={} signer={}",
            snapshot.schema(),
            snapshot.image(),
            snapshot.signer()
        );
        assert_eq!(output.matches(&expected).count(), 2);
        assert!(output.contains(&format!("resident-hol {}", snapshot.image())));
        assert!(output.contains("imported-namespace 1\n"));
        assert!(output.contains("term: Bool(true)"));
        let exported = repl.export_hol_snapshot(target).unwrap();
        let validated = covalence_repl::ValidatedHolImage::validate(exported.bytes()).unwrap();
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);
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

    #[test]
    fn exports_named_hol_snapshot_through_the_terminal_surface() {
        let path = std::env::temp_dir().join(format!(
            "nucleus-hol-export-{}.sqlite",
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let json_path = path.with_extension("schema.json");
        let compiled_path = path.with_extension("compiled.hol-schema");
        fs::write(
            &json_path,
            r#"{"version":1,"columns":[{"table":"node","name":"origin","storage":"text"}],"indexes":[{"table":"node","name":"by_origin","columns":["origin"]}]}"#,
        )
        .unwrap();
        let descriptor_path = format!("{}.hol-schema", path.display());
        let script = format!(
            ".kernel new\n.hol-schema compile {} {}\n.open @1 hol --schema-json {}\n.hol star\n.hol metadata set {{\"target\":{{\"kind\":\"node\",\"id\":1}},\"assignments\":[{{\"column\":\"origin\",\"value\":{{\"kind\":\"text\",\"value\":\"terminal demo\"}}}}]}}\n.hol metadata get {{\"target\":{{\"kind\":\"node\",\"id\":1}},\"columns\":[\"origin\"]}}\n.hol namespace create 0 demo\n.hol namespace show 1\n.hol export bind 1 7 kind 1 star\n.hol export show 1 7\n.hol export resolve 1 star\n.hol snapshot export {}\n.open @1 hol --descriptor {}\n.quit\n",
            json_path.display(),
            compiled_path.display(),
            json_path.display(),
            path.display(),
            descriptor_path
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();
        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");
        let bytes = fs::read(&path).expect("read signed snapshot");
        let descriptor = fs::read(&descriptor_path).expect("read schema descriptor");
        let compiled = fs::read(&compiled_path).expect("read compiled descriptor");
        fs::remove_file(path).expect("remove signed snapshot");
        fs::remove_file(descriptor_path).expect("remove schema descriptor");
        fs::remove_file(json_path).expect("remove schema JSON");
        fs::remove_file(compiled_path).expect("remove compiled descriptor");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("namespace 1 defined\n"));
        assert!(output.contains("opened hol connection 2 on kernel 1\n"));
        assert!(output.contains("opened hol connection 3 on kernel 1\n"));
        assert!(output.contains("metadata updated\n"));
        assert!(output.contains("metadata [{\"kind\":\"text\",\"value\":\"terminal demo\"}]\n"));
        assert!(output.contains("namespace 1 parent=0 name=demo\n"));
        assert!(output.contains("export 1:7 = kind 1 name=star\n"));
        assert!(output.contains("schema "));
        assert!(output.contains("image "));
        assert!(output.contains("public-key "));
        assert!(output.contains("signature "));
        assert!(bytes.starts_with(b"SQLite format 3"));
        assert_eq!(compiled, descriptor);
        covalence_repl::HolSchemaDescriptor::decode(&descriptor).unwrap();
        assert!(errors.is_empty(), "{}", String::from_utf8(errors).unwrap());
    }
}
