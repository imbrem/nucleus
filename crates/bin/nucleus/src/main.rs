use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::process::ExitCode;

use covalence_repl::{
    ConnectionId, ContextId, ExportId, KindId, KindView, LocalRepl, NamespaceExport, NamespaceId,
    O256, Outcome, ProofError, TermId, TermView, TrustedImportId, TypeId, TypeView, Value,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;
fn open_connection(repl: &mut LocalRepl, protocol: &str) -> Result<ConnectionId> {
    match protocol {
        "sql" => Ok(repl.open_sql()?),
        "hol" => Ok(repl.open_hol()?),
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
    let connection = repl.sql_mut(id)?;
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
        let protocol = line.strip_prefix(".open").expect("matched prefix").trim();
        let protocol = if protocol.is_empty() { "sql" } else { protocol };
        let id = open_connection(repl, protocol)?;
        writeln!(output, "opened {protocol} connection {id}")?;
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
        repl.close(id)?;
        writeln!(output, "closed connection {id}")?;
        return Ok(true);
    }
    if line.starts_with(".load") {
        let (schema, path) = parse_load(line).ok_or("usage: .load SCHEMA PATH")?;
        load_image(repl, output, schema, path)?;
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
    let outcome = repl.sql_mut(id)?.run(line, &[])?;
    print_outcome(output, &outcome)?;
    Ok(true)
}

fn print_help(output: &mut impl io::Write) -> io::Result<()> {
    writeln!(
        output,
        ".load SCHEMA PATH  attach a complete immutable SQLite image"
    )?;
    writeln!(output, ".open [sql|hol]    open and select a connection")?;
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
        ".hol namespace ... define/inspect export namespaces"
    )?;
    writeln!(output, ".hol export ...    bind/inspect namespace exports")?;
    writeln!(
        output,
        ".hol snapshot export PATH  write a signed HOL image"
    )?;
    writeln!(
        output,
        ".hol import trust ...      trust and persist a hash-first signed import"
    )?;
    writeln!(
        output,
        ".hol import show ID        inspect a trusted import"
    )?;
    writeln!(output, ".hol prove ...     apply an explicit HOL rule")?;
    writeln!(output, ".quit              exit")
}

fn run_hol(repl: &mut LocalRepl, output: &mut impl io::Write, arguments: &str) -> Result<()> {
    let connection = repl.active()?.ok_or("no active connection")?;
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
                "usage: .hol star|arrow|show|rank|type|term|ctx|namespace|export|snapshot|import|prove|proved ..."
                    .into(),
            );
        }
    }
    Ok(())
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
        _ => {
            return Err(
                "usage: .hol import trust SCHEMA IMAGE SIGNER PUBLIC_KEY SIGNATURE|show ID".into(),
            );
        }
    }
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
                TypeView::Arrow { domain, codomain } => writeln!(
                    output,
                    "type {} = {} -> {}",
                    ty.get(),
                    domain.get(),
                    codomain.get()
                )?,
            }
        }
        _ => return Err("usage: .hol type bool|arrow D C|show ID".into()),
    }
    Ok(())
}

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
                "usage: .hol term bool|free|bound|app|lam|eq|show|type|freevars|closed|unbound ..."
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
    writeln!(output, "       nucleus --help")
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
            let outcome = repl.sql_mut(id)?.run(&sql, &[])?;
            print_outcome(&mut io::stdout().lock(), &outcome)?;
            Ok(())
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
        assert!(output.contains("opened sql connection 2\n"));
        assert!(output.contains("absent\n0\n"));
        assert!(output.contains("using connection 1\n"));
        assert!(output.contains("value\n42\n"));
        assert!(output.contains("* 1\tnucleus/sql\n"));
        assert!(output.contains("  2\tnucleus/sql\n"));
        assert!(output.contains("closed connection 2\n"));
        assert!(errors.is_empty());
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
        assert!(output.contains("opened hol connection 2\n"));
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
        assert!(output.contains("  1\tnucleus/sql\n"));
        assert!(output.contains("* 2\tnucleus/hol-common-v2\n"));
        assert!(output.contains("sql_still_live\n42\n"));
        assert!(errors.is_empty());
    }

    #[test]
    fn terminal_trusts_and_inspects_a_hash_first_hol_import() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
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

        let output = String::from_utf8(output).unwrap();
        let expected = format!(
            "trusted-import 0 import=0 schema={} image={} signer={}",
            snapshot.schema(),
            snapshot.image(),
            snapshot.signer()
        );
        assert_eq!(output.matches(&expected).count(), 2);
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
        let script = format!(
            ".open hol\n.hol star\n.hol namespace create 0 demo\n.hol namespace show 1\n.hol export bind 1 7 kind 1 star\n.hol export show 1 7\n.hol export resolve 1 star\n.hol snapshot export {}\n.quit\n",
            path.display()
        );
        let mut input = Cursor::new(script);
        let mut output = Vec::new();
        let mut errors = Vec::new();
        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");
        let bytes = fs::read(&path).expect("read signed snapshot");
        fs::remove_file(path).expect("remove signed snapshot");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("namespace 1 defined\n"));
        assert!(output.contains("namespace 1 parent=0 name=demo\n"));
        assert!(output.contains("export 1:7 = kind 1 name=star\n"));
        assert!(output.contains("schema "));
        assert!(output.contains("image "));
        assert!(output.contains("public-key "));
        assert!(output.contains("signature "));
        assert!(bytes.starts_with(b"SQLite format 3"));
        assert!(errors.is_empty(), "{}", String::from_utf8(errors).unwrap());
    }
}
