use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::process::ExitCode;

use covalence_repl::{ConnectionId, KindId, KindView, LocalRepl, Outcome, Value};

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
        writeln!(output, ".quit              exit")?;
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
        _ => return Err("usage: .hol star|arrow D C|show ID|rank ID".into()),
    }
    Ok(())
}

fn parse_kind_id(value: Option<&str>, name: &str) -> Result<KindId> {
    let value = value.ok_or_else(|| format!("missing {name} kind ID"))?;
    Ok(KindId::from_i64(value.parse()?))
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
            ".open hol\n.hol star\n.hol arrow 1 1\n.hol show 2\n.hol rank 2\n.connections\n.use 1\nSELECT 42 AS sql_still_live\n.quit\n",
        );
        let mut output = Vec::new();
        let mut errors = Vec::new();

        run_repl(&mut input, &mut output, &mut errors, false).expect("run REPL");

        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("opened hol connection 2\n"));
        assert!(output.contains("kind 1 = star\n"));
        assert!(output.contains("kind 2 = 1 -> 1\n"));
        assert!(output.contains("rank 2 = 1\n"));
        assert!(output.contains("  1\tnucleus/sql\n"));
        assert!(output.contains("* 2\tnucleus/hol-omega-v0\n"));
        assert!(output.contains("sql_still_live\n42\n"));
        assert!(errors.is_empty());
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
