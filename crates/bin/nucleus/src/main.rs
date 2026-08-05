use std::env;
use std::error::Error;
use std::fs;
use std::io;
use std::process::ExitCode;

use covalence_repl::{
    AllowAll, ConnectionId, HolRecipe, HolRecipeResult, Kernel, LocalConnection, MAX_IMAGE_BYTES,
    Outcome, Repl, Value,
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
    match outcome.judgement_id() {
        Some(id) => writeln!(output, "judgement\t{id}")?,
        None => writeln!(output, "judgement\t-")?,
    }
    writeln!(output, "statement\t{}", outcome.statement())
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
