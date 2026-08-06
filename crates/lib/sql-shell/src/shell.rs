//! The shell itself: state, the input loop, and dot-command execution.

use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use covalence_lib_sqlite::fallible_iterator::FallibleIterator as _;
use covalence_lib_sqlite::{Batch, Connection, OpenFlags, Statement};

use crate::command::{Command, ParseError};
use crate::complete::is_complete;
use crate::mode::Mode;
use crate::render::{Renderer, Style};
use crate::value::{Cell, quote_identifier};

/// How deep `.read` may nest before the shell assumes a cycle.
const MAX_READ_DEPTH: usize = 16;

/// Width assumed for `.tables` columns.
const SCREEN_WIDTH: usize = 80;

/// Where the shell writes.
struct ShellIo {
    default_out: Box<dyn Write>,
    redirect: Option<BufWriter<File>>,
    err: Box<dyn Write>,
}

impl ShellIo {
    /// The current result sink: the `.output` file if one is set.
    fn out(&mut self) -> &mut dyn Write {
        match &mut self.redirect {
            Some(file) => file,
            None => &mut *self.default_out,
        }
    }
}

/// A SQL shell over one connection.
///
/// Owns its output so that `.output` can redirect it; use
/// [`SharedBuffer`](crate::SharedBuffer) to read back what it wrote.
pub struct Shell {
    connection: Connection,
    style: Style,
    io: ShellIo,
    interactive: bool,
    quit: bool,
    errors: usize,
}

impl Shell {
    /// Constructs a shell around an open connection.
    #[must_use]
    pub fn new(connection: Connection, out: Box<dyn Write>, err: Box<dyn Write>) -> Self {
        Self {
            connection,
            style: Style::default(),
            io: ShellIo {
                default_out: out,
                redirect: None,
                err,
            },
            interactive: false,
            quit: false,
            errors: 0,
        }
    }

    /// Whether to print `sqlite> ` prompts.
    pub const fn set_interactive(&mut self, interactive: bool) {
        self.interactive = interactive;
    }

    /// The connection the shell is currently pointed at.
    #[must_use]
    pub const fn connection(&self) -> &Connection {
        &self.connection
    }

    /// How many statements or commands have failed.
    #[must_use]
    pub const fn errors(&self) -> usize {
        self.errors
    }

    /// Reads input until it runs out or `.quit` is seen.
    ///
    /// A line is a dot command when it begins with `.` *and* no partial
    /// statement is pending, which is upstream's rule and the reason
    /// `SELECT\n.5;` is a number rather than a broken command.
    ///
    /// # Errors
    ///
    /// Returns an error only when the sink fails. `SQL` errors are reported
    /// to the error stream and counted by [`Shell::errors`].
    pub fn run(&mut self, input: &mut dyn BufRead) -> io::Result<()> {
        self.run_at_depth(input, 0)
    }

    fn run_at_depth(&mut self, input: &mut dyn BufRead, depth: usize) -> io::Result<()> {
        let mut pending = String::new();
        loop {
            if self.interactive && depth == 0 {
                let prompt = if pending.is_empty() {
                    "sqlite> "
                } else {
                    "   ...> "
                };
                write!(self.io.default_out, "{prompt}")?;
                self.io.default_out.flush()?;
            }
            let mut line = String::new();
            if input.read_line(&mut line)? == 0 {
                break;
            }
            if pending.is_empty() && line.starts_with('.') {
                self.dot_command(line.trim_end_matches(['\r', '\n']), depth)?;
                if self.quit {
                    return Ok(());
                }
                continue;
            }
            pending.push_str(&line);
            if is_complete(&pending) {
                self.execute(&pending)?;
                pending.clear();
            }
        }
        if !pending.trim().is_empty() {
            self.execute(&pending)?;
        }
        Ok(())
    }

    /// Runs one or more `SQL` statements, printing any rows they produce.
    ///
    /// # Errors
    ///
    /// Returns an error only when the sink fails.
    pub fn execute(&mut self, sql: &str) -> io::Result<()> {
        // Disjoint field borrows: the batch holds the connection while the
        // renderer holds the output.
        let connection = &self.connection;
        let style = &self.style;
        let io = &mut self.io;
        let mut failure = None;
        let mut batch = Batch::new(connection, sql);
        loop {
            match batch.next() {
                Ok(None) => break,
                Ok(Some(mut statement)) => {
                    match render_statement(&mut statement, style, io.out()) {
                        Ok(()) => {}
                        Err(StatementError::Sql(error)) => {
                            failure = Some(error.to_string());
                            break;
                        }
                        Err(StatementError::Sink(error)) => return Err(error),
                    }
                }
                Err(error) => {
                    failure = Some(error.to_string());
                    break;
                }
            }
        }
        if let Some(message) = failure {
            self.report(&message)?;
        }
        Ok(())
    }

    /// Reports a failure and counts it.
    fn report(&mut self, message: &str) -> io::Result<()> {
        self.errors += 1;
        writeln!(self.io.err, "Error: {message}")
    }

    fn dot_command(&mut self, line: &str, depth: usize) -> io::Result<()> {
        let command = match Command::parse(line) {
            Ok(command) => command,
            Err(ParseError::NotACommand) => return Ok(()),
            Err(error) => return self.report(&error.to_string()),
        };
        match command {
            Command::Quit => self.quit = true,
            Command::Help(pattern) => self.help(pattern.as_deref())?,
            Command::Mode(None) => {
                let mode = self.style.mode;
                writeln!(self.io.out(), "current output mode: {mode}")?;
            }
            Command::Mode(Some(mode)) => {
                self.style.mode = mode;
                if mode.implies_headers() {
                    self.style.headers = true;
                }
            }
            Command::Headers(on) => self.style.headers = on,
            Command::NullValue(text) => self.style.null_text = text,
            Command::Separator(text) => self.style.separator = text,
            Command::Open { readonly, target } => self.open(readonly, target.as_deref())?,
            Command::Output(target) => self.output(target.as_deref())?,
            Command::Read(path) => self.read(&path, depth)?,
            Command::Databases => self.databases()?,
            Command::Tables(pattern) => self.tables(pattern.as_deref())?,
            Command::Schema(pattern) => self.schema(pattern.as_deref())?,
            Command::Dump(pattern) => self.dump(pattern.as_deref())?,
        }
        Ok(())
    }

    fn help(&mut self, pattern: Option<&str>) -> io::Result<()> {
        const ENTRIES: [(&str, &str); 13] = [
            (".databases", "List names and files of attached databases"),
            (".dump ?TABLE?", "Render database content as SQL"),
            (".headers on|off", "Turn display of headers on or off"),
            (".help ?PATTERN?", "Show help text"),
            (".mode ?MODE?", "Set output mode"),
            (".nullvalue STRING", "Use STRING in place of NULL values"),
            (
                ".open ?--readonly? ?FILE?",
                "Close the database and reopen FILE",
            ),
            (".output ?FILE?", "Send output to FILE or stdout"),
            (".quit", "Exit this program"),
            (".read FILE", "Read input from FILE"),
            (".schema ?PATTERN?", "Show the CREATE statements"),
            (
                ".separator STRING",
                "Set the column separator for list mode",
            ),
            (".tables ?PATTERN?", "List names of tables and views"),
        ];
        let out = self.io.out();
        for (name, description) in ENTRIES {
            if pattern.is_none_or(|needle| name.contains(needle)) {
                writeln!(out, "{name:<28}{description}")?;
            }
        }
        if pattern.is_none() {
            let modes: Vec<&str> = Mode::all().iter().map(|mode| mode.as_str()).collect();
            writeln!(out, "\nMODE is one of: {}", modes.join(" "))?;
        }
        Ok(())
    }

    fn open(&mut self, readonly: bool, target: Option<&str>) -> io::Result<()> {
        let flags = if readonly {
            OpenFlags::SQLITE_OPEN_READ_ONLY
                | OpenFlags::SQLITE_OPEN_NO_MUTEX
                | OpenFlags::SQLITE_OPEN_URI
        } else {
            OpenFlags::default()
        };
        let opened = match target {
            None => Connection::open_in_memory(),
            Some(path) => Connection::open_with_flags(path, flags),
        };
        match opened {
            Ok(connection) => {
                self.connection = connection;
                Ok(())
            }
            // Upstream keeps the old connection when a `.open` fails, so that
            // a typo does not silently lose the session.
            Err(error) => self.report(&error.to_string()),
        }
    }

    fn output(&mut self, target: Option<&str>) -> io::Result<()> {
        if let Some(file) = self.io.redirect.take() {
            drop(file);
        }
        let Some(path) = target else {
            return Ok(());
        };
        match File::create(path) {
            Ok(file) => {
                self.io.redirect = Some(BufWriter::new(file));
                Ok(())
            }
            Err(error) => self.report(&format!("cannot open \"{path}\": {error}")),
        }
    }

    fn read(&mut self, path: &str, depth: usize) -> io::Result<()> {
        if depth >= MAX_READ_DEPTH {
            return self.report(&format!(".read nested more than {MAX_READ_DEPTH} deep"));
        }
        match File::open(Path::new(path)) {
            Ok(file) => {
                let mut reader = BufReader::new(file);
                self.run_at_depth(&mut reader, depth + 1)
            }
            Err(error) => self.report(&format!("cannot open \"{path}\": {error}")),
        }
    }

    /// Runs a query for its rows, reporting any failure the way `SQL` errors
    /// are reported.
    fn collect(&mut self, sql: &str) -> io::Result<Option<Vec<Vec<Cell>>>> {
        let result = (|| -> covalence_lib_sqlite::Result<Vec<Vec<Cell>>> {
            let mut statement = self.connection.prepare(sql)?;
            let width = statement.column_count();
            let mut rows = statement.raw_query();
            let mut collected = Vec::new();
            while let Some(row) = rows.next()? {
                collected.push(
                    (0..width)
                        .map(|index| row.get_ref(index).map(Cell::capture))
                        .collect::<covalence_lib_sqlite::Result<Vec<Cell>>>()?,
                );
            }
            Ok(collected)
        })();
        match result {
            Ok(rows) => Ok(Some(rows)),
            Err(error) => {
                self.report(&error.to_string())?;
                Ok(None)
            }
        }
    }

    fn databases(&mut self) -> io::Result<()> {
        let Some(rows) = self.collect("PRAGMA database_list")? else {
            return Ok(());
        };
        for row in rows {
            let name = row.get(1).map_or_else(String::new, |cell| cell.plain(""));
            let file = row.get(2).map_or_else(String::new, |cell| cell.plain(""));
            let access = match self.connection.is_readonly(name.as_str()) {
                Ok(true) => "r/o",
                Ok(false) => "r/w",
                Err(_) => "?",
            };
            writeln!(self.io.out(), "{name}: {file} {access}")?;
        }
        Ok(())
    }

    /// The names of every attached database, `main` first.
    fn attached(&mut self) -> io::Result<Vec<String>> {
        Ok(self.collect("PRAGMA database_list")?.map_or_else(
            || vec!["main".to_owned()],
            |rows| {
                rows.iter()
                    .filter_map(|row| row.get(1).map(|cell| cell.plain("")))
                    .collect()
            },
        ))
    }

    fn tables(&mut self, pattern: Option<&str>) -> io::Result<()> {
        let mut names = Vec::new();
        for database in self.attached()? {
            let quoted = quote_identifier(&database);
            let sql = format!(
                "SELECT name FROM {quoted}.sqlite_schema \
                 WHERE type IN ('table','view') AND name NOT LIKE 'sqlite\\_%' ESCAPE '\\' \
                 ORDER BY name"
            );
            let Some(rows) = self.collect(&sql)? else {
                continue;
            };
            for row in rows {
                let Some(name) = row.first().map(|cell| cell.plain("")) else {
                    continue;
                };
                if pattern.is_some_and(|needle| !glob_matches(needle, &name)) {
                    continue;
                }
                names.push(if database == "main" {
                    name
                } else {
                    format!("{database}.{name}")
                });
            }
        }
        if names.is_empty() {
            return Ok(());
        }
        // Column-major, like upstream, so alphabetical order reads downwards.
        let column_width = names
            .iter()
            .map(|name| name.chars().count())
            .max()
            .unwrap_or(0)
            + 2;
        let columns = (SCREEN_WIDTH / column_width).max(1);
        let rows = names.len().div_ceil(columns);
        for row in 0..rows {
            let mut line = String::new();
            for column in 0..columns {
                let Some(name) = names.get(column * rows + row) else {
                    continue;
                };
                let padding = column_width.saturating_sub(name.chars().count());
                line.push_str(name);
                line.push_str(&" ".repeat(padding));
            }
            writeln!(self.io.out(), "{}", line.trim_end())?;
        }
        Ok(())
    }

    fn schema(&mut self, pattern: Option<&str>) -> io::Result<()> {
        for database in self.attached()? {
            let quoted = quote_identifier(&database);
            let sql = format!(
                "SELECT name, sql FROM {quoted}.sqlite_schema \
                 WHERE sql IS NOT NULL AND name NOT LIKE 'sqlite\\_%' ESCAPE '\\' \
                 ORDER BY rowid"
            );
            let Some(rows) = self.collect(&sql)? else {
                continue;
            };
            for row in rows {
                let name = row.first().map_or_else(String::new, |cell| cell.plain(""));
                if pattern.is_some_and(|needle| !glob_matches(needle, &name)) {
                    continue;
                }
                let Some(text) = row.get(1).map(|cell| cell.plain("")) else {
                    continue;
                };
                writeln!(self.io.out(), "{text};")?;
            }
        }
        Ok(())
    }

    /// `.dump`, in its simple form.
    ///
    /// Emits the schema and a literal `INSERT` per row, wrapped in one
    /// transaction. It does not reproduce `sqlite_sequence`, virtual table
    /// contents, `WITHOUT ROWID` rowid preservation, generated columns, or
    /// anything upstream does to survive a corrupt schema.
    fn dump(&mut self, pattern: Option<&str>) -> io::Result<()> {
        writeln!(self.io.out(), "PRAGMA foreign_keys=OFF;")?;
        writeln!(self.io.out(), "BEGIN TRANSACTION;")?;

        let Some(objects) = self.collect(
            "SELECT type, name, sql FROM sqlite_schema \
             WHERE sql IS NOT NULL AND name NOT LIKE 'sqlite\\_%' ESCAPE '\\' \
             ORDER BY rowid",
        )?
        else {
            return writeln!(self.io.out(), "COMMIT;");
        };

        let mut deferred = Vec::new();
        for object in &objects {
            let kind = object
                .first()
                .map_or_else(String::new, |cell| cell.plain(""));
            let name = object
                .get(1)
                .map_or_else(String::new, |cell| cell.plain(""));
            let sql = object
                .get(2)
                .map_or_else(String::new, |cell| cell.plain(""));
            if pattern.is_some_and(|needle| !glob_matches(needle, &name)) {
                continue;
            }
            if kind == "table" {
                writeln!(self.io.out(), "{sql};")?;
                self.dump_rows(&name)?;
            } else {
                deferred.push(sql);
            }
        }
        // Indexes, triggers and views come after the data they refer to.
        for sql in deferred {
            writeln!(self.io.out(), "{sql};")?;
        }
        writeln!(self.io.out(), "COMMIT;")
    }

    fn dump_rows(&mut self, table: &str) -> io::Result<()> {
        let quoted = quote_identifier(table);
        let Some(rows) = self.collect(&format!("SELECT * FROM {quoted}"))? else {
            return Ok(());
        };
        for row in rows {
            let values: Vec<String> = row.iter().map(Cell::sql_literal).collect();
            writeln!(
                self.io.out(),
                "INSERT INTO {quoted} VALUES({});",
                values.join(",")
            )?;
        }
        Ok(())
    }
}

/// A statement can fail two ways, and they are not handled the same: `SQL`
/// errors are reported and counted, sink errors abort the shell.
enum StatementError {
    Sql(covalence_lib_sqlite::Error),
    Sink(io::Error),
}

impl From<covalence_lib_sqlite::Error> for StatementError {
    fn from(error: covalence_lib_sqlite::Error) -> Self {
        Self::Sql(error)
    }
}

impl From<io::Error> for StatementError {
    fn from(error: io::Error) -> Self {
        Self::Sink(error)
    }
}

/// Renders one prepared statement's rows.
fn render_statement(
    statement: &mut Statement<'_>,
    style: &Style,
    out: &mut dyn Write,
) -> Result<(), StatementError> {
    let columns: Vec<String> = statement
        .column_names()
        .into_iter()
        .map(ToOwned::to_owned)
        .collect();
    let width = columns.len();
    let mut renderer = Renderer::new(style, columns);
    let mut rows = statement.raw_query();
    while let Some(row) = rows.next()? {
        let cells = (0..width)
            .map(|index| row.get_ref(index).map(Cell::capture))
            .collect::<covalence_lib_sqlite::Result<Vec<Cell>>>()?;
        renderer.row(out, cells)?;
    }
    renderer.finish(out)?;
    Ok(())
}

/// `LIKE`-style matching for `.tables` and `.schema` patterns.
///
/// Upstream passes the pattern to `SQL` `LIKE`; this understands `%` and `_`
/// the same way, plus a bare name matching itself.
fn glob_matches(pattern: &str, name: &str) -> bool {
    fn matches(pattern: &[char], name: &[char]) -> bool {
        match pattern.first() {
            None => name.is_empty(),
            Some('%') => (0..=name.len()).any(|skip| matches(&pattern[1..], &name[skip..])),
            Some('_') => !name.is_empty() && matches(&pattern[1..], &name[1..]),
            Some(expected) => name.first().is_some_and(|actual| {
                actual.eq_ignore_ascii_case(expected) && matches(&pattern[1..], &name[1..])
            }),
        }
    }
    let pattern: Vec<char> = pattern.chars().collect();
    let name: Vec<char> = name.chars().collect();
    matches(&pattern, &name)
}

#[cfg(test)]
mod tests {
    use crate::SharedBuffer;

    use super::*;

    struct Fixture {
        shell: Shell,
        out: SharedBuffer,
        err: SharedBuffer,
    }

    impl Fixture {
        fn new() -> Self {
            let out = SharedBuffer::new();
            let err = SharedBuffer::new();
            let shell = Shell::new(
                Connection::open_in_memory().unwrap(),
                Box::new(out.clone()),
                Box::new(err.clone()),
            );
            Self { shell, out, err }
        }

        fn feed(&mut self, script: &str) -> String {
            self.shell.run(&mut script.as_bytes()).unwrap();
            self.out.take_string()
        }
    }

    #[test]
    fn it_evaluates_sql_from_its_input() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT 1+1;\n"), "2\n");
        assert_eq!(fixture.shell.errors(), 0);
    }

    #[test]
    fn a_statement_may_span_lines() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT\n  1,\n  2;\n"), "1|2\n");
    }

    #[test]
    fn a_trigger_body_is_not_split_at_its_inner_semicolons() {
        let mut fixture = Fixture::new();
        let script = concat!(
            "CREATE TABLE t(a);\n",
            "CREATE TRIGGER tr AFTER INSERT ON t BEGIN\n",
            "  SELECT 1;\n",
            "  SELECT 2;\n",
            "END;\n",
            "INSERT INTO t VALUES (1);\n",
            "SELECT count(*) FROM t;\n",
        );
        assert_eq!(fixture.feed(script), "1\n");
        assert_eq!(fixture.shell.errors(), 0);
    }

    #[test]
    fn several_statements_on_one_line_all_run() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT 1; SELECT 2;\n"), "1\n2\n");
    }

    #[test]
    fn a_trailing_statement_without_a_semicolon_still_runs() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT 9"), "9\n");
    }

    #[test]
    fn a_failing_statement_is_reported_and_counted() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT * FROM missing;\n"), "");
        assert_eq!(fixture.shell.errors(), 1);
        assert!(fixture.err.take_string().starts_with("Error: "));
        // The shell stays usable.
        assert_eq!(fixture.feed("SELECT 1;\n"), "1\n");
    }

    #[test]
    fn quit_stops_reading() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed("SELECT 1;\n.quit\nSELECT 2;\n"), "1\n");
    }

    #[test]
    fn a_leading_dot_is_only_a_command_between_statements() {
        let mut fixture = Fixture::new();
        // `.5` continues the pending statement rather than being a command.
        assert_eq!(fixture.feed("SELECT\n.5;\n"), "0.5\n");
        assert_eq!(fixture.shell.errors(), 0);
    }

    #[test]
    fn mode_and_headers_change_the_rendering() {
        let mut fixture = Fixture::new();
        assert_eq!(
            fixture.feed(".mode json\nSELECT 1 AS n;\n"),
            "[{\"n\":1}]\n"
        );
        assert_eq!(
            fixture.feed(".mode list\n.headers on\nSELECT 1 AS n;\n"),
            "n\n1\n"
        );
        assert_eq!(fixture.feed(".mode\n"), "current output mode: list\n");
    }

    #[test]
    fn box_mode_turns_headers_on_by_itself() {
        let mut fixture = Fixture::new();
        let output = fixture.feed(".mode box\nSELECT 1 AS n;\n");
        assert!(output.contains(" n "), "{output}");
        assert!(output.starts_with('\u{256d}'), "{output}");
    }

    #[test]
    fn nullvalue_and_separator_apply_to_list_mode() {
        let mut fixture = Fixture::new();
        assert_eq!(
            fixture.feed(".nullvalue NIL\n.separator ::\nSELECT NULL, 2;\n"),
            "NIL::2\n"
        );
    }

    #[test]
    fn an_unknown_command_is_reported_without_stopping() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed(".archive\nSELECT 1;\n"), "1\n");
        assert_eq!(fixture.shell.errors(), 1);
        assert!(fixture.err.take_string().contains("archive"));
    }

    #[test]
    fn tables_and_schema_report_what_was_created() {
        let mut fixture = Fixture::new();
        fixture.feed("CREATE TABLE beta(x); CREATE TABLE alpha(y); CREATE VIEW v AS SELECT 1;\n");
        assert_eq!(fixture.feed(".tables\n"), "alpha  beta   v\n");
        assert_eq!(fixture.feed(".schema alpha\n"), "CREATE TABLE alpha(y);\n");
        assert_eq!(fixture.feed(".tables al%\n"), "alpha\n");
    }

    #[test]
    fn databases_lists_the_main_database() {
        let mut fixture = Fixture::new();
        let output = fixture.feed(".databases\n");
        assert!(output.starts_with("main: "), "{output}");
        assert!(output.trim_end().ends_with("r/w"), "{output}");
    }

    #[test]
    fn dump_round_trips_through_a_fresh_database() {
        let mut fixture = Fixture::new();
        fixture.feed(concat!(
            "CREATE TABLE t(a,b,c);\n",
            "INSERT INTO t VALUES(1,'it''s',x'00ff41');\n",
            "INSERT INTO t VALUES(NULL,'',3.5);\n",
            "CREATE INDEX i ON t(a);\n",
        ));
        let dumped = fixture.feed(".dump\n");
        assert!(
            dumped.starts_with("PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\n"),
            "{dumped}"
        );
        assert!(
            dumped.contains("INSERT INTO t VALUES(1,'it''s',x'00ff41');"),
            "{dumped}"
        );
        assert!(
            dumped.contains("INSERT INTO t VALUES(NULL,'',3.5);"),
            "{dumped}"
        );
        assert!(dumped.trim_end().ends_with("COMMIT;"), "{dumped}");
        // The index is emitted after the data it indexes.
        let insert = dumped.find("INSERT INTO t").unwrap();
        let index = dumped.find("CREATE INDEX").unwrap();
        assert!(insert < index, "{dumped}");

        // Replaying it into an empty database reproduces the content.
        let mut replay = Fixture::new();
        replay.shell.run(&mut dumped.as_bytes()).unwrap();
        assert_eq!(replay.shell.errors(), 0);
        assert_eq!(replay.feed("SELECT count(*) FROM t;\n"), "2\n");
    }

    #[test]
    fn output_redirects_to_a_file_and_back() {
        let path = std::env::temp_dir().join("covalence-sql-shell-output.txt");
        let _ = std::fs::remove_file(&path);
        let mut fixture = Fixture::new();
        let script = format!(
            ".output {}\nSELECT 'redirected';\n.output\nSELECT 'direct';\n",
            path.display()
        );
        assert_eq!(fixture.feed(&script), "direct\n");
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "redirected\n");
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_runs_a_file_as_input() {
        let path = std::env::temp_dir().join("covalence-sql-shell-read.sql");
        std::fs::write(&path, "SELECT 'from a file';\n").unwrap();
        let mut fixture = Fixture::new();
        assert_eq!(
            fixture.feed(&format!(".read {}\n", path.display())),
            "from a file\n"
        );
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn read_reports_a_missing_file() {
        let mut fixture = Fixture::new();
        assert_eq!(fixture.feed(".read /nonexistent/nope.sql\n"), "");
        assert_eq!(fixture.shell.errors(), 1);
    }

    #[test]
    fn open_switches_databases_and_keeps_the_old_one_on_failure() {
        let path = std::env::temp_dir().join("covalence-sql-shell-open.sqlite");
        let _ = std::fs::remove_file(&path);
        let mut fixture = Fixture::new();
        fixture.feed("CREATE TABLE original(x);\n");
        assert_eq!(fixture.feed(&format!(".open {}\n", path.display())), "");
        fixture.feed("CREATE TABLE opened(y);\n");
        assert_eq!(fixture.feed(".tables\n"), "opened\n");

        // A directory is not a database; the connection must survive.
        assert_eq!(fixture.feed(".open /\n"), "");
        assert!(fixture.shell.errors() > 0);
        assert_eq!(fixture.feed(".tables\n"), "opened\n");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn interactive_mode_prompts() {
        let out = SharedBuffer::new();
        let mut shell = Shell::new(
            Connection::open_in_memory().unwrap(),
            Box::new(out.clone()),
            Box::new(SharedBuffer::new()),
        );
        shell.set_interactive(true);
        shell.run(&mut "SELECT\n1;\n".as_bytes()).unwrap();
        assert_eq!(out.take_string(), "sqlite>    ...> 1\nsqlite> ");
    }

    #[test]
    fn like_patterns_behave() {
        assert!(glob_matches("alpha", "alpha"));
        assert!(glob_matches("ALPHA", "alpha"));
        assert!(glob_matches("al%", "alpha"));
        assert!(glob_matches("%ph%", "alpha"));
        assert!(glob_matches("al_ha", "alpha"));
        assert!(!glob_matches("al_a", "alpha"));
        assert!(!glob_matches("beta", "alpha"));
    }
}
