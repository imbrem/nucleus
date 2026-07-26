//! A deliberately small DEF/USE and trace-query vertical slice.
//!
//! Primary-key columns define connection-local identities. Foreign-key
//! columns use identities defined by another row. [`Def`] and [`Use`] make
//! that distinction visible at the Rust boundary while `SQLite` checks it at
//! the storage boundary.

use std::marker::PhantomData;

use covalence_data_sexpr::{SExpr, Symbol, sax::FromEvents, text};
use covalence_lib_error::snafu;
use covalence_lib_sqlite::{OptionalExtension, params};
use covalence_neutron::{
    BOOTSTRAP_CATALOG, EXECUTORS_METATABLE_V0, EXPRESSIONS_METATABLE_V0, MetatableKind, ScanError,
    TERM_EXECUTION_TRACES_INTERPRETATION_V0, TERM_EXECUTION_TRACES_METATABLE_V0,
    TERMS_INTERPRETATION_V0, TERMS_METATABLE_V0, TYPES_INTERPRETATION_V0, TYPES_METATABLE_V0,
    metatable_name, scan_metatables,
};
use snafu::Snafu;

use crate::{
    CatalogError, ExecutionModelError, ExecutorId, NeutronCatalog, TraceOutcome, TrustedDb,
};

const INTERPRETATIONS: [(&str, covalence_lib_hash::O256); 3] = [
    (TYPES_INTERPRETATION_V0, TYPES_METATABLE_V0),
    (TERMS_INTERPRETATION_V0, TERMS_METATABLE_V0),
    (
        TERM_EXECUTION_TRACES_INTERPRETATION_V0,
        TERM_EXECUTION_TRACES_METATABLE_V0,
    ),
];

/// Marker for the identity domain defined by the type table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeIdentity {}

/// Marker for the identity domain defined by the term table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermIdentity {}

/// Marker for the identity domain defined by the term-trace table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermTraceIdentity {}

/// An identity introduced by a `DEF` column.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Def<K> {
    raw: i64,
    kind: PhantomData<fn() -> K>,
}

impl<K> Clone for Def<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Def<K> {}

impl<K> Def<K> {
    const fn new(raw: i64) -> Self {
        Self {
            raw,
            kind: PhantomData,
        }
    }

    /// Borrows the defined identity for a `USE` position.
    #[must_use]
    pub const fn use_id(self) -> Use<K> {
        Use::new(self.raw)
    }

    /// Returns the connection-local integer representation.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.raw
    }
}

/// An identity consumed by a `USE` column.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Use<K> {
    raw: i64,
    kind: PhantomData<fn() -> K>,
}

impl<K> Clone for Use<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Use<K> {}

impl<K> Use<K> {
    const fn new(raw: i64) -> Self {
        Self {
            raw,
            kind: PhantomData,
        }
    }

    /// Returns the connection-local integer representation.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.raw
    }
}

/// One row of the existential successful-output relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SuccessfulOutput {
    /// Program identity retained by projection.
    pub program: Use<TermIdentity>,
    /// Output identity retained by projection.
    pub output: Use<TermIdentity>,
}

/// Positive first-order trace query used by the initial REPL.
///
/// Its logical reading is:
///
/// `∃ trace executor input. returned(trace, executor, program, input, output)`.
///
/// `program = None` leaves the program free in the projected result. Supplying
/// a program adds an equality atom. Trace, executor, and input are always
/// existentially bound; program and output are projected.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SuccessfulTraceQuery {
    /// Optional equality constraint for the projected program.
    pub program: Option<Use<TermIdentity>>,
}

impl SuccessfulTraceQuery {
    /// Projects every observed `(program, output)` pair.
    #[must_use]
    pub const fn all() -> Self {
        Self { program: None }
    }

    /// Projects outputs witnessed for one program.
    #[must_use]
    pub const fn for_program(program: Use<TermIdentity>) -> Self {
        Self {
            program: Some(program),
        }
    }
}

/// Result of installing the DEF/USE vertical slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstallKnowledgeOutcome {
    /// At least one required extension family was installed.
    Installed,
    /// Every required extension was already present.
    AlreadyPresent,
}

/// Checked access to type definitions, term definitions, and term traces.
pub struct KnowledgeModel<'db> {
    database: &'db mut TrustedDb,
}

impl TrustedDb {
    /// Installs the execution model plus type, term, and term-trace tables.
    ///
    /// # Errors
    ///
    /// Returns a checked execution, database, scanner, or catalog error.
    pub fn install_knowledge_model(&mut self) -> Result<InstallKnowledgeOutcome, KnowledgeError> {
        let execution_installed = matches!(
            self.install_execution_model()
                .map_err(|source| KnowledgeError::Execution { source })?,
            crate::InstallExecutionModelOutcome::Installed
        );
        let present = INTERPRETATIONS
            .iter()
            .filter(|(interpretation, _)| self.catalog.by_interpretation(interpretation).is_some())
            .count();
        if present == INTERPRETATIONS.len() {
            return Ok(if execution_installed {
                InstallKnowledgeOutcome::Installed
            } else {
                InstallKnowledgeOutcome::AlreadyPresent
            });
        }
        if present != 0 {
            return Err(KnowledgeError::PartialInstallation);
        }

        let expressions = table_name(EXPRESSIONS_METATABLE_V0);
        let executors = table_name(EXECUTORS_METATABLE_V0);
        let types = table_name(TYPES_METATABLE_V0);
        let terms = table_name(TERMS_METATABLE_V0);
        let traces = table_name(TERM_EXECUTION_TRACES_METATABLE_V0);
        let bootstrap = table_name(BOOTSTRAP_CATALOG);
        let transaction = self
            .connection
            .transaction()
            .map_err(KnowledgeError::sqlite)?;
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {types} (
                    id INTEGER PRIMARY KEY,
                    name TEXT NOT NULL UNIQUE,
                    definition_expression INTEGER NOT NULL UNIQUE
                        REFERENCES {expressions}(id)
                ) STRICT;
                CREATE TABLE {terms} (
                    id INTEGER PRIMARY KEY,
                    name TEXT NOT NULL UNIQUE,
                    type_id INTEGER NOT NULL REFERENCES {types}(id),
                    definition_expression INTEGER NOT NULL UNIQUE
                        REFERENCES {expressions}(id)
                ) STRICT;
                CREATE TABLE {traces} (
                    id INTEGER PRIMARY KEY,
                    executor_id INTEGER NOT NULL REFERENCES {executors}(id),
                    program_term INTEGER NOT NULL REFERENCES {terms}(id),
                    input_term INTEGER NOT NULL REFERENCES {terms}(id),
                    output_term INTEGER REFERENCES {terms}(id),
                    outcome TEXT NOT NULL CHECK (outcome IN ('returned', 'failed'))
                ) STRICT;"
            ))
            .map_err(KnowledgeError::sqlite)?;
        for (interpretation, kind) in INTERPRETATIONS {
            transaction
                .execute(
                    &format!(
                        "INSERT INTO {bootstrap} (table_name, interpretation) VALUES (?1, ?2)"
                    ),
                    params![table_name(kind), interpretation],
                )
                .map_err(KnowledgeError::sqlite)?;
        }
        let candidate = scan_metatables(&transaction).map_err(KnowledgeError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(KnowledgeError::catalog)?;
        transaction.commit().map_err(KnowledgeError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(InstallKnowledgeOutcome::Installed)
    }

    /// Resolves the complete knowledge-model capability.
    ///
    /// # Errors
    ///
    /// Returns an error unless all required extension tables are installed.
    pub fn knowledge_model(&mut self) -> Result<KnowledgeModel<'_>, KnowledgeError> {
        if INTERPRETATIONS
            .iter()
            .all(|(interpretation, _)| self.catalog.by_interpretation(interpretation).is_some())
        {
            Ok(KnowledgeModel { database: self })
        } else {
            Err(KnowledgeError::NotInstalled)
        }
    }
}

impl KnowledgeModel<'_> {
    /// Defines a named type using one checked S-expression.
    ///
    /// # Errors
    ///
    /// Returns a checked expression or database error.
    pub fn define_type(
        &mut self,
        name: &str,
        definition: &str,
    ) -> Result<Def<TypeIdentity>, KnowledgeError> {
        let expression = self
            .database
            .execution_model()
            .map_err(|source| KnowledgeError::Execution { source })?
            .register_expression(definition)
            .map_err(|source| KnowledgeError::Execution { source })?;
        let table = table_name(TYPES_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT OR IGNORE INTO {table} (name, definition_expression) VALUES (?1, ?2)"
                ),
                params![name, expression.get()],
            )
            .map_err(KnowledgeError::sqlite)?;
        let (id, stored_expression) = self
            .database
            .connection
            .query_row(
                &format!("SELECT id, definition_expression FROM {table} WHERE name = ?1"),
                [name],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .map_err(KnowledgeError::sqlite)?;
        if stored_expression != expression.get() {
            return Err(KnowledgeError::ConflictingDefinition {
                namespace: "type",
                name: name.to_owned(),
            });
        }
        Ok(Def::new(id))
    }

    /// Defines a named term with a `USE` of its type identity.
    ///
    /// # Errors
    ///
    /// Returns a checked expression or database error.
    pub fn define_term(
        &mut self,
        name: &str,
        r#type: Use<TypeIdentity>,
        definition: &str,
    ) -> Result<Def<TermIdentity>, KnowledgeError> {
        let expression = self
            .database
            .execution_model()
            .map_err(|source| KnowledgeError::Execution { source })?
            .register_expression(definition)
            .map_err(|source| KnowledgeError::Execution { source })?;
        let table = table_name(TERMS_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT OR IGNORE INTO {table}
                     (name, type_id, definition_expression) VALUES (?1, ?2, ?3)"
                ),
                params![name, r#type.get(), expression.get()],
            )
            .map_err(KnowledgeError::sqlite)?;
        let (id, stored_type, stored_expression) = self
            .database
            .connection
            .query_row(
                &format!("SELECT id, type_id, definition_expression FROM {table} WHERE name = ?1"),
                [name],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .map_err(KnowledgeError::sqlite)?;
        if stored_type != r#type.get() || stored_expression != expression.get() {
            return Err(KnowledgeError::ConflictingDefinition {
                namespace: "term",
                name: name.to_owned(),
            });
        }
        Ok(Def::new(id))
    }

    /// Registers an executor through the underlying execution model.
    ///
    /// # Errors
    ///
    /// Returns a checked execution-model error.
    pub fn register_executor(&mut self, name: &str) -> Result<ExecutorId, KnowledgeError> {
        self.database
            .execution_model()
            .map_err(|source| KnowledgeError::Execution { source })?
            .register_executor(name, None)
            .map_err(|source| KnowledgeError::Execution { source })
    }

    /// Records a term-level execution trace.
    ///
    /// The primary key is a `DEF Trace`; every other identity column is a
    /// checked `USE`.
    ///
    /// # Errors
    ///
    /// Returns a checked database error, including invalid identity uses.
    pub fn record_trace(
        &mut self,
        executor: ExecutorId,
        program: Use<TermIdentity>,
        input: Use<TermIdentity>,
        output: Option<Use<TermIdentity>>,
        outcome: TraceOutcome,
    ) -> Result<Def<TermTraceIdentity>, KnowledgeError> {
        let traces = table_name(TERM_EXECUTION_TRACES_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT INTO {traces}
                     (executor_id, program_term, input_term, output_term, outcome)
                     VALUES (?1, ?2, ?3, ?4, ?5)"
                ),
                params![
                    executor.get(),
                    program.get(),
                    input.get(),
                    output.map(Use::get),
                    outcome_text(outcome)
                ],
            )
            .map_err(KnowledgeError::sqlite)?;
        Ok(Def::new(self.database.connection.last_insert_rowid()))
    }

    /// Evaluates the positive first-order query
    /// `∃ trace executor input. returned(trace, executor, program, input, output)`.
    ///
    /// Projection existentially hides the trace, executor, and input columns;
    /// `DISTINCT` gives the result logical set semantics.
    ///
    /// # Errors
    ///
    /// Returns a checked database error.
    pub fn query_successful_traces(
        &self,
        query: SuccessfulTraceQuery,
    ) -> Result<Vec<SuccessfulOutput>, KnowledgeError> {
        let traces = table_name(TERM_EXECUTION_TRACES_METATABLE_V0);
        let mut statement = self
            .database
            .connection
            .prepare(&format!(
                "SELECT DISTINCT program_term, output_term
                 FROM {traces}
                 WHERE outcome = 'returned'
                   AND output_term IS NOT NULL
                   AND (?1 IS NULL OR program_term = ?1)
                 ORDER BY program_term, output_term"
            ))
            .map_err(KnowledgeError::sqlite)?;
        statement
            .query_map([query.program.map(Use::get)], |row| {
                Ok(SuccessfulOutput {
                    program: Use::new(row.get(0)?),
                    output: Use::new(row.get(1)?),
                })
            })
            .map_err(KnowledgeError::sqlite)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(KnowledgeError::sqlite)
    }

    /// Looks up a type definition by its human-facing session name.
    ///
    /// # Errors
    ///
    /// Returns a checked database error.
    pub fn type_named(&self, name: &str) -> Result<Option<Def<TypeIdentity>>, KnowledgeError> {
        lookup_id(
            &self.database.connection,
            TYPES_METATABLE_V0,
            name,
            Def::new,
        )
    }

    /// Looks up a term definition by its human-facing session name.
    ///
    /// # Errors
    ///
    /// Returns a checked database error.
    pub fn term_named(&self, name: &str) -> Result<Option<Def<TermIdentity>>, KnowledgeError> {
        lookup_id(
            &self.database.connection,
            TERMS_METATABLE_V0,
            name,
            Def::new,
        )
    }

    fn term_name(&self, term: Use<TermIdentity>) -> Result<String, KnowledgeError> {
        let terms = table_name(TERMS_METATABLE_V0);
        self.database
            .connection
            .query_row(
                &format!("SELECT name FROM {terms} WHERE id = ?1"),
                [term.get()],
                |row| row.get(0),
            )
            .map_err(KnowledgeError::sqlite)
    }
}

/// A scriptable, line-oriented session suitable for a first REPL.
pub struct ReplSession {
    database: TrustedDb,
}

impl ReplSession {
    /// Creates an empty in-memory session with all vertical-slice tables.
    ///
    /// # Errors
    ///
    /// Returns a checked setup error.
    pub fn new() -> Result<Self, KnowledgeError> {
        let mut database = TrustedDb::create_in_memory()
            .map_err(|source| KnowledgeError::TrustedDatabase { source })?;
        database.install_knowledge_model()?;
        Ok(Self { database })
    }

    /// Evaluates one complete command S-expression.
    ///
    /// Supported commands are `type`, `term`, `executor`, `trace`, and
    /// `outputs`.
    ///
    /// # Errors
    ///
    /// Returns a syntax, command-shape, name-resolution, or database error.
    pub fn eval(&mut self, input: &str) -> Result<String, KnowledgeError> {
        let command = parse_expression(input)?;
        let list = command
            .as_list()
            .ok_or_else(|| KnowledgeError::InvalidCommand {
                reason: String::from("command must be a list"),
            })?;
        let Some(name) = list.first().and_then(SExpr::as_atom).map(Symbol::as_str) else {
            return Err(KnowledgeError::InvalidCommand {
                reason: String::from("command must start with an atom"),
            });
        };
        match (name, &list[1..]) {
            ("type", [name, definition]) => {
                let name = atom(name, "type name")?;
                let definition = print_expression(definition);
                let id = self
                    .database
                    .knowledge_model()?
                    .define_type(name, &definition)?;
                Ok(format!("(defined type {name} {})", id.get()))
            }
            ("term", [name, r#type, definition]) => {
                let name = atom(name, "term name")?;
                let type_name = atom(r#type, "type name")?;
                let definition = print_expression(definition);
                let mut model = self.database.knowledge_model()?;
                let type_id =
                    model
                        .type_named(type_name)?
                        .ok_or_else(|| KnowledgeError::UnknownName {
                            namespace: "type",
                            name: type_name.to_owned(),
                        })?;
                let id = model.define_term(name, type_id.use_id(), &definition)?;
                Ok(format!("(defined term {name} {})", id.get()))
            }
            ("executor", [name]) => {
                let name = atom(name, "executor name")?;
                let id = self.database.knowledge_model()?.register_executor(name)?;
                Ok(format!("(defined executor {name} {})", id.get()))
            }
            ("trace", [executor, program, input, output]) => {
                let executor_name = atom(executor, "executor name")?;
                let program_name = atom(program, "program term")?;
                let input_name = atom(input, "input term")?;
                let output_name = atom(output, "output term")?;
                let mut model = self.database.knowledge_model()?;
                let executor = model
                    .database
                    .execution_model()
                    .map_err(|source| KnowledgeError::Execution { source })?
                    .executor_named(executor_name)
                    .map_err(|source| KnowledgeError::Execution { source })?
                    .ok_or_else(|| KnowledgeError::UnknownName {
                        namespace: "executor",
                        name: executor_name.to_owned(),
                    })?;
                let program = required_term(&model, program_name)?;
                let input = required_term(&model, input_name)?;
                let output = required_term(&model, output_name)?;
                let trace = model.record_trace(
                    executor,
                    program.use_id(),
                    input.use_id(),
                    Some(output.use_id()),
                    TraceOutcome::Returned,
                )?;
                Ok(format!("(recorded trace {})", trace.get()))
            }
            ("outputs", [program]) => {
                let program_name = atom(program, "program term")?;
                let model = self.database.knowledge_model()?;
                let program = required_term(&model, program_name)?;
                let outputs = model
                    .query_successful_traces(SuccessfulTraceQuery::for_program(program.use_id()))?;
                let names = outputs
                    .into_iter()
                    .map(|row| model.term_name(row.output))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("({})", names.join(" ")))
            }
            (unknown, _)
                if !matches!(unknown, "type" | "term" | "executor" | "trace" | "outputs") =>
            {
                Err(KnowledgeError::UnknownCommand {
                    command: unknown.to_owned(),
                })
            }
            _ => Err(KnowledgeError::InvalidCommand {
                reason: format!("wrong arguments for `{name}`"),
            }),
        }
    }
}

/// Failure in the DEF/USE knowledge-model prototype.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum KnowledgeError {
    /// The normalized execution model failed.
    #[snafu(display("execution model failed: {source}"))]
    Execution {
        /// Underlying execution-model error.
        source: ExecutionModelError,
    },
    /// Initial trusted database construction failed.
    #[snafu(display("trusted database setup failed: {source}"))]
    TrustedDatabase {
        /// Underlying trusted database error.
        source: crate::TrustedDbError,
    },
    /// `SQLite` rejected an operation.
    #[snafu(display("knowledge-model operation failed: {source}"))]
    Sqlite {
        /// Underlying `SQLite` error.
        source: covalence_lib_sqlite::Error,
    },
    /// Mechanical catalog scanning failed.
    #[snafu(display("could not scan knowledge metatables: {source}"))]
    Scan {
        /// Scanner failure.
        source: ScanError,
    },
    /// Compiled catalog policy rejected the tables.
    #[snafu(display("could not accept knowledge metatables: {source}"))]
    Catalog {
        /// Catalog failure.
        source: CatalogError,
    },
    /// Only part of the extension family was present.
    #[snafu(display("knowledge metatables are only partially installed"))]
    PartialInstallation,
    /// The extension family has not been installed.
    #[snafu(display("knowledge metatables are not installed"))]
    NotInstalled,
    /// A command S-expression had invalid syntax.
    #[snafu(display("invalid command syntax: {source}"))]
    ExpressionSyntax {
        /// Parser error.
        source: text::Error,
    },
    /// A command event stream did not contain one expression.
    #[snafu(display("invalid command structure: {source}"))]
    ExpressionStructure {
        /// Structural error.
        source: covalence_data_sexpr::sax::BuildError,
    },
    /// The command name was unknown.
    #[snafu(display("unknown command `{command}`"))]
    UnknownCommand {
        /// Unknown command atom.
        command: String,
    },
    /// The command shape was invalid.
    #[snafu(display("invalid command: {reason}"))]
    InvalidCommand {
        /// Stable command-shape detail.
        reason: String,
    },
    /// A name did not resolve in the requested namespace.
    #[snafu(display("unknown {namespace} `{name}`"))]
    UnknownName {
        /// Namespace searched.
        namespace: &'static str,
        /// Missing name.
        name: String,
    },
    /// A session name was reused for a different definition.
    #[snafu(display("conflicting definition for {namespace} `{name}`"))]
    ConflictingDefinition {
        /// Namespace containing the definition.
        namespace: &'static str,
        /// Conflicting name.
        name: String,
    },
}

impl KnowledgeError {
    fn sqlite(source: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite { source }
    }

    const fn scan(source: ScanError) -> Self {
        Self::Scan { source }
    }

    const fn catalog(source: CatalogError) -> Self {
        Self::Catalog { source }
    }
}

fn parse_expression(input: &str) -> Result<SExpr, KnowledgeError> {
    let events = text::parse_symbols(input)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|source| KnowledgeError::ExpressionSyntax { source })?;
    SExpr::from_events(events).map_err(|source| KnowledgeError::ExpressionStructure { source })
}

fn print_expression(expression: &SExpr) -> String {
    match expression {
        SExpr::Atom(atom) => {
            let text = atom.as_str();
            if text.is_empty()
                || text
                    .chars()
                    .any(|character| character.is_whitespace() || "()\";".contains(character))
            {
                format!("\"{}\"", text.replace('\\', "\\\\").replace('"', "\\\""))
            } else {
                text.to_owned()
            }
        }
        SExpr::List(children) => format!(
            "({})",
            children
                .iter()
                .map(print_expression)
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

fn atom<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, KnowledgeError> {
    expression
        .as_atom()
        .map(Symbol::as_str)
        .ok_or_else(|| KnowledgeError::InvalidCommand {
            reason: format!("{role} must be an atom"),
        })
}

fn required_term(
    model: &KnowledgeModel<'_>,
    name: &str,
) -> Result<Def<TermIdentity>, KnowledgeError> {
    model
        .term_named(name)?
        .ok_or_else(|| KnowledgeError::UnknownName {
            namespace: "term",
            name: name.to_owned(),
        })
}

fn lookup_id<T>(
    connection: &covalence_lib_sqlite::Connection,
    kind: covalence_lib_hash::O256,
    name: &str,
    construct: impl FnOnce(i64) -> T,
) -> Result<Option<T>, KnowledgeError> {
    let table = table_name(kind);
    connection
        .query_row(
            &format!("SELECT id FROM {table} WHERE name = ?1"),
            [name],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map(|id| id.map(construct))
        .map_err(KnowledgeError::sqlite)
}

const fn outcome_text(outcome: TraceOutcome) -> &'static str {
    match outcome {
        TraceOutcome::Returned => "returned",
        TraceOutcome::Failed => "failed",
    }
}

fn table_name(kind: covalence_lib_hash::O256) -> String {
    metatable_name(MetatableKind::new(kind))
}

#[cfg(test)]
mod tests {
    use super::{InstallKnowledgeOutcome, ReplSession};
    use crate::TrustedDb;

    #[test]
    fn installation_is_incremental_and_idempotent() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(
            database.install_knowledge_model().unwrap(),
            InstallKnowledgeOutcome::Installed
        );
        assert_eq!(
            database.install_knowledge_model().unwrap(),
            InstallKnowledgeOutcome::AlreadyPresent
        );
        assert_eq!(database.catalog().metatables().len(), 7);
    }

    #[test]
    fn repl_reaches_the_existential_trace_query() {
        let mut session = ReplSession::new().unwrap();
        session.eval("(type Value (value-type))").unwrap();
        session.eval("(term add Value (add 20 22))").unwrap();
        session.eval("(term nil Value ())").unwrap();
        session.eval("(term forty-two Value 42)").unwrap();
        session.eval("(executor evaluator)").unwrap();
        session.eval("(trace evaluator add nil forty-two)").unwrap();

        assert_eq!(session.eval("(outputs add)").unwrap(), "(forty-two)");
    }

    #[test]
    fn absence_remains_an_empty_positive_result() {
        let mut session = ReplSession::new().unwrap();
        session.eval("(type Value (value-type))").unwrap();
        session.eval("(term add Value (add 20 22))").unwrap();
        assert_eq!(session.eval("(outputs add)").unwrap(), "()");
    }

    #[test]
    fn trace_uses_existing_definitions_and_names_do_not_silently_rebind() {
        let mut session = ReplSession::new().unwrap();
        session.eval("(type Value (value-type))").unwrap();
        assert!(session.eval("(type Value (different-type))").is_err());
        session.eval("(term add Value (add 20 22))").unwrap();
        session.eval("(term nil Value ())").unwrap();
        session.eval("(term forty-two Value 42)").unwrap();
        assert!(session.eval("(trace missing add nil forty-two)").is_err());
    }
}
