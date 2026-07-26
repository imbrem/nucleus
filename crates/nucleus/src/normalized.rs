//! Prototype A: compiled interpretations with normalized parameter tables.

use covalence_data_sexpr::{SExpr, sax::FromEvents, text};
use covalence_lib_error::snafu;
use covalence_lib_sqlite::{OptionalExtension, params};
use covalence_neutron::{
    BOOTSTRAP_CATALOG, EXECUTION_TRACES_INTERPRETATION_V0, EXECUTION_TRACES_METATABLE_V0,
    EXECUTORS_INTERPRETATION_V0, EXECUTORS_METATABLE_V0, EXPRESSIONS_INTERPRETATION_V0,
    EXPRESSIONS_METATABLE_V0, MetatableKind, ScanError, TABLE_INTERPRETATIONS_INTERPRETATION_V0,
    TABLE_INTERPRETATIONS_METATABLE_V0, metatable_name, scan_metatables,
};
use snafu::Snafu;

use crate::{CatalogError, NeutronCatalog, TrustedDb};

const INTERPRETATIONS: [(&str, covalence_lib_hash::O256); 4] = [
    (EXPRESSIONS_INTERPRETATION_V0, EXPRESSIONS_METATABLE_V0),
    (EXECUTORS_INTERPRETATION_V0, EXECUTORS_METATABLE_V0),
    (
        TABLE_INTERPRETATIONS_INTERPRETATION_V0,
        TABLE_INTERPRETATIONS_METATABLE_V0,
    ),
    (
        EXECUTION_TRACES_INTERPRETATION_V0,
        EXECUTION_TRACES_METATABLE_V0,
    ),
];

/// Result of atomically installing the normalized execution model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstallExecutionModelOutcome {
    /// All four extension metatables were installed.
    Installed,
    /// All four extension metatables were already present.
    AlreadyPresent,
}

macro_rules! local_id {
    ($name:ident) => {
        #[doc = "A connection-local row identifier."]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(i64);

        impl $name {
            /// Returns the stored `SQLite` integer.
            #[must_use]
            pub const fn get(self) -> i64 {
                self.0
            }
        }
    };
}

local_id!(ExpressionId);
local_id!(ExecutorId);
local_id!(TraceId);

/// Stable coarse outcome recorded by the prototype trace table.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TraceOutcome {
    /// The executor returned a value.
    Returned,
    /// The executor reported failure.
    Failed,
}

impl TraceOutcome {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Returned => "returned",
            Self::Failed => "failed",
        }
    }
}

/// Checked access to the normalized execution metatables.
pub struct ExecutionModel<'db> {
    database: &'db mut TrustedDb,
}

impl TrustedDb {
    /// Installs expression, executor, table-interpretation, and trace metatables.
    ///
    /// # Errors
    ///
    /// Installation fails atomically if the catalog is partially installed or
    /// if `SQLite`, scanning, or catalog acceptance fails.
    pub fn install_execution_model(
        &mut self,
    ) -> Result<InstallExecutionModelOutcome, ExecutionModelError> {
        let present = INTERPRETATIONS
            .iter()
            .filter(|(interpretation, _)| self.catalog.by_interpretation(interpretation).is_some())
            .count();
        if present == INTERPRETATIONS.len() {
            return Ok(InstallExecutionModelOutcome::AlreadyPresent);
        }
        if present != 0 {
            return Err(ExecutionModelError::PartialInstallation);
        }

        let expressions = table_name(EXPRESSIONS_METATABLE_V0);
        let executors = table_name(EXECUTORS_METATABLE_V0);
        let table_interpretations = table_name(TABLE_INTERPRETATIONS_METATABLE_V0);
        let traces = table_name(EXECUTION_TRACES_METATABLE_V0);
        let bootstrap = table_name(BOOTSTRAP_CATALOG);
        let transaction = self
            .connection
            .transaction()
            .map_err(ExecutionModelError::sqlite)?;
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {expressions} (
                    id INTEGER PRIMARY KEY,
                    sexpr TEXT NOT NULL UNIQUE
                ) STRICT;
                CREATE TABLE {executors} (
                    id INTEGER PRIMARY KEY,
                    name TEXT NOT NULL UNIQUE,
                    configuration_expression INTEGER
                        REFERENCES {expressions}(id)
                ) STRICT;
                CREATE TABLE {table_interpretations} (
                    table_name TEXT PRIMARY KEY,
                    expression_id INTEGER NOT NULL
                        REFERENCES {expressions}(id)
                ) STRICT;
                CREATE TABLE {traces} (
                    id INTEGER PRIMARY KEY,
                    executor_id INTEGER NOT NULL REFERENCES {executors}(id),
                    program_expression INTEGER NOT NULL REFERENCES {expressions}(id),
                    input_expression INTEGER NOT NULL REFERENCES {expressions}(id),
                    output_expression INTEGER REFERENCES {expressions}(id),
                    outcome TEXT NOT NULL CHECK (outcome IN ('returned', 'failed'))
                ) STRICT;"
            ))
            .map_err(ExecutionModelError::sqlite)?;
        for (interpretation, kind) in INTERPRETATIONS {
            transaction
                .execute(
                    &format!(
                        "INSERT INTO {bootstrap} (table_name, interpretation) VALUES (?1, ?2)"
                    ),
                    params![table_name(kind), interpretation],
                )
                .map_err(ExecutionModelError::sqlite)?;
        }
        let candidate = scan_metatables(&transaction).map_err(ExecutionModelError::scan)?;
        let catalog = NeutronCatalog::accept(&candidate, &transaction)
            .map_err(ExecutionModelError::catalog)?;
        transaction.commit().map_err(ExecutionModelError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(InstallExecutionModelOutcome::Installed)
    }

    /// Resolves the complete normalized execution model.
    ///
    /// # Errors
    ///
    /// Returns an error unless all four interpretations are installed.
    pub fn execution_model(&mut self) -> Result<ExecutionModel<'_>, ExecutionModelError> {
        if INTERPRETATIONS
            .iter()
            .all(|(interpretation, _)| self.catalog.by_interpretation(interpretation).is_some())
        {
            Ok(ExecutionModel { database: self })
        } else {
            Err(ExecutionModelError::NotInstalled)
        }
    }
}

impl ExecutionModel<'_> {
    /// Validates and interns exactly one textual S-expression.
    ///
    /// Text is not yet normalized: syntactically different spellings remain
    /// distinct rows in this prototype.
    ///
    /// # Errors
    ///
    /// Returns a syntax, structural, or `SQLite` error.
    pub fn register_expression(
        &mut self,
        expression: &str,
    ) -> Result<ExpressionId, ExecutionModelError> {
        let events = text::parse_symbols(expression)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|source| ExecutionModelError::ExpressionSyntax { source })?;
        let _: SExpr = SExpr::from_events(events)
            .map_err(|source| ExecutionModelError::ExpressionStructure { source })?;
        let table = table_name(EXPRESSIONS_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (sexpr) VALUES (?1)"),
                [expression],
            )
            .map_err(ExecutionModelError::sqlite)?;
        self.database
            .connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE sexpr = ?1"),
                [expression],
                |row| row.get::<_, i64>(0).map(ExpressionId),
            )
            .map_err(ExecutionModelError::sqlite)
    }

    /// Registers a named executor with an optional configuration expression.
    ///
    /// # Errors
    ///
    /// Returns a checked `SQLite` error, including foreign-key violations.
    pub fn register_executor(
        &mut self,
        name: &str,
        configuration: Option<ExpressionId>,
    ) -> Result<ExecutorId, ExecutionModelError> {
        let table = table_name(EXECUTORS_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT OR IGNORE INTO {table} (name, configuration_expression) VALUES (?1, ?2)"
                ),
                params![name, configuration.map(ExpressionId::get)],
            )
            .map_err(ExecutionModelError::sqlite)?;
        self.database
            .connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE name = ?1"),
                [name],
                |row| row.get::<_, i64>(0).map(ExecutorId),
            )
            .map_err(ExecutionModelError::sqlite)
    }

    /// Associates an expression with the interpretation of an existing table.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing table or invalid expression ID.
    pub fn interpret_table(
        &mut self,
        table: &str,
        interpretation: ExpressionId,
    ) -> Result<(), ExecutionModelError> {
        let exists = self
            .database
            .connection
            .query_row(
                "SELECT 1 FROM sqlite_schema WHERE type = 'table' AND name = ?1",
                [table],
                |_| Ok(()),
            )
            .optional()
            .map_err(ExecutionModelError::sqlite)?
            .is_some();
        if !exists {
            return Err(ExecutionModelError::MissingTable {
                table: table.to_owned(),
            });
        }
        let interpretations = table_name(TABLE_INTERPRETATIONS_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT INTO {interpretations} (table_name, expression_id) VALUES (?1, ?2)
                     ON CONFLICT(table_name) DO UPDATE SET expression_id = excluded.expression_id"
                ),
                params![table, interpretation.get()],
            )
            .map(|_| ())
            .map_err(ExecutionModelError::sqlite)
    }

    /// Records one executor invocation.
    ///
    /// # Errors
    ///
    /// Returns a checked `SQLite` error, including invalid references.
    pub fn record_trace(
        &mut self,
        executor: ExecutorId,
        program: ExpressionId,
        input: ExpressionId,
        output: Option<ExpressionId>,
        outcome: TraceOutcome,
    ) -> Result<TraceId, ExecutionModelError> {
        let traces = table_name(EXECUTION_TRACES_METATABLE_V0);
        self.database
            .connection
            .execute(
                &format!(
                    "INSERT INTO {traces}
                     (executor_id, program_expression, input_expression, output_expression, outcome)
                     VALUES (?1, ?2, ?3, ?4, ?5)"
                ),
                params![
                    executor.get(),
                    program.get(),
                    input.get(),
                    output.map(ExpressionId::get),
                    outcome.as_str()
                ],
            )
            .map_err(ExecutionModelError::sqlite)?;
        Ok(TraceId(self.database.connection.last_insert_rowid()))
    }
}

/// Failure while installing or using prototype A.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum ExecutionModelError {
    /// `SQLite` rejected an operation.
    #[snafu(display("execution metadata operation failed: {source}"))]
    Sqlite {
        /// Underlying `SQLite` failure.
        source: covalence_lib_sqlite::Error,
    },
    /// Mechanical metatable scanning failed.
    #[snafu(display("could not scan execution metatables: {source}"))]
    Scan {
        /// Scanner failure.
        source: ScanError,
    },
    /// Compiled catalog policy rejected the result.
    #[snafu(display("could not accept execution metatables: {source}"))]
    Catalog {
        /// Catalog failure.
        source: CatalogError,
    },
    /// Only some members of the extension family were present.
    #[snafu(display("normalized execution metatables are only partially installed"))]
    PartialInstallation,
    /// The extension family has not been installed.
    #[snafu(display("normalized execution metatables are not installed"))]
    NotInstalled,
    /// Expression text was not syntactically valid.
    #[snafu(display("invalid S-expression syntax: {source}"))]
    ExpressionSyntax {
        /// Parser failure.
        source: text::Error,
    },
    /// Events did not describe exactly one expression.
    #[snafu(display("invalid S-expression structure: {source}"))]
    ExpressionStructure {
        /// Tree construction failure.
        source: covalence_data_sexpr::sax::BuildError,
    },
    /// A table-interpretation row named an absent table.
    #[snafu(display("cannot interpret missing table `{table}`"))]
    MissingTable {
        /// Requested physical table.
        table: String,
    },
}

impl ExecutionModelError {
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

fn table_name(kind: covalence_lib_hash::O256) -> String {
    metatable_name(MetatableKind::new(kind))
}

#[cfg(test)]
mod tests {
    use covalence_neutron::{EXECUTION_TRACES_METATABLE_V0, MetatableKind, metatable_name};

    use super::{InstallExecutionModelOutcome, TraceOutcome};
    use crate::TrustedDb;

    #[test]
    fn normalized_tables_cover_the_north_star_flow() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(
            database.install_execution_model().unwrap(),
            InstallExecutionModelOutcome::Installed
        );
        assert_eq!(
            database.install_execution_model().unwrap(),
            InstallExecutionModelOutcome::AlreadyPresent
        );
        assert_eq!(database.catalog().metatables().len(), 4);

        let mut model = database.execution_model().unwrap();
        let configuration = model.register_expression("(fuel 1000)").unwrap();
        let program = model.register_expression("(add 20 22)").unwrap();
        let input = model.register_expression("()").unwrap();
        let output = model.register_expression("42").unwrap();
        let executor = model
            .register_executor("covalence.test/evaluator", Some(configuration))
            .unwrap();
        let trace_table = metatable_name(MetatableKind::new(EXECUTION_TRACES_METATABLE_V0));
        model.interpret_table(&trace_table, program).unwrap();
        let trace = model
            .record_trace(
                executor,
                program,
                input,
                Some(output),
                TraceOutcome::Returned,
            )
            .unwrap();
        assert!(trace.get() > 0);
    }

    #[test]
    fn expression_registry_rejects_zero_or_multiple_roots() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_execution_model().unwrap();
        let mut model = database.execution_model().unwrap();
        assert!(model.register_expression("").is_err());
        assert!(model.register_expression("a b").is_err());
    }
}
