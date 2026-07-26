use std::{any::type_name, collections::BTreeSet};

use covalence_lib_error::snafu;
use covalence_lib_sqlite::{Connection, OptionalExtension, params};
use covalence_neutron::{
    BOOTSTRAP_CATALOG, CatalogCandidate, MetatableKind, RUST_TYPES_INTERPRETATION_V0,
    RUST_TYPES_METATABLE_V0, ScanError, metatable_name, scan_metatables,
};
use snafu::Snafu;

/// One metatable accepted from the permanent bootstrap catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metatable {
    table_name: String,
    interpretation: String,
}

impl Metatable {
    /// Returns the physical metatable name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table_name
    }

    /// Returns the interpretation selected by the bootstrap.
    #[must_use]
    pub fn interpretation(&self) -> &str {
        &self.interpretation
    }
}

/// Accepted connection-local metatable interpretations.
///
/// Acceptance requires exactly one bootstrap catalog with the permanent
/// [`covalence_neutron::BOOTSTRAP_CATALOG`] identity and physical ABI.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NeutronCatalog {
    metatables: Vec<Metatable>,
}

impl NeutronCatalog {
    /// Returns extension metatables registered by the bootstrap.
    #[must_use]
    pub fn metatables(&self) -> &[Metatable] {
        &self.metatables
    }

    fn accept(candidate: &CatalogCandidate, connection: &Connection) -> Result<Self, CatalogError> {
        let bootstrap = candidate
            .bootstrap()
            .ok_or(CatalogError::MissingBootstrapCatalog)?;
        let metatables = bootstrap
            .declarations()
            .iter()
            .map(|declaration| Metatable {
                table_name: declaration.table_name().to_owned(),
                interpretation: declaration.interpretation().to_owned(),
            })
            .collect::<Vec<_>>();
        let mut interpretations = BTreeSet::new();
        for metatable in &metatables {
            if !interpretations.insert(metatable.interpretation.as_str()) {
                return Err(CatalogError::DuplicateInterpretation {
                    interpretation: metatable.interpretation.clone(),
                });
            }
            if metatable.interpretation == RUST_TYPES_INTERPRETATION_V0 {
                validate_rust_types_metatable(connection, metatable)?;
            }
        }
        Ok(Self { metatables })
    }

    fn by_interpretation(&self, interpretation: &str) -> Option<&Metatable> {
        self.metatables
            .iter()
            .find(|metatable| metatable.interpretation == interpretation)
    }
}

/// Rejection while accepting structurally decoded metadata as a known API.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum CatalogError {
    /// The required bootstrap catalog was absent.
    #[snafu(display("missing bootstrap catalog"))]
    MissingBootstrapCatalog,
    /// A known interpretation appeared at an unexpected physical table.
    #[snafu(display(
        "interpretation `{interpretation}` must use table `{expected}`, found `{actual}`"
    ))]
    WrongInterpretationTable {
        /// Interpretation selected by the bootstrap.
        interpretation: String,
        /// Required physical name.
        expected: String,
        /// Actual registered name.
        actual: String,
    },
    /// A recognized extension had the wrong permanent shape.
    #[snafu(display("invalid `{interpretation}` metatable schema: {reason}"))]
    InvalidExtensionSchema {
        /// Interpretation being validated.
        interpretation: String,
        /// Stable rejection detail.
        reason: String,
    },
    /// Two physical tables selected the same singleton interpretation.
    #[snafu(display("duplicate metatable interpretation `{interpretation}`"))]
    DuplicateInterpretation {
        /// Duplicated interpretation.
        interpretation: String,
    },
    /// `SQLite` failed during interpretation validation.
    #[snafu(display("could not validate metatable interpretation: {source}"))]
    ValidationSqlite {
        /// Underlying `SQLite` failure.
        source: covalence_lib_sqlite::Error,
    },
}

/// The only writable trusted `SQLite` owner in this initial slice.
///
/// The raw connection is intentionally private and has no public escape hatch.
/// Construction accepts exactly one bootstrap catalog in `main`; the MVP does
/// not yet support attached database namespaces.
pub struct TrustedDb {
    connection: Connection,
    catalog: NeutronCatalog,
    generation: u64,
}

impl TrustedDb {
    /// Creates a fresh trusted database containing an empty bootstrap catalog.
    ///
    /// At this point the database supports no extension metatable
    /// interpretations and exposes no typed relation capabilities.
    ///
    /// # Errors
    ///
    /// Fails atomically if `SQLite` setup, metatable scanning, or catalog
    /// acceptance fails.
    pub fn create_in_memory() -> Result<Self, TrustedDbError> {
        let mut connection = Connection::open_in_memory().map_err(TrustedDbError::sqlite)?;
        connection
            .execute_batch("PRAGMA foreign_keys = ON;")
            .map_err(TrustedDbError::sqlite)?;
        let transaction = connection.transaction().map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{bootstrap}\" (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        Ok(Self {
            connection,
            catalog,
            generation: 0,
        })
    }

    /// Returns the accepted connection-local catalog.
    #[must_use]
    pub const fn catalog(&self) -> &NeutronCatalog {
        &self.catalog
    }

    /// Returns the schema generation.
    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    /// Installs the first extension metatable: Rust type names to integer IDs.
    ///
    /// The extension table and its bootstrap registration are created in one
    /// transaction, rescanned, and accepted before becoming visible.
    ///
    /// # Errors
    ///
    /// Returns a checked database, scan, or catalog error.
    pub fn install_rust_types(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        if self
            .catalog
            .by_interpretation(RUST_TYPES_INTERPRETATION_V0)
            .is_some()
        {
            return Ok(InstallOutcome::AlreadyPresent);
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let rust_types = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{rust_types}\" (
                    id INTEGER PRIMARY KEY,
                    rust_type TEXT NOT NULL UNIQUE
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![rust_types, RUST_TYPES_INTERPRETATION_V0],
            )
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(InstallOutcome::Installed)
    }

    /// Resolves the installed Rust-type registry as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingRustTypes`] before the extension has
    /// been installed.
    pub fn rust_types(&mut self) -> Result<RustTypes<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(RUST_TYPES_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingRustTypes)?;
        Ok(RustTypes {
            connection: &mut self.connection,
            metatable,
        })
    }
}

/// Result of installing a singleton extension metatable.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum InstallOutcome {
    /// The extension and its bootstrap row were created.
    Installed,
    /// The accepted catalog already contained the extension.
    AlreadyPresent,
}

/// A connection-local integer identifying one Rust type name.
///
/// The ID and [`std::any::type_name`] text are execution metadata, not stable
/// substrate semantics or a portable Rust ABI.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RustTypeId(i64);

impl RustTypeId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// Checked access to the Rust-type registry extension.
pub struct RustTypes<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

impl RustTypes<'_> {
    /// Registers `T`'s diagnostic Rust type name and returns its local ID.
    ///
    /// Repeated registration of the same name returns the same ID.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if insertion or lookup fails.
    pub fn register<T: ?Sized>(&mut self) -> Result<RustTypeId, TrustedDbError> {
        self.register_name(type_name::<T>())
    }

    /// Returns all registered IDs and diagnostic names in ID order.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the registry cannot be read.
    pub fn entries(&self) -> Result<Vec<(RustTypeId, String)>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        let mut statement = self
            .connection
            .prepare(&format!("SELECT id, rust_type FROM {table} ORDER BY id"))
            .map_err(TrustedDbError::sqlite)?;
        statement
            .query_map((), |row| {
                Ok((RustTypeId(row.get(0)?), row.get::<_, String>(1)?))
            })
            .map_err(TrustedDbError::sqlite)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(TrustedDbError::sqlite)
    }

    fn register_name(&mut self, name: &str) -> Result<RustTypeId, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (rust_type) VALUES (?1)"),
                [name],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE rust_type = ?1"),
                [name],
                |row| row.get::<_, i64>(0).map(RustTypeId),
            )
            .map_err(TrustedDbError::sqlite)
    }
}

/// Failure while constructing or using the exclusive trusted wrapper.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum TrustedDbError {
    /// `SQLite` failed within a checked operation.
    #[snafu(display("trusted SQLite operation failed: {source}"))]
    Sqlite {
        /// Underlying failure.
        source: covalence_lib_sqlite::Error,
    },
    /// Mechanical metatable scanning failed.
    #[snafu(display("could not scan metatables: {source}"))]
    Scan {
        /// Scanner failure.
        source: ScanError,
    },
    /// Structurally valid metadata was not accepted by compiled policy.
    #[snafu(display("could not accept Neutron catalog: {source}"))]
    Catalog {
        /// Acceptance failure.
        source: CatalogError,
    },
    /// The Rust-type extension has not been installed.
    #[snafu(display("the Rust-type metatable is not installed"))]
    MissingRustTypes,
}

impl TrustedDbError {
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

fn validate_rust_types_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
    if metatable.table_name != expected {
        return Err(CatalogError::WrongInterpretationTable {
            interpretation: metatable.interpretation.clone(),
            expected,
            actual: metatable.table_name.clone(),
        });
    }
    if !table_is_strict(connection, &metatable.table_name)? {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("table must be STRICT"),
        });
    }
    let columns = table_columns(connection, &metatable.table_name)?;
    let expected_columns = [
        ("id", "INTEGER", false, 1_u32),
        ("rust_type", "TEXT", true, 0),
    ];
    if columns.len() != expected_columns.len()
        || !columns.iter().zip(expected_columns).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("columns do not match the Rust-type registry contract"),
        });
    }
    Ok(())
}

type PhysicalColumn = (String, String, bool, u32);

fn table_columns(
    connection: &Connection,
    table: &str,
) -> Result<Vec<PhysicalColumn>, CatalogError> {
    let mut statement = connection
        .prepare(&format!(
            "PRAGMA main.table_info({})",
            quote_identifier(table)
        ))
        .map_err(|source| CatalogError::ValidationSqlite { source })?;
    statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)? != 0,
                row.get::<_, u32>(5)?,
            ))
        })
        .map_err(|source| CatalogError::ValidationSqlite { source })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|source| CatalogError::ValidationSqlite { source })
}

fn table_is_strict(connection: &Connection, table: &str) -> Result<bool, CatalogError> {
    connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [table],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map(|strict| strict == Some(1))
        .map_err(|source| CatalogError::ValidationSqlite { source })
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use super::{InstallOutcome, TrustedDb, TrustedDbError};

    #[test]
    fn creation_accepts_an_empty_bootstrap() {
        let database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(database.generation(), 0);
        assert!(database.catalog().metatables().is_empty());
    }

    #[test]
    fn no_typed_extension_exists_before_installation() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.rust_types(),
            Err(TrustedDbError::MissingRustTypes)
        ));
    }

    #[test]
    fn rust_type_registry_is_installed_through_the_bootstrap() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(
            database.install_rust_types().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_rust_types().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        assert_eq!(database.generation(), 1);
        assert_eq!(database.catalog().metatables().len(), 1);

        let mut types = database.rust_types().unwrap();
        let bool_id = types.register::<bool>().unwrap();
        assert_eq!(types.register::<bool>().unwrap(), bool_id);
        let u64_id = types.register::<u64>().unwrap();
        assert_ne!(bool_id, u64_id);
        assert_eq!(
            types.entries().unwrap(),
            vec![
                (bool_id, String::from("bool")),
                (u64_id, String::from("u64"))
            ]
        );
    }
}
