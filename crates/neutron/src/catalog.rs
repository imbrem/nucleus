//! Database-local catalogs of interpreted tables.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{CONNECTION_CATALOG, Connection};

/// Physical catalog table name within each persistent database.
pub const DB_CATALOG: &str = "cov_db_catalog";

/// One uninterpreted database-catalog entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogEntry {
    /// Catalog-local stable identifier for the physical table.
    pub table_id: i64,
    /// Physical table name within the catalog's database.
    pub table_name: String,
    /// Uninterpreted meaning assigned by the higher layer.
    pub interpretation: String,
}

/// Mechanical access to a database or connection catalog.
#[derive(Debug)]
pub struct Catalog<'conn> {
    connection: &'conn Connection,
    database_name: String,
}

impl Connection {
    /// Opens a catalog, creating an empty database-local one when absent.
    ///
    /// `temp` selects the connection catalog initialized by Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing database, incompatible existing catalog,
    /// or storage failure.
    pub fn catalog(&self, database_name: &str) -> Result<Catalog<'_>, CatalogError> {
        validate_database(self.sqlite(), database_name)?;
        let catalog = Catalog {
            connection: self,
            database_name: database_name.to_owned(),
        };
        catalog.create_if_absent()?;
        catalog.validate()?;
        Ok(catalog)
    }
}

impl<'conn> Catalog<'conn> {
    /// Returns the database schema containing this catalog.
    #[must_use]
    pub fn database_name(&self) -> &str {
        &self.database_name
    }

    /// Tests whether this is the connection-local catalog in `temp`.
    #[must_use]
    pub fn is_conn(&self) -> bool {
        self.database_name == "temp"
    }

    /// Tests whether this is the primary database's catalog.
    #[must_use]
    pub fn is_main(&self) -> bool {
        self.database_name == "main"
    }

    /// Returns the underlying permeable Neutron connection.
    #[must_use]
    pub const fn connection(&self) -> &'conn Connection {
        self.connection
    }

    /// Tests whether this database is marked both trusted and exclusive.
    ///
    /// This reads Neutron's connection-local database registry. It does not
    /// independently establish either property.
    ///
    /// # Errors
    ///
    /// Returns an error if the registry cannot be read or no longer contains
    /// this database.
    pub fn is_trusted_exclusive(&self) -> Result<bool, CatalogError> {
        if self.is_conn() {
            return Ok(true);
        }
        self.connection
            .sqlite()
            .query_row(
                "SELECT is_trusted AND is_exclusive
                 FROM temp.cov_conn_attached
                 WHERE schema_name = ?1",
                [&self.database_name],
                |row| row.get(0),
            )
            .context(DatabaseRegistrationSnafu {
                database_name: &self.database_name,
            })
    }

    /// Loads all uninterpreted catalog entries.
    ///
    /// # Errors
    ///
    /// Returns an error if storage cannot be read.
    pub fn entries(&self) -> Result<Vec<CatalogEntry>, CatalogError> {
        let mut statement = self
            .connection
            .sqlite()
            .prepare(&format!(
                "SELECT table_id, table_name, interpretation
                 FROM {} ORDER BY table_id",
                self.qualified_catalog()
            ))
            .context(StorageSnafu)?;
        statement
            .query_map((), |row| {
                Ok(CatalogEntry {
                    table_id: row.get(0)?,
                    table_name: row.get(1)?,
                    interpretation: row.get(2)?,
                })
            })
            .context(StorageSnafu)?
            .collect::<sqlite::Result<Vec<_>>>()
            .context(StorageSnafu)
    }

    /// Registers an uninterpreted physical table.
    ///
    /// Neutron makes no claim that the table exists or that the interpretation
    /// is sound. A policy layer must establish those properties before calling
    /// this method.
    ///
    /// # Errors
    ///
    /// Returns an error if storage rejects the entry.
    pub fn register(&self, table_name: &str, interpretation: &str) -> Result<(), CatalogError> {
        self.connection
            .sqlite()
            .execute(
                &format!(
                    "INSERT INTO {} (table_id, table_name, interpretation)
                     VALUES (
                         (SELECT COALESCE(MAX(table_id), 0) + 1 FROM {}),
                         ?1,
                         ?2
                     )",
                    self.qualified_catalog(),
                    self.qualified_catalog()
                ),
                (table_name, interpretation),
            )
            .context(StorageSnafu)?;
        Ok(())
    }

    fn create_if_absent(&self) -> Result<(), CatalogError> {
        if self.is_conn() {
            return Ok(());
        }
        self.connection
            .sqlite()
            .execute_batch(&format!(
                "CREATE TABLE IF NOT EXISTS {} (
                    table_id INTEGER PRIMARY KEY,
                    table_name TEXT NOT NULL UNIQUE,
                    interpretation TEXT NOT NULL
                ) STRICT;",
                self.qualified_catalog()
            ))
            .context(StorageSnafu)
    }

    fn validate(&self) -> Result<(), CatalogError> {
        let catalog_name = self.catalog_name();
        let columns = self
            .connection
            .sqlite()
            .prepare(&format!(
                "PRAGMA {}.table_info({})",
                quote_identifier(&self.database_name),
                quote_identifier(catalog_name)
            ))
            .context(StorageSnafu)?
            .query_map((), |row| {
                Ok((
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, bool>(3)?,
                    row.get::<_, i64>(5)?,
                ))
            })
            .context(StorageSnafu)?
            .collect::<sqlite::Result<Vec<_>>>()
            .context(StorageSnafu)?;
        let flags = self
            .connection
            .sqlite()
            .query_row(
                "SELECT strict, wr FROM pragma_table_list
                 WHERE schema = ?1 AND name = ?2",
                (&self.database_name, catalog_name),
                |row| Ok((row.get::<_, bool>(0)?, row.get::<_, bool>(1)?)),
            )
            .context(StorageSnafu)?;
        let expected_columns = [
            (String::from("table_id"), String::from("INTEGER"), false, 1),
            (String::from("table_name"), String::from("TEXT"), true, 0),
            (
                String::from("interpretation"),
                String::from("TEXT"),
                true,
                0,
            ),
        ];
        if columns != expected_columns || flags != (true, false) {
            return Err(CatalogError::Malformed {
                database_name: self.database_name.clone(),
            });
        }
        Ok(())
    }

    fn qualified_catalog(&self) -> String {
        format!(
            "{}.{}",
            quote_identifier(&self.database_name),
            quote_identifier(self.catalog_name())
        )
    }

    fn catalog_name(&self) -> &'static str {
        if self.is_conn() {
            CONNECTION_CATALOG
        } else {
            DB_CATALOG
        }
    }
}

fn validate_database(sqlite: &sqlite::Connection, database_name: &str) -> Result<(), CatalogError> {
    let exists = sqlite
        .prepare("PRAGMA database_list")
        .context(StorageSnafu)?
        .query_map((), |row| row.get::<_, String>(1))
        .context(StorageSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(StorageSnafu)?
        .into_iter()
        .any(|name| name == database_name);
    if !exists {
        return Err(CatalogError::MissingDatabase {
            database_name: database_name.to_owned(),
        });
    }
    Ok(())
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to create, validate, or access a database-local catalog.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CatalogError {
    /// The requested attached database does not exist.
    #[snafu(display("database {database_name:?} is not attached"))]
    MissingDatabase { database_name: String },

    /// An existing catalog has incompatible geometry.
    #[snafu(display("database {database_name:?} has a malformed catalog"))]
    Malformed { database_name: String },

    /// The database is absent from Neutron's connection-local registry.
    #[snafu(display("database {database_name:?} is absent from Neutron's connection registry"))]
    DatabaseRegistration {
        database_name: String,
        source: sqlite::Error,
    },

    /// The underlying storage operation failed.
    #[snafu(display("database catalog storage operation failed: {source}"))]
    Storage { source: sqlite::Error },
}
