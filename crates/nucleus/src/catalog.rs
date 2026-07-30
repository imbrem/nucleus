use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Connection, LockError, Standard};

/// Physical name of the connection-local catalog.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of a database-local catalog.
pub const DB_CATALOG: &str = "cov_db_catalog";

/// One catalog assertion about a physical table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CatalogEntry {
    /// Stable identifier within this catalog.
    pub table_id: i64,
    /// Physical table name.
    pub table_name: String,
    /// Nucleus interpretation assigned to the table.
    pub interpretation: String,
}

/// Nucleus assertions about tables in one database or this connection.
#[derive(Debug)]
pub struct Catalog<'conn> {
    pub(crate) connection: &'conn Connection<Standard>,
    pub(crate) database_name: String,
}

impl Connection<Standard> {
    /// Opens a trusted catalog, creating a database-local catalog when absent.
    ///
    /// `temp` selects the connection catalog.
    ///
    /// # Errors
    ///
    /// Returns an error unless the database exists and is trusted and
    /// exclusive, or when catalog storage is malformed.
    pub fn catalog(&self, database_name: &str) -> Result<Catalog<'_>, CatalogError> {
        validate_database(self.sqlite(), database_name)?;
        let catalog = Catalog {
            connection: self,
            database_name: database_name.to_owned(),
        };
        if !catalog.is_trusted_exclusive()? {
            return Err(CatalogError::NotTrustedExclusive {
                database_name: database_name.to_owned(),
            });
        }
        if !catalog.exists()? {
            crate::lock::ensure_database_write_unlocked(self, database_name)
                .map_err(|source| CatalogError::Locked { source })?;
            catalog.create()?;
        }
        catalog.validate()?;
        Ok(catalog)
    }
}

impl Catalog<'_> {
    /// Returns the containing `SQLite` database name.
    #[must_use]
    pub fn database_name(&self) -> &str {
        &self.database_name
    }

    /// Tests whether this catalog describes connection-local state.
    #[must_use]
    pub fn is_conn(&self) -> bool {
        self.database_name == "temp"
    }

    /// Tests whether this is the primary database catalog.
    #[must_use]
    pub fn is_main(&self) -> bool {
        self.database_name == "main"
    }

    /// Loads the catalog assertions.
    ///
    /// # Errors
    ///
    /// Returns an error if catalog storage cannot be read.
    pub fn entries(&self) -> Result<Vec<CatalogEntry>, CatalogError> {
        self.connection
            .sqlite()
            .prepare(&format!(
                "SELECT table_id, table_name, interpretation
                 FROM {} ORDER BY table_id",
                self.qualified_catalog()
            ))
            .context(StorageSnafu)?
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

    fn is_trusted_exclusive(&self) -> Result<bool, CatalogError> {
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
            .context(StorageSnafu)
    }

    fn exists(&self) -> Result<bool, CatalogError> {
        self.connection
            .sqlite()
            .query_row(
                "SELECT EXISTS (
                    SELECT 1 FROM pragma_table_list
                    WHERE schema = ?1 AND name = ?2
                )",
                (&self.database_name, self.catalog_name()),
                |row| row.get(0),
            )
            .context(StorageSnafu)
    }

    fn create(&self) -> Result<(), CatalogError> {
        if self.is_conn() {
            return Ok(());
        }
        self.connection
            .sqlite()
            .execute_batch(&format!(
                "CREATE TABLE {} (
                    table_id INTEGER PRIMARY KEY,
                    table_name TEXT NOT NULL UNIQUE,
                    interpretation TEXT NOT NULL
                ) STRICT;",
                self.qualified_catalog()
            ))
            .context(StorageSnafu)
    }

    fn validate(&self) -> Result<(), CatalogError> {
        let columns = self
            .connection
            .sqlite()
            .prepare(&format!(
                "PRAGMA {}.table_info({})",
                quote_identifier(&self.database_name),
                quote_identifier(self.catalog_name())
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
                (&self.database_name, self.catalog_name()),
                |row| Ok((row.get::<_, bool>(0)?, row.get::<_, bool>(1)?)),
            )
            .context(StorageSnafu)?;
        if columns
            != [
                (String::from("table_id"), String::from("INTEGER"), false, 1),
                (String::from("table_name"), String::from("TEXT"), true, 0),
                (
                    String::from("interpretation"),
                    String::from("TEXT"),
                    true,
                    0,
                ),
            ]
            || flags != (true, false)
        {
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

pub(crate) fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to access a Nucleus catalog.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CatalogError {
    /// The requested `SQLite` database does not exist.
    #[snafu(display("database {database_name:?} is not attached"))]
    MissingDatabase { database_name: String },

    /// Nucleus does not have trusted exclusive access to the database.
    #[snafu(display("database {database_name:?} is not trusted and exclusive"))]
    NotTrustedExclusive { database_name: String },

    /// The catalog has incompatible geometry.
    #[snafu(display("database {database_name:?} has a malformed catalog"))]
    Malformed { database_name: String },

    /// A logical lock prevents creation of the database-local catalog.
    #[snafu(display("database catalog creation conflicts with a logical lock: {source}"))]
    Locked { source: LockError },

    /// Catalog storage failed.
    #[snafu(display("catalog storage operation failed: {source}"))]
    Storage { source: sqlite::Error },
}
