use std::{cell::Cell, path::Path};

use bytes::Bytes;
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use covalence_neutron as neutron;

use crate::{Invariant, Standard, Unchecked};

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const CREATE_DEFAULT_CAS_SQL: &str = include_str!("../sql/create_default_cas.sql");
const CREATE_DATABASE_CATALOG_SQL: &str = include_str!("../sql/create_database_catalog.sql");
const CREATE_DATABASE_LOCKS_SQL: &str = include_str!("../sql/lock/create_database_locks.sql");
const CREATE_TABLE_LOCKS_SQL: &str = include_str!("../sql/lock/create_table_locks.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");

/// Physical name of the connection-local attached-database assertions.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Physical name of the connection's default CAS.
pub const DEFAULT_CAS: &str = "cov_conn_cas";

/// Interpretation of the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Interpretation of the attached-database assertions.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

/// Interpretation of the default CAS.
pub const DEFAULT_CAS_INTERPRETATION: &str = "cov.cas.default/v0";

/// A policy-enforcing connection to Nucleus state.
#[derive(Debug)]
pub struct Connection<I: Invariant = Standard> {
    pub(crate) neutron: neutron::Connection,
    pub(crate) invariant: I,
    pub(crate) poisoned: Cell<bool>,
}

impl Connection<Standard> {
    /// Opens a file-backed database without asserting semantic validity.
    ///
    /// # Errors
    ///
    /// Returns an error when opening or initialization fails.
    pub fn open(path: impl AsRef<Path>) -> Result<Connection<Unchecked>, ConnectionError> {
        neutron::Connection::open(path)
            .map(|neutron| Connection {
                neutron,
                invariant: Unchecked::new(),
                poisoned: Cell::new(false),
            })
            .context(OpenSnafu)
    }

    /// Opens a fresh trusted, exclusive in-memory Nucleus connection.
    ///
    /// # Errors
    ///
    /// Returns an error when opening or initialization fails.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let mut neutron = neutron::Connection::open_in_memory().context(OpenSnafu)?;
        initialize(&mut neutron)?;
        Ok(Self {
            neutron,
            invariant: Standard::new(),
            poisoned: Cell::new(false),
        })
    }

    /// Loads a database image without asserting semantic validity.
    ///
    /// # Errors
    ///
    /// Returns an error when loading fails.
    pub fn deserialize(bytes: &Bytes) -> Result<Connection<Unchecked>, ConnectionError> {
        neutron::Connection::deserialize(bytes)
            .map(|neutron| Connection {
                neutron,
                invariant: Unchecked::new(),
                poisoned: Cell::new(false),
            })
            .context(ImageSnafu)
    }
}

impl<I: Invariant> Connection<I> {
    /// Borrows the evidence carried as this connection's invariant.
    #[must_use]
    pub const fn invariant(&self) -> &I {
        &self.invariant
    }

    /// Reports whether a failed capability cleanup has poisoned this
    /// connection's mutation discipline.
    #[must_use]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned.get()
    }

    /// Serializes the primary database without connection-local state.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot serialize the database.
    pub fn serialize(&self) -> Result<Bytes, ConnectionError> {
        self.neutron.serialize().context(ImageSnafu)
    }

    pub(crate) const fn sqlite(&self) -> &sqlite::Connection {
        self.neutron.sqlite()
    }

    pub(crate) fn poison(&self) {
        self.poisoned.set(true);
    }
}

fn initialize(connection: &mut neutron::Connection) -> Result<(), ConnectionError> {
    let transaction = connection
        .sqlite_mut()
        .transaction()
        .context(InitializeSnafu)?;
    transaction
        .execute_batch(CREATE_CONNECTION_CATALOG_SQL)
        .context(InitializeSnafu)?;
    transaction
        .execute_batch(CREATE_DATABASE_CATALOG_SQL)
        .context(InitializeSnafu)?;
    register_table(
        &transaction,
        1,
        crate::CONNECTION_CATALOG,
        CONNECTION_CATALOG_INTERPRETATION,
    )?;
    create_and_register_table(
        &transaction,
        2,
        ATTACHED_DATABASES,
        ATTACHED_DATABASES_INTERPRETATION,
        CREATE_ATTACHED_DATABASES_SQL,
    )?;
    create_and_register_table(
        &transaction,
        3,
        DEFAULT_CAS,
        DEFAULT_CAS_INTERPRETATION,
        CREATE_DEFAULT_CAS_SQL,
    )?;
    create_and_register_table(
        &transaction,
        4,
        crate::DATABASE_LOCKS,
        "cov.conn.db-lock/v0",
        CREATE_DATABASE_LOCKS_SQL,
    )?;
    create_and_register_table(
        &transaction,
        5,
        crate::TABLE_LOCKS,
        "cov.conn.tab-lock/v0",
        CREATE_TABLE_LOCKS_SQL,
    )?;
    transaction
        .execute(REGISTER_ATTACHED_DATABASE_SQL, (1, "main", true, true))
        .context(InitializeSnafu)?;
    transaction.commit().context(InitializeSnafu)
}

fn create_and_register_table(
    transaction: &sqlite::Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
    create_sql: &str,
) -> Result<(), ConnectionError> {
    transaction
        .execute_batch(create_sql)
        .context(InitializeSnafu)?;
    register_table(transaction, table_id, table_name, interpretation)
}

fn register_table(
    transaction: &sqlite::Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
) -> Result<(), ConnectionError> {
    transaction
        .execute(REGISTER_TABLE_SQL, (table_id, table_name, interpretation))
        .context(InitializeSnafu)?;
    Ok(())
}

/// Failure to open or initialize a Nucleus connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// Neutron could not open the underlying connection.
    #[snafu(display("could not open Nucleus storage: {source}"))]
    Open { source: neutron::ConnectionError },

    /// A `SQLite` database image operation failed.
    #[snafu(display("Nucleus database image operation failed: {source}"))]
    Image { source: neutron::ImageError },

    /// Nucleus connection-local state could not be initialized.
    #[snafu(display("could not initialize Nucleus connection state: {source}"))]
    Initialize { source: sqlite::Error },
}

#[cfg(test)]
mod tests {
    use super::{Connection, DEFAULT_CAS};

    #[test]
    fn nucleus_owns_connection_initialization() {
        let connection = Connection::open_in_memory().unwrap();
        let tables = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema
                 WHERE name IN ('cov_conn_catalog', 'cov_conn_attached', ?1)",
                [DEFAULT_CAS],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(tables, 3);
    }
}
