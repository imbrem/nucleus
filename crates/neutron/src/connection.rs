use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const CREATE_DEFAULT_CAS_SQL: &str = include_str!("../sql/create_default_cas.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");

/// Physical name of Neutron's connection catalog in `temp`.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of Neutron's registered-database table in `temp`.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Physical name of Neutron's connection-local default CAS.
pub const DEFAULT_CAS: &str = "cov_conn_default_cas";

/// Uninterpreted symbol assigned to the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Uninterpreted symbol assigned to the attached-database registry.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

/// Uninterpreted symbol assigned to the connection-local default CAS.
pub const DEFAULT_CAS_INTERPRETATION: &str = "cov.cas.default/v0";

/// A permeable `SQLite` connection with Neutron's connection-local metadata.
///
/// This type makes no claim that the database is valid Nucleus state. Direct
/// access to the underlying connection is intentional.
#[derive(Debug)]
pub struct Connection {
    sqlite: sqlite::Connection,
}

impl Connection {
    /// Opens a `SQLite` database and initializes its Neutron connection state.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened or the connection
    /// metadata cannot be initialized atomically.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open(path).context(OpenSnafu)?;
        Self::from_sqlite_with_main_access(sqlite, false, false)
    }

    /// Opens an in-memory `SQLite` database and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        Self::from_sqlite_with_main_access(sqlite, true, true)
    }

    /// Adopts a raw connection and initializes Neutron's temporary metadata.
    ///
    /// Initialization is transactional. Existing objects using Neutron's
    /// reserved connection names cause initialization to fail.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn from_sqlite(mut sqlite: sqlite::Connection) -> Result<Self, ConnectionError> {
        initialize(&mut sqlite, false, false)?;
        Ok(Self { sqlite })
    }

    pub(crate) fn from_sqlite_with_main_access(
        mut sqlite: sqlite::Connection,
        is_trusted: bool,
        is_exclusive: bool,
    ) -> Result<Self, ConnectionError> {
        initialize(&mut sqlite, is_trusted, is_exclusive)?;
        Ok(Self { sqlite })
    }

    /// Borrows the underlying `SQLite` connection.
    #[must_use]
    pub const fn sqlite(&self) -> &sqlite::Connection {
        &self.sqlite
    }

    /// Mutably borrows the underlying `SQLite` connection.
    ///
    /// Mutations made through this escape hatch can invalidate any assumptions
    /// a higher layer has established.
    #[must_use]
    pub const fn sqlite_mut(&mut self) -> &mut sqlite::Connection {
        &mut self.sqlite
    }

    /// Consumes the wrapper and returns the underlying connection.
    #[must_use]
    pub fn into_sqlite(self) -> sqlite::Connection {
        self.sqlite
    }
}

/// Failure to open or initialize a Neutron connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// The raw `SQLite` connection could not be opened.
    #[snafu(display("could not open SQLite connection: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Neutron's connection-local schema could not be initialized.
    #[snafu(display("could not initialize Neutron connection metadata: {source}"))]
    Initialize {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}

fn initialize(
    connection: &mut sqlite::Connection,
    main_is_trusted: bool,
    main_is_exclusive: bool,
) -> Result<(), ConnectionError> {
    let transaction = connection.transaction().context(InitializeSnafu)?;

    transaction
        .execute_batch(CREATE_CONNECTION_CATALOG_SQL)
        .context(InitializeSnafu)?;
    register_table(
        &transaction,
        1,
        CONNECTION_CATALOG,
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

    register_attached_database(&transaction, 1, "main", main_is_trusted, main_is_exclusive)?;

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

fn register_attached_database(
    transaction: &sqlite::Transaction<'_>,
    database_id: i64,
    schema_name: &str,
    is_trusted: bool,
    is_exclusive: bool,
) -> Result<(), ConnectionError> {
    transaction
        .execute(
            REGISTER_ATTACHED_DATABASE_SQL,
            (database_id, schema_name, is_trusted, is_exclusive),
        )
        .context(InitializeSnafu)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        ATTACHED_DATABASES, CONNECTION_CATALOG, Connection, ConnectionError, DEFAULT_CAS,
        initialize,
    };
    use covalence_lib_sqlite as sqlite;

    #[test]
    fn initializes_catalog_and_main_registration() {
        let connection = Connection::open_in_memory().expect("initialize Neutron");

        let catalog = connection
            .sqlite()
            .prepare(
                "SELECT table_id, table_name, interpretation
                 FROM temp.cov_conn_catalog
                 ORDER BY table_id",
            )
            .expect("prepare catalog query")
            .query_map((), |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                ))
            })
            .expect("query catalog")
            .collect::<sqlite::Result<Vec<_>>>()
            .expect("read catalog");

        assert_eq!(
            catalog,
            [
                (
                    1,
                    String::from(CONNECTION_CATALOG),
                    String::from("cov.conn.catalog/v0")
                ),
                (
                    2,
                    String::from(ATTACHED_DATABASES),
                    String::from("cov.conn.attached/v0")
                ),
                (
                    3,
                    String::from(DEFAULT_CAS),
                    String::from("cov.cas.default/v0")
                ),
            ]
        );

        let attached = connection
            .sqlite()
            .query_row(
                "SELECT database_id, schema_name, is_trusted, is_exclusive
                 FROM temp.cov_conn_attached",
                (),
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, bool>(2)?,
                        row.get::<_, bool>(3)?,
                    ))
                },
            )
            .expect("read attached database");
        assert_eq!(attached, (1, String::from("main"), true, true));
    }

    #[test]
    fn initialization_does_not_modify_main() {
        let connection = Connection::open_in_memory().expect("initialize Neutron");
        let main_tables = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema WHERE type = 'table'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("count main tables");
        assert_eq!(main_tables, 0);
    }

    #[test]
    fn failed_initialization_rolls_back_new_metadata() {
        let mut sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        sqlite
            .execute(
                "CREATE TEMP TABLE cov_conn_attached (sentinel INTEGER) STRICT",
                (),
            )
            .expect("reserve connection name");

        assert!(matches!(
            initialize(&mut sqlite, false, false),
            Err(ConnectionError::Initialize { .. })
        ));

        let catalog_exists = sqlite
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema
                 WHERE type = 'table' AND name = 'cov_conn_catalog'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect rolled-back schema");
        assert_eq!(catalog_exists, 0);

        let sentinel_exists = sqlite
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema
                 WHERE type = 'table' AND name = 'cov_conn_attached'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect pre-existing schema");
        assert_eq!(sentinel_exists, 1);
    }

    #[test]
    fn existing_connection_catalog_is_rejected() {
        let mut sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        sqlite
            .execute(
                "CREATE TEMP TABLE cov_conn_catalog (sentinel INTEGER) STRICT",
                (),
            )
            .expect("reserve catalog name");

        assert!(matches!(
            initialize(&mut sqlite, false, false),
            Err(ConnectionError::Initialize { .. })
        ));

        let columns = sqlite
            .query_row(
                "SELECT count(*) FROM temp.pragma_table_info('cov_conn_catalog')",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect pre-existing catalog");
        assert_eq!(columns, 1);
    }

    #[test]
    fn exposes_underlying_connection() {
        let mut connection = Connection::open_in_memory().expect("initialize Neutron");
        connection
            .sqlite_mut()
            .execute("CREATE TABLE application_data (value TEXT)", ())
            .expect("write through escape hatch");

        let sqlite = connection.into_sqlite();
        let exists = sqlite
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema
                 WHERE type = 'table' AND name = 'application_data'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect raw connection");
        assert_eq!(exists, 1);
    }
}
