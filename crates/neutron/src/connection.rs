use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite::{self as sqlite, Statement};

use crate::sql::{self, Param, Transaction};

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");

/// Physical name of Neutron's connection catalog in `temp`.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of Neutron's registered-database table in `temp`.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Uninterpreted symbol assigned to the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Uninterpreted symbol assigned to the attached-database registry.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

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
        // `sqlite3_open_v2` takes a `char *`. A path which is not UTF-8 has no
        // faithful representation there, so it is refused rather than
        // lossily converted into a path naming a different file.
        let path = path.as_ref();
        let path = path.to_str().ok_or_else(|| ConnectionError::NonUtf8Path {
            path: path.to_owned(),
        })?;
        let path = sql::c_string(path).context(OpenSnafu)?;
        let sqlite = sqlite::Connection::open(&path).context(OpenSnafu)?;
        Self::from_sqlite(sqlite)
    }

    /// Opens an in-memory `SQLite` database and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        Self::from_sqlite(sqlite)
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
        initialize(&mut sqlite)?;
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

    /// The database path is not valid UTF-8.
    ///
    /// `SQLite` names files with a `char *`, so a path this crate cannot
    /// represent as UTF-8 is refused rather than converted lossily into a path
    /// naming some other file.
    #[snafu(display("database path is not valid UTF-8: {}", path.display()))]
    NonUtf8Path {
        /// The rejected path.
        path: std::path::PathBuf,
    },
}

fn initialize(connection: &mut sqlite::Connection) -> Result<(), ConnectionError> {
    let transaction = Transaction::begin(connection).context(InitializeSnafu)?;

    Statement::execute_batch(transaction.connection(), CREATE_CONNECTION_CATALOG_SQL)
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

    register_attached_database(&transaction, 1, "main")?;

    transaction.commit().context(InitializeSnafu)
}

fn create_and_register_table(
    transaction: &Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
    create_sql: &str,
) -> Result<(), ConnectionError> {
    Statement::execute_batch(transaction.connection(), create_sql).context(InitializeSnafu)?;
    register_table(transaction, table_id, table_name, interpretation)
}

fn register_table(
    transaction: &Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
) -> Result<(), ConnectionError> {
    sql::execute(
        transaction.connection(),
        REGISTER_TABLE_SQL,
        &[
            Param::Integer(table_id),
            Param::Text(table_name),
            Param::Text(interpretation),
        ],
    )
    .context(InitializeSnafu)?;
    Ok(())
}

fn register_attached_database(
    transaction: &Transaction<'_>,
    database_id: i64,
    schema_name: &str,
) -> Result<(), ConnectionError> {
    sql::execute(
        transaction.connection(),
        REGISTER_ATTACHED_DATABASE_SQL,
        &[Param::Integer(database_id), Param::Text(schema_name)],
    )
    .context(InitializeSnafu)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{ATTACHED_DATABASES, CONNECTION_CATALOG, Connection, ConnectionError, initialize};
    use crate::sql;
    use covalence_lib_sqlite::{self as sqlite, Statement};

    #[test]
    fn initializes_catalog_and_main_registration() {
        let connection = Connection::open_in_memory().expect("initialize Neutron");

        let catalog = sql::query_all(
            connection.sqlite(),
            "SELECT table_id, table_name, interpretation
             FROM temp.cov_conn_catalog
             ORDER BY table_id",
            &[],
            |row| Ok((row.integer(0)?, row.text(1)?, row.text(2)?)),
        )
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
            ]
        );

        let attached = sql::query_row(
            connection.sqlite(),
            "SELECT database_id, schema_name FROM temp.cov_conn_attached",
            &[],
            |row| Ok((row.integer(0)?, row.text(1)?)),
        )
        .expect("read attached database")
        .expect("one attached database");
        assert_eq!(attached, (1, String::from("main")));
    }

    #[test]
    fn initialization_does_not_modify_main() {
        let connection = Connection::open_in_memory().expect("initialize Neutron");
        let main_tables = sql::query_row(
            connection.sqlite(),
            "SELECT count(*) FROM main.sqlite_schema WHERE type = 'table'",
            &[],
            |row| row.integer(0),
        )
        .expect("count main tables");
        assert_eq!(main_tables, Some(0));
    }

    #[test]
    fn failed_initialization_rolls_back_new_metadata() {
        let mut sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        Statement::execute_batch(
            &sqlite,
            "CREATE TEMP TABLE cov_conn_attached (sentinel INTEGER) STRICT",
        )
        .expect("reserve connection name");

        assert!(matches!(
            initialize(&mut sqlite),
            Err(ConnectionError::Initialize { .. })
        ));

        let catalog_exists = sql::query_row(
            &sqlite,
            "SELECT count(*) FROM temp.sqlite_schema
                 WHERE type = 'table' AND name = 'cov_conn_catalog'",
            &[],
            |row| row.integer(0),
        )
        .expect("inspect rolled-back schema");
        assert_eq!(catalog_exists, Some(0));

        let sentinel_exists = sql::query_row(
            &sqlite,
            "SELECT count(*) FROM temp.sqlite_schema
                 WHERE type = 'table' AND name = 'cov_conn_attached'",
            &[],
            |row| row.integer(0),
        )
        .expect("inspect pre-existing schema");
        assert_eq!(sentinel_exists, Some(1));
    }

    #[test]
    fn existing_connection_catalog_is_rejected() {
        let mut sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        Statement::execute_batch(
            &sqlite,
            "CREATE TEMP TABLE cov_conn_catalog (sentinel INTEGER) STRICT",
        )
        .expect("reserve catalog name");

        assert!(matches!(
            initialize(&mut sqlite),
            Err(ConnectionError::Initialize { .. })
        ));

        let columns = sql::query_row(
            &sqlite,
            "SELECT count(*) FROM temp.pragma_table_info('cov_conn_catalog')",
            &[],
            |row| row.integer(0),
        )
        .expect("inspect pre-existing catalog");
        assert_eq!(columns, Some(1));
    }

    #[test]
    fn exposes_underlying_connection() {
        let mut connection = Connection::open_in_memory().expect("initialize Neutron");
        Statement::execute_batch(
            connection.sqlite_mut(),
            "CREATE TABLE application_data (value TEXT)",
        )
        .expect("write through escape hatch");

        let sqlite = connection.into_sqlite();
        let exists = sql::query_row(
            &sqlite,
            "SELECT count(*) FROM main.sqlite_schema
                 WHERE type = 'table' AND name = 'application_data'",
            &[],
            |row| row.integer(0),
        )
        .expect("inspect raw connection");
        assert_eq!(exists, Some(1));
    }
}
