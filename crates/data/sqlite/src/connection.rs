use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::sql::{self, Param, Transaction};

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");

/// Physical name of the connection catalog in `temp`.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of the registered-database table in `temp`.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Uninterpreted symbol assigned to the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Uninterpreted symbol assigned to the attached-database registry.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

/// A permeable `SQLite` connection with connection-local metadata.
///
/// This type makes no claim that the database is valid Nucleus state. Direct
/// access to the underlying connection is intentional.
#[derive(Debug)]
pub struct Connection {
    sqlite: sqlite::Connection,
}

impl Connection {
    /// Opens a `SQLite` database and initializes its connection metadata.
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

    /// Opens an in-memory `SQLite` database and initializes its metadata.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        Self::from_sqlite(sqlite)
    }

    /// Adopts a raw connection and initializes temporary metadata.
    ///
    /// Initialization is transactional. Existing objects using the layer's
    /// reserved connection names cause initialization to fail.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn from_sqlite(sqlite: sqlite::Connection) -> Result<Self, ConnectionError> {
        let connection = Self { sqlite };
        connection.initialize()?;
        Ok(connection)
    }

    /// Borrows the underlying `SQLite` connection.
    ///
    /// Crate-private: `lib/sqlite` is an implementation detail of this layer,
    /// and everything callers need is a method on [`Connection`]. Widen it if
    /// something outside genuinely needs the handle.
    #[must_use]
    pub(crate) const fn sqlite(&self) -> &sqlite::Connection {
        &self.sqlite
    }

    /// Consumes the wrapper and returns the underlying connection.
    #[must_use]
    pub fn into_sqlite(self) -> sqlite::Connection {
        self.sqlite
    }
}

/// Failure to open or initialize a data-layer `SQLite` connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// The raw `SQLite` connection could not be opened.
    #[snafu(display("could not open SQLite connection: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The connection-local schema could not be initialized.
    #[snafu(display("could not initialize SQLite connection metadata: {source}"))]
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

impl Connection {
    /// Installs connection-local metadata.
    ///
    /// Transactional: a connection which already holds objects under the
    /// reserved names leaves nothing behind when this fails.
    fn initialize(&self) -> Result<(), ConnectionError> {
        let transaction = Transaction::begin(self).context(InitializeSnafu)?;

        transaction
            .connection()
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

        register_attached_database(&transaction, 1, "main")?;

        transaction.commit().context(InitializeSnafu)
    }
}

fn create_and_register_table(
    transaction: &Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
    create_sql: &str,
) -> Result<(), ConnectionError> {
    transaction
        .connection()
        .execute_batch(create_sql)
        .context(InitializeSnafu)?;
    register_table(transaction, table_id, table_name, interpretation)
}

fn register_table(
    transaction: &Transaction<'_>,
    table_id: i64,
    table_name: &str,
    interpretation: &str,
) -> Result<(), ConnectionError> {
    transaction
        .connection()
        .execute(
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
    transaction
        .connection()
        .execute(
            REGISTER_ATTACHED_DATABASE_SQL,
            &[Param::Integer(database_id), Param::Text(schema_name)],
        )
        .context(InitializeSnafu)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use covalence_lib_sqlite::{Statement, Step};

    use super::{ATTACHED_DATABASES, CONNECTION_CATALOG, Connection, ConnectionError};
    use covalence_lib_sqlite as sqlite;

    #[test]
    fn initializes_catalog_and_main_registration() {
        let connection = Connection::open_in_memory().expect("initialize metadata");

        let catalog = connection
            .query_all(
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

        let attached = connection
            .query_row(
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
        let connection = Connection::open_in_memory().expect("initialize metadata");
        let main_tables = connection
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema WHERE type = 'table'",
                &[],
                |row| row.integer(0),
            )
            .expect("count main tables");
        assert_eq!(main_tables, Some(0));
    }

    #[test]
    fn failed_initialization_rolls_back_new_metadata() {
        // The metadata lives in `temp`, which is connection-local, so this has
        // to inspect the same connection that failed. Wrapping without
        // initializing is how it keeps hold of it.
        let connection = Connection {
            sqlite: sqlite::Connection::open_in_memory().expect("open SQLite"),
        };
        connection
            .execute_batch("CREATE TEMP TABLE cov_conn_attached (sentinel INTEGER) STRICT")
            .expect("reserve connection name");

        assert!(matches!(
            connection.initialize(),
            Err(ConnectionError::Initialize { .. })
        ));

        let catalog_exists = connection
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema
                 WHERE type = 'table' AND name = 'cov_conn_catalog'",
                &[],
                |row| row.integer(0),
            )
            .expect("inspect rolled-back schema");
        assert_eq!(catalog_exists, Some(0));

        let sentinel_exists = connection
            .query_row(
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
        let connection = Connection {
            sqlite: sqlite::Connection::open_in_memory().expect("open SQLite"),
        };
        connection
            .execute_batch("CREATE TEMP TABLE cov_conn_catalog (sentinel INTEGER) STRICT")
            .expect("reserve catalog name");

        assert!(matches!(
            connection.initialize(),
            Err(ConnectionError::Initialize { .. })
        ));

        let columns = connection
            .query_row(
                "SELECT count(*) FROM temp.pragma_table_info('cov_conn_catalog')",
                &[],
                |row| row.integer(0),
            )
            .expect("inspect pre-existing catalog");
        assert_eq!(columns, Some(1));
    }

    #[test]
    fn exposes_underlying_connection() {
        let connection = Connection::open_in_memory().expect("initialize metadata");
        connection
            .execute_batch("CREATE TABLE application_data (value TEXT)")
            .expect("write through the wrapper");

        // The escape hatch still hands back the raw connection, with the
        // table this wrote still on it.
        let sqlite = connection.into_sqlite();
        let mut statement = Statement::prepare(
            &sqlite,
            "SELECT count(*) FROM main.sqlite_schema
             WHERE type = 'table' AND name = 'application_data'",
        )
        .expect("compile");
        assert_eq!(statement.step().expect("step"), Step::Row);
        assert_eq!(statement.column(0).as_integer(), Some(1));
    }
}
