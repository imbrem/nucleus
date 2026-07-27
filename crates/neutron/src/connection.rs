use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");
const LIST_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/list_attached_databases.sql");
const DATABASE_IS_EXCLUSIVE_SQL: &str = include_str!("../sql/database_is_exclusive.sql");
const DATABASE_ROLE_SQL: &str = include_str!("../sql/database_role.sql");

/// Physical name of Neutron's connection catalog in `temp`.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of Neutron's registered-database table in `temp`.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Uninterpreted symbol assigned to the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Uninterpreted symbol assigned to the attached-database registry.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

/// Connection-local identity of a database registered with Neutron.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DatabaseId(i64);

impl DatabaseId {
    /// Returns the integer stored in `cov_conn_attached`.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// A database's role within its `SQLite` connection.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DatabaseRole {
    /// The connection's primary database.
    Main,
    /// Any other database, including `temp` and attached databases.
    Auxiliary,
}

impl DatabaseRole {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Main => "main",
            Self::Auxiliary => "aux",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "main" => Some(Self::Main),
            "aux" => Some(Self::Auxiliary),
            _ => None,
        }
    }
}

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
        Self::from_sqlite(sqlite)
    }

    /// Opens an in-memory `SQLite` database and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        let mut sqlite = sqlite;
        initialize(&mut sqlite, true)?;
        Ok(Self { sqlite })
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
        initialize(&mut sqlite, false)?;
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

    /// Attaches and registers a new in-memory database.
    ///
    /// `schema_name` is `SQLite`'s connection-local name for addressing the
    /// attachment, not a persistent database identity.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database or Neutron cannot
    /// record it in the connection metadata.
    pub fn attach_in_memory(&mut self, schema_name: &str) -> Result<DatabaseId, ConnectionError> {
        self.attach_database(":memory:", schema_name, true)
    }

    /// Attaches and registers a file-backed database.
    ///
    /// `schema_name` is `SQLite`'s connection-local name for addressing the
    /// attachment, not a persistent database identity.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database or Neutron cannot
    /// record it in the connection metadata.
    pub fn attach_file(
        &mut self,
        path: impl AsRef<Path>,
        schema_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        let path = path
            .as_ref()
            .to_str()
            .ok_or_else(|| ConnectionError::NonUtf8Path {
                path: path.as_ref().to_path_buf(),
            })?;
        self.attach_database(path, schema_name, false)
    }

    fn attach_database(
        &mut self,
        location: &str,
        schema_name: &str,
        is_exclusive: bool,
    ) -> Result<DatabaseId, ConnectionError> {
        let attach_sql = format!("ATTACH DATABASE ?1 AS {}", quote_identifier(schema_name));
        self.sqlite
            .execute(&attach_sql, [location])
            .with_context(|_| AttachSnafu {
                schema_name: schema_name.to_owned(),
            })?;

        match register_attached_database(
            &self.sqlite,
            schema_name,
            DatabaseRole::Auxiliary,
            is_exclusive,
        ) {
            Ok(database_id) => Ok(database_id),
            Err(source) => {
                let detach_sql = format!("DETACH DATABASE {}", quote_identifier(schema_name));
                let rollback_error = self.sqlite.execute(&detach_sql, ()).err().map(Box::new);
                Err(ConnectionError::RegisterAttached {
                    schema_name: schema_name.to_owned(),
                    source,
                    rollback_error,
                })
            }
        }
    }

    /// Returns whether a registered database is known to be connection-exclusive.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_is_exclusive(&self, database_id: DatabaseId) -> Result<bool, ConnectionError> {
        self.sqlite
            .query_row(DATABASE_IS_EXCLUSIVE_SQL, [database_id.get()], |row| {
                row.get::<_, bool>(0)
            })
            .with_context(|_| QueryDatabaseSnafu {
                database_id: database_id.get(),
            })
    }

    /// Returns the database's connection-local role.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried or contains
    /// an invalid role.
    pub fn database_role(&self, database_id: DatabaseId) -> Result<DatabaseRole, ConnectionError> {
        let role = self
            .sqlite
            .query_row(DATABASE_ROLE_SQL, [database_id.get()], |row| {
                row.get::<_, String>(0)
            })
            .with_context(|_| QueryDatabaseSnafu {
                database_id: database_id.get(),
            })?;
        DatabaseRole::parse(&role).ok_or(ConnectionError::InvalidDatabaseRole {
            database_id: database_id.get(),
            role,
        })
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

    /// A path could not be represented for `SQLite`'s UTF-8 SQL interface.
    #[snafu(display("database path is not valid UTF-8: {}", path.display()))]
    NonUtf8Path {
        /// Rejected path.
        path: std::path::PathBuf,
    },

    /// `SQLite` could not attach a database.
    #[snafu(display("could not attach SQLite database as `{schema_name}`: {source}"))]
    Attach {
        /// Requested schema name.
        schema_name: String,
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The attachment succeeded but its Neutron registration failed.
    #[snafu(display(
        "could not register attached database `{schema_name}`: {source}; detach result: {rollback_error:?}"
    ))]
    RegisterAttached {
        /// Requested schema name.
        schema_name: String,
        /// Registration failure.
        source: sqlite::Error,
        /// Failure while compensating with `DETACH`, if any.
        rollback_error: Option<Box<sqlite::Error>>,
    },

    /// Connection metadata for a database could not be queried.
    #[snafu(display("could not query connection database {database_id}: {source}"))]
    QueryDatabase {
        /// Connection-local database identity.
        database_id: i64,
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// Connection metadata contained an unknown database role.
    #[snafu(display("connection database {database_id} has invalid role `{role}`"))]
    InvalidDatabaseRole {
        /// Connection-local database identity.
        database_id: i64,
        /// Invalid stored role.
        role: String,
    },
}

fn initialize(
    connection: &mut sqlite::Connection,
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

    register_visible_databases(&transaction, main_is_exclusive)?;

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
    connection: &sqlite::Connection,
    sqlite_name: &str,
    role: DatabaseRole,
    is_exclusive: bool,
) -> sqlite::Result<DatabaseId> {
    connection.execute(
        REGISTER_ATTACHED_DATABASE_SQL,
        (sqlite_name, role.as_str(), is_exclusive),
    )?;
    Ok(DatabaseId(connection.last_insert_rowid()))
}

fn register_visible_databases(
    transaction: &sqlite::Transaction<'_>,
    main_is_exclusive: bool,
) -> Result<(), ConnectionError> {
    let databases = {
        let mut statement = transaction
            .prepare(LIST_ATTACHED_DATABASES_SQL)
            .context(InitializeSnafu)?;
        statement
            .query_map((), |row| row.get::<_, String>(0))
            .context(InitializeSnafu)?
            .collect::<sqlite::Result<Vec<_>>>()
            .context(InitializeSnafu)?
    };

    for sqlite_name in databases {
        let role = if sqlite_name == "main" {
            DatabaseRole::Main
        } else {
            DatabaseRole::Auxiliary
        };
        let is_exclusive =
            sqlite_name == "temp" || (role == DatabaseRole::Main && main_is_exclusive);
        register_attached_database(transaction, &sqlite_name, role, is_exclusive)
            .context(InitializeSnafu)?;
    }
    Ok(())
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::{ATTACHED_DATABASES, CONNECTION_CATALOG, Connection, ConnectionError, initialize};
    use covalence_lib_sqlite as sqlite;

    static NEXT_DATABASE: AtomicU64 = AtomicU64::new(0);

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
            ]
        );

        let attached = connection
            .sqlite()
            .prepare(
                "SELECT sqlite_name, database_role, is_exclusive
                 FROM temp.cov_conn_attached
                 ORDER BY database_id",
            )
            .expect("prepare attached database query")
            .query_map((), |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, bool>(2)?,
                ))
            })
            .expect("query attached databases")
            .collect::<sqlite::Result<Vec<_>>>()
            .expect("read attached databases");
        assert_eq!(
            attached,
            [
                (String::from("main"), String::from("main"), true),
                (String::from("temp"), String::from("aux"), true),
            ]
        );
    }

    #[test]
    fn imports_databases_attached_before_neutron_initialization() {
        let sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        sqlite
            .execute("ATTACH DATABASE ':memory:' AS preexisting", ())
            .expect("attach raw database");

        let connection = Connection::from_sqlite(sqlite).expect("initialize Neutron");
        let registered = connection
            .sqlite()
            .query_row(
                "SELECT database_role, is_exclusive FROM temp.cov_conn_attached
                 WHERE sqlite_name = 'preexisting'",
                (),
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, bool>(1)?)),
            )
            .expect("read imported database");
        assert_eq!(registered, (String::from("aux"), false));
    }

    #[test]
    fn attach_in_memory_registers_role_and_exclusivity() {
        let mut connection = Connection::open_in_memory().expect("initialize Neutron");
        let id = connection
            .attach_in_memory("working set")
            .expect("attach in-memory database");

        let registered = connection
            .sqlite()
            .query_row(
                "SELECT sqlite_name, database_role
                 FROM temp.cov_conn_attached
                 WHERE database_id = ?1",
                [id.get()],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)),
            )
            .expect("read registered database");
        assert_eq!(
            registered,
            (String::from("working set"), String::from("aux"))
        );
        assert!(
            connection
                .database_is_exclusive(id)
                .expect("query exclusivity")
        );
        assert_eq!(
            connection.database_role(id).expect("query role"),
            super::DatabaseRole::Auxiliary
        );

        connection
            .sqlite()
            .query_row(
                "SELECT 1 FROM pragma_database_list WHERE name = 'working set'",
                (),
                |_| Ok(()),
            )
            .expect("database is visible to SQLite");
    }

    #[test]
    fn attach_file_registers_role_and_exclusivity() {
        let suffix = NEXT_DATABASE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "nucleus-neutron-{}-{suffix}.sqlite",
            std::process::id()
        ));

        let mut connection = Connection::open_in_memory().expect("initialize Neutron");
        let id = connection
            .attach_file(&path, "persistent")
            .expect("attach file database");

        let role = connection
            .sqlite()
            .query_row(
                "SELECT database_role FROM temp.cov_conn_attached
                 WHERE database_id = ?1",
                [id.get()],
                |row| row.get::<_, String>(0),
            )
            .expect("read registered database");
        assert_eq!(role, "aux");
        assert!(
            !connection
                .database_is_exclusive(id)
                .expect("query exclusivity")
        );

        drop(connection);
        std::fs::remove_file(path).expect("remove test database");
    }

    #[test]
    fn failed_registration_compensates_by_detaching() {
        let mut connection = Connection::open_in_memory().expect("initialize Neutron");
        connection
            .sqlite_mut()
            .execute("DROP TABLE temp.cov_conn_attached", ())
            .expect("break permeable Neutron metadata");

        assert!(matches!(
            connection.attach_in_memory("orphan"),
            Err(ConnectionError::RegisterAttached {
                rollback_error: None,
                ..
            })
        ));

        let visible = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM pragma_database_list WHERE name = 'orphan'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect SQLite database list");
        assert_eq!(visible, 0);
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
            initialize(&mut sqlite, false),
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
            initialize(&mut sqlite, false),
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
