use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

const CREATE_CONNECTION_CATALOG_SQL: &str = include_str!("../sql/create_connection_catalog.sql");
const CREATE_VFS_INSTANCES_SQL: &str = include_str!("../sql/create_vfs_instances.sql");
const CREATE_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/create_attached_databases.sql");
const REGISTER_TABLE_SQL: &str = include_str!("../sql/register_table.sql");
const REGISTER_VFS_INSTANCE_SQL: &str = include_str!("../sql/register_vfs_instance.sql");
const REGISTER_ATTACHED_DATABASE_SQL: &str = include_str!("../sql/register_attached_database.sql");
const LIST_ATTACHED_DATABASES_SQL: &str = include_str!("../sql/list_attached_databases.sql");
const DATABASE_IS_EXCLUSIVE_SQL: &str = include_str!("../sql/database_is_exclusive.sql");
const DATABASE_ROLE_SQL: &str = include_str!("../sql/database_role.sql");
const DATABASE_VFS_SQL: &str = include_str!("../sql/database_vfs.sql");
const MAIN_DATABASE_ID_SQL: &str = include_str!("../sql/main_database_id.sql");

/// Physical name of Neutron's connection catalog in `temp`.
pub const CONNECTION_CATALOG: &str = "cov_conn_catalog";

/// Physical name of Neutron's registered-database table in `temp`.
pub const ATTACHED_DATABASES: &str = "cov_conn_attached";

/// Physical name of Neutron's connection-local VFS registry in `temp`.
pub const VFS_INSTANCES: &str = "cov_conn_vfs";

/// Uninterpreted symbol assigned to the connection catalog.
pub const CONNECTION_CATALOG_INTERPRETATION: &str = "cov.conn.catalog/v0";

/// Uninterpreted symbol assigned to the attached-database registry.
pub const ATTACHED_DATABASES_INTERPRETATION: &str = "cov.conn.attached/v0";

/// Uninterpreted symbol assigned to the VFS-instance registry.
pub const VFS_INSTANCES_INTERPRETATION: &str = "cov.conn.vfs/v0";

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

/// A connection-local use of a `SQLite` VFS.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VfsInstance {
    id: i64,
    name: Option<String>,
    is_readonly: bool,
}

impl VfsInstance {
    /// Returns the integer stored in `cov_conn_vfs`.
    #[must_use]
    pub const fn id(&self) -> i64 {
        self.id
    }

    /// Returns the explicitly selected VFS name.
    ///
    /// `None` means that `SQLite` selected its default VFS.
    #[must_use]
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// Returns whether this database use is read-only.
    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.is_readonly
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
        Self::from_sqlite_with_main_vfs(sqlite, None, false)
    }

    /// Opens a `SQLite` database using `vfs_name` and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened with the requested
    /// VFS or the connection metadata cannot be initialized atomically.
    pub fn open_with_vfs(path: impl AsRef<Path>, vfs_name: &str) -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_with_flags_and_vfs(
            path,
            sqlite::OpenFlags::default(),
            vfs_name,
        )
        .context(OpenSnafu)?;
        Self::from_sqlite_with_main_vfs(sqlite, Some(vfs_name), false)
    }

    /// Opens an in-memory `SQLite` database and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection metadata cannot be initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        Self::from_sqlite_with_main_vfs(sqlite, None, true)
    }

    /// Opens an in-memory database using `vfs_name` and initializes Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened with the requested
    /// VFS or the connection metadata cannot be initialized.
    pub fn open_in_memory_with_vfs(vfs_name: &str) -> Result<Self, ConnectionError> {
        let sqlite = sqlite::Connection::open_in_memory_with_flags_and_vfs(
            sqlite::OpenFlags::default(),
            vfs_name,
        )
        .context(OpenSnafu)?;
        Self::from_sqlite_with_main_vfs(sqlite, Some(vfs_name), true)
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
        initialize(&mut sqlite, false, None)?;
        Ok(Self { sqlite })
    }

    fn from_sqlite_with_main_vfs(
        mut sqlite: sqlite::Connection,
        main_vfs_name: Option<&str>,
        main_is_exclusive: bool,
    ) -> Result<Self, ConnectionError> {
        initialize(&mut sqlite, main_is_exclusive, main_vfs_name)?;
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
        self.attach_database(":memory:", schema_name, true, None)
    }

    /// Attaches and registers a new in-memory database using `vfs_name`.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database using the
    /// requested VFS or Neutron cannot record it.
    pub fn attach_in_memory_with_vfs(
        &mut self,
        schema_name: &str,
        vfs_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        self.attach_database(":memory:", schema_name, true, Some(vfs_name))
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
        self.attach_database(path, schema_name, false, None)
    }

    /// Attaches and registers a file-backed database using `vfs_name`.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database using the
    /// requested VFS or Neutron cannot record it.
    pub fn attach_file_with_vfs(
        &mut self,
        path: impl AsRef<Path>,
        schema_name: &str,
        vfs_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        let path = path
            .as_ref()
            .to_str()
            .ok_or_else(|| ConnectionError::NonUtf8Path {
                path: path.as_ref().to_path_buf(),
            })?;
        self.attach_database(path, schema_name, false, Some(vfs_name))
    }

    fn attach_database(
        &mut self,
        location: &str,
        schema_name: &str,
        is_exclusive: bool,
        vfs_name: Option<&str>,
    ) -> Result<DatabaseId, ConnectionError> {
        let attach_sql = format!("ATTACH DATABASE ?1 AS {}", quote_identifier(schema_name));
        let location_with_vfs = vfs_name.map(|vfs_name| sqlite_uri_with_vfs(location, vfs_name));
        self.sqlite
            .execute(
                &attach_sql,
                [location_with_vfs.as_deref().unwrap_or(location)],
            )
            .with_context(|_| AttachSnafu {
                schema_name: schema_name.to_owned(),
            })?;

        let registration = (|| -> sqlite::Result<DatabaseId> {
            let transaction = self.sqlite.transaction()?;
            let is_readonly = transaction.is_readonly(schema_name)?;
            let vfs_id = register_vfs_instance(&transaction, vfs_name, is_readonly)?;
            let database_id = register_attached_database(
                &transaction,
                schema_name,
                DatabaseRole::Auxiliary,
                is_exclusive,
                vfs_id,
            )?;
            transaction.commit()?;
            Ok(database_id)
        })();
        match registration {
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

    /// Returns the connection-local VFS instance used by a database.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_vfs(&self, database_id: DatabaseId) -> Result<VfsInstance, ConnectionError> {
        self.sqlite
            .query_row(DATABASE_VFS_SQL, [database_id.get()], |row| {
                Ok(VfsInstance {
                    id: row.get(0)?,
                    name: row.get(1)?,
                    is_readonly: row.get(2)?,
                })
            })
            .with_context(|_| QueryDatabaseSnafu {
                database_id: database_id.get(),
            })
    }

    /// Returns the connection's primary database identity.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn main_database_id(&self) -> Result<DatabaseId, ConnectionError> {
        self.sqlite
            .query_row(MAIN_DATABASE_ID_SQL, (), |row| {
                row.get::<_, i64>(0).map(DatabaseId)
            })
            .with_context(|_| QueryMainDatabaseSnafu)
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

    /// Connection metadata for the main database could not be queried.
    #[snafu(display("could not query the connection's main database: {source}"))]
    QueryMainDatabase {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}

fn initialize(
    connection: &mut sqlite::Connection,
    main_is_exclusive: bool,
    main_vfs_name: Option<&str>,
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
        3,
        VFS_INSTANCES,
        VFS_INSTANCES_INTERPRETATION,
        CREATE_VFS_INSTANCES_SQL,
    )?;

    create_and_register_table(
        &transaction,
        2,
        ATTACHED_DATABASES,
        ATTACHED_DATABASES_INTERPRETATION,
        CREATE_ATTACHED_DATABASES_SQL,
    )?;

    register_visible_databases(&transaction, main_is_exclusive, main_vfs_name)?;

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
    vfs_id: i64,
) -> sqlite::Result<DatabaseId> {
    connection.execute(
        REGISTER_ATTACHED_DATABASE_SQL,
        (sqlite_name, role.as_str(), is_exclusive, vfs_id),
    )?;
    Ok(DatabaseId(connection.last_insert_rowid()))
}

fn register_vfs_instance(
    connection: &sqlite::Connection,
    vfs_name: Option<&str>,
    is_readonly: bool,
) -> sqlite::Result<i64> {
    connection.execute(REGISTER_VFS_INSTANCE_SQL, (vfs_name, is_readonly))?;
    Ok(connection.last_insert_rowid())
}

fn register_visible_databases(
    transaction: &sqlite::Transaction<'_>,
    main_is_exclusive: bool,
    main_vfs_name: Option<&str>,
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
        let vfs_name = (role == DatabaseRole::Main)
            .then_some(main_vfs_name)
            .flatten();
        let is_readonly = transaction
            .is_readonly(sqlite_name.as_str())
            .context(InitializeSnafu)?;
        let vfs_id =
            register_vfs_instance(transaction, vfs_name, is_readonly).context(InitializeSnafu)?;
        register_attached_database(transaction, &sqlite_name, role, is_exclusive, vfs_id)
            .context(InitializeSnafu)?;
    }
    Ok(())
}

fn sqlite_uri_with_vfs(location: &str, vfs_name: &str) -> String {
    let location = if location == ":memory:" {
        String::from(":memory:")
    } else {
        percent_encode_uri_component(location, true)
    };
    format!(
        "file:{location}?vfs={}",
        percent_encode_uri_component(vfs_name, false)
    )
}

fn percent_encode_uri_component(value: &str, preserve_slash: bool) -> String {
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric()
            || matches!(byte, b'-' | b'.' | b'_' | b'~')
            || (preserve_slash && byte == b'/')
            || (preserve_slash && byte == b':')
        {
            encoded.push(char::from(byte));
        } else {
            use std::fmt::Write;
            write!(encoded, "%{byte:02X}").expect("writing to a String cannot fail");
        }
    }
    encoded
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::{
        ATTACHED_DATABASES, CONNECTION_CATALOG, Connection, ConnectionError, VFS_INSTANCES,
        initialize,
    };
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
                (
                    3,
                    String::from(VFS_INSTANCES),
                    String::from("cov.conn.vfs/v0")
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

        let vfs_instances = connection
            .sqlite()
            .prepare(
                "SELECT vfs_name, is_readonly
                 FROM temp.cov_conn_vfs
                 ORDER BY vfs_id",
            )
            .expect("prepare VFS query")
            .query_map((), |row| {
                Ok((row.get::<_, Option<String>>(0)?, row.get::<_, bool>(1)?))
            })
            .expect("query VFS instances")
            .collect::<sqlite::Result<Vec<_>>>()
            .expect("read VFS instances");
        assert_eq!(vfs_instances, [(None, false), (None, false)]);
    }

    #[cfg(unix)]
    #[test]
    fn records_explicit_vfs_for_main_and_attached_databases() {
        let mut connection =
            Connection::open_in_memory_with_vfs("unix").expect("open main through unix VFS");
        let main_id = connection.main_database_id().expect("find main database");
        let main_vfs = connection.database_vfs(main_id).expect("query main VFS");
        assert_eq!(main_vfs.name(), Some("unix"));
        assert!(!main_vfs.is_readonly());

        let attached_id = connection
            .attach_in_memory_with_vfs("scratch", "unix")
            .expect("attach through unix VFS");
        let attached_vfs = connection
            .database_vfs(attached_id)
            .expect("query attached VFS");
        assert_eq!(attached_vfs.name(), Some("unix"));
        assert!(!attached_vfs.is_readonly());
        assert_ne!(main_vfs.id(), attached_vfs.id());
    }

    #[test]
    fn records_readonly_state_from_sqlite() {
        let suffix = NEXT_DATABASE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "nucleus-neutron-readonly-{}-{suffix}.sqlite",
            std::process::id()
        ));
        drop(sqlite::Connection::open(&path).expect("create SQLite database"));

        let sqlite = sqlite::Connection::open_with_flags(
            &path,
            sqlite::OpenFlags::SQLITE_OPEN_READ_ONLY
                | sqlite::OpenFlags::SQLITE_OPEN_NO_MUTEX
                | sqlite::OpenFlags::SQLITE_OPEN_URI,
        )
        .expect("open read-only SQLite database");
        let connection = Connection::from_sqlite(sqlite).expect("initialize Neutron");
        let main_id = connection.main_database_id().expect("find main database");
        assert!(
            connection
                .database_vfs(main_id)
                .expect("query main VFS")
                .is_readonly()
        );

        drop(connection);
        std::fs::remove_file(path).expect("remove test database");
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
            initialize(&mut sqlite, false, None),
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
            initialize(&mut sqlite, false, None),
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
