use std::marker::PhantomData;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{RegistryInvariant, RegistrySession};

const ACQUIRE_SHARED_DATABASE_SQL: &str =
    include_str!("../sql/session/acquire_shared_database.sql");
const ACQUIRE_EXCLUSIVE_DATABASE_SQL: &str =
    include_str!("../sql/session/acquire_exclusive_database.sql");
const ACQUIRE_SHARED_TABLE_SQL: &str = include_str!("../sql/session/acquire_shared_table.sql");
const ACQUIRE_EXCLUSIVE_TABLE_SQL: &str =
    include_str!("../sql/session/acquire_exclusive_table.sql");
const RELEASE_DATABASE_SQL: &str = include_str!("../sql/session/release_database.sql");
const DECREMENT_DATABASE_SQL: &str = include_str!("../sql/session/decrement_database.sql");
const RELEASE_TABLE_SQL: &str = include_str!("../sql/session/release_table.sql");
const DECREMENT_TABLE_SQL: &str = include_str!("../sql/session/decrement_table.sql");
const DATABASE_EXISTS_SQL: &str = include_str!("../sql/session/database_exists.sql");
const TABLE_EXISTS_SQL: &str = include_str!("../sql/session/table_exists.sql");

mod private {
    pub trait Sealed {}
}

/// A shared visibility lease.
#[derive(Clone, Copy, Debug)]
pub struct Shared;

/// An exclusive visibility lease.
#[derive(Clone, Copy, Debug)]
pub struct Exclusive;

impl private::Sealed for Shared {}
impl private::Sealed for Exclusive {}

/// The lock mode carried by a database or table handle.
pub trait LockMode: private::Sealed {}

impl LockMode for Shared {}
impl LockMode for Exclusive {}

/// A visibility capability for one attached database.
#[derive(Debug)]
pub struct Database<'session, I: RegistryInvariant, K: LockMode> {
    session: &'session RegistrySession<'session, I>,
    name: String,
    _lease: DatabaseLease<'session>,
    mode: PhantomData<K>,
}

impl<I: RegistryInvariant, K: LockMode> Database<'_, I, K> {
    /// Returns the `SQLite` schema name of this database.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn sqlite(&self) -> &sqlite::Connection {
        self.session.connection.sqlite()
    }

    /// Acquires a shared handle to a table in this database.
    ///
    /// # Errors
    ///
    /// Returns an error if the table does not exist or is exclusively owned.
    pub fn shared_table(
        &self,
        name: impl Into<String>,
    ) -> Result<Table<'_, I, Shared>, HandleError> {
        self.table(name.into(), None)
    }

    fn table<T: LockMode>(
        &self,
        name: String,
        owner: Option<&'static str>,
    ) -> Result<Table<'_, I, T>, HandleError> {
        require_table(self.session.connection.sqlite(), &self.name, &name)?;
        let lease =
            TableLease::acquire(self.session.connection.sqlite(), &self.name, &name, owner)?;
        Ok(Table {
            session: self.session,
            database: self.name.clone(),
            name,
            _lease: lease,
            mode: PhantomData,
        })
    }
}

impl<I: RegistryInvariant> Database<'_, I, Exclusive> {
    /// Acquires an exclusive handle to a table in this database.
    ///
    /// # Errors
    ///
    /// Returns an error if the table does not exist or is already visible.
    pub fn exclusive_table(
        &self,
        name: impl Into<String>,
    ) -> Result<Table<'_, I, Exclusive>, HandleError> {
        self.table(name.into(), Some("covalence_nucleus::Table<Exclusive>"))
    }
}

/// A visibility capability for one table.
#[derive(Debug)]
pub struct Table<'database, I: RegistryInvariant, K: LockMode> {
    session: &'database RegistrySession<'database, I>,
    database: String,
    name: String,
    _lease: TableLease<'database>,
    mode: PhantomData<K>,
}

impl<'database, I: RegistryInvariant, K: LockMode> Table<'database, I, K> {
    /// Returns the physical database name.
    #[must_use]
    pub fn database_name(&self) -> &str {
        &self.database
    }

    /// Returns the physical table name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn sqlite(&self) -> &'database sqlite::Connection {
        self.session.connection.sqlite()
    }
}

impl<I: RegistryInvariant> RegistrySession<'_, I> {
    /// Acquires a shared database handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the database does not exist or is exclusively owned.
    pub fn shared_database(
        &self,
        name: impl Into<String>,
    ) -> Result<Database<'_, I, Shared>, HandleError> {
        self.database(name.into(), None)
    }

    /// Acquires an exclusive database handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the database does not exist or is already visible.
    pub fn exclusive_database(
        &self,
        name: impl Into<String>,
    ) -> Result<Database<'_, I, Exclusive>, HandleError> {
        self.database(name.into(), Some("covalence_nucleus::Database<Exclusive>"))
    }

    fn database<K: LockMode>(
        &self,
        name: String,
        owner: Option<&'static str>,
    ) -> Result<Database<'_, I, K>, HandleError> {
        require_database(self.connection.sqlite(), &name)?;
        let lease = DatabaseLease::acquire(self.connection.sqlite(), &name, owner)?;
        Ok(Database {
            session: self,
            name,
            _lease: lease,
            mode: PhantomData,
        })
    }
}

#[derive(Debug)]
struct DatabaseLease<'connection> {
    connection: &'connection sqlite::Connection,
    name: String,
}

impl<'connection> DatabaseLease<'connection> {
    fn acquire(
        connection: &'connection sqlite::Connection,
        name: &str,
        owner: Option<&'static str>,
    ) -> Result<Self, HandleError> {
        let result = match owner {
            Some(owner) => {
                connection.query_row(ACQUIRE_EXCLUSIVE_DATABASE_SQL, (name, owner), |row| {
                    row.get::<_, i64>(0)
                })
            }
            None => connection.query_row(ACQUIRE_SHARED_DATABASE_SQL, [name], |row| {
                row.get::<_, i64>(0)
            }),
        };
        result.map_err(lock_error)?;
        Ok(Self {
            connection,
            name: name.to_owned(),
        })
    }
}

impl Drop for DatabaseLease<'_> {
    fn drop(&mut self) {
        let removed = self
            .connection
            .execute(RELEASE_DATABASE_SQL, [&self.name])
            .expect("a live database lease remains registered");
        if removed == 0 {
            assert_eq!(
                self.connection
                    .execute(DECREMENT_DATABASE_SQL, [&self.name])
                    .expect("a live shared database lease remains registered"),
                1,
                "a live shared database lease remains registered"
            );
        }
    }
}

#[derive(Debug)]
struct TableLease<'connection> {
    connection: &'connection sqlite::Connection,
    database: String,
    table: String,
}

impl<'connection> TableLease<'connection> {
    fn acquire(
        connection: &'connection sqlite::Connection,
        database: &str,
        table: &str,
        owner: Option<&'static str>,
    ) -> Result<Self, HandleError> {
        let result = match owner {
            Some(owner) => connection.query_row(
                ACQUIRE_EXCLUSIVE_TABLE_SQL,
                (database, table, owner),
                |row| row.get::<_, i64>(0),
            ),
            None => connection.query_row(ACQUIRE_SHARED_TABLE_SQL, (database, table), |row| {
                row.get::<_, i64>(0)
            }),
        };
        result.map_err(lock_error)?;
        Ok(Self {
            connection,
            database: database.to_owned(),
            table: table.to_owned(),
        })
    }
}

impl Drop for TableLease<'_> {
    fn drop(&mut self) {
        let removed = self
            .connection
            .execute(RELEASE_TABLE_SQL, (&self.database, &self.table))
            .expect("a live table lease remains registered");
        if removed == 0 {
            assert_eq!(
                self.connection
                    .execute(DECREMENT_TABLE_SQL, (&self.database, &self.table))
                    .expect("a live shared table lease remains registered"),
                1,
                "a live shared table lease remains registered"
            );
        }
    }
}

fn require_database(connection: &sqlite::Connection, name: &str) -> Result<(), HandleError> {
    let exists = connection
        .query_row(DATABASE_EXISTS_SQL, [name], |row| row.get::<_, bool>(0))
        .context(StorageSnafu)?;
    if exists {
        Ok(())
    } else {
        Err(HandleError::UnknownDatabase {
            name: name.to_owned(),
        })
    }
}

fn require_table(
    connection: &sqlite::Connection,
    database: &str,
    table: &str,
) -> Result<(), HandleError> {
    let exists = connection
        .query_row(TABLE_EXISTS_SQL, (database, table), |row| {
            row.get::<_, bool>(0)
        })
        .context(StorageSnafu)?;
    if exists {
        Ok(())
    } else {
        Err(HandleError::UnknownTable {
            database: database.to_owned(),
            table: table.to_owned(),
        })
    }
}

fn lock_error(source: sqlite::Error) -> HandleError {
    if matches!(source, sqlite::Error::QueryReturnedNoRows) {
        HandleError::Conflict
    } else {
        HandleError::Storage { source }
    }
}

/// Failure to acquire a database or table capability.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HandleError {
    /// The requested database is not attached.
    #[snafu(display("database {name:?} is not attached"))]
    UnknownDatabase { name: String },

    /// The requested table does not exist.
    #[snafu(display("table {database:?}.{table:?} does not exist"))]
    UnknownTable { database: String, table: String },

    /// The requested lock is incompatible with an existing capability.
    #[snafu(display("the requested object is already held incompatibly"))]
    Conflict,

    /// Visibility state could not be accessed.
    #[snafu(display("could not update the visibility registry: {source}"))]
    Storage { source: sqlite::Error },
}

#[cfg(test)]
mod tests {
    use crate::{Connection, Registry};

    #[test]
    fn registry_rows_record_counts_modes_and_exclusive_owners() {
        let mut connection = Connection::open_in_memory().unwrap();
        let session = connection.enter(Registry).unwrap();
        let first = session.shared_database("main").unwrap();
        let second = session.shared_database("main").unwrap();

        let shared = session
            .connection
            .sqlite()
            .query_row(
                "SELECT lock_type, ref_count, owner_type
                 FROM temp.cov_conn_dbvis WHERE db_name = 'main'",
                (),
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, Option<String>>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(shared, (String::from("SHARED"), 2, None));

        drop(first);
        drop(second);
        let database = session.exclusive_database("main").unwrap();
        let owner = session
            .connection
            .sqlite()
            .query_row(
                "SELECT owner_type FROM temp.cov_conn_dbvis WHERE db_name = 'main'",
                (),
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(owner, "covalence_nucleus::Database<Exclusive>");

        let table = database.exclusive_table("cov_db_catalog").unwrap();
        let owner = session
            .connection
            .sqlite()
            .query_row(
                "SELECT owner_type FROM temp.cov_conn_tabvis
                 WHERE db_name = 'main' AND table_name = 'cov_db_catalog'",
                (),
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(owner, "covalence_nucleus::Table<Exclusive>");
        drop(table);
    }
}
