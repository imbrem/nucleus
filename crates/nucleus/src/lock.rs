use covalence_lib_error::snafu::Snafu;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

use crate::{
    BorrowedConnection, Cas, Connection, MutableConnectionCarrier, Reader, SessionProtocol,
    Standard, ViewProtocol,
};

const ACQUIRE_SHARED_DATABASE_SQL: &str = include_str!("../sql/lock/acquire_shared_database.sql");
const ACQUIRE_EXCLUSIVE_DATABASE_SQL: &str =
    include_str!("../sql/lock/acquire_exclusive_database.sql");
const ACQUIRE_SHARED_TABLE_SQL: &str = include_str!("../sql/lock/acquire_shared_table.sql");
const DATABASE_EXISTS_SQL: &str = include_str!("../sql/lock/database_exists.sql");
const DATABASE_IS_EXCLUSIVE_SQL: &str = include_str!("../sql/lock/database_is_exclusive.sql");
const TABLE_EXISTS_SQL: &str = include_str!("../sql/lock/table_exists.sql");

const DELETE_DATABASE_LOCK_SQL: &str =
    "DELETE FROM temp.cov_conn_db_lock WHERE db_name = ?1 AND ref_count = 1";
const DECREMENT_DATABASE_LOCK_SQL: &str = "
    UPDATE temp.cov_conn_db_lock
    SET ref_count = ref_count - 1
    WHERE db_name = ?1 AND mode = 'SHARED' AND ref_count > 1
";
const DELETE_TABLE_LOCK_SQL: &str = "
    DELETE FROM temp.cov_conn_tab_lock
    WHERE db_name = ?1 AND table_name = ?2 AND ref_count = 1
";
const DECREMENT_TABLE_LOCK_SQL: &str = "
    UPDATE temp.cov_conn_tab_lock
    SET ref_count = ref_count - 1
    WHERE db_name = ?1 AND table_name = ?2 AND ref_count > 1
";
const CLEAR_DATABASE_TABLE_LOCKS_SQL: &str =
    "DELETE FROM temp.cov_conn_tab_lock WHERE db_name = ?1";
const CLEAR_EXCLUSIVE_DATABASE_LOCK_SQL: &str = "
    DELETE FROM temp.cov_conn_db_lock
    WHERE db_name = ?1 AND mode = 'EXCLUSIVE'
";
const DATABASE_WRITE_UNLOCKED_SQL: &str = "
    SELECT NOT EXISTS (
        SELECT 1 FROM temp.cov_conn_db_lock WHERE db_name = ?1
    ) AND NOT EXISTS (
        SELECT 1 FROM temp.cov_conn_tab_lock WHERE db_name = ?1
    )
";
const COUNT_ALL_LOCKS_SQL: &str = "
    SELECT
        (SELECT count(*) FROM temp.cov_conn_db_lock) +
        (SELECT count(*) FROM temp.cov_conn_tab_lock)
";
const CLEAR_ALL_TABLE_LOCKS_SQL: &str = "DELETE FROM temp.cov_conn_tab_lock";
const CLEAR_ALL_DATABASE_LOCKS_SQL: &str = "DELETE FROM temp.cov_conn_db_lock";

/// Physical name of the connection-local database lock table.
pub const DATABASE_LOCKS: &str = "cov_conn_db_lock";

/// Physical name of the connection-local table lock table.
pub const TABLE_LOCKS: &str = "cov_conn_tab_lock";

/// Namespace for the standard logical lock protocol.
#[derive(Clone, Copy, Debug, Default)]
pub struct Lock;

impl Lock {
    /// Selects a database for a shared view or exclusive session.
    #[must_use]
    pub fn database(database: impl Into<String>) -> DatabaseLock {
        DatabaseLock {
            database: database.into(),
        }
    }
}

impl<C> SessionProtocol<C> for Lock
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    type Error = LockError;
    type Session = LockSession<C>;

    fn enter(self, carrier: C) -> Result<Self::Session, (LockError, C)> {
        if let Err(error) = require_empty_lock_registry(carrier.connection()) {
            return Err((error, carrier));
        }
        Ok(LockSession {
            carrier: Some(carrier),
        })
    }
}

/// Root cleanup boundary for the standard logical lock protocol.
///
/// Views and database sessions may deliberately retain child locks. Every such
/// lock is removed when this session ends. Forgetting the root session instead
/// leaves any retained rows in place, causing checked writes to fail closed.
#[derive(Debug)]
pub struct LockSession<C>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    carrier: Option<C>,
}

impl<C> LockSession<C>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    /// Returns the connection-local standard CAS.
    #[must_use]
    pub fn cas(&self) -> Cas<'_> {
        Cas::new(self.carrier().connection())
    }

    /// Creates a shared database view within this cleanup boundary.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot be locked.
    pub fn view(
        &mut self,
        database: DatabaseLock,
    ) -> Result<DatabaseView<BorrowedConnection<'_, Standard>>, LockError> {
        database
            .view(BorrowedConnection::new(self.carrier_mut().connection_mut()))
            .map_err(|(error, _)| error)
    }

    /// Creates an exclusive database session within this cleanup boundary.
    ///
    /// # Errors
    ///
    /// Returns an error if the database cannot be locked.
    pub fn session(
        &mut self,
        database: DatabaseLock,
    ) -> Result<DatabaseSession<BorrowedConnection<'_, Standard>>, LockError> {
        database
            .enter(BorrowedConnection::new(self.carrier_mut().connection_mut()))
            .map_err(|(error, _)| error)
    }

    /// Creates a reader spanning any attached database.
    #[must_use]
    pub fn database_reader(&mut self, database: impl Into<String>) -> Reader<'_> {
        Reader::database(self.carrier_mut().connection_mut(), database)
    }

    /// Creates a reader confined to any table in the connection.
    #[must_use]
    pub fn table_reader(
        &mut self,
        database: impl Into<String>,
        table: impl Into<String>,
    ) -> Reader<'_> {
        Reader::table(self.carrier_mut().connection_mut(), database, table)
    }

    /// Ends the lock protocol, clears all locks, and returns the carrier.
    ///
    /// # Errors
    ///
    /// Returns the error and carrier if cleanup fails. The connection is
    /// poisoned so later checked writes fail closed.
    pub fn finish(mut self) -> Result<C, (LockError, C)> {
        let result = clear_all_locks(self.carrier().connection());
        if result.is_err() {
            self.carrier().connection().poison();
        }
        let carrier = self.take_carrier();
        match result {
            Ok(()) => Ok(carrier),
            Err(error) => Err((error, carrier)),
        }
    }

    fn carrier(&self) -> &C {
        self.carrier.as_ref().expect("live lock session")
    }

    fn carrier_mut(&mut self) -> &mut C {
        self.carrier.as_mut().expect("live lock session")
    }

    fn take_carrier(&mut self) -> C {
        self.carrier.take().expect("live lock session")
    }
}

impl<C> Drop for LockSession<C>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    fn drop(&mut self) {
        if let Some(carrier) = self.carrier.as_ref()
            && clear_all_locks(carrier.connection()).is_err()
        {
            carrier.connection().poison();
        }
    }
}

/// A database selected for the lock protocol.
///
/// This descriptor independently implements [`ViewProtocol`] for a shared
/// database view and [`SessionProtocol`] for an exclusive database session.
#[derive(Clone, Debug)]
pub struct DatabaseLock {
    database: String,
}

impl<C> ViewProtocol<C> for DatabaseLock
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    type Error = LockError;
    type View = DatabaseView<C>;

    fn view(self, carrier: C) -> Result<Self::View, (LockError, C)> {
        if let Err(error) = acquire_database(carrier.connection(), &self.database, Mode::Shared) {
            return Err((error, carrier));
        }
        Ok(Database {
            carrier: Some(carrier),
            database: self.database,
        })
    }
}

impl<C> SessionProtocol<C> for DatabaseLock
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    type Error = LockError;
    type Session = DatabaseSession<C>;

    fn enter(self, carrier: C) -> Result<Self::Session, (LockError, C)> {
        if let Err(error) = acquire_database(carrier.connection(), &self.database, Mode::Exclusive)
        {
            return Err((error, carrier));
        }
        Ok(Database {
            carrier: Some(carrier),
            database: self.database,
        })
    }
}

/// A database protected from mutation by a shared logical lock.
pub type DatabaseView<C> = Database<C, false>;

/// Exclusive logical ownership of one attached database.
pub type DatabaseSession<C> = Database<C, true>;

/// A database held under the logical lock protocol.
#[derive(Debug)]
pub struct Database<C, const EXCLUSIVE: bool>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    carrier: Option<C>,
    database: String,
}

impl<C, const EXCLUSIVE: bool> Database<C, EXCLUSIVE>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    /// Returns the connection-local standard CAS.
    #[must_use]
    pub fn cas(&self) -> Cas<'_> {
        Cas::new(self.carrier().connection())
    }

    /// Returns the attached database name.
    #[must_use]
    pub fn database_name(&self) -> &str {
        &self.database
    }

    /// Creates a reader spanning this database.
    #[must_use]
    pub fn reader(&mut self) -> Reader<'_> {
        let database = self.database.clone();
        Reader::database(self.carrier_mut().connection_mut(), database)
    }

    /// Creates a reader spanning any attached database.
    #[must_use]
    pub fn database_reader(&mut self, database: impl Into<String>) -> Reader<'_> {
        Reader::database(self.carrier_mut().connection_mut(), database)
    }

    /// Creates a reader confined to any table in the connection.
    #[must_use]
    pub fn table_reader(
        &mut self,
        database: impl Into<String>,
        table: impl Into<String>,
    ) -> Reader<'_> {
        Reader::table(self.carrier_mut().connection_mut(), database, table)
    }

    /// Releases the database capability and returns the connection carrier.
    ///
    /// # Errors
    ///
    /// Returns the error and carrier if lock cleanup fails. The remaining lock
    /// row then keeps later writes fail-closed.
    pub fn finish(mut self) -> Result<C, (LockError, C)> {
        let result = self.release();
        if result.is_err() {
            self.carrier().connection().poison();
        }
        let carrier = self.take_carrier();
        match result {
            Ok(()) => Ok(carrier),
            Err(error) => Err((error, carrier)),
        }
    }

    fn carrier(&self) -> &C {
        self.carrier.as_ref().expect("live database capability")
    }

    fn carrier_mut(&mut self) -> &mut C {
        self.carrier.as_mut().expect("live database capability")
    }

    fn take_carrier(&mut self) -> C {
        self.carrier.take().expect("live database capability")
    }

    fn release(&self) -> Result<(), LockError> {
        if EXCLUSIVE {
            clear_database_session(self.carrier().connection(), &self.database)
        } else {
            release_database(self.carrier().connection(), &self.database)
        }
    }

    fn table_view<const LOCKED: bool>(&mut self, table: String) -> TableView<'_, LOCKED> {
        let database = self.database.clone();
        TableView {
            connection: self.carrier_mut().connection_mut(),
            database,
            table,
            release_on_drop: LOCKED,
        }
    }
}

impl<C, const EXCLUSIVE: bool> Drop for Database<C, EXCLUSIVE>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    fn drop(&mut self) {
        if let Some(carrier) = self.carrier.as_ref()
            && if EXCLUSIVE {
                clear_database_session(carrier.connection(), &self.database)
            } else {
                release_database(carrier.connection(), &self.database)
            }
            .is_err()
        {
            carrier.connection().poison();
        }
    }
}

impl<C> Database<C, false>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    /// Creates a table view whose immutability follows from the database lock.
    ///
    /// # Errors
    ///
    /// Returns an error if the table does not exist.
    pub fn table(&mut self, table: impl Into<String>) -> Result<TableView<'_, false>, LockError> {
        let table = table.into();
        require_table(self.carrier().connection(), &self.database, &table)?;
        Ok(self.table_view(table))
    }

    /// Leaves the shared lock registered and returns the connection carrier.
    #[must_use]
    pub fn retain_lock(mut self) -> C {
        self.take_carrier()
    }
}

impl<C> Database<C, true>
where
    C: MutableConnectionCarrier<Invariant = Standard>,
{
    /// Creates a shared table view nested under this exclusive session.
    ///
    /// # Errors
    ///
    /// Returns an error if the table does not exist or cannot be locked.
    pub fn table(&mut self, table: impl Into<String>) -> Result<TableView<'_, true>, LockError> {
        let table = table.into();
        require_table(self.carrier().connection(), &self.database, &table)?;
        acquire_table(self.carrier().connection(), &self.database, &table)?;
        Ok(self.table_view(table))
    }
}

/// A table view inheriting immutability from a shared database lock.
pub type InheritedTableView<'connection> = TableView<'connection, false>;

/// A table protected by a shared lock nested under an exclusive session.
#[derive(Debug)]
pub struct TableView<'connection, const LOCKED: bool> {
    connection: &'connection mut Connection<Standard>,
    database: String,
    table: String,
    release_on_drop: bool,
}

impl<const LOCKED: bool> TableView<'_, LOCKED> {
    /// Returns the connection-local standard CAS.
    #[must_use]
    pub fn cas(&self) -> Cas<'_> {
        Cas::new(self.connection)
    }

    /// Returns the containing database name.
    #[must_use]
    pub fn database_name(&self) -> &str {
        &self.database
    }

    /// Returns the table name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table
    }

    /// Creates a reader confined to this table.
    #[must_use]
    pub fn reader(&mut self) -> Reader<'_> {
        Reader::table(self.connection, self.database.clone(), self.table.clone())
    }
}

impl TableView<'_, true> {
    /// Releases this table lock and reports cleanup failure.
    ///
    /// # Errors
    ///
    /// Returns an error if the lock row cannot be released.
    pub fn finish(mut self) -> Result<(), LockError> {
        self.release_on_drop = false;
        let result = release_table(self.connection, &self.database, &self.table);
        if result.is_err() {
            self.connection.poison();
        }
        result
    }

    /// Leaves this lock registered until its database session ends.
    pub fn retain_lock(mut self) {
        self.release_on_drop = false;
    }
}

impl<const LOCKED: bool> Drop for TableView<'_, LOCKED> {
    fn drop(&mut self) {
        if LOCKED
            && self.release_on_drop
            && release_table(self.connection, &self.database, &self.table).is_err()
        {
            self.connection.poison();
        }
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Shared,
    Exclusive,
}

fn acquire_database(
    connection: &Connection<Standard>,
    database: &str,
    mode: Mode,
) -> Result<(), LockError> {
    require_unpoisoned(connection)?;
    require_database(connection, database)?;
    require_exclusive_access(connection, database)?;
    let sql = match mode {
        Mode::Shared => ACQUIRE_SHARED_DATABASE_SQL,
        Mode::Exclusive => ACQUIRE_EXCLUSIVE_DATABASE_SQL,
    };
    connection
        .sqlite()
        .query_row(sql, [database], |row| row.get::<_, i64>(0))
        .optional()
        .map_err(storage)?
        .ok_or(LockError::Conflict)?;
    Ok(())
}

fn require_empty_lock_registry(connection: &Connection<Standard>) -> Result<(), LockError> {
    require_unpoisoned(connection)?;
    let count = connection
        .sqlite()
        .query_row(COUNT_ALL_LOCKS_SQL, [], |row| row.get::<_, i64>(0))
        .map_err(storage)?;
    if count == 0 {
        Ok(())
    } else {
        Err(LockError::Conflict)
    }
}

fn clear_all_locks(connection: &Connection<Standard>) -> Result<(), LockError> {
    let tables = connection.sqlite().execute(CLEAR_ALL_TABLE_LOCKS_SQL, []);
    let databases = connection
        .sqlite()
        .execute(CLEAR_ALL_DATABASE_LOCKS_SQL, []);
    tables.map_err(storage)?;
    databases.map_err(storage)?;
    Ok(())
}

fn acquire_table(
    connection: &Connection<Standard>,
    database: &str,
    table: &str,
) -> Result<(), LockError> {
    connection
        .sqlite()
        .query_row(ACQUIRE_SHARED_TABLE_SQL, (database, table), |row| {
            row.get::<_, i64>(0)
        })
        .optional()
        .map_err(storage)?
        .ok_or(LockError::Conflict)?;
    Ok(())
}

fn release_database(connection: &Connection<Standard>, database: &str) -> Result<(), LockError> {
    if connection
        .sqlite()
        .execute(DELETE_DATABASE_LOCK_SQL, [database])
        .map_err(storage)?
        == 0
        && connection
            .sqlite()
            .execute(DECREMENT_DATABASE_LOCK_SQL, [database])
            .map_err(storage)?
            == 0
    {
        return Err(LockError::MissingLock);
    }
    Ok(())
}

fn release_table(
    connection: &Connection<Standard>,
    database: &str,
    table: &str,
) -> Result<(), LockError> {
    if connection
        .sqlite()
        .execute(DELETE_TABLE_LOCK_SQL, (database, table))
        .map_err(storage)?
        == 0
        && connection
            .sqlite()
            .execute(DECREMENT_TABLE_LOCK_SQL, (database, table))
            .map_err(storage)?
            == 0
    {
        return Err(LockError::MissingLock);
    }
    Ok(())
}

fn clear_database_session(
    connection: &Connection<Standard>,
    database: &str,
) -> Result<(), LockError> {
    let tables = connection
        .sqlite()
        .execute(CLEAR_DATABASE_TABLE_LOCKS_SQL, [database]);
    let database_lock = connection
        .sqlite()
        .execute(CLEAR_EXCLUSIVE_DATABASE_LOCK_SQL, [database]);

    tables.map_err(storage)?;
    if database_lock.map_err(storage)? == 0 {
        return Err(LockError::MissingLock);
    }
    Ok(())
}

fn require_database(connection: &Connection<Standard>, database: &str) -> Result<(), LockError> {
    let exists = connection
        .sqlite()
        .query_row(DATABASE_EXISTS_SQL, [database], |row| row.get::<_, bool>(0))
        .map_err(storage)?;
    if exists {
        Ok(())
    } else {
        Err(LockError::UnknownDatabase {
            database: database.to_owned(),
        })
    }
}

fn require_exclusive_access(
    connection: &Connection<Standard>,
    database: &str,
) -> Result<(), LockError> {
    let exclusive = connection
        .sqlite()
        .query_row(DATABASE_IS_EXCLUSIVE_SQL, [database], |row| {
            row.get::<_, bool>(0)
        })
        .map_err(storage)?;
    if exclusive {
        Ok(())
    } else {
        Err(LockError::NotExclusive {
            database: database.to_owned(),
        })
    }
}

fn require_table(
    connection: &Connection<Standard>,
    database: &str,
    table: &str,
) -> Result<(), LockError> {
    let exists = connection
        .sqlite()
        .query_row(TABLE_EXISTS_SQL, (database, table), |row| {
            row.get::<_, bool>(0)
        })
        .map_err(storage)?;
    if exists {
        Ok(())
    } else {
        Err(LockError::UnknownTable {
            database: database.to_owned(),
            table: table.to_owned(),
        })
    }
}

pub(crate) fn ensure_database_write_unlocked(
    connection: &Connection<Standard>,
    database: &str,
) -> Result<(), LockError> {
    require_unpoisoned(connection)?;
    let unlocked = connection
        .sqlite()
        .query_row(DATABASE_WRITE_UNLOCKED_SQL, [database], |row| {
            row.get::<_, bool>(0)
        })
        .map_err(storage)?;
    if unlocked {
        Ok(())
    } else {
        Err(LockError::Conflict)
    }
}

fn require_unpoisoned(connection: &Connection<Standard>) -> Result<(), LockError> {
    if connection.is_poisoned() {
        Err(LockError::Poisoned)
    } else {
        Ok(())
    }
}

fn storage(source: sqlite::Error) -> LockError {
    LockError::Storage { source }
}

/// Failure to acquire, inspect, or release a logical lock.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum LockError {
    /// A prior capability could not restore the logical lock invariant.
    #[snafu(display("the connection's logical lock discipline is poisoned"))]
    Poisoned,

    /// The requested database is not attached.
    #[snafu(display("database {database:?} is not attached"))]
    UnknownDatabase { database: String },

    /// Other connections may write the requested database.
    #[snafu(display("database {database:?} is not exclusively held by this connection"))]
    NotExclusive { database: String },

    /// The requested table does not exist.
    #[snafu(display("table {database:?}.{table:?} does not exist"))]
    UnknownTable { database: String, table: String },

    /// Another logical capability conflicts with the requested operation.
    #[snafu(display("the requested object is already held incompatibly"))]
    Conflict,

    /// A lock expected to be live was no longer registered.
    #[snafu(display("a live logical lock was not registered"))]
    MissingLock,

    /// Logical lock storage failed.
    #[snafu(display("could not access the logical lock registry: {source}"))]
    Storage { source: sqlite::Error },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Connection, ConnectionCarrier};

    #[test]
    fn missing_lock_during_drop_poisons_the_connection() {
        let mut connection = Connection::open_in_memory().unwrap();
        {
            let view = connection.view_mut(Lock::database("main")).unwrap();
            view.carrier()
                .connection()
                .sqlite()
                .execute(
                    "DELETE FROM temp.cov_conn_db_lock WHERE db_name = 'main'",
                    [],
                )
                .unwrap();
        }

        assert!(connection.is_poisoned());
        assert!(matches!(
            connection.session(Lock::database("main")),
            Err(LockError::Poisoned)
        ));
    }
}
