use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

/// A thin, permeable owner of an `SQLite` connection.
///
/// Neutron assigns no interpretation to the database and installs no schema.
/// Callers may access the underlying connection directly and are responsible
/// for every semantic invariant they require. Nucleus provides protocol
/// enclosures above this mechanical wrapper.
#[derive(Debug)]
pub struct Connection {
    sqlite: sqlite::Connection,
}

impl Connection {
    /// Opens an `SQLite` database.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        sqlite::Connection::open(path)
            .context(OpenSnafu)
            .map(Self::from_sqlite)
    }

    /// Opens an in-memory `SQLite` database.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        sqlite::Connection::open_in_memory()
            .context(OpenSnafu)
            .map(Self::from_sqlite)
    }

    /// Adopts an existing `SQLite` connection without changing it.
    #[must_use]
    pub const fn from_sqlite(sqlite: sqlite::Connection) -> Self {
        Self { sqlite }
    }

    /// Borrows the underlying `SQLite` connection.
    #[must_use]
    pub const fn sqlite(&self) -> &sqlite::Connection {
        &self.sqlite
    }

    /// Mutably borrows the underlying `SQLite` connection.
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

/// Failure to open a Neutron connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// The raw `SQLite` connection could not be opened.
    #[snafu(display("could not open SQLite connection: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}

#[cfg(test)]
mod tests {
    use super::Connection;
    use covalence_lib_sqlite as sqlite;

    #[test]
    fn opening_does_not_install_schema() {
        let connection = Connection::open_in_memory().expect("open Neutron");
        let schemas = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema WHERE type = 'table'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("count temporary tables");
        assert_eq!(schemas, 0);
    }

    #[test]
    fn adopts_connection_without_modifying_it() {
        let sqlite = sqlite::Connection::open_in_memory().expect("open SQLite");
        sqlite
            .execute("CREATE TEMP TABLE existing (value INTEGER)", ())
            .expect("create temporary table");

        let connection = Connection::from_sqlite(sqlite);
        let exists = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema WHERE name = 'existing'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect adopted connection");
        assert_eq!(exists, 1);
    }

    #[test]
    fn exposes_underlying_connection() {
        let mut connection = Connection::open_in_memory().expect("open Neutron");
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
