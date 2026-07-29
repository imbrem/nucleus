use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

/// A permeable mechanical wrapper around one `SQLite` connection.
///
/// Neutron creates no application tables and assigns no semantics to the
/// connection. Higher layers may use the raw connection deliberately.
#[derive(Debug)]
pub struct Connection {
    sqlite: sqlite::Connection,
}

impl Connection {
    /// Opens a `SQLite` database.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        sqlite::Connection::open(path)
            .map(Self::from_sqlite)
            .context(OpenSnafu)
    }

    /// Opens a new in-memory `SQLite` database.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot open the database.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        sqlite::Connection::open_in_memory()
            .map(Self::from_sqlite)
            .context(OpenSnafu)
    }

    /// Adopts a raw `SQLite` connection without modifying it.
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

    /// Consumes this wrapper and returns the `SQLite` connection.
    #[must_use]
    pub fn into_sqlite(self) -> sqlite::Connection {
        self.sqlite
    }
}

/// Failure to open a Neutron connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// `SQLite` could not open the requested connection.
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
    fn opening_does_not_create_tables() {
        let connection = Connection::open_in_memory().unwrap();
        let tables = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema WHERE type = 'table'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(tables, 0);
    }

    #[test]
    fn adopts_without_modifying_a_connection() {
        let sqlite = sqlite::Connection::open_in_memory().unwrap();
        sqlite
            .execute("CREATE TEMP TABLE existing (value INTEGER)", ())
            .unwrap();
        let connection = Connection::from_sqlite(sqlite);
        let tables = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema WHERE name = 'existing'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(tables, 1);
    }
}
