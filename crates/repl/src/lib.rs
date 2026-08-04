//! Transport-neutral REPL orchestration.
//!
//! A [`Repl`] is not a Nucleus connection protocol. It maintains an ordinary,
//! inspectable `SQLite` directory in a raw Neutron connection and associates its
//! rows with runtime connection handles owned by the current process.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_sqlite as sqlite;

pub use covalence_nucleus::sql::{ImageError, Outcome, QueryResult, Statement, Value};
pub use covalence_nucleus::{
    AllowAll, Connection, ContextError, ContextId, Hol, HolOpenError, Kernel, Kind, KindError,
    KindId, KindView, ProofError, Sql, TermError, TermId, TermView, Theorem, TypeError, TypeId,
    TypeView,
};

const SCHEMA: &str = "
PRAGMA foreign_keys = ON;
CREATE TABLE repl_kernel (
    kernel_id INTEGER PRIMARY KEY,
    transport TEXT NOT NULL,
    endpoint TEXT,
    public_key BLOB NOT NULL CHECK (length(public_key) = 32)
) STRICT;
CREATE TABLE repl_connection (
    connection_id INTEGER PRIMARY KEY,
    kernel_id INTEGER NOT NULL REFERENCES repl_kernel,
    protocol TEXT NOT NULL,
    remote_connection_id TEXT
) STRICT;
CREATE TABLE repl_state (
    singleton INTEGER PRIMARY KEY CHECK (singleton = 0),
    active_connection_id INTEGER REFERENCES repl_connection
) STRICT;
INSERT INTO repl_state(singleton) VALUES (0);
";

/// Process-local identifier for a managed connection.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConnectionId(i64);

impl ConnectionId {
    /// Creates an ID from the browser ABI's unsigned representation.
    #[must_use]
    pub const fn from_u32(id: u32) -> Self {
        Self(id as i64)
    }

    /// Returns the integer stored in the REPL state database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

impl fmt::Display for ConnectionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A connection directory backed by its own raw `SQLite` database.
pub struct Repl<C> {
    state: covalence_neutron::Connection,
    connections: HashMap<ConnectionId, C>,
}

impl<C> Repl<C> {
    /// Opens an empty, in-memory REPL state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the raw Neutron connection or state schema cannot
    /// be opened.
    pub fn new(local_public_key: &[u8]) -> Result<Self, ReplError> {
        let state = covalence_neutron::Connection::open_in_memory()?;
        let transaction = state.sqlite().unchecked_transaction()?;
        transaction.execute_batch(SCHEMA)?;
        transaction.execute(
            "INSERT INTO repl_kernel(kernel_id, transport, public_key) VALUES (0, 'local', ?1)",
            [local_public_key],
        )?;
        transaction.commit()?;
        Ok(Self {
            state,
            connections: HashMap::new(),
        })
    }

    /// Returns the raw state connection for inspection and debugging.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        &self.state
    }

    /// Adds a runtime handle and records its protocol in the state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the directory cannot be updated.
    pub fn insert(&mut self, protocol: &str, connection: C) -> Result<ConnectionId, ReplError> {
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "INSERT INTO repl_connection(kernel_id, protocol) VALUES (0, ?1)",
            [protocol],
        )?;
        let id = ConnectionId(transaction.last_insert_rowid());
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = COALESCE(active_connection_id, ?1)
             WHERE singleton = 0",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections.insert(id, connection);
        Ok(id)
    }

    /// Returns the active connection ID, if any.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database cannot be read.
    pub fn active(&self) -> Result<Option<ConnectionId>, ReplError> {
        self.state
            .sqlite()
            .query_row(
                "SELECT active_connection_id FROM repl_state WHERE singleton = 0",
                (),
                |row| row.get::<_, Option<i64>>(0),
            )
            .map(|id| id.map(ConnectionId))
            .map_err(ReplError::from)
    }

    /// Selects an existing connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), ReplError> {
        self.require(id)?;
        self.state.sqlite().execute(
            "UPDATE repl_state SET active_connection_id = ?1 WHERE singleton = 0",
            [id.0],
        )?;
        Ok(())
    }

    /// Returns a mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or closed connection.
    pub fn get_mut(&mut self, id: ConnectionId) -> Result<&mut C, ReplError> {
        self.connections
            .get_mut(&id)
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Returns the active mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection is selected or state inspection fails.
    pub fn active_mut(&mut self) -> Result<&mut C, ReplError> {
        let id = self.active()?.ok_or(ReplError::NoActiveConnection)?;
        self.get_mut(id)
    }

    /// Closes and returns a runtime handle.
    ///
    /// If it was active, the lowest remaining ID becomes active.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn remove(&mut self, id: ConnectionId) -> Result<C, ReplError> {
        self.require(id)?;
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = (
                 SELECT min(connection_id) FROM repl_connection WHERE connection_id <> ?1
             )
             WHERE singleton = 0 AND active_connection_id = ?1",
            [id.0],
        )?;
        transaction.execute(
            "DELETE FROM repl_connection WHERE connection_id = ?1",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections
            .remove(&id)
            .ok_or(ReplError::UnknownConnection(id))
    }

    fn require(&self, id: ConnectionId) -> Result<(), ReplError> {
        if self.connections.contains_key(&id) {
            Ok(())
        } else {
            Err(ReplError::UnknownConnection(id))
        }
    }
}

/// One process-local connection managed by the shared terminal/browser core.
pub enum LocalConnection {
    /// An unrestricted raw SQL session.
    Sql(Connection<Sql>),
    /// The current minimal HOL-omega protocol under an explicit demo policy.
    Hol(Connection<Hol<AllowAll>>),
}

impl LocalConnection {
    const fn protocol(&self) -> &'static str {
        match self {
            Self::Sql(_) => "nucleus/sql",
            Self::Hol(_) => "nucleus/hol-omega-v0",
        }
    }
}

/// A local kernel and heterogeneous connection directory shared by all UIs.
pub struct LocalRepl {
    kernel: Kernel,
    directory: Repl<LocalConnection>,
}

impl LocalRepl {
    /// Creates a REPL with one fresh ephemeral kernel identity.
    ///
    /// # Errors
    ///
    /// Returns an error if its raw `SQLite` state database cannot open.
    pub fn new() -> Result<Self, LocalReplError> {
        let kernel = Kernel::ephemeral();
        let directory = Repl::new(kernel.verifying_key().as_bytes())?;
        Ok(Self { kernel, directory })
    }

    /// Returns the inspectable raw REPL state database.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        self.directory.state()
    }

    /// Returns the selected connection ID, if any.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database cannot be read.
    pub fn active(&self) -> Result<Option<ConnectionId>, LocalReplError> {
        self.directory.active().map_err(Into::into)
    }

    /// Selects an existing heterogeneous connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or state update failure.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), LocalReplError> {
        self.directory.select(id).map_err(Into::into)
    }

    /// Opens and selects a raw in-memory SQL session.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection or directory row cannot be created.
    pub fn open_sql(&mut self) -> Result<ConnectionId, LocalReplError> {
        let connection = self.kernel.open_sql().map_err(LocalReplError::SqlOpen)?;
        let id = self
            .directory
            .insert("nucleus/sql", LocalConnection::Sql(connection))?;
        self.directory.select(id)?;
        Ok(id)
    }

    /// Opens and selects a minimal HOL-omega connection.
    ///
    /// The demo explicitly chooses [`AllowAll`]; it does not weaken the HOL
    /// connection API or expose its underlying `SQLite` handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection/schema or directory row cannot open.
    pub fn open_hol(&mut self) -> Result<ConnectionId, LocalReplError> {
        let connection = self
            .kernel
            .open_hol(AllowAll)
            .map_err(LocalReplError::HolOpen)?;
        let id = self
            .directory
            .insert("nucleus/hol-omega-v0", LocalConnection::Hol(connection))?;
        self.directory.select(id)?;
        Ok(id)
    }

    /// Closes any managed connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or state update failure.
    pub fn close(&mut self, id: ConnectionId) -> Result<(), LocalReplError> {
        self.directory.remove(id).map(drop).map_err(Into::into)
    }

    /// Returns a mutable SQL session, rejecting HOL connection IDs.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or protocol mismatch.
    pub fn sql_mut(&mut self, id: ConnectionId) -> Result<&mut Connection<Sql>, LocalReplError> {
        let connection = self.directory.get_mut(id)?;
        match connection {
            LocalConnection::Sql(connection) => Ok(connection),
            other @ LocalConnection::Hol(_) => Err(LocalReplError::WrongProtocol {
                id,
                expected: "nucleus/sql",
                actual: other.protocol(),
            }),
        }
    }

    /// Returns a mutable HOL session, rejecting SQL connection IDs.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or protocol mismatch.
    pub fn hol_mut(
        &mut self,
        id: ConnectionId,
    ) -> Result<&mut Connection<Hol<AllowAll>>, LocalReplError> {
        let connection = self.directory.get_mut(id)?;
        match connection {
            LocalConnection::Hol(connection) => Ok(connection),
            other @ LocalConnection::Sql(_) => Err(LocalReplError::WrongProtocol {
                id,
                expected: "nucleus/hol-omega-v0",
                actual: other.protocol(),
            }),
        }
    }
}

/// Failure in the shared local-kernel REPL layer.
#[derive(Debug)]
pub enum LocalReplError {
    /// The connection directory failed.
    Directory(ReplError),
    /// A raw SQL connection could not open.
    SqlOpen(covalence_neutron::ConnectionError),
    /// A HOL connection or its schema could not open.
    HolOpen(HolOpenError),
    /// A command was sent to a connection of another protocol.
    WrongProtocol {
        /// Requested connection.
        id: ConnectionId,
        /// Protocol required by the operation.
        expected: &'static str,
        /// Protocol actually owned by the connection.
        actual: &'static str,
    },
}

impl fmt::Display for LocalReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Directory(error) => error.fmt(formatter),
            Self::SqlOpen(error) => write!(formatter, "could not open SQL connection: {error}"),
            Self::HolOpen(error) => error.fmt(formatter),
            Self::WrongProtocol {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "connection {id} uses {actual}; operation requires {expected}"
            ),
        }
    }
}

impl StdError for LocalReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Directory(error) => Some(error),
            Self::SqlOpen(error) => Some(error),
            Self::HolOpen(error) => Some(error),
            Self::WrongProtocol { .. } => None,
        }
    }
}

impl From<ReplError> for LocalReplError {
    fn from(error: ReplError) -> Self {
        Self::Directory(error)
    }
}

/// Failure to operate the REPL directory.
#[derive(Debug)]
pub enum ReplError {
    /// The raw state connection could not be opened.
    Open(covalence_neutron::ConnectionError),
    /// The state database rejected an operation.
    State(sqlite::Error),
    /// A requested runtime connection does not exist.
    UnknownConnection(ConnectionId),
    /// No runtime connection is currently selected.
    NoActiveConnection,
}

impl fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(error) => write!(formatter, "could not open REPL state: {error}"),
            Self::State(error) => write!(formatter, "could not access REPL state: {error}"),
            Self::UnknownConnection(id) => write!(formatter, "unknown connection {id}"),
            Self::NoActiveConnection => formatter.write_str("no active connection"),
        }
    }
}

impl StdError for ReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Open(error) => Some(error),
            Self::State(error) => Some(error),
            Self::UnknownConnection(_) | Self::NoActiveConnection => None,
        }
    }
}

impl From<covalence_neutron::ConnectionError> for ReplError {
    fn from(error: covalence_neutron::ConnectionError) -> Self {
        Self::Open(error)
    }
}

impl From<sqlite::Error> for ReplError {
    fn from(error: sqlite::Error) -> Self {
        Self::State(error)
    }
}

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
mod web;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub use web::{WebKernel, WebKind, WebOutcome, WebTerm, WebType};

/// Returns the cross-target `SQLite` smoke-test value.
#[must_use]
#[cfg_attr(
    all(target_arch = "wasm32", target_os = "unknown"),
    wasm_bindgen::prelude::wasm_bindgen
)]
pub fn smoke() -> u32 {
    covalence_nucleus::smoke()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_lifecycle_and_selection_in_sqlite() {
        let mut repl = Repl::new(&[7; 32]).unwrap();
        let first = repl.insert("one", String::from("first")).unwrap();
        let second = repl.insert("two", String::from("second")).unwrap();
        assert_eq!(repl.active().unwrap(), Some(first));

        repl.select(second).unwrap();
        assert_eq!(repl.active().unwrap(), Some(second));
        assert_eq!(repl.active_mut().unwrap(), "second");
        assert_eq!(repl.remove(second).unwrap(), "second");
        assert_eq!(repl.active().unwrap(), Some(first));

        let rows = repl
            .state()
            .sqlite()
            .query_row("SELECT count(*) FROM repl_connection", (), |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 1);
        let public_key = repl
            .state()
            .sqlite()
            .query_row(
                "SELECT public_key FROM repl_kernel WHERE kernel_id = 0",
                (),
                |row| row.get::<_, Vec<u8>>(0),
            )
            .unwrap();
        assert_eq!(public_key, vec![7; 32]);
    }

    #[test]
    fn local_kernel_directory_manages_sql_and_hol_without_crossing_protocols() {
        let mut repl = LocalRepl::new().unwrap();
        let sql = repl.open_sql().unwrap();
        let hol = repl.open_hol().unwrap();

        repl.sql_mut(sql).unwrap().run("SELECT 1", &[]).unwrap();
        let star = repl.hol_mut(hol).unwrap().insert_kind(&Kind::Star).unwrap();
        assert_eq!(star.get(), 1);
        assert!(matches!(
            repl.sql_mut(hol),
            Err(LocalReplError::WrongProtocol {
                expected: "nucleus/sql",
                actual: "nucleus/hol-omega-v0",
                ..
            })
        ));
        assert!(matches!(
            repl.hol_mut(sql),
            Err(LocalReplError::WrongProtocol {
                expected: "nucleus/hol-omega-v0",
                actual: "nucleus/sql",
                ..
            })
        ));
        let protocols = repl
            .state()
            .sqlite()
            .prepare("SELECT protocol FROM repl_connection ORDER BY connection_id")
            .unwrap()
            .query_map([], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(protocols, ["nucleus/sql", "nucleus/hol-omega-v0"]);
    }
}
