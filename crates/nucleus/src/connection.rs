use std::path::Path;

use covalence_neutron as neutron;

/// Failure to open a Nucleus connection.
pub type ConnectionError = neutron::ConnectionError;

/// Connection-local identity of a database registered with Nucleus.
pub type DatabaseId = neutron::DatabaseId;

/// A policy-enforcing connection to Nucleus state.
///
/// This initial wrapper intentionally exposes no access to its underlying
/// Neutron or `SQLite` connections. Later APIs can add operations only when
/// Nucleus can preserve their semantic invariants by construction.
#[derive(Debug)]
pub struct Connection {
    neutron: neutron::Connection,
}

impl Connection {
    /// Opens a database through Neutron and encloses it in the Nucleus boundary.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying `SQLite` connection cannot be
    /// opened or Neutron's connection metadata cannot be initialized.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        neutron::Connection::open(path).map(|neutron| Self { neutron })
    }

    /// Opens an in-memory database through Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when Neutron's connection metadata cannot be
    /// initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        neutron::Connection::open_in_memory().map(|neutron| Self { neutron })
    }

    /// Attaches an in-memory database while preserving Nucleus connection
    /// metadata.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database or Neutron cannot
    /// register it.
    pub fn attach_in_memory(&mut self, schema_name: &str) -> Result<DatabaseId, ConnectionError> {
        self.neutron.attach_in_memory(schema_name)
    }

    /// Attaches a file-backed database while preserving Nucleus connection
    /// metadata.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database or Neutron cannot
    /// register it.
    pub fn attach_file(
        &mut self,
        path: impl AsRef<Path>,
        schema_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        self.neutron.attach_file(path, schema_name)
    }

    /// Returns whether a database is known to be exclusive to this connection.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_is_exclusive(
        &self,
        database_id: DatabaseId,
    ) -> Result<Option<bool>, ConnectionError> {
        self.neutron.database_is_exclusive(database_id)
    }
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[test]
    fn opens_through_neutron() {
        let _connection = Connection::open_in_memory().expect("open Nucleus connection");
    }

    #[test]
    fn attaches_without_exposing_neutron() {
        let mut connection = Connection::open_in_memory().expect("open Nucleus connection");
        let id = connection
            .attach_in_memory("workspace")
            .expect("attach through Nucleus");
        assert!(id.get() > 0);
        assert_eq!(
            connection
                .database_is_exclusive(id)
                .expect("query exclusivity"),
            Some(true)
        );
    }
}
