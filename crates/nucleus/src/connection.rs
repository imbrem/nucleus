use std::path::Path;

use covalence_neutron as neutron;

/// Failure to open a Nucleus connection.
pub type ConnectionError = neutron::ConnectionError;

/// Connection-local identity of a database registered with Nucleus.
pub type DatabaseId = neutron::DatabaseId;

/// A database's role within its `SQLite` connection.
pub type DatabaseRole = neutron::DatabaseRole;

/// A connection-local use of a `SQLite` VFS.
pub type VfsInstance = neutron::VfsInstance;

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

    /// Opens a database through the requested `SQLite` VFS.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened with the requested
    /// VFS or Neutron's connection metadata cannot be initialized.
    pub fn open_with_vfs(path: impl AsRef<Path>, vfs_name: &str) -> Result<Self, ConnectionError> {
        neutron::Connection::open_with_vfs(path, vfs_name).map(|neutron| Self { neutron })
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

    /// Opens an in-memory database through the requested `SQLite` VFS.
    ///
    /// # Errors
    ///
    /// Returns an error when the database cannot be opened with the requested
    /// VFS or Neutron's connection metadata cannot be initialized.
    pub fn open_in_memory_with_vfs(vfs_name: &str) -> Result<Self, ConnectionError> {
        neutron::Connection::open_in_memory_with_vfs(vfs_name).map(|neutron| Self { neutron })
    }

    /// Attaches an in-memory database while preserving Nucleus connection
    /// metadata.
    ///
    /// `schema_name` is `SQLite`'s connection-local name for addressing the
    /// attachment, not a persistent database identity.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database or Neutron cannot
    /// register it.
    pub fn attach_in_memory(&mut self, schema_name: &str) -> Result<DatabaseId, ConnectionError> {
        self.neutron.attach_in_memory(schema_name)
    }

    /// Attaches an in-memory database through the requested `SQLite` VFS.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database using the
    /// requested VFS or Neutron cannot register it.
    pub fn attach_in_memory_with_vfs(
        &mut self,
        schema_name: &str,
        vfs_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        self.neutron
            .attach_in_memory_with_vfs(schema_name, vfs_name)
    }

    /// Attaches a file-backed database while preserving Nucleus connection
    /// metadata.
    ///
    /// `schema_name` is `SQLite`'s connection-local name for addressing the
    /// attachment, not a persistent database identity.
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

    /// Attaches a file-backed database through the requested `SQLite` VFS.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot attach the database using the
    /// requested VFS or Neutron cannot register it.
    pub fn attach_file_with_vfs(
        &mut self,
        path: impl AsRef<Path>,
        schema_name: &str,
        vfs_name: &str,
    ) -> Result<DatabaseId, ConnectionError> {
        self.neutron
            .attach_file_with_vfs(path, schema_name, vfs_name)
    }

    /// Returns whether a database is exclusive to this connection.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_is_exclusive(&self, database_id: DatabaseId) -> Result<bool, ConnectionError> {
        self.neutron.database_is_exclusive(database_id)
    }

    /// Returns the database's connection-local role.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_role(&self, database_id: DatabaseId) -> Result<DatabaseRole, ConnectionError> {
        self.neutron.database_role(database_id)
    }

    /// Returns the connection-local VFS instance used by a database.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn database_vfs(&self, database_id: DatabaseId) -> Result<VfsInstance, ConnectionError> {
        self.neutron.database_vfs(database_id)
    }

    /// Returns the connection's primary database identity.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection metadata cannot be queried.
    pub fn main_database_id(&self) -> Result<DatabaseId, ConnectionError> {
        self.neutron.main_database_id()
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
        assert!(
            connection
                .database_is_exclusive(id)
                .expect("query exclusivity")
        );
        assert_eq!(
            connection.database_role(id).expect("query role"),
            super::DatabaseRole::Auxiliary
        );
    }

    #[cfg(unix)]
    #[test]
    fn exposes_vfs_selection_without_exposing_neutron() {
        let mut connection =
            Connection::open_in_memory_with_vfs("unix").expect("open through unix VFS");
        let main = connection.main_database_id().expect("find main database");
        assert_eq!(
            connection
                .database_vfs(main)
                .expect("query main VFS")
                .name(),
            Some("unix")
        );

        let auxiliary = connection
            .attach_in_memory_with_vfs("scratch", "unix")
            .expect("attach through unix VFS");
        assert_eq!(
            connection
                .database_vfs(auxiliary)
                .expect("query auxiliary VFS")
                .name(),
            Some("unix")
        );
    }
}
