use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_neutron as neutron;

/// Failure to open a Nucleus connection.
pub type ConnectionError = neutron::ConnectionError;

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

    /// Creates fresh in-memory persistent Nucleus state.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection or persistent catalog cannot be
    /// created.
    pub fn create_in_memory() -> Result<Self, DatabaseError> {
        let neutron = neutron::Connection::open_in_memory().context(OpenSnafu)?;
        neutron.create_persistent_catalog().context(AdditionSnafu)?;
        Ok(Self { neutron })
    }

    /// Loads and validates persistent Nucleus state from a database image.
    ///
    /// This validates structure and addition relations; it does not establish
    /// trust in the image or its signer.
    ///
    /// # Errors
    ///
    /// Returns an error when deserialization or validation fails.
    pub fn from_image(bytes: &neutron::Bytes) -> Result<Self, DatabaseError> {
        let neutron = neutron::Connection::deserialize(bytes).context(ImageSnafu)?;
        neutron.validate_addition_tables().context(AdditionSnafu)?;
        Ok(Self { neutron })
    }

    /// Serializes the persistent `main` database, excluding connection state.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot serialize the image.
    pub fn serialize(&self) -> Result<neutron::Bytes, neutron::ImageError> {
        self.neutron.serialize()
    }

    /// Returns the connection's default content-addressed store.
    #[must_use]
    pub const fn cas(&self) -> crate::Cas<'_> {
        self.neutron.cas()
    }

    /// Creates and registers an addition table.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid names or database failures.
    pub fn create_addition_table(
        &mut self,
        name: &str,
        layout: neutron::AdditionLayout,
    ) -> Result<neutron::AdditionTable, neutron::AdditionError> {
        self.neutron.create_addition_table(name, layout)
    }

    /// Returns all validated addition tables.
    ///
    /// # Errors
    ///
    /// Returns an error if the catalog, a table, or any fact is invalid.
    pub fn addition_tables(&self) -> Result<Vec<neutron::AdditionTable>, neutron::AdditionError> {
        self.neutron.validate_addition_tables()
    }

    /// Inserts one checked addition fact.
    ///
    /// # Errors
    ///
    /// Returns an error when the fact or table is invalid.
    pub fn insert_addition(
        &self,
        table: &neutron::AdditionTable,
        fact: neutron::AdditionFact,
    ) -> Result<(), neutron::AdditionError> {
        self.neutron.insert_addition(table, fact)
    }

    /// Loads the checked facts in an addition table.
    ///
    /// # Errors
    ///
    /// Returns an error when a row is invalid.
    pub fn addition_facts(
        &self,
        table: &neutron::AdditionTable,
    ) -> Result<Vec<neutron::AdditionFact>, neutron::AdditionError> {
        self.neutron.addition_facts(table)
    }
}

/// Failure to create or import persistent Nucleus state.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DatabaseError {
    /// A Neutron connection could not be opened.
    #[snafu(display("could not open Nucleus state: {source}"))]
    Open {
        /// Underlying connection failure.
        source: neutron::ConnectionError,
    },

    /// A database image could not be installed.
    #[snafu(display("could not load Nucleus state: {source}"))]
    Image {
        /// Underlying image failure.
        source: neutron::ImageError,
    },

    /// Persistent relational state is invalid.
    #[snafu(display("invalid Nucleus relations: {source}"))]
    Addition {
        /// Addition catalog or row failure.
        source: neutron::AdditionError,
    },
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[test]
    fn opens_through_neutron() {
        let connection = Connection::open_in_memory().expect("open Nucleus connection");
        let _cas: crate::Cas<'_> = connection.cas();
    }

    #[test]
    fn persists_multiple_addition_geometries() {
        let mut connection = Connection::create_in_memory().expect("create");
        let rowid = connection
            .create_addition_table("small", crate::AdditionLayout::RowId)
            .expect("rowid");
        let compact = connection
            .create_addition_table("large", crate::AdditionLayout::WithoutRowId)
            .expect("without rowid");
        connection
            .insert_addition(&rowid, crate::AdditionFact::sum(1, 2).expect("valid sum"))
            .expect("insert");
        connection
            .insert_addition(
                &compact,
                crate::AdditionFact::sum(i64::MIN, 1).expect("valid sum"),
            )
            .expect("insert");

        let image = connection.serialize().expect("serialize");
        let restored = Connection::from_image(&image).expect("restore");
        assert_eq!(restored.addition_tables().expect("tables").len(), 2);
    }
}
