use std::path::Path;

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

    /// Returns the connection's default content-addressed store.
    #[must_use]
    pub const fn cas(&self) -> crate::Cas<'_> {
        self.neutron.cas()
    }

    /// Creates a persistent segment-map table and returns its prepared adapter.
    ///
    /// # Errors
    ///
    /// Returns an error when `table` is not a safe `SQLite` identifier, the
    /// table already exists, or `SQLite` cannot create and prepare the map.
    pub fn create_segment_map(
        &self,
        table: &str,
    ) -> Result<crate::SegmentMap<'_>, crate::SegmentMapError> {
        crate::SegmentMap::create(&self.neutron, table)
    }

    /// Opens and validates an existing persistent segment-map table.
    ///
    /// # Errors
    ///
    /// Returns an error when the table schema or any stored segment violates
    /// the segment-map invariants, or `SQLite` cannot prepare the map.
    pub fn open_segment_map(
        &self,
        table: &str,
    ) -> Result<crate::SegmentMap<'_>, crate::SegmentMapError> {
        crate::SegmentMap::open(&self.neutron, table)
    }

    /// Creates a persistent, unkeyed BLAKE3 segment CAS.
    ///
    /// # Errors
    ///
    /// Returns an error when the caller-selected table family cannot be
    /// created and validated atomically.
    pub fn create_blake3_segment_cas(
        &self,
        table: &str,
    ) -> Result<crate::Blake3SegmentCas<'_>, crate::SegmentCasError> {
        crate::Blake3SegmentCas::create(&self.neutron, table)
    }

    /// Opens a persistent, unkeyed BLAKE3 segment CAS after physical and
    /// semantic validation.
    ///
    /// # Errors
    ///
    /// Returns an error when the database fails `SQLite` integrity checking,
    /// the table family is incompatible, or stored evidence does not prove its
    /// claimed BLAKE3 object.
    pub fn open_blake3_segment_cas(
        &self,
        table: &str,
    ) -> Result<crate::Blake3SegmentCas<'_>, crate::SegmentCasError> {
        crate::Blake3SegmentCas::open(&self.neutron, table)
    }
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[test]
    fn opens_through_neutron() {
        let connection = Connection::open_in_memory().expect("open Nucleus connection");
        let _cas: crate::Cas<'_> = connection.cas();
    }
}
