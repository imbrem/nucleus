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
    _neutron: neutron::Connection,
}

impl Connection {
    /// Opens a database through Neutron and encloses it in the Nucleus boundary.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying `SQLite` connection cannot be
    /// opened or Neutron's connection metadata cannot be initialized.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        neutron::Connection::open(path).map(|neutron| Self { _neutron: neutron })
    }

    /// Opens an in-memory database through Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when Neutron's connection metadata cannot be
    /// initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        neutron::Connection::open_in_memory().map(|neutron| Self { _neutron: neutron })
    }

    /// Shared access to the enclosed connection and protocol state.
    ///
    /// Protocol modules use this to build borrowing views whose operations
    /// take `&self` (for example, a proof view holding cached prepared
    /// statements). Exclusive operations such as garbage collection stay on
    /// `parts_mut`, so they are statically impossible while any borrowing
    /// view is alive.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "first borrowing-view protocol lands next")
    )]
    pub(crate) const fn parts(&self) -> (&neutron::Connection, &P) {
        (&self.neutron, &self.protocol)
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
    fn shares_connection_and_protocol_with_borrowing_views() {
        let neutron = covalence_neutron::Connection::open_in_memory().expect("open Neutron");
        let connection = Connection::from_neutron(
            neutron,
            TestProtocol {
                admitted_generation: 3,
            },
        );

        let (first_neutron, first_protocol) = connection.parts();
        let (second_neutron, second_protocol) = connection.parts();
        assert_eq!(first_protocol.admitted_generation, 3);
        assert_eq!(second_protocol.admitted_generation, 3);
        for neutron in [first_neutron, second_neutron] {
            assert_eq!(
                neutron
                    .sqlite()
                    .query_row("SELECT 42", (), |row| row.get::<_, i64>(0))
                    .expect("query enclosed connection"),
                42
            );
        }
    }
}
