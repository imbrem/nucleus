use covalence_neutron as neutron;

/// A protocol-enforcing connection to Nucleus state.
///
/// `P` is the connection's protocol and carries its connection-local policy
/// and evidence. Protocol modules construct this enclosure only after
/// admitting the underlying `SQLite` connection, and expose operations only
/// for the reads and writes their logic permits.
///
/// There is intentionally no generic constructor, statement API, or escape
/// hatch to the enclosed Neutron connection. A deliberately permeable
/// protocol, such as a SQL shell, must make that authority explicit in its own
/// API.
pub struct Connection<P> {
    neutron: neutron::Connection,
    protocol: P,
}

impl<P> Connection<P> {
    /// Returns the protocol state carried by this connection.
    #[must_use]
    pub const fn protocol(&self) -> &P {
        &self.protocol
    }

    pub(crate) const fn from_neutron(neutron: neutron::Connection, protocol: P) -> Self {
        Self { neutron, protocol }
    }

    pub(crate) const fn parts_mut(&mut self) -> (&mut neutron::Connection, &mut P) {
        (&mut self.neutron, &mut self.protocol)
    }

    /// Shared access to the enclosed connection and protocol state.
    ///
    /// Protocol modules use this to build borrowing views whose operations
    /// take `&self` (for example, a proof view holding cached prepared
    /// statements). Exclusive operations such as garbage collection stay on
    /// `parts_mut`, so they are statically impossible while any borrowing
    /// view is alive.
    pub(crate) const fn parts(&self) -> (&neutron::Connection, &P) {
        (&self.neutron, &self.protocol)
    }
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[derive(Debug, Eq, PartialEq)]
    struct TestProtocol {
        admitted_generation: u64,
    }

    #[test]
    fn encloses_protocol_state_with_neutron_connection() {
        let neutron = covalence_neutron::Connection::open_in_memory().expect("open Neutron");
        let mut connection = Connection::from_neutron(
            neutron,
            TestProtocol {
                admitted_generation: 7,
            },
        );

        assert_eq!(connection.protocol().admitted_generation, 7);
        let (neutron, protocol) = connection.parts_mut();
        assert_eq!(
            neutron
                .sqlite()
                .query_row("SELECT 42", (), |row| row.get::<_, i64>(0))
                .expect("query enclosed connection"),
            42
        );
        protocol.admitted_generation += 1;
        assert_eq!(connection.protocol().admitted_generation, 8);
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
