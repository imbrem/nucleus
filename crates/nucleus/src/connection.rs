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
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by protocol modules in stacked changes")
    )]
    neutron: neutron::Connection,
    protocol: P,
}

impl<P> Connection<P> {
    /// Returns the protocol state carried by this connection.
    #[must_use]
    pub const fn protocol(&self) -> &P {
        &self.protocol
    }

    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by protocol modules in stacked changes")
    )]
    pub(crate) const fn from_neutron(neutron: neutron::Connection, protocol: P) -> Self {
        Self { neutron, protocol }
    }

    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "used by protocol modules in stacked changes")
    )]
    pub(crate) const fn parts_mut(&mut self) -> (&mut neutron::Connection, &mut P) {
        (&mut self.neutron, &mut self.protocol)
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
}
