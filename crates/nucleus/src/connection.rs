use covalence_neutron as neutron;

/// A protocol-enforcing connection to Nucleus state.
///
/// The protocol value carries connection-local policy and evidence. There is
/// deliberately no generic SQL escape hatch: each protocol exposes only the
/// operations that preserve its invariants.
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

    pub(crate) const fn parts(&self) -> (&neutron::Connection, &P) {
        (&self.neutron, &self.protocol)
    }
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[test]
    fn encloses_protocol_state() {
        let neutron = covalence_neutron::Connection::open_in_memory().expect("open Neutron");
        let connection = Connection::from_neutron(neutron, 7_u64);
        assert_eq!(*connection.protocol(), 7);
        assert_eq!(*connection.parts().1, 7);
    }
}
