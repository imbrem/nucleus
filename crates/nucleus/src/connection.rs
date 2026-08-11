use std::path::Path;
use std::sync::{Mutex, MutexGuard};

use covalence_neutron as neutron;

/// Failure to open a Nucleus connection.
pub type ConnectionError = neutron::ConnectionError;

/// Protocol state for the existing unrestricted connection constructors.
#[derive(Clone, Copy, Debug, Default)]
pub struct RawProtocol;

/// A protocol-enforcing connection to Nucleus state.
///
/// The default [`RawProtocol`] preserves the original general connection API.
/// Other protocols expose only operations that maintain their invariants.
#[derive(Debug)]
pub struct Connection<P = RawProtocol> {
    neutron: neutron::Connection,
    protocol: P,
    operation: Mutex<()>,
}

impl Connection<RawProtocol> {
    /// Opens a database through Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying connection cannot be opened.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        neutron::Connection::open(path).map(|neutron| Self {
            neutron,
            protocol: RawProtocol,
            operation: Mutex::new(()),
        })
    }

    /// Opens an in-memory database through Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying connection cannot be opened.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        neutron::Connection::open_in_memory().map(|neutron| Self {
            neutron,
            protocol: RawProtocol,
            operation: Mutex::new(()),
        })
    }
}

impl<P> Connection<P> {
    /// Returns the protocol state carried by this connection.
    #[must_use]
    pub const fn protocol(&self) -> &P {
        &self.protocol
    }

    pub(crate) const fn from_neutron(neutron: neutron::Connection, protocol: P) -> Self {
        Self {
            neutron,
            protocol,
            operation: Mutex::new(()),
        }
    }

    pub(crate) const fn parts(&self) -> (&neutron::Connection, &P) {
        (&self.neutron, &self.protocol)
    }

    /// Serializes a complete protocol operation.
    ///
    /// Call policy code before taking this lock. Composite operations must
    /// acquire it once and use private locked primitives rather than nesting
    /// public operations, because the mutex is intentionally not reentrant.
    pub(crate) fn lock_operation(&self) -> MutexGuard<'_, ()> {
        self.operation
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

#[cfg(test)]
mod tests {
    use super::{Connection, RawProtocol};

    #[test]
    fn preserves_raw_constructors() {
        let connection = Connection::open_in_memory().expect("open Nucleus connection");
        assert!(matches!(connection.protocol(), RawProtocol));
    }

    #[test]
    fn shares_protocol_with_borrowing_views() {
        let neutron = covalence_neutron::Connection::open_in_memory().expect("open Neutron");
        let connection = Connection::from_neutron(neutron, 7_u64);
        assert_eq!(*connection.parts().1, 7);
    }
}
