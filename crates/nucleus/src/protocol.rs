use crate::{Connection, Invariant};

/// An open protocol which obtains exclusive access to an invariant connection.
pub trait SessionProtocol<I: Invariant> {
    /// Failure to enter the protocol.
    type Error;

    /// Capability returned while the protocol is active.
    type Session<'a>
    where
        Self: 'a,
        I: 'a;

    /// Enters the protocol.
    ///
    /// # Errors
    ///
    /// Returns an error when the protocol's preconditions are not satisfied.
    fn enter(self, connection: &mut Connection<I>) -> Result<Self::Session<'_>, Self::Error>;
}

/// An open protocol which obtains shared access to an invariant connection.
pub trait ViewProtocol<I: Invariant> {
    /// Failure to construct the view.
    type Error;

    /// Capability returned by the protocol.
    type View<'a>
    where
        Self: 'a,
        I: 'a;

    /// Constructs a view governed by this protocol.
    ///
    /// # Errors
    ///
    /// Returns an error when the protocol's preconditions are not satisfied.
    fn view(self, connection: &Connection<I>) -> Result<Self::View<'_>, Self::Error>;
}

impl<I: Invariant> Connection<I> {
    /// Enters an open session protocol.
    ///
    /// # Errors
    ///
    /// Returns the protocol's error when its preconditions are not satisfied.
    pub fn enter<P>(&mut self, protocol: P) -> Result<P::Session<'_>, P::Error>
    where
        P: SessionProtocol<I>,
    {
        protocol.enter(self)
    }

    /// Constructs a capability through an open view protocol.
    ///
    /// # Errors
    ///
    /// Returns the protocol's error when its preconditions are not satisfied.
    pub fn view<P>(&self, protocol: P) -> Result<P::View<'_>, P::Error>
    where
        P: ViewProtocol<I>,
    {
        protocol.view(self)
    }
}
