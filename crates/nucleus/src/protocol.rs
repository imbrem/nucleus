use crate::{
    BorrowedConnection, Connection, ConnectionCarrier, Invariant, MutableConnectionCarrier,
    OwnedConnection, SharedConnection,
};

/// An open protocol which obtains exclusive access to a connection carrier.
///
/// Session and view protocols are deliberately independent. A protocol which
/// supports both modes implements both traits explicitly.
pub trait SessionProtocol<C: MutableConnectionCarrier> {
    /// Failure to enter the protocol.
    type Error;

    /// Capability returned while the protocol is active.
    type Session;

    /// Enters the protocol.
    ///
    /// On failure, returns both the error and the original carrier.
    ///
    /// # Errors
    ///
    /// Returns the protocol error and carrier when its preconditions fail.
    fn enter(self, carrier: C) -> Result<Self::Session, (Self::Error, C)>;
}

/// An open protocol which constructs an observational capability.
///
/// A view may still require an exclusive or owned carrier when its guarantee
/// is that no mutating API remains accessible through this connection.
pub trait ViewProtocol<C: ConnectionCarrier> {
    /// Failure to construct the view.
    type Error;

    /// Capability returned by the protocol.
    type View;

    /// Constructs the view.
    ///
    /// On failure, returns both the error and the original carrier.
    ///
    /// # Errors
    ///
    /// Returns the protocol error and carrier when its preconditions fail.
    fn view(self, carrier: C) -> Result<Self::View, (Self::Error, C)>;
}

/// Result of constructing an owned protocol view.
pub type OwnedViewResult<I, P> = Result<
    <P as ViewProtocol<OwnedConnection<I>>>::View,
    (
        <P as ViewProtocol<OwnedConnection<I>>>::Error,
        Connection<I>,
    ),
>;

/// Result of constructing an owned protocol session.
pub type OwnedSessionResult<I, P> = Result<
    <P as SessionProtocol<OwnedConnection<I>>>::Session,
    (
        <P as SessionProtocol<OwnedConnection<I>>>::Error,
        Connection<I>,
    ),
>;

impl<I: Invariant> Connection<I> {
    /// Constructs a view from an immutable connection borrow.
    ///
    /// # Errors
    ///
    /// Returns the protocol's error when its preconditions are not satisfied.
    pub fn view<'connection, P>(
        &'connection self,
        protocol: P,
    ) -> Result<
        <P as ViewProtocol<SharedConnection<'connection, I>>>::View,
        <P as ViewProtocol<SharedConnection<'connection, I>>>::Error,
    >
    where
        P: ViewProtocol<SharedConnection<'connection, I>>,
    {
        protocol
            .view(SharedConnection::new(self))
            .map_err(|(error, _)| error)
    }

    /// Constructs a view which exclusively borrows the connection.
    ///
    /// # Errors
    ///
    /// Returns the protocol's error when its preconditions are not satisfied.
    pub fn view_mut<'connection, P>(
        &'connection mut self,
        protocol: P,
    ) -> Result<
        <P as ViewProtocol<BorrowedConnection<'connection, I>>>::View,
        <P as ViewProtocol<BorrowedConnection<'connection, I>>>::Error,
    >
    where
        P: ViewProtocol<BorrowedConnection<'connection, I>>,
    {
        protocol
            .view(BorrowedConnection::new(self))
            .map_err(|(error, _)| error)
    }

    /// Enters a protocol which exclusively borrows the connection.
    ///
    /// # Errors
    ///
    /// Returns the protocol's error when its preconditions are not satisfied.
    pub fn session<'connection, P>(
        &'connection mut self,
        protocol: P,
    ) -> Result<
        <P as SessionProtocol<BorrowedConnection<'connection, I>>>::Session,
        <P as SessionProtocol<BorrowedConnection<'connection, I>>>::Error,
    >
    where
        P: SessionProtocol<BorrowedConnection<'connection, I>>,
    {
        protocol
            .enter(BorrowedConnection::new(self))
            .map_err(|(error, _)| error)
    }

    /// Constructs a view which owns the connection.
    ///
    /// # Errors
    ///
    /// Returns the protocol error together with the original connection.
    pub fn into_view<P>(self, protocol: P) -> OwnedViewResult<I, P>
    where
        P: ViewProtocol<OwnedConnection<I>>,
    {
        protocol
            .view(OwnedConnection::new(self))
            .map_err(|(error, carrier)| (error, carrier.into_connection()))
    }

    /// Enters a protocol which owns the connection.
    ///
    /// # Errors
    ///
    /// Returns the protocol error together with the original connection.
    pub fn into_session<P>(self, protocol: P) -> OwnedSessionResult<I, P>
    where
        P: SessionProtocol<OwnedConnection<I>>,
    {
        protocol
            .enter(OwnedConnection::new(self))
            .map_err(|(error, carrier)| (error, carrier.into_connection()))
    }
}
