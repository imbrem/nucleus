use crate::{Connection, Invariant};

mod private {
    pub trait Sealed {}
}

/// A sealed way for a protocol to retain access to a Nucleus connection.
///
/// Applications can implement open protocol traits for these carriers, but
/// cannot introduce a carrier which bypasses Nucleus's connection ownership
/// rules.
pub trait ConnectionCarrier: private::Sealed {
    /// Invariant carried by the connection.
    type Invariant: Invariant;

    /// Borrows the connection.
    fn connection(&self) -> &Connection<Self::Invariant>;
}

/// A carrier with exclusive access to its connection.
pub trait MutableConnectionCarrier: ConnectionCarrier {
    /// Mutably borrows the connection.
    fn connection_mut(&mut self) -> &mut Connection<Self::Invariant>;
}

/// An immutable borrow used to construct shared views.
#[derive(Debug)]
pub struct SharedConnection<'connection, I: Invariant> {
    connection: &'connection Connection<I>,
}

impl<'connection, I: Invariant> SharedConnection<'connection, I> {
    pub(crate) const fn new(connection: &'connection Connection<I>) -> Self {
        Self { connection }
    }
}

impl<I: Invariant> private::Sealed for SharedConnection<'_, I> {}

impl<I: Invariant> ConnectionCarrier for SharedConnection<'_, I> {
    type Invariant = I;

    fn connection(&self) -> &Connection<I> {
        self.connection
    }
}

/// An exclusive borrow used to construct borrowed protocol values.
#[derive(Debug)]
pub struct BorrowedConnection<'connection, I: Invariant> {
    connection: &'connection mut Connection<I>,
}

impl<'connection, I: Invariant> BorrowedConnection<'connection, I> {
    pub(crate) const fn new(connection: &'connection mut Connection<I>) -> Self {
        Self { connection }
    }
}

impl<I: Invariant> private::Sealed for BorrowedConnection<'_, I> {}

impl<I: Invariant> ConnectionCarrier for BorrowedConnection<'_, I> {
    type Invariant = I;

    fn connection(&self) -> &Connection<I> {
        self.connection
    }
}

impl<I: Invariant> MutableConnectionCarrier for BorrowedConnection<'_, I> {
    fn connection_mut(&mut self) -> &mut Connection<I> {
        self.connection
    }
}

/// An owned connection used by a protocol which outlives its caller's borrow.
#[derive(Debug)]
pub struct OwnedConnection<I: Invariant> {
    connection: Connection<I>,
}

impl<I: Invariant> OwnedConnection<I> {
    pub(crate) const fn new(connection: Connection<I>) -> Self {
        Self { connection }
    }

    /// Recovers the owned connection.
    ///
    /// Active protocol values expose this only through their explicit
    /// `finish` operations, after restoring their protocol invariants.
    #[must_use]
    pub fn into_connection(self) -> Connection<I> {
        self.connection
    }
}

impl<I: Invariant> private::Sealed for OwnedConnection<I> {}

impl<I: Invariant> ConnectionCarrier for OwnedConnection<I> {
    type Invariant = I;

    fn connection(&self) -> &Connection<I> {
        &self.connection
    }
}

impl<I: Invariant> MutableConnectionCarrier for OwnedConnection<I> {
    fn connection_mut(&mut self) -> &mut Connection<I> {
        &mut self.connection
    }
}
