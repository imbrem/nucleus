use std::convert::Infallible;

use crate::{
    Connection, Invariant, MutableConnectionCarrier, OwnedConnection, Reader, ViewProtocol,
};

/// A protocol which withholds every mutating operation on a connection.
///
/// `ReadOnly` requires an exclusive borrow or ownership of the connection. Its
/// resulting capability exposes only scoped [`Reader`] values, so changes
/// observed while it is active must originate outside this connection.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReadOnly;

impl<C: MutableConnectionCarrier> ViewProtocol<C> for ReadOnly {
    type Error = Infallible;
    type View = ReadOnlyView<C>;

    fn view(self, carrier: C) -> Result<Self::View, (Infallible, C)> {
        Ok(ReadOnlyView { carrier })
    }
}

/// An exclusively held connection exposing only scoped reads.
#[derive(Debug)]
pub struct ReadOnlyView<C: MutableConnectionCarrier> {
    carrier: C,
}

impl<C: MutableConnectionCarrier> ReadOnlyView<C> {
    /// Creates a reader scoped to one attached database.
    #[must_use]
    pub fn database_reader(&mut self, database: impl Into<String>) -> Reader<'_> {
        Reader::database(self.carrier.connection_mut(), database)
    }

    /// Creates a reader scoped to one table in an attached database.
    #[must_use]
    pub fn table_reader(
        &mut self,
        database: impl Into<String>,
        table: impl Into<String>,
    ) -> Reader<'_> {
        Reader::table(self.carrier.connection_mut(), database, table)
    }

    /// Ends the protocol and returns its connection carrier.
    #[must_use]
    pub fn finish(self) -> C {
        self.carrier
    }
}

impl<I: Invariant> ReadOnlyView<OwnedConnection<I>> {
    /// Ends an owned protocol and recovers the connection.
    #[must_use]
    pub fn into_connection(self) -> Connection<I> {
        self.carrier.into_connection()
    }
}
