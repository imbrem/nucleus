use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Connection, Invariant, SessionProtocol, Standard};

const EMPTY_VISIBILITY_SQL: &str = include_str!("../sql/session/empty_visibility.sql");
const CLEAR_VISIBILITY_SQL: &str = include_str!("../sql/session/clear_visibility.sql");

mod private {
    pub trait Sealed {}
}

/// An invariant which admits the standard visibility registry protocol.
pub trait RegistryInvariant: Invariant + private::Sealed {}

impl private::Sealed for Standard {}
impl RegistryInvariant for Standard {}

/// The standard database/table visibility protocol.
#[derive(Clone, Copy, Debug, Default)]
pub struct Registry;

/// Exclusive access to a connection following the standard registry protocol.
#[derive(Debug)]
pub struct RegistrySession<'conn, I: RegistryInvariant> {
    pub(crate) connection: &'conn mut Connection<I>,
}

impl<I: RegistryInvariant> SessionProtocol<I> for Registry {
    type Error = RegistryError;
    type Session<'a>
        = RegistrySession<'a, I>
    where
        I: 'a;

    fn enter(self, connection: &mut Connection<I>) -> Result<Self::Session<'_>, Self::Error> {
        let visible = connection
            .sqlite()
            .query_row(EMPTY_VISIBILITY_SQL, (), |row| row.get::<_, i64>(0))
            .context(StorageSnafu)?;
        if visible != 0 {
            return Err(RegistryError::AlreadyActive);
        }
        Ok(RegistrySession { connection })
    }
}

impl<I: RegistryInvariant> RegistrySession<'_, I> {
    /// Borrows the invariant maintained by this session.
    #[must_use]
    pub const fn invariant(&self) -> &I {
        self.connection.invariant()
    }
}

impl<I: RegistryInvariant> Drop for RegistrySession<'_, I> {
    fn drop(&mut self) {
        self.connection
            .sqlite()
            .execute_batch(CLEAR_VISIBILITY_SQL)
            .expect("standard visibility tables remain writable during a registry session");
    }
}

/// Failure to enter or maintain the standard registry protocol.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RegistryError {
    /// Visibility rows from another active or interrupted session exist.
    #[snafu(display("the connection visibility registry is not empty"))]
    AlreadyActive,

    /// Visibility state could not be accessed.
    #[snafu(display("could not access the connection visibility registry: {source}"))]
    Storage { source: sqlite::Error },
}

#[cfg(test)]
mod tests {
    use super::*;

    const ADD_VISIBLE_DATABASE: &str = "
        INSERT INTO temp.cov_conn_dbvis
            (db_name, lock_type, ref_count, owner_type)
        VALUES ('main', 'EXCLUSIVE', 1, 'test')
    ";

    #[test]
    fn a_session_clears_its_visibility_rows_on_drop() {
        let mut connection = Connection::open_in_memory().unwrap();
        {
            let session = connection.enter(Registry).unwrap();
            session
                .connection
                .sqlite()
                .execute(ADD_VISIBLE_DATABASE, ())
                .unwrap();
        }

        connection.enter(Registry).unwrap();
    }

    #[test]
    fn a_session_rejects_preexisting_visibility_rows() {
        let mut connection = Connection::open_in_memory().unwrap();
        connection
            .sqlite()
            .execute(ADD_VISIBLE_DATABASE, ())
            .unwrap();

        assert!(matches!(
            connection.enter(Registry),
            Err(RegistryError::AlreadyActive)
        ));
    }
}
