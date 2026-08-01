//! Structurally checked `SQLite` connections.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use covalence_neutron as neutron;

const DATABASES_SQL: &str = "SELECT name FROM pragma_database_list ORDER BY seq";

/// An owning connection whose currently attached databases passed `SQLite`'s
/// structural integrity check.
///
/// This is deliberately a small witness, not a general connection protocol.
/// It exposes no raw SQL or unchecked attachment operation. It says nothing
/// about Nucleus catalogs, signatures, theorem truth, or application data.
#[derive(Debug)]
pub struct WfConnection {
    connection: neutron::Connection,
}

impl WfConnection {
    /// Checks every currently attached database and encloses `connection`.
    ///
    /// `SQLite`'s `integrity_check` establishes structural consistency. Foreign
    /// key constraints and all Nucleus-level meanings are outside this type's
    /// claim.
    ///
    /// # Errors
    ///
    /// Returns an error when attached databases cannot be enumerated, a check
    /// cannot run, or a database reports structural damage.
    pub fn check(connection: neutron::Connection) -> Result<Self, WfError> {
        check_all(&connection)?;
        Ok(Self { connection })
    }

    /// Opens and checks a fresh private in-memory connection.
    ///
    /// # Errors
    ///
    /// Returns an error when Neutron initialization or structural checking
    /// fails.
    pub fn open_in_memory() -> Result<Self, WfError> {
        let connection = neutron::Connection::open_in_memory().context(OpenSnafu)?;
        Self::check(connection)
    }

    /// Erases the structural witness and returns the permeable raw connection.
    #[must_use]
    pub fn into_connection(self) -> neutron::Connection {
        self.connection
    }
}

impl TryFrom<neutron::Connection> for WfConnection {
    type Error = WfError;

    fn try_from(connection: neutron::Connection) -> Result<Self, Self::Error> {
        Self::check(connection)
    }
}

/// Failure to establish `SQLite` structural well-formedness.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WfError {
    /// A fresh Neutron connection could not be opened.
    #[snafu(display("could not open a connection for structural checking: {source}"))]
    Open {
        /// Underlying connection failure.
        source: neutron::ConnectionError,
    },

    /// Attached databases could not be enumerated.
    #[snafu(display("could not enumerate attached SQLite databases: {source}"))]
    Enumerate {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// `SQLite` could not run a structural check.
    #[snafu(display("could not check SQLite database {schema:?}: {source}"))]
    Check {
        /// Attached schema name.
        schema: String,
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// `SQLite` reported structural inconsistencies.
    #[snafu(display("SQLite database {schema:?} is not structurally well-formed: {messages:?}"))]
    Malformed {
        /// Attached schema name.
        schema: String,
        /// Diagnostics returned by `PRAGMA integrity_check`.
        messages: Vec<String>,
    },
}

fn check_all(connection: &neutron::Connection) -> Result<(), WfError> {
    let schemas = connection
        .sqlite()
        .prepare(DATABASES_SQL)
        .context(EnumerateSnafu)?
        .query_map((), |row| row.get::<_, String>(0))
        .context(EnumerateSnafu)?
        .collect::<sqlite::Result<Vec<_>>>()
        .context(EnumerateSnafu)?;

    for schema in schemas {
        check_schema(connection, &schema)?;
    }
    Ok(())
}

fn check_schema(connection: &neutron::Connection, schema: &str) -> Result<(), WfError> {
    let sql = format!("PRAGMA {}.integrity_check", quote_identifier(schema));
    let messages = connection
        .sqlite()
        .prepare(&sql)
        .with_context(|_| CheckSnafu {
            schema: schema.to_owned(),
        })?
        .query_map((), |row| row.get::<_, String>(0))
        .with_context(|_| CheckSnafu {
            schema: schema.to_owned(),
        })?
        .collect::<sqlite::Result<Vec<_>>>()
        .with_context(|_| CheckSnafu {
            schema: schema.to_owned(),
        })?;
    if messages.as_slice() == ["ok"] {
        Ok(())
    } else {
        Err(WfError::Malformed {
            schema: schema.to_owned(),
            messages,
        })
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}
