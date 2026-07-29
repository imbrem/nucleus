use covalence_lib_error::snafu::Snafu;
use covalence_neutron as neutron;

use crate::Connection;

/// Failure to access a trusted database-local catalog.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CatalogError {
    /// Neutron could not create, validate, or inspect the catalog.
    #[snafu(display("could not access database catalog: {source}"))]
    Neutron { source: neutron::CatalogError },

    /// Nucleus only interprets catalogs in trusted, exclusively owned databases.
    #[snafu(display("database {database_name:?} is not trusted and exclusive"))]
    NotTrustedExclusive { database_name: String },
}

/// Policy boundary around a database-local Neutron catalog.
///
/// This first slice exposes no operation that can assign a meaning. Later
/// Nucleus relation APIs consume this capability and register only meanings
/// whose invariants they preserve.
#[derive(Debug)]
pub struct Catalog<'conn> {
    pub(crate) neutron: neutron::Catalog<'conn>,
}

impl Catalog<'_> {
    /// Returns the containing database schema.
    #[must_use]
    pub fn database_name(&self) -> &str {
        self.neutron.database_name()
    }

    /// Tests whether this is the connection-local catalog.
    #[must_use]
    pub fn is_conn(&self) -> bool {
        self.neutron.is_conn()
    }

    /// Tests whether this is the primary database's catalog.
    #[must_use]
    pub fn is_main(&self) -> bool {
        self.neutron.is_main()
    }
}

impl Connection {
    /// Opens or creates a catalog for an attached database or the connection.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing database, incompatible existing catalog,
    /// insufficient trust or exclusivity, or storage failure.
    pub fn catalog(&self, database_name: &str) -> Result<Catalog<'_>, CatalogError> {
        let neutron = self
            .neutron
            .catalog(database_name)
            .map_err(|source| CatalogError::Neutron { source })?;
        if !neutron
            .is_trusted_exclusive()
            .map_err(|source| CatalogError::Neutron { source })?
        {
            return Err(CatalogError::NotTrustedExclusive {
                database_name: database_name.to_owned(),
            });
        }
        Ok(Catalog { neutron })
    }
}

#[cfg(test)]
mod tests {
    use super::{CatalogError, Connection};

    #[test]
    fn rejects_a_database_without_trusted_exclusive_access() {
        let sqlite = covalence_lib_sqlite::Connection::open_in_memory().unwrap();
        let neutron = covalence_neutron::Connection::from_sqlite(sqlite).unwrap();
        let connection = Connection { neutron };

        assert!(matches!(
            connection.catalog("main"),
            Err(CatalogError::NotTrustedExclusive { database_name })
                if database_name == "main"
        ));
    }
}
