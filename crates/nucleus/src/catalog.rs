use covalence_neutron as neutron;

use crate::Connection;

/// Failure to create or structurally validate a database-local catalog.
pub type CatalogError = neutron::CatalogError;

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
}

impl Connection {
    /// Opens or creates a catalog in an attached non-temporary database.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing or temporary database, incompatible
    /// existing catalog, or storage failure.
    pub fn catalog(&self, database_name: &str) -> Result<Catalog<'_>, CatalogError> {
        self.neutron
            .catalog(database_name)
            .map(|neutron| Catalog { neutron })
    }
}
