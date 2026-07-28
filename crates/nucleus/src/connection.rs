use std::path::Path;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_neutron as neutron;

/// Failure to open a Nucleus connection.
pub type ConnectionError = neutron::ConnectionError;

/// A policy-enforcing connection to Nucleus state.
///
/// This initial wrapper intentionally exposes no access to its underlying
/// Neutron or `SQLite` connections. Later APIs can add operations only when
/// Nucleus can preserve their semantic invariants by construction.
#[derive(Debug)]
pub struct Connection {
    pub(crate) neutron: neutron::Connection,
}

impl Connection {
    fn from_neutron(neutron: neutron::Connection) -> Self {
        Self { neutron }
    }

    /// Opens a database through Neutron and encloses it in the Nucleus boundary.
    ///
    /// # Errors
    ///
    /// Returns an error when the underlying `SQLite` connection cannot be
    /// opened or Neutron's connection metadata cannot be initialized.
    pub fn open(path: impl AsRef<Path>) -> Result<Self, ConnectionError> {
        neutron::Connection::open(path).map(Self::from_neutron)
    }

    /// Opens an in-memory database through Neutron.
    ///
    /// # Errors
    ///
    /// Returns an error when Neutron's connection metadata cannot be
    /// initialized.
    pub fn open_in_memory() -> Result<Self, ConnectionError> {
        neutron::Connection::open_in_memory().map(Self::from_neutron)
    }

    /// Creates fresh in-memory persistent Nucleus state.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection or persistent catalog cannot be
    /// created.
    pub fn create_in_memory() -> Result<Self, DatabaseError> {
        let connection = Self::open_in_memory().context(OpenSnafu)?;
        crate::catalog::create(connection.neutron.sqlite()).context(CreateCatalogSnafu)?;
        Ok(connection)
    }

    /// Loads and validates persistent Nucleus state from a database image.
    ///
    /// This establishes structural validity, not trust in the image or signer.
    ///
    /// # Errors
    ///
    /// Returns an error when deserialization or logical validation fails.
    pub fn from_image(bytes: &neutron::Bytes) -> Result<Self, DatabaseError> {
        let connection =
            Self::from_neutron(neutron::Connection::deserialize(bytes).context(ImageSnafu)?);
        connection.validate().context(ValidateSnafu)?;
        Ok(connection)
    }

    /// Serializes the persistent `main` database.
    ///
    /// Connection-local metadata is excluded by `SQLite` serialization.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot serialize the image.
    pub fn serialize(&self) -> Result<neutron::Bytes, neutron::ImageError> {
        self.neutron.serialize()
    }

    /// Returns the connection's default content-addressed store.
    #[must_use]
    pub const fn cas(&self) -> crate::Cas<'_> {
        self.neutron.cas()
    }

    fn validate(&self) -> Result<(), ValidationError> {
        let sqlite = self.neutron.sqlite();
        for entry in crate::catalog::entries(sqlite).context(CatalogSnafu)? {
            match entry.interpretation.as_str() {
                crate::addition::INTERPRETATION => {
                    crate::addition::validate_table(sqlite, &entry.table).context(AdditionSnafu)?;
                }
                crate::byte_length::INTERPRETATION => {
                    crate::byte_length::validate_table(sqlite, &entry.table)
                        .context(ByteLengthSnafu)?;
                }
                crate::table_meaning::INTERPRETATION => {
                    crate::table_meaning::validate_table(sqlite, &entry.table)
                        .context(TableMeaningSnafu)?;
                }
                _ => {
                    return Err(ValidationError::UnknownInterpretation {
                        table: entry.table,
                        interpretation: entry.interpretation,
                    });
                }
            }
        }
        Ok(())
    }
}

/// Failure to create or load persistent Nucleus state.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DatabaseError {
    /// The Neutron connection could not be opened.
    #[snafu(display("could not open Nucleus database: {source}"))]
    Open {
        /// Underlying failure.
        source: ConnectionError,
    },

    /// A serialized `SQLite` image could not be loaded.
    #[snafu(display("could not deserialize Nucleus database: {source}"))]
    Image {
        /// Underlying failure.
        source: neutron::ImageError,
    },

    /// The persistent catalog could not be created.
    #[snafu(display("could not create Nucleus catalog: {source}"))]
    CreateCatalog {
        /// Underlying failure.
        source: crate::CatalogError,
    },

    /// Persistent logical relations are invalid.
    #[snafu(display("invalid Nucleus relations: {source}"))]
    Validate {
        /// Underlying failure.
        source: ValidationError,
    },
}

/// Failure to validate persistent Nucleus relations.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ValidationError {
    /// The persistent catalog is missing or malformed.
    #[snafu(display("{source}"))]
    Catalog {
        /// Underlying failure.
        source: crate::CatalogError,
    },

    /// A catalog entry has no known logical interpretation.
    #[snafu(display("table {table:?} has unknown interpretation {interpretation:?}"))]
    UnknownInterpretation {
        /// Physical table.
        table: String,
        /// Unrecognized interpretation.
        interpretation: String,
    },

    /// An addition relation is invalid.
    #[snafu(display("{source}"))]
    Addition {
        /// Underlying failure.
        source: crate::AdditionError,
    },

    /// A byte-length relation is invalid.
    #[snafu(display("{source}"))]
    ByteLength {
        /// Underlying failure.
        source: crate::ByteLengthError,
    },

    /// A table-meaning relation is invalid.
    #[snafu(display("{source}"))]
    TableMeaning {
        /// Underlying failure.
        source: crate::TableMeaningError,
    },
}

#[cfg(test)]
mod tests {
    use super::Connection;

    #[test]
    fn opens_through_neutron() {
        let connection = Connection::open_in_memory().expect("open Nucleus connection");
        let _cas: crate::Cas<'_> = connection.cas();
    }
    #[test]
    fn relation_discovery_filters_before_database_validation() {
        let connection = Connection::create_in_memory().expect("create");
        connection
            .create_addition("addition")
            .expect("create addition");
        connection
            .neutron
            .sqlite()
            .execute_batch(
                "CREATE TABLE future (value INTEGER PRIMARY KEY) STRICT;
                 INSERT INTO cov_catalog VALUES ('future', 'cov.future/v0');",
            )
            .expect("add future interpretation");

        assert_eq!(connection.additions().expect("discover additions").len(), 1);

        let image = connection.serialize().expect("serialize");
        assert!(matches!(
            Connection::from_image(&image),
            Err(super::DatabaseError::Validate {
                source: super::ValidationError::UnknownInterpretation { .. }
            })
        ));
    }
}
