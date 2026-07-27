use std::{collections::BTreeMap, path::Path};

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_neutron as neutron;

use crate::{SignError, Signer, VerificationError, Verifier};

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
    signers: BTreeMap<O256, Box<dyn Signer>>,
    verifiers: BTreeMap<O256, Box<dyn Verifier>>,
}

impl Connection {
    fn from_neutron(neutron: neutron::Connection) -> Self {
        Self {
            neutron,
            signers: BTreeMap::new(),
            verifiers: BTreeMap::new(),
        }
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

    /// Installs a signing capability for `key`.
    ///
    /// Installing a signer does not make the key trusted.
    ///
    /// # Errors
    ///
    /// Returns an error when connection-local metadata cannot be updated.
    pub fn register_signer(
        &mut self,
        key: O256,
        signer: Box<dyn Signer>,
    ) -> Result<Option<Box<dyn Signer>>, neutron::TrustMetadataError> {
        self.neutron.record_signing_key(key)?;
        Ok(self.signers.insert(key, signer))
    }

    /// Installs and trusts a verification capability for `key`.
    ///
    /// Trusting a verifier does not require possessing the signing key.
    ///
    /// # Errors
    ///
    /// Returns an error when connection-local metadata cannot be updated.
    pub fn trust_verifier(
        &mut self,
        key: O256,
        verifier: Box<dyn Verifier>,
    ) -> Result<Option<Box<dyn Verifier>>, neutron::TrustMetadataError> {
        self.neutron.record_trusted_key(key)?;
        Ok(self.verifiers.insert(key, verifier))
    }

    /// Signs an O256 statement using an installed capability.
    ///
    /// # Errors
    ///
    /// Returns an error when no signer is installed for `key` or signing fails.
    pub fn sign(&self, key: O256, statement: O256) -> Result<neutron::Bytes, SignError> {
        self.signers
            .get(&key)
            .ok_or(SignError::UnknownKey { key })?
            .sign(key, statement)
    }

    /// Verifies a statement using a connection-trusted capability.
    ///
    /// # Errors
    ///
    /// Returns an error when `key` is not trusted or verification fails.
    pub fn verify(
        &self,
        key: O256,
        statement: O256,
        signature: &[u8],
    ) -> Result<(), VerificationError> {
        self.verifiers
            .get(&key)
            .ok_or(VerificationError::UnknownKey { key })?
            .verify(key, statement, signature)
    }

    /// Creates another connection-local trusted-snapshot relation.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid or duplicate name or a database failure.
    pub fn create_trusted_snapshot_table(
        &mut self,
        name: &str,
    ) -> Result<(), neutron::TrustMetadataError> {
        self.neutron.create_trusted_snapshot_table(name)
    }

    /// Records an accepted snapshot and optional evidence hash.
    ///
    /// # Errors
    ///
    /// Returns an error unless `table` is a registered trusted-snapshot table.
    pub fn record_trusted_snapshot(
        &self,
        table: &str,
        snapshot: O256,
        justification: Option<O256>,
    ) -> Result<(), neutron::TrustMetadataError> {
        self.neutron
            .record_trusted_snapshot(table, snapshot, justification)
    }

    /// Tests whether a connection table records a snapshot as trusted.
    ///
    /// # Errors
    ///
    /// Returns an error unless the table is registered or it cannot be queried.
    pub fn snapshot_is_trusted(
        &self,
        table: &str,
        snapshot: O256,
    ) -> Result<bool, neutron::TrustMetadataError> {
        self.neutron.snapshot_is_trusted(table, snapshot)
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
}

#[cfg(test)]
mod tests {
    use covalence_lib_crypto::ed25519::SigningKey;
    use covalence_lib_hash::O256;
    use covalence_neutron as neutron;

    use super::Connection;

    #[test]
    fn opens_through_neutron() {
        let connection = Connection::open_in_memory().expect("open Nucleus connection");
        let _cas: crate::Cas<'_> = connection.cas();
    }

    #[test]
    fn capabilities_and_trust_are_independent_and_connection_local() {
        let signing_key = SigningKey::from_bytes(&[11; 32]);
        let signer = crate::Ed25519Signer::new(signing_key.clone());
        let verifier = crate::Ed25519Verifier::new(signing_key.verifying_key());
        let key = signer.key_id();
        let statement = O256::from_bytes(b"statement");

        let mut connection = Connection::create_in_memory().expect("create");
        connection
            .register_signer(key, Box::new(signer))
            .expect("register signer");
        let signature = connection.sign(key, statement).expect("sign");
        assert!(matches!(
            connection.verify(key, statement, &signature),
            Err(crate::VerificationError::UnknownKey { .. })
        ));

        connection
            .trust_verifier(key, Box::new(verifier))
            .expect("trust verifier");
        connection
            .verify(key, statement, &signature)
            .expect("verify");

        let image = connection.serialize().expect("serialize");
        let restored = Connection::from_image(&image).expect("restore");
        assert!(matches!(
            restored.sign(key, statement),
            Err(crate::SignError::UnknownKey { .. })
        ));
        assert!(matches!(
            restored.verify(key, statement, &signature),
            Err(crate::VerificationError::UnknownKey { .. })
        ));
    }

    #[test]
    fn snapshot_trust_is_not_serialized() {
        let snapshot = O256::from_bytes(b"snapshot");
        let evidence = O256::from_bytes(b"evidence");
        let mut connection = Connection::create_in_memory().expect("create");
        connection
            .create_trusted_snapshot_table("cov_conn_peer_snapshots")
            .expect("create peer table");
        connection
            .record_trusted_snapshot(neutron::TRUSTED_SNAPSHOTS, snapshot, Some(evidence))
            .expect("trust default");
        connection
            .record_trusted_snapshot("cov_conn_peer_snapshots", snapshot, None)
            .expect("trust peer");
        assert!(
            connection
                .snapshot_is_trusted("cov_conn_peer_snapshots", snapshot)
                .expect("query peer")
        );

        let image = connection.serialize().expect("serialize");
        let restored = Connection::from_image(&image).expect("restore");
        assert!(
            !restored
                .snapshot_is_trusted(neutron::TRUSTED_SNAPSHOTS, snapshot)
                .expect("query empty default")
        );
        assert!(matches!(
            restored.snapshot_is_trusted("cov_conn_peer_snapshots", snapshot),
            Err(neutron::TrustMetadataError::NotSnapshotTable { .. })
        ));
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
