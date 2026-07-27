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
    neutron: neutron::Connection,
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
        let neutron = neutron::Connection::open_in_memory().context(OpenSnafu)?;
        neutron.create_persistent_catalog().context(AdditionSnafu)?;
        Ok(Self::from_neutron(neutron))
    }

    /// Loads and validates persistent Nucleus state from a database image.
    ///
    /// This validates structure and addition relations; it does not establish
    /// trust in the image or its signer.
    ///
    /// # Errors
    ///
    /// Returns an error when deserialization or validation fails.
    pub fn from_image(bytes: &neutron::Bytes) -> Result<Self, DatabaseError> {
        let neutron = neutron::Connection::deserialize(bytes).context(ImageSnafu)?;
        neutron.validate_addition_tables().context(AdditionSnafu)?;
        Ok(Self::from_neutron(neutron))
    }

    /// Serializes the persistent `main` database, excluding connection state.
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
    /// Returns an error when the table cannot be queried.
    pub fn snapshot_is_trusted(
        &self,
        table: &str,
        snapshot: O256,
    ) -> Result<bool, neutron::TrustMetadataError> {
        self.neutron.snapshot_is_trusted(table, snapshot)
    }

    /// Creates and registers an addition table.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid names or database failures.
    pub fn create_addition_table(
        &mut self,
        name: &str,
        layout: neutron::AdditionLayout,
    ) -> Result<neutron::AdditionTable, neutron::AdditionError> {
        self.neutron.create_addition_table(name, layout)
    }

    /// Returns all validated addition tables.
    ///
    /// # Errors
    ///
    /// Returns an error if the catalog, a table, or any fact is invalid.
    pub fn addition_tables(&self) -> Result<Vec<neutron::AdditionTable>, neutron::AdditionError> {
        self.neutron.validate_addition_tables()
    }

    /// Inserts one checked addition fact.
    ///
    /// # Errors
    ///
    /// Returns an error when the fact or table is invalid.
    pub fn insert_addition(
        &self,
        table: &neutron::AdditionTable,
        fact: neutron::AdditionFact,
    ) -> Result<(), neutron::AdditionError> {
        self.neutron.insert_addition(table, fact)
    }

    /// Loads the checked facts in an addition table.
    ///
    /// # Errors
    ///
    /// Returns an error when a row is invalid.
    pub fn addition_facts(
        &self,
        table: &neutron::AdditionTable,
    ) -> Result<Vec<neutron::AdditionFact>, neutron::AdditionError> {
        self.neutron.addition_facts(table)
    }
}

/// Failure to create or import persistent Nucleus state.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DatabaseError {
    /// A Neutron connection could not be opened.
    #[snafu(display("could not open Nucleus state: {source}"))]
    Open {
        /// Underlying connection failure.
        source: neutron::ConnectionError,
    },

    /// A database image could not be installed.
    #[snafu(display("could not load Nucleus state: {source}"))]
    Image {
        /// Underlying image failure.
        source: neutron::ImageError,
    },

    /// Persistent relational state is invalid.
    #[snafu(display("invalid Nucleus relations: {source}"))]
    Addition {
        /// Addition catalog or row failure.
        source: neutron::AdditionError,
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
    fn persists_multiple_addition_geometries() {
        let mut connection = Connection::create_in_memory().expect("create");
        let rowid = connection
            .create_addition_table("small", crate::AdditionLayout::RowId)
            .expect("rowid");
        let compact = connection
            .create_addition_table("large", crate::AdditionLayout::WithoutRowId)
            .expect("without rowid");
        connection
            .insert_addition(&rowid, crate::AdditionFact::sum(1, 2).expect("valid sum"))
            .expect("insert");
        connection
            .insert_addition(
                &compact,
                crate::AdditionFact::sum(i64::MIN, 1).expect("valid sum"),
            )
            .expect("insert");

        let image = connection.serialize().expect("serialize");
        let restored = Connection::from_image(&image).expect("restore");
        assert_eq!(restored.addition_tables().expect("tables").len(), 2);
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
    fn supports_multiple_non_serialized_snapshot_trust_relations() {
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
                .snapshot_is_trusted(neutron::TRUSTED_SNAPSHOTS, snapshot)
                .expect("query default")
        );
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
    }
}
