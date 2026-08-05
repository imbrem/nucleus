use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{
    AuthenticatedValidatedHolImage, Hol, HolDatabaseRef, ImportError, ImportId, MetadataError,
    MetadataTarget, MetadataValue, Operation, Policy, ValidatedHolImage,
};
use crate::{AuthenticatedSnapshotClaim, Connection};

const CONNECTION_TRUST_SCHEMA: &str = "
CREATE TEMP TABLE cov_conn_hol_trusted_snapshot_signer (
    signer_hash BLOB PRIMARY KEY,
    public_key BLOB NOT NULL UNIQUE,
    CHECK (typeof(signer_hash) = 'blob' AND length(signer_hash) = 32),
    CHECK (typeof(public_key) = 'blob' AND length(public_key) = 32)
) STRICT, WITHOUT ROWID;

CREATE TEMP TABLE cov_conn_hol_accepted_snapshot (
    schema_hash BLOB NOT NULL,
    image_hash BLOB NOT NULL,
    signer_hash BLOB NOT NULL,
    signature BLOB NOT NULL,
    CHECK (typeof(schema_hash) = 'blob' AND length(schema_hash) = 32),
    CHECK (typeof(image_hash) = 'blob' AND length(image_hash) = 32),
    CHECK (typeof(signer_hash) = 'blob' AND length(signer_hash) = 32),
    CHECK (typeof(signature) = 'blob' AND length(signature) = 64),
    PRIMARY KEY (schema_hash, image_hash, signer_hash)
) STRICT, WITHOUT ROWID;
";

/// Database-local identity of one persisted accepted-import assumption.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TrustedImportId(i64);

impl TrustedImportId {
    /// Constructs a lookup handle from its stored integer.
    #[must_use]
    pub const fn from_i64(id: i64) -> Self {
        Self(id)
    }

    /// Returns the stored integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// Read-only view of one persistent accepted-import assumption.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrustedImportView {
    /// Exact inert import reference whose attestation was accepted.
    pub import: ImportId,
    /// Signing-key identity recorded with the assumption.
    pub signer: O256,
    /// Exact Ed25519 public key recorded with the assumption.
    pub public_key: [u8; 32],
    /// Exact Ed25519 signature recorded with the assumption.
    pub signature: Vec<u8>,
}

/// Connection-branded evidence that exact validated bytes match one persistent trust assumption.
///
/// This capability keeps its originating connection mutably borrowed. It does not expose imported
/// theorem authority; later scoped readers may consume it to expose validated immutable data.
pub struct MatchedTrustedHolImage<'connection, P> {
    connection: &'connection mut Connection<Hol<P>>,
    trusted_import: TrustedImportId,
    import: ImportId,
    image: AuthenticatedValidatedHolImage,
}

impl<'connection, P> MatchedTrustedHolImage<'connection, P> {
    /// Returns the exact persistent assumption matched by this capability.
    #[must_use]
    pub const fn trusted_import(&self) -> TrustedImportId {
        self.trusted_import
    }

    /// Returns the inert import-directory row named by the assumption.
    #[must_use]
    pub const fn import(&self) -> ImportId {
        self.import
    }

    /// Returns the independently validated exact image.
    #[must_use]
    pub const fn image(&self) -> &ValidatedHolImage {
        self.image.image()
    }

    /// Returns the authenticated signer identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.image.claim().signer()
    }

    pub(super) fn into_parts(
        self,
    ) -> (
        &'connection mut Connection<Hol<P>>,
        TrustedImportId,
        ImportId,
        AuthenticatedValidatedHolImage,
    ) {
        (
            self.connection,
            self.trusted_import,
            self.import,
            self.image,
        )
    }
}

pub(super) fn install_connection_trust_schema(
    connection: &sqlite::Connection,
) -> sqlite::Result<()> {
    connection.execute_batch(CONNECTION_TRUST_SCHEMA)
}

impl<P: Policy> Connection<Hol<P>> {
    /// Trusts an authenticated signer for the fixed schema-qualified snapshot assertion.
    ///
    /// The trust root is local to this connection's `temp` database. It is never serialized with
    /// `main`, and it does not accept a snapshot, register an import, validate bytes, or grant HOL
    /// authority.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the operation, the connection-local table conflicts with
    /// the authenticated signer identity, or `SQLite` rejects the transaction.
    pub fn trust_snapshot_signer(
        &mut self,
        snapshot: &AuthenticatedSnapshotClaim,
    ) -> Result<(), SnapshotTrustError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::TrustSnapshotSigner)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        transaction.execute(
            "INSERT INTO temp.cov_conn_hol_trusted_snapshot_signer(signer_hash, public_key)
             VALUES (?1, ?2)
             ON CONFLICT(signer_hash) DO NOTHING",
            sqlite::params![snapshot.signer().as_ref(), snapshot.public_key().as_slice()],
        )?;
        let stored = trusted_signer_key(&transaction, snapshot.signer())?
            .ok_or(SnapshotTrustError::ConflictingSigner(snapshot.signer()))?;
        if stored.as_slice() != snapshot.public_key() {
            return Err(SnapshotTrustError::ConflictingSigner(snapshot.signer()));
        }
        transaction.commit()?;
        Ok(())
    }

    /// Reports whether this connection trusts the authenticated signer for snapshot assertions.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the stored row conflicts with the authenticated
    /// identity, or `SQLite` rejects the query.
    pub fn snapshot_signer_is_trusted(
        &mut self,
        snapshot: &AuthenticatedSnapshotClaim,
    ) -> Result<bool, SnapshotTrustError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadTrustedSnapshotSigner)?;
        let Some(stored) = trusted_signer_key(neutron.sqlite(), snapshot.signer())? else {
            return Ok(false);
        };
        if stored.as_slice() != snapshot.public_key() {
            return Err(SnapshotTrustError::ConflictingSigner(snapshot.signer()));
        }
        Ok(true)
    }

    /// Explicitly accepts one exact authenticated snapshot assertion from a trusted signer.
    ///
    /// Acceptance is connection-local policy state. This method does not parse the bytes, validate
    /// a schema, register an import, attach a database, or expose imported HOL values.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the operation, the signer is not trusted on this
    /// connection, stored evidence conflicts, or `SQLite` rejects the transaction.
    pub fn accept_authenticated_snapshot(
        &mut self,
        snapshot: &AuthenticatedSnapshotClaim,
    ) -> Result<(), SnapshotTrustError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::AcceptAuthenticatedSnapshot)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_trusted_signer(&transaction, snapshot)?;
        transaction.execute(
            "INSERT INTO temp.cov_conn_hol_accepted_snapshot(
                 schema_hash, image_hash, signer_hash, signature
             ) VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(schema_hash, image_hash, signer_hash) DO NOTHING",
            sqlite::params![
                snapshot.schema().as_ref(),
                snapshot.image().as_ref(),
                snapshot.signer().as_ref(),
                snapshot.signature()
            ],
        )?;
        require_matching_acceptance(&transaction, snapshot)?;
        transaction.commit()?;
        Ok(())
    }

    /// Reports whether this exact authenticated snapshot assertion was explicitly accepted.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, stored evidence conflicts, or `SQLite` rejects
    /// the query.
    pub fn authenticated_snapshot_is_accepted(
        &mut self,
        snapshot: &AuthenticatedSnapshotClaim,
    ) -> Result<bool, SnapshotTrustError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadAcceptedSnapshot)?;
        let stored = accepted_signature(neutron.sqlite(), snapshot)?;
        match stored {
            None => Ok(false),
            Some(stored) if stored.as_slice() == snapshot.signature() => Ok(true),
            Some(_) => Err(SnapshotTrustError::ConflictingSnapshot {
                schema: snapshot.schema(),
                image: snapshot.image(),
                signer: snapshot.signer(),
            }),
        }
    }

    /// Reports whether any trusted signer assertion for these exact coordinates was accepted.
    ///
    /// The inert schema/image pair need not have been fetched, parsed, registered as an import, or
    /// used as logical authority.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or `SQLite` rejects the query.
    pub fn snapshot_reference_is_accepted(
        &mut self,
        database: HolDatabaseRef,
    ) -> Result<bool, SnapshotTrustError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadAcceptedSnapshot)?;
        Ok(neutron.sqlite().query_row(
            "SELECT EXISTS(
                 SELECT 1 FROM temp.cov_conn_hol_accepted_snapshot
                 WHERE schema_hash = ?1 AND image_hash = ?2
             )",
            sqlite::params![database.schema().as_ref(), database.image().as_ref()],
            |row| row.get(0),
        )?)
    }

    /// Persists an auditable accepted assumption for one exact registered import.
    ///
    /// This requires the hash-first authenticated claim, its connection-local trusted signer, and
    /// an exact prior connection-local acceptance of that claim. It does not fetch, parse, attach,
    /// or expose the imported database.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies persistence, the import coordinates differ from the
    /// claim, its signer/claim was not explicitly accepted on this connection, IDs are exhausted,
    /// evidence conflicts, or `SQLite` rejects the transaction.
    pub fn accept_trusted_import(
        &mut self,
        import: ImportId,
        claim: &AuthenticatedSnapshotClaim,
    ) -> Result<TrustedImportId, TrustedImportError> {
        self.accept_trusted_import_with_metadata(import, claim, &[])
    }

    /// Persists an accepted import assumption and user metadata atomically.
    ///
    /// Repeating the exact assumption is idempotent; supplied metadata replaces selected columns.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies either required operation, the import/claim/trust
    /// evidence is invalid, metadata is invalid, IDs are exhausted, or `SQLite` rejects the
    /// transaction.
    pub fn accept_trusted_import_with_metadata(
        &mut self,
        import: ImportId,
        claim: &AuthenticatedSnapshotClaim,
        metadata: &[(&str, MetadataValue)],
    ) -> Result<TrustedImportId, TrustedImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_trusted_import(&mut hol.policy, Operation::AcceptTrustedImport)?;
        if !metadata.is_empty() && !hol.policy.allows(Operation::WriteMetadata) {
            return Err(TrustedImportError::Metadata(MetadataError::Denied(
                Operation::WriteMetadata,
            )));
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let expected = super::import::read_import(&transaction, import)?.database;
        let actual = HolDatabaseRef::new(claim.schema(), claim.image());
        if expected != actual {
            return Err(TrustedImportError::ImportClaimMismatch {
                import,
                coordinates: Box::new((expected, actual)),
            });
        }
        require_trusted_signer(&transaction, claim)?;
        require_matching_acceptance(&transaction, claim)?;
        let existing = find_trusted_import(&transaction, import, claim.signer())?;
        let id = if let Some((id, public_key, signature)) = existing {
            if public_key.as_slice() != claim.public_key() || signature != claim.signature() {
                return Err(TrustedImportError::ConflictingAttestation {
                    import,
                    signer: claim.signer(),
                });
            }
            id
        } else {
            let maximum = transaction.query_row(
                "SELECT max(trusted_import_id) FROM hol_trusted_import",
                [],
                |row| row.get::<_, Option<i64>>(0),
            )?;
            let id = TrustedImportId(
                maximum
                    .unwrap_or(-1)
                    .checked_add(1)
                    .ok_or(TrustedImportError::IdOverflow)?,
            );
            transaction.execute(
                "INSERT INTO hol_trusted_import(
                     trusted_import_id, import_id, signer_hash, public_key, signature
                 ) VALUES (?1, ?2, ?3, ?4, ?5)",
                sqlite::params![
                    id.get(),
                    import.get(),
                    claim.signer().as_ref(),
                    claim.public_key().as_slice(),
                    claim.signature()
                ],
            )?;
            id
        };
        super::write_target_metadata(
            &transaction,
            &hol.schema,
            MetadataTarget::trusted_import(id),
            metadata,
        )?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads one persistent accepted-import assumption by its local ID.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is absent or malformed, or `SQLite`
    /// rejects the query.
    pub fn trusted_import(
        &mut self,
        id: TrustedImportId,
    ) -> Result<TrustedImportView, TrustedImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_trusted_import(&mut hol.policy, Operation::ReadTrustedImport)?;
        read_trusted_import(neutron.sqlite(), id)
    }

    /// Matches exact authenticated and validated bytes to one persistent accepted import.
    ///
    /// This is the connection-local authority transition from portable detached evidence to a
    /// branded capability. It does not consult ephemeral `temp` trust state, attach the image,
    /// expose imported values, or treat imported judgements as true.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies matching, the persistent row is absent or corrupt, its
    /// import is orphaned, or any stored coordinate/key/signature differs from the evidence.
    pub fn match_trusted_import_image(
        &mut self,
        id: TrustedImportId,
        image: AuthenticatedValidatedHolImage,
    ) -> Result<MatchedTrustedHolImage<'_, P>, TrustedImportImageError> {
        let import = {
            let (neutron, hol) = self.parts_mut();
            if !hol.policy.allows(Operation::MatchTrustedImportImage) {
                return Err(TrustedImportImageError::Denied(
                    Operation::MatchTrustedImportImage,
                ));
            }
            let row = neutron
                .sqlite()
                .query_row(
                    "SELECT ti.import_id, i.schema_hash, i.image_hash, ti.signer_hash,
                            ti.public_key, ti.signature
                     FROM hol_trusted_import AS ti
                     LEFT JOIN hol_import AS i ON i.import_id = ti.import_id
                     WHERE ti.trusted_import_id = ?1",
                    [id.get()],
                    |row| {
                        Ok((
                            ImportId::from_i64(row.get(0)?),
                            row.get::<_, Option<Vec<u8>>>(1)?,
                            row.get::<_, Option<Vec<u8>>>(2)?,
                            row.get::<_, Vec<u8>>(3)?,
                            row.get::<_, Vec<u8>>(4)?,
                            row.get::<_, Vec<u8>>(5)?,
                        ))
                    },
                )
                .optional()?
                .ok_or(TrustedImportImageError::Unknown(id))?;
            let (Some(schema_bytes), Some(image_bytes)) = (&row.1, &row.2) else {
                return Err(TrustedImportImageError::Orphan(id));
            };
            let schema = fixed_o256(schema_bytes, id)?;
            let image_hash = fixed_o256(image_bytes, id)?;
            let signer = fixed_o256(&row.3, id)?;
            let public_key = <[u8; 32]>::try_from(row.4.as_slice())
                .map_err(|_| TrustedImportImageError::Corrupt(id))?;
            if row.5.len() != 64 {
                return Err(TrustedImportImageError::Corrupt(id));
            }
            let claim = image.claim();
            let validated = image.image();
            if schema != claim.schema() || schema != validated.schema() {
                return Err(TrustedImportImageError::SchemaMismatch(id));
            }
            if image_hash != claim.image() || image_hash != validated.hash() {
                return Err(TrustedImportImageError::ImageMismatch(id));
            }
            if signer != claim.signer() {
                return Err(TrustedImportImageError::SignerMismatch(id));
            }
            if public_key.as_slice() != claim.public_key() {
                return Err(TrustedImportImageError::PublicKeyMismatch(id));
            }
            if row.5.as_slice() != claim.signature() {
                return Err(TrustedImportImageError::SignatureMismatch(id));
            }
            row.0
        };
        Ok(MatchedTrustedHolImage {
            connection: self,
            trusted_import: id,
            import,
            image,
        })
    }
}

fn fixed_o256(bytes: &[u8], id: TrustedImportId) -> Result<O256, TrustedImportImageError> {
    <[u8; 32]>::try_from(bytes)
        .map(O256::from_array)
        .map_err(|_| TrustedImportImageError::Corrupt(id))
}

fn authorize_trusted_import(
    policy: &mut impl Policy,
    operation: Operation,
) -> Result<(), TrustedImportError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(TrustedImportError::Denied(operation))
    }
}

type StoredTrustedImport = (TrustedImportId, Vec<u8>, Vec<u8>);

fn find_trusted_import(
    connection: &sqlite::Connection,
    import: ImportId,
    signer: O256,
) -> sqlite::Result<Option<StoredTrustedImport>> {
    connection
        .query_row(
            "SELECT trusted_import_id, public_key, signature
             FROM hol_trusted_import
             WHERE import_id = ?1 AND signer_hash = ?2",
            sqlite::params![import.get(), signer.as_ref()],
            |row| Ok((TrustedImportId(row.get(0)?), row.get(1)?, row.get(2)?)),
        )
        .optional()
}

fn read_trusted_import(
    connection: &sqlite::Connection,
    id: TrustedImportId,
) -> Result<TrustedImportView, TrustedImportError> {
    let row = connection
        .query_row(
            "SELECT import_id, signer_hash, public_key, signature
             FROM hol_trusted_import WHERE trusted_import_id = ?1",
            [id.get()],
            |row| {
                Ok((
                    ImportId::from_i64(row.get(0)?),
                    row.get::<_, Vec<u8>>(1)?,
                    row.get::<_, Vec<u8>>(2)?,
                    row.get::<_, Vec<u8>>(3)?,
                ))
            },
        )
        .optional()?
        .ok_or(TrustedImportError::UnknownTrustedImport(id))?;
    let signer = <[u8; 32]>::try_from(row.1)
        .map(O256::from_array)
        .map_err(|_| TrustedImportError::CorruptTrustedImport(id))?;
    let public_key =
        <[u8; 32]>::try_from(row.2).map_err(|_| TrustedImportError::CorruptTrustedImport(id))?;
    if row.3.len() != 64 {
        return Err(TrustedImportError::CorruptTrustedImport(id));
    }
    Ok(TrustedImportView {
        import: row.0,
        signer,
        public_key,
        signature: row.3,
    })
}

fn authorize(policy: &mut impl Policy, operation: Operation) -> Result<(), SnapshotTrustError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(SnapshotTrustError::Denied(operation))
    }
}

fn trusted_signer_key(
    connection: &sqlite::Connection,
    signer: O256,
) -> sqlite::Result<Option<Vec<u8>>> {
    connection
        .query_row(
            "SELECT public_key
             FROM temp.cov_conn_hol_trusted_snapshot_signer
             WHERE signer_hash = ?1",
            [signer.as_ref()],
            |row| row.get(0),
        )
        .optional()
}

fn require_trusted_signer(
    connection: &sqlite::Connection,
    snapshot: &AuthenticatedSnapshotClaim,
) -> Result<(), SnapshotTrustError> {
    let Some(stored) = trusted_signer_key(connection, snapshot.signer())? else {
        return Err(SnapshotTrustError::UntrustedSigner(snapshot.signer()));
    };
    if stored.as_slice() != snapshot.public_key() {
        return Err(SnapshotTrustError::ConflictingSigner(snapshot.signer()));
    }
    Ok(())
}

fn accepted_signature(
    connection: &sqlite::Connection,
    snapshot: &AuthenticatedSnapshotClaim,
) -> sqlite::Result<Option<Vec<u8>>> {
    connection
        .query_row(
            "SELECT signature
             FROM temp.cov_conn_hol_accepted_snapshot
             WHERE schema_hash = ?1 AND image_hash = ?2 AND signer_hash = ?3",
            sqlite::params![
                snapshot.schema().as_ref(),
                snapshot.image().as_ref(),
                snapshot.signer().as_ref()
            ],
            |row| row.get(0),
        )
        .optional()
}

fn require_matching_acceptance(
    connection: &sqlite::Connection,
    snapshot: &AuthenticatedSnapshotClaim,
) -> Result<(), SnapshotTrustError> {
    match accepted_signature(connection, snapshot)? {
        Some(stored) if stored.as_slice() == snapshot.signature() => Ok(()),
        None => Err(SnapshotTrustError::SnapshotNotAccepted {
            schema: snapshot.schema(),
            image: snapshot.image(),
            signer: snapshot.signer(),
        }),
        Some(_) => Err(SnapshotTrustError::ConflictingSnapshot {
            schema: snapshot.schema(),
            image: snapshot.image(),
            signer: snapshot.signer(),
        }),
    }
}

/// Failure to consult or mutate connection-local snapshot trust state.
#[derive(Debug)]
pub enum SnapshotTrustError {
    /// The connection policy denied the operation before trust state was inspected.
    Denied(Operation),
    /// The snapshot signer is not a connection-local trust root.
    UntrustedSigner(O256),
    /// Stored public-key material conflicts with the authenticated signer identity.
    ConflictingSigner(O256),
    /// The exact authenticated assertion was not explicitly accepted on this connection.
    SnapshotNotAccepted {
        schema: O256,
        image: O256,
        signer: O256,
    },
    /// Stored accepted evidence conflicts with the authenticated signature.
    ConflictingSnapshot {
        schema: O256,
        image: O256,
        signer: O256,
    },
    /// `SQLite` rejected the trust-table operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for SnapshotTrustError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UntrustedSigner(signer) => {
                write!(formatter, "snapshot signer {signer} is not trusted")
            }
            Self::ConflictingSigner(signer) => {
                write!(
                    formatter,
                    "snapshot signer {signer} has conflicting key material"
                )
            }
            Self::SnapshotNotAccepted {
                schema,
                image,
                signer,
            } => write!(
                formatter,
                "snapshot ({schema}, {image}, {signer}) was not explicitly accepted"
            ),
            Self::ConflictingSnapshot {
                schema,
                image,
                signer,
            } => write!(
                formatter,
                "accepted snapshot ({schema}, {image}, {signer}) has conflicting evidence"
            ),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for SnapshotTrustError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<sqlite::Error> for SnapshotTrustError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to match validated bytes to a persistent trusted-import assumption.
#[derive(Debug)]
pub enum TrustedImportImageError {
    /// Policy denied the authority transition before database state was inspected.
    Denied(Operation),
    /// The requested persistent assumption is absent.
    Unknown(TrustedImportId),
    /// The persistent assumption references an absent import-directory row.
    Orphan(TrustedImportId),
    /// Stored fixed-width evidence is corrupt.
    Corrupt(TrustedImportId),
    /// The stored schema differs from the authenticated validated image.
    SchemaMismatch(TrustedImportId),
    /// The stored image hash differs from the authenticated validated image.
    ImageMismatch(TrustedImportId),
    /// The stored signer differs from the authenticated claim.
    SignerMismatch(TrustedImportId),
    /// The stored public key differs from the authenticated claim.
    PublicKeyMismatch(TrustedImportId),
    /// The stored signature differs from the authenticated claim.
    SignatureMismatch(TrustedImportId),
    /// `SQLite` rejected the joined read.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TrustedImportImageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::Unknown(id) => write!(
                formatter,
                "trusted-import assumption {} is absent",
                id.get()
            ),
            Self::Orphan(id) => write!(
                formatter,
                "trusted-import assumption {} is orphaned",
                id.get()
            ),
            Self::Corrupt(id) => write!(
                formatter,
                "trusted-import assumption {} has corrupt evidence",
                id.get()
            ),
            Self::SchemaMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has a different schema",
                id.get()
            ),
            Self::ImageMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has a different image hash",
                id.get()
            ),
            Self::SignerMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has a different signer",
                id.get()
            ),
            Self::PublicKeyMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has a different public key",
                id.get()
            ),
            Self::SignatureMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has a different signature",
                id.get()
            ),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TrustedImportImageError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<sqlite::Error> for TrustedImportImageError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to persist or inspect an accepted import assumption.
#[derive(Debug)]
pub enum TrustedImportError {
    /// The connection policy denied the operation before database state was inspected.
    Denied(Operation),
    /// The registered import and authenticated claim name different schema/image coordinates.
    ImportClaimMismatch {
        import: ImportId,
        coordinates: Box<(HolDatabaseRef, HolDatabaseRef)>,
    },
    /// Existing persistent evidence conflicts with the authenticated claim.
    ConflictingAttestation { import: ImportId, signer: O256 },
    /// The local trusted-import ID is absent.
    UnknownTrustedImport(TrustedImportId),
    /// The stored trusted-import row has an invalid fixed-width representation.
    CorruptTrustedImport(TrustedImportId),
    /// No further non-negative trusted-import ID can be allocated.
    IdOverflow,
    /// Import lookup failed.
    Import(ImportError),
    /// Connection-local signer trust failed.
    Trust(SnapshotTrustError),
    /// User metadata failed.
    Metadata(MetadataError),
    /// `SQLite` rejected the operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TrustedImportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::ImportClaimMismatch {
                import,
                coordinates,
            } => write!(
                formatter,
                "import {} names ({}, {}), not authenticated claim ({}, {})",
                import.get(),
                coordinates.0.schema(),
                coordinates.0.image(),
                coordinates.1.schema(),
                coordinates.1.image()
            ),
            Self::ConflictingAttestation { import, signer } => write!(
                formatter,
                "import {} has conflicting evidence for signer {signer}",
                import.get()
            ),
            Self::UnknownTrustedImport(id) => {
                write!(formatter, "unknown trusted-import assumption {}", id.get())
            }
            Self::CorruptTrustedImport(id) => {
                write!(
                    formatter,
                    "trusted-import assumption {} is corrupt",
                    id.get()
                )
            }
            Self::IdOverflow => formatter.write_str("trusted-import ID overflow"),
            Self::Import(error) => error.fmt(formatter),
            Self::Trust(error) => error.fmt(formatter),
            Self::Metadata(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TrustedImportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Import(error) => Some(error),
            Self::Trust(error) => Some(error),
            Self::Metadata(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ImportError> for TrustedImportError {
    fn from(error: ImportError) -> Self {
        Self::Import(error)
    }
}

impl From<SnapshotTrustError> for TrustedImportError {
    fn from(error: SnapshotTrustError) -> Self {
        Self::Trust(error)
    }
}

impl From<MetadataError> for TrustedImportError {
    fn from(error: MetadataError) -> Self {
        Self::Metadata(error)
    }
}

impl From<sqlite::Error> for TrustedImportError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_lib_crypto::ed25519::SigningKey;

    use crate::{
        AllowAll, Ed25519Signer, HolSchema, Kernel, MetadataTable, MetadataType,
        SignedSnapshotAttestation, SignedSnapshotEnvelope, Signer as _,
        schema_valid_snapshot_statement,
    };

    fn authenticated(kernel: &Kernel) -> AuthenticatedSnapshotClaim {
        let mut source = kernel.open_hol(AllowAll).unwrap();
        let signed = kernel.export_hol(&mut source).unwrap();
        let attestation = signed.attestation();
        SignedSnapshotEnvelope::new(
            signed.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap()
        .into_claim()
    }

    fn authenticated_validated(kernel: &Kernel) -> AuthenticatedValidatedHolImage {
        let mut source = kernel.open_hol(AllowAll).unwrap();
        source.insert_bool_term(true).unwrap();
        let signed = kernel.export_hol(&mut source).unwrap();
        let attestation = signed.attestation();
        let authenticated = SignedSnapshotEnvelope::new(
            signed.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap();
        AuthenticatedValidatedHolImage::validate_default(authenticated).unwrap()
    }

    fn persist_evidence(
        connection: &mut Connection<Hol<impl Policy>>,
        evidence: &AuthenticatedValidatedHolImage,
    ) -> TrustedImportId {
        let claim = evidence.claim();
        connection.trust_snapshot_signer(claim).unwrap();
        connection.accept_authenticated_snapshot(claim).unwrap();
        let import = connection
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        connection.accept_trusted_import(import, claim).unwrap()
    }

    fn hash_first_claim(seed: u8, schema: &[u8], image: &[u8]) -> AuthenticatedSnapshotClaim {
        let signer = Ed25519Signer::new(SigningKey::from_bytes(&[seed; 32]));
        let schema = O256::from_bytes(schema);
        let image = O256::from_bytes(image);
        let signature = signer
            .sign(
                signer.key_id(),
                schema_valid_snapshot_statement(schema, image),
            )
            .unwrap();
        SignedSnapshotAttestation::new(
            schema,
            image,
            signer.key_id(),
            *signer.verifying_key().as_bytes(),
            &signature,
        )
        .authenticate()
        .unwrap()
    }

    #[test]
    fn authentication_does_not_trust_or_accept_a_snapshot() {
        let kernel = Kernel::ephemeral();
        let snapshot = authenticated(&kernel);
        let mut connection = kernel.open_hol(AllowAll).unwrap();

        assert!(!connection.snapshot_signer_is_trusted(&snapshot).unwrap());
        assert!(
            !connection
                .authenticated_snapshot_is_accepted(&snapshot)
                .unwrap()
        );
        assert!(matches!(
            connection.accept_authenticated_snapshot(&snapshot),
            Err(SnapshotTrustError::UntrustedSigner(_))
        ));
    }

    #[test]
    fn trust_and_acceptance_are_explicit_idempotent_and_connection_local() {
        let kernel = Kernel::ephemeral();
        let snapshot = authenticated(&kernel);
        let mut first = kernel.open_hol(AllowAll).unwrap();
        let mut second = kernel.open_hol(AllowAll).unwrap();

        first.trust_snapshot_signer(&snapshot).unwrap();
        first.trust_snapshot_signer(&snapshot).unwrap();
        assert!(first.snapshot_signer_is_trusted(&snapshot).unwrap());
        assert!(!second.snapshot_signer_is_trusted(&snapshot).unwrap());

        first.accept_authenticated_snapshot(&snapshot).unwrap();
        first.accept_authenticated_snapshot(&snapshot).unwrap();
        assert!(first.authenticated_snapshot_is_accepted(&snapshot).unwrap());
        assert!(
            first
                .snapshot_reference_is_accepted(HolDatabaseRef::new(
                    snapshot.schema(),
                    snapshot.image()
                ))
                .unwrap()
        );
        assert!(
            !second
                .authenticated_snapshot_is_accepted(&snapshot)
                .unwrap()
        );
    }

    #[test]
    fn trust_tables_are_temp_only_and_do_not_register_imports() {
        let kernel = Kernel::ephemeral();
        let snapshot = authenticated(&kernel);
        let mut connection = kernel.open_hol(AllowAll).unwrap();
        connection.trust_snapshot_signer(&snapshot).unwrap();
        connection.accept_authenticated_snapshot(&snapshot).unwrap();

        let sqlite = connection.parts_mut().0.sqlite();
        let temp_objects = sqlite
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema
                 WHERE name IN (
                     'cov_conn_hol_trusted_snapshot_signer',
                     'cov_conn_hol_accepted_snapshot'
                 )",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        let main_objects = sqlite
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema WHERE name LIKE 'cov_conn_%'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        let imports = sqlite
            .query_row("SELECT count(*) FROM main.hol_import", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(temp_objects, 2);
        assert_eq!(main_objects, 0);
        assert_eq!(imports, 0);
    }

    #[test]
    fn temp_trust_does_not_change_the_persistent_snapshot() {
        let kernel = Kernel::ephemeral();
        let snapshot = authenticated(&kernel);
        let mut connection = kernel.open_hol(AllowAll).unwrap();
        let before = kernel.export_hol(&mut connection).unwrap();

        connection.trust_snapshot_signer(&snapshot).unwrap();
        connection.accept_authenticated_snapshot(&snapshot).unwrap();

        let after = kernel.export_hol(&mut connection).unwrap();
        assert_eq!(before.attestation().image(), after.attestation().image());
        assert_eq!(before.image().bytes(), after.image().bytes());
    }

    #[test]
    fn persistent_import_trust_requires_exact_accepted_hash_first_claim() {
        let first_claim = hash_first_claim(7, b"schema A", b"unfetched image A");
        let other_claim = hash_first_claim(8, b"schema B", b"unfetched image B");
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let first = connection
            .register_import(HolDatabaseRef::new(
                first_claim.schema(),
                first_claim.image(),
            ))
            .unwrap();
        let other = connection
            .register_import(HolDatabaseRef::new(
                other_claim.schema(),
                other_claim.image(),
            ))
            .unwrap();

        connection.trust_snapshot_signer(&first_claim).unwrap();
        assert!(matches!(
            connection.accept_trusted_import(first, &first_claim),
            Err(TrustedImportError::Trust(
                SnapshotTrustError::SnapshotNotAccepted { .. }
            ))
        ));
        connection
            .accept_authenticated_snapshot(&first_claim)
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "DELETE FROM temp.cov_conn_hol_trusted_snapshot_signer
                 WHERE signer_hash = ?1",
                [first_claim.signer().as_ref()],
            )
            .unwrap();
        assert!(matches!(
            connection.accept_trusted_import(first, &first_claim),
            Err(TrustedImportError::Trust(
                SnapshotTrustError::UntrustedSigner(_)
            ))
        ));
        connection.trust_snapshot_signer(&first_claim).unwrap();
        assert!(matches!(
            connection.accept_trusted_import(other, &first_claim),
            Err(TrustedImportError::ImportClaimMismatch { .. })
        ));

        let id = connection
            .accept_trusted_import(first, &first_claim)
            .unwrap();
        assert_eq!(
            connection
                .accept_trusted_import(first, &first_claim)
                .unwrap(),
            id
        );
        let stored = connection.trusted_import(id).unwrap();
        assert_eq!(stored.import, first);
        assert_eq!(stored.signer, first_claim.signer());
        assert_eq!(stored.public_key, *first_claim.public_key());
        assert_eq!(stored.signature, first_claim.signature());
        assert_eq!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_trusted_import", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            1
        );
    }

    #[test]
    fn trusted_import_metadata_and_index_are_user_extensible() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::TrustedImport, "reason", MetadataType::Text)
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::TrustedImport,
                "hol_trusted_import_reason",
                ["reason"],
                false,
            )
            .unwrap();
        let claim = hash_first_claim(9, b"schema", b"never fetched");
        let mut connection =
            Connection::open_hol_in_memory_with_schema(AllowAll, schema.clone()).unwrap();
        let import = connection
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        connection.trust_snapshot_signer(&claim).unwrap();
        connection.accept_authenticated_snapshot(&claim).unwrap();
        assert!(matches!(
            connection.accept_trusted_import_with_metadata(
                import,
                &claim,
                &[("unknown", MetadataValue::Text("no".to_owned()))],
            ),
            Err(TrustedImportError::Metadata(MetadataError::UnknownColumn(
                _
            )))
        ));
        assert_eq!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_trusted_import", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            0
        );
        let id = connection
            .accept_trusted_import_with_metadata(
                import,
                &claim,
                &[("reason", MetadataValue::Text("test key".to_owned()))],
            )
            .unwrap();
        assert_eq!(
            connection
                .metadata(MetadataTarget::trusted_import(id), &["reason"])
                .unwrap(),
            [MetadataValue::Text("test key".to_owned())]
        );
        let bytes = connection.parts_mut().0.serialize().unwrap();
        let validated =
            super::super::ValidatedHolImage::validate_with_schema(&bytes, &schema).unwrap();
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);
        assert!(matches!(
            super::super::ValidatedHolImage::validate(&bytes),
            Err(super::super::HolImageValidationError::SchemaMismatch)
        ));
    }

    #[test]
    fn detached_validation_rechecks_persistent_import_signature() {
        let claim = hash_first_claim(10, b"remote schema", b"remote image");
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let import = connection
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        connection.trust_snapshot_signer(&claim).unwrap();
        connection.accept_authenticated_snapshot(&claim).unwrap();
        let id = connection.accept_trusted_import(import, &claim).unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "UPDATE hol_trusted_import SET signature = zeroblob(64)
                 WHERE trusted_import_id = ?1",
                [id.get()],
            )
            .unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();
        assert!(matches!(
            super::super::ValidatedHolImage::validate(&bytes),
            Err(
                super::super::HolImageValidationError::InvalidTrustedImportSignature(actual)
            ) if actual == id
        ));
    }

    #[derive(Default)]
    struct ToggleTrust {
        allow: bool,
        seen: Vec<Operation>,
    }

    impl Policy for ToggleTrust {
        fn allows(&mut self, operation: Operation) -> bool {
            self.seen.push(operation);
            self.allow
        }
    }

    #[test]
    fn policy_denial_is_reported_before_trust_state_is_used() {
        let kernel = Kernel::ephemeral();
        let snapshot = authenticated(&kernel);
        let mut connection = kernel
            .open_hol(ToggleTrust {
                allow: true,
                seen: Vec::new(),
            })
            .unwrap();
        connection.trust_snapshot_signer(&snapshot).unwrap();
        connection.accept_authenticated_snapshot(&snapshot).unwrap();
        connection.parts_mut().1.policy.allow = false;

        assert!(matches!(
            connection.trust_snapshot_signer(&snapshot),
            Err(SnapshotTrustError::Denied(Operation::TrustSnapshotSigner))
        ));
        assert!(matches!(
            connection.accept_authenticated_snapshot(&snapshot),
            Err(SnapshotTrustError::Denied(
                Operation::AcceptAuthenticatedSnapshot
            ))
        ));
        assert!(matches!(
            connection.authenticated_snapshot_is_accepted(&snapshot),
            Err(SnapshotTrustError::Denied(Operation::ReadAcceptedSnapshot))
        ));
        assert_eq!(
            connection.protocol().policy().seen,
            [
                Operation::TrustSnapshotSigner,
                Operation::AcceptAuthenticatedSnapshot,
                Operation::TrustSnapshotSigner,
                Operation::AcceptAuthenticatedSnapshot,
                Operation::ReadAcceptedSnapshot,
            ]
        );
        let sqlite = connection.parts_mut().0.sqlite();
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM temp.cov_conn_hol_trusted_snapshot_signer",
                    [],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            1
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM temp.cov_conn_hol_accepted_snapshot",
                    [],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            1
        );
    }

    #[test]
    fn persistent_trust_policy_denial_precedes_idempotent_reads_and_writes() {
        let claim = hash_first_claim(11, b"schema", b"image");
        let mut connection = Connection::open_hol_in_memory(ToggleTrust {
            allow: true,
            seen: Vec::new(),
        })
        .unwrap();
        let import = connection
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        connection.trust_snapshot_signer(&claim).unwrap();
        connection.accept_authenticated_snapshot(&claim).unwrap();
        let id = connection.accept_trusted_import(import, &claim).unwrap();
        let seen_before = connection.protocol().policy().seen.len();
        connection.parts_mut().1.policy.allow = false;

        assert!(matches!(
            connection.accept_trusted_import(import, &claim),
            Err(TrustedImportError::Denied(Operation::AcceptTrustedImport))
        ));
        assert!(matches!(
            connection.trusted_import(id),
            Err(TrustedImportError::Denied(Operation::ReadTrustedImport))
        ));
        assert_eq!(
            &connection.protocol().policy().seen[seen_before..],
            [Operation::AcceptTrustedImport, Operation::ReadTrustedImport]
        );
    }

    #[test]
    fn exact_persistent_assumption_brands_authenticated_validated_bytes() {
        let kernel = Kernel::ephemeral();
        let evidence = authenticated_validated(&kernel);
        let expected_schema = evidence.image().schema();
        let expected_image = evidence.image().hash();
        let expected_signer = evidence.claim().signer();
        let mut target = kernel.open_hol(AllowAll).unwrap();
        let trusted = persist_evidence(&mut target, &evidence);
        let before = target.parts_mut().0.serialize().unwrap();

        target
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "DELETE FROM temp.cov_conn_hol_accepted_snapshot;
                 DELETE FROM temp.cov_conn_hol_trusted_snapshot_signer;",
            )
            .unwrap();
        let matched = target
            .match_trusted_import_image(trusted, evidence)
            .unwrap();
        assert_eq!(matched.trusted_import(), trusted);
        assert_eq!(matched.import(), ImportId::from_i64(0));
        assert_eq!(matched.image().schema(), expected_schema);
        assert_eq!(matched.image().hash(), expected_image);
        assert_eq!(matched.signer(), expected_signer);
        drop(matched);

        assert_eq!(target.parts_mut().0.serialize().unwrap(), before);
    }

    #[test]
    fn coincident_numeric_ids_do_not_cross_connection_authority() {
        let first_kernel = Kernel::ephemeral();
        let first_evidence = authenticated_validated(&first_kernel);
        let second_kernel = Kernel::ephemeral();
        let second_evidence = authenticated_validated(&second_kernel);
        assert_ne!(
            first_evidence.claim().signer(),
            second_evidence.claim().signer()
        );

        let mut first = first_kernel.open_hol(AllowAll).unwrap();
        let first_id = persist_evidence(&mut first, &first_evidence);
        let mut second = second_kernel.open_hol(AllowAll).unwrap();
        let second_id = persist_evidence(&mut second, &second_evidence);
        assert_eq!(first_id, second_id);

        assert!(matches!(
            second.match_trusted_import_image(second_id, first_evidence),
            Err(TrustedImportImageError::SignerMismatch(_))
        ));
    }

    #[test]
    fn matching_policy_denial_precedes_persistent_row_probe() {
        #[derive(Default)]
        struct DenyMatch(Vec<Operation>);

        impl Policy for DenyMatch {
            fn allows(&mut self, operation: Operation) -> bool {
                self.0.push(operation);
                operation != Operation::MatchTrustedImportImage
            }
        }

        let kernel = Kernel::ephemeral();
        let evidence = authenticated_validated(&kernel);
        let mut target = kernel.open_hol(DenyMatch::default()).unwrap();
        let trusted = persist_evidence(&mut target, &evidence);
        target
            .parts_mut()
            .0
            .sqlite()
            .execute("DELETE FROM hol_import", [])
            .unwrap();

        assert!(matches!(
            target.match_trusted_import_image(trusted, evidence),
            Err(TrustedImportImageError::Denied(
                Operation::MatchTrustedImportImage
            ))
        ));
        assert_eq!(
            target.protocol().policy().0.last(),
            Some(&Operation::MatchTrustedImportImage)
        );
    }
}
