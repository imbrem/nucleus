use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{Hol, HolDatabaseRef, Operation, Policy};
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
        _ => Err(SnapshotTrustError::ConflictingSnapshot {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AllowAll, Kernel, SignedSnapshotEnvelope};

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
}
