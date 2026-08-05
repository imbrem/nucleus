use std::{error::Error as StdError, fmt};

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{
    Hol, HolDatabaseRef, ImportId, MatchedTrustedHolImage, Operation, Policy, TrustedImportId,
};
use crate::Connection;

/// Failure to adopt one exact signed snapshot as an independent authoritative HOL state.
#[derive(Debug)]
pub enum TrustedStateOpenError {
    /// The originating connection denied this distinct trust assumption.
    Denied(Operation),
    /// The retained bytes no longer have their authenticated content address.
    ImageMismatch { expected: O256, actual: O256 },
    /// The private writable in-memory copy could not be created.
    Image(covalence_neutron::ImageError),
    /// A local provenance ID cannot be allocated.
    IdOverflow(&'static str),
    /// Existing provenance for the source coordinates conflicts with the exact attestation.
    ConflictingProvenance { import: ImportId, signer: O256 },
    /// `SQLite` rejected fresh TEMP trust initialization or atomic provenance insertion.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TrustedStateOpenError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::ImageMismatch { expected, actual } => write!(
                formatter,
                "authenticated image hash {expected} differs from retained bytes hash {actual}"
            ),
            Self::Image(error) => error.fmt(formatter),
            Self::IdOverflow(table) => write!(formatter, "{table} IDs are exhausted"),
            Self::ConflictingProvenance { import, signer } => write!(
                formatter,
                "source provenance for import {} and signer {signer} conflicts",
                import.get()
            ),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TrustedStateOpenError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Image(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<covalence_neutron::ImageError> for TrustedStateOpenError {
    fn from(error: covalence_neutron::ImageError) -> Self {
        Self::Image(error)
    }
}

impl From<sqlite::Error> for TrustedStateOpenError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

impl<P: Policy> MatchedTrustedHolImage<'_, P> {
    /// Opens the exact signed bytes as an independent writable HOL connection.
    ///
    /// This is a separate policy assumption: the originating `P` explicitly decides that the
    /// matched signed bytes are authoritative serialized kernel state. Authentication, detached
    /// structural validation, and an accepted-import row alone do **not** establish theorem truth;
    /// without this operation the matched image's judgement rows grant no authority in the owner.
    ///
    /// The child receives an independent caller-supplied `Q`, preserves the exact validated
    /// metadata schema, and starts with fresh empty connection-local TEMP trust tables. Its main
    /// database records the exact source schema/image and signer/key/signature as import
    /// provenance. No theorem handle crosses the boundary: a persisted judgement becomes usable
    /// only through [`super::ProofSession::load_theorem`] in a scoped child proof session.
    ///
    /// The exact bytes are copied into private writable memory. This consumes the matched
    /// capability but does not mutate its owner's main database or TEMP trust tables. The origin
    /// policy may record authorization. After failure the owner can obtain fresh matching evidence
    /// and retry if that stateful policy permits it.
    ///
    /// # Errors
    ///
    /// Returns an error before returning any child if the origin policy denies this assumption,
    /// the retained bytes fail their final content-address check, private deserialization fails,
    /// provenance IDs are exhausted/conflicting, or `SQLite` rejects the atomic initialization.
    pub fn open_as_trusted_state<Q: Policy>(
        self,
        child_policy: Q,
    ) -> Result<Connection<Hol<Q>>, TrustedStateOpenError> {
        let (owner, _trusted_import, _import, evidence) = self.into_parts();
        if !owner
            .parts_mut()
            .1
            .policy
            .allows(Operation::OpenTrustedSnapshotAsState)
        {
            return Err(TrustedStateOpenError::Denied(
                Operation::OpenTrustedSnapshotAsState,
            ));
        }

        let image = evidence.image();
        let expected = image.hash();
        let actual = O256::from_bytes(image.bytes());
        if actual != expected {
            return Err(TrustedStateOpenError::ImageMismatch { expected, actual });
        }

        let schema = image.metadata_schema().clone();
        let database = HolDatabaseRef::new(image.schema(), image.hash());
        let bytes = covalence_neutron::Bytes::copy_from_slice(image.bytes());
        let claim = evidence.claim();
        let signer = claim.signer();
        let public_key = *claim.public_key();
        let signature = claim.signature().to_vec();

        let neutron = covalence_neutron::Connection::deserialize(&bytes)?;
        initialize_trusted_state(&neutron, database, signer, &public_key, &signature)?;

        Ok(Connection::from_neutron(
            neutron,
            Hol {
                policy: child_policy,
                schema,
            },
        ))
    }
}

fn initialize_trusted_state(
    neutron: &covalence_neutron::Connection,
    database: HolDatabaseRef,
    signer: O256,
    public_key: &[u8; 32],
    signature: &[u8],
) -> Result<(), TrustedStateOpenError> {
    let transaction = neutron.sqlite().unchecked_transaction()?;
    super::trust::install_connection_trust_schema(&transaction)?;
    let import = find_or_insert_import(&transaction, database)?;
    find_or_insert_attestation(&transaction, import, signer, public_key, signature)?;
    transaction.commit()?;
    Ok(())
}

fn find_or_insert_import(
    connection: &sqlite::Connection,
    database: HolDatabaseRef,
) -> Result<ImportId, TrustedStateOpenError> {
    if let Some(id) = connection
        .query_row(
            "SELECT import_id FROM hol_import WHERE schema_hash = ?1 AND image_hash = ?2",
            sqlite::params![database.schema().as_ref(), database.image().as_ref()],
            |row| row.get::<_, i64>(0).map(ImportId::from_i64),
        )
        .optional()?
    {
        return Ok(id);
    }
    let id = next_id(connection, "hol_import", "import_id")?;
    connection.execute(
        "INSERT INTO hol_import(import_id, schema_hash, image_hash) VALUES (?1, ?2, ?3)",
        sqlite::params![id, database.schema().as_ref(), database.image().as_ref()],
    )?;
    Ok(ImportId::from_i64(id))
}

fn find_or_insert_attestation(
    connection: &sqlite::Connection,
    import: ImportId,
    signer: O256,
    public_key: &[u8; 32],
    signature: &[u8],
) -> Result<TrustedImportId, TrustedStateOpenError> {
    let existing = connection
        .query_row(
            "SELECT trusted_import_id, public_key, signature
             FROM hol_trusted_import WHERE import_id = ?1 AND signer_hash = ?2",
            sqlite::params![import.get(), signer.as_ref()],
            |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, Vec<u8>>(1)?,
                    row.get::<_, Vec<u8>>(2)?,
                ))
            },
        )
        .optional()?;
    if let Some((id, stored_key, stored_signature)) = existing {
        if stored_key.as_slice() != public_key || stored_signature.as_slice() != signature {
            return Err(TrustedStateOpenError::ConflictingProvenance { import, signer });
        }
        return Ok(TrustedImportId::from_i64(id));
    }
    let id = next_id(connection, "hol_trusted_import", "trusted_import_id")?;
    connection.execute(
        "INSERT INTO hol_trusted_import(
             trusted_import_id, import_id, signer_hash, public_key, signature
         ) VALUES (?1, ?2, ?3, ?4, ?5)",
        sqlite::params![
            id,
            import.get(),
            signer.as_ref(),
            public_key.as_slice(),
            signature
        ],
    )?;
    Ok(TrustedImportId::from_i64(id))
}

fn next_id(
    connection: &sqlite::Connection,
    table: &'static str,
    column: &'static str,
) -> Result<i64, TrustedStateOpenError> {
    let sql = format!("SELECT max({column}) FROM {table}");
    connection
        .query_row(&sql, [], |row| row.get::<_, Option<i64>>(0))?
        .unwrap_or(-1)
        .checked_add(1)
        .ok_or(TrustedStateOpenError::IdOverflow(table))
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, rc::Rc};

    use super::*;
    use crate::{
        AllowAll, AuthenticatedValidatedHolImage, ContextId, Kernel, MetadataTable, MetadataType,
        SignedHolSnapshot, SignedSnapshotEnvelope, TermId,
    };

    #[derive(Clone)]
    struct DenyOperation {
        denied: Operation,
        enabled: Rc<Cell<bool>>,
        seen: Rc<std::cell::RefCell<Vec<Operation>>>,
    }

    impl Policy for DenyOperation {
        fn allows(&mut self, operation: Operation) -> bool {
            self.seen.borrow_mut().push(operation);
            !(self.enabled.get() && operation == self.denied)
        }
    }

    fn deny(operation: Operation) -> DenyOperation {
        DenyOperation {
            denied: operation,
            enabled: Rc::new(Cell::new(true)),
            seen: Rc::new(std::cell::RefCell::new(Vec::new())),
        }
    }

    fn authenticated_validated(snapshot: &SignedHolSnapshot) -> AuthenticatedValidatedHolImage {
        let attestation = snapshot.attestation();
        let authenticated = SignedSnapshotEnvelope::new(
            snapshot.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap();
        AuthenticatedValidatedHolImage::validate_with_descriptor(
            authenticated,
            snapshot.descriptor(),
        )
        .unwrap()
    }

    fn persist_and_match<'a, P: Policy>(
        owner: &'a mut Connection<Hol<P>>,
        snapshot: &SignedHolSnapshot,
    ) -> MatchedTrustedHolImage<'a, P> {
        let evidence = authenticated_validated(snapshot);
        let claim = evidence.claim();
        owner.trust_snapshot_signer(claim).unwrap();
        owner.accept_authenticated_snapshot(claim).unwrap();
        let import = owner
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        let trusted = owner.accept_trusted_import(import, claim).unwrap();
        owner.match_trusted_import_image(trusted, evidence).unwrap()
    }

    fn persist_evidence<P: Policy>(
        owner: &mut Connection<Hol<P>>,
        snapshot: &SignedHolSnapshot,
    ) -> TrustedImportId {
        let evidence = authenticated_validated(snapshot);
        let claim = evidence.claim();
        owner.trust_snapshot_signer(claim).unwrap();
        owner.accept_authenticated_snapshot(claim).unwrap();
        let import = owner
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        owner.accept_trusted_import(import, claim).unwrap()
    }

    fn assumption_snapshot(
        with_metadata: bool,
    ) -> (Kernel, SignedHolSnapshot, TermId, super::super::HolSchema) {
        let kernel = Kernel::ephemeral();
        let mut schema = super::super::HolSchema::new();
        if with_metadata {
            schema
                .add_column_to(
                    MetadataTable::Judgement,
                    "assumption_set",
                    MetadataType::Text,
                )
                .unwrap();
        }
        let mut source =
            Connection::open_hol_in_memory_with_schema(AllowAll, schema.clone()).unwrap();
        // Deliberately persist a closed non-theorem by raw SQL in this test-only assumption-set
        // fixture. Production has no assumption/admission rule, and the source signature claims
        // only that these exact bytes validate structurally under the HOL schema.
        let assumption = source.insert_bool_term(false).unwrap();
        let sql = if with_metadata {
            "INSERT INTO hol_judgement(ctx_id, term_id, assumption_set) VALUES (0, ?1, 'fixture')"
        } else {
            "INSERT INTO hol_judgement(ctx_id, term_id) VALUES (0, ?1)"
        };
        source
            .parts_mut()
            .0
            .sqlite()
            .execute(sql, [assumption.get()])
            .unwrap();
        let snapshot = kernel.export_hol(&mut source).unwrap();
        (kernel, snapshot, assumption, schema)
    }

    #[test]
    fn origin_denial_precedes_copy_and_owner_can_rematch_and_retry() {
        let (_source_kernel, snapshot, _assumption, _) = assumption_snapshot(false);
        let policy = deny(Operation::OpenTrustedSnapshotAsState);
        let enabled = policy.enabled.clone();
        let seen = policy.seen.clone();
        let mut owner = Connection::open_hol_in_memory(policy).unwrap();
        let trusted = persist_evidence(&mut owner, &snapshot);
        let before = owner.parts_mut().0.serialize().unwrap();
        let matched = owner
            .match_trusted_import_image(trusted, authenticated_validated(&snapshot))
            .unwrap();

        assert!(matches!(
            matched.open_as_trusted_state(AllowAll),
            Err(TrustedStateOpenError::Denied(
                Operation::OpenTrustedSnapshotAsState
            ))
        ));
        assert_eq!(
            seen.borrow().last(),
            Some(&Operation::OpenTrustedSnapshotAsState)
        );

        // The consumed capability released the owner without changing persistent state. Fresh
        // exact evidence can be matched and retried after policy changes.
        enabled.set(false);
        let after_denial = owner.parts_mut().0.serialize().unwrap();
        assert_eq!(after_denial.as_ref(), before.as_ref());
        let child = persist_and_match(&mut owner, &snapshot)
            .open_as_trusted_state(AllowAll)
            .unwrap();
        assert_eq!(child.protocol().schema().metadata_type("absent"), None);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn trusted_state_is_independent_preserves_schema_and_records_exact_provenance() {
        let (_source_kernel, snapshot, assumption, schema) = assumption_snapshot(true);
        let source_hash = snapshot.attestation().image();
        let source_schema = snapshot.attestation().schema();
        let source_signer = snapshot.attestation().signer();
        let source_key = *snapshot.attestation().public_key();
        let source_signature = snapshot.attestation().signature().to_vec();
        let mut owner = Connection::open_hol_in_memory(AllowAll).unwrap();
        assert_eq!(owner.insert_bool_term(false).unwrap(), assumption);
        let trusted = persist_evidence(&mut owner, &snapshot);
        let owner_before = owner.parts_mut().0.serialize().unwrap();
        let matched = owner
            .match_trusted_import_image(trusted, authenticated_validated(&snapshot))
            .unwrap();
        let mut child = matched.open_as_trusted_state(AllowAll).unwrap();
        assert_eq!(owner.parts_mut().0.serialize().unwrap(), owner_before);

        assert_eq!(
            child
                .protocol()
                .schema()
                .metadata_type_on(MetadataTable::Judgement, "assumption_set"),
            Some(MetadataType::Text)
        );
        assert_eq!(
            child
                .protocol()
                .schema()
                .metadata_type_on(MetadataTable::Judgement, "assumption_set"),
            schema.metadata_type_on(MetadataTable::Judgement, "assumption_set")
        );

        let sqlite = child.parts_mut().0.sqlite();
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM temp.cov_conn_hol_trusted_snapshot_signer",
                    [],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            0
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM temp.cov_conn_hol_accepted_snapshot",
                    [],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            0
        );
        let provenance = sqlite
            .query_row(
                "SELECT i.schema_hash, i.image_hash, ti.signer_hash, ti.public_key, ti.signature
                 FROM hol_import AS i JOIN hol_trusted_import AS ti USING (import_id)
                 WHERE i.schema_hash = ?1 AND i.image_hash = ?2 AND ti.signer_hash = ?3",
                sqlite::params![
                    source_schema.as_ref(),
                    source_hash.as_ref(),
                    source_signer.as_ref()
                ],
                |row| {
                    Ok((
                        row.get::<_, Vec<u8>>(0)?,
                        row.get::<_, Vec<u8>>(1)?,
                        row.get::<_, Vec<u8>>(2)?,
                        row.get::<_, Vec<u8>>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(provenance.0, source_schema.as_ref());
        assert_eq!(provenance.1, source_hash.as_ref());
        assert_eq!(provenance.2, source_signer.as_ref());
        assert_eq!(provenance.3, source_key);
        assert_eq!(provenance.4, source_signature);

        // A persisted source row is branded only inside the child session. Use it to derive an
        // implication and then persist a genuinely new weakened judgement.
        let context = child.define_context([assumption]).unwrap();
        child.with_proof_session(|mut proof| {
            let loaded = proof
                .load_theorem(ContextId::empty(), assumption)
                .unwrap()
                .unwrap();
            let assumption_edge = proof
                .prove_context_implication(
                    ContextId::empty(),
                    context,
                    std::slice::from_ref(&loaded),
                )
                .unwrap();
            proof.persist_context_implication(&assumption_edge).unwrap();
            let implication = proof
                .prove_context_implication(context, ContextId::empty(), &[])
                .unwrap();
            let weakened = proof.weaken(&implication, &loaded).unwrap();
            proof.persist_theorem(&weakened).unwrap();
        });
        assert_eq!(
            child
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT count(*) FROM hol_judgement WHERE ctx_id = ?1 AND term_id = ?2",
                    [context.get(), assumption.get()],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            1
        );

        // The owner contains only inert provenance and never received the source judgement.
        assert!(
            owner
                .with_proof_session(|mut proof| proof
                    .load_theorem(ContextId::empty(), assumption)
                    .map(|theorem| theorem.is_none()))
                .unwrap()
        );

        let child_kernel = Kernel::ephemeral();
        let child_snapshot = child_kernel.export_hol(&mut child).unwrap();
        assert_ne!(child_snapshot.attestation().image(), source_hash);
        let validated = authenticated_validated(&child_snapshot);
        assert_eq!(
            validated.image().hash(),
            child_snapshot.attestation().image()
        );
        assert_eq!(validated.image().schema(), source_schema);
    }

    #[test]
    fn child_policy_is_independent_and_not_consulted_during_open() {
        let (_source_kernel, snapshot, assumption, _) = assumption_snapshot(false);
        let mut owner = Connection::open_hol_in_memory(AllowAll).unwrap();
        let child_policy = deny(Operation::ReadTheorem);
        let seen = child_policy.seen.clone();
        let mut child = persist_and_match(&mut owner, &snapshot)
            .open_as_trusted_state(child_policy)
            .unwrap();
        assert!(seen.borrow().is_empty());
        assert!(child.with_proof_session(|mut proof| matches!(
            proof.load_theorem(ContextId::empty(), assumption),
            Err(super::super::ProofError::Denied(Operation::ReadTheorem))
        )));
    }

    #[test]
    fn exhausted_source_import_ids_fail_without_mutating_the_owner() {
        let source_kernel = Kernel::ephemeral();
        let mut source = Connection::open_hol_in_memory(AllowAll).unwrap();
        source
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "INSERT INTO hol_import(import_id, schema_hash, image_hash)
                 VALUES (?1, zeroblob(32), zeroblob(32))",
                [i64::MAX],
            )
            .unwrap();
        let snapshot = source_kernel.export_hol(&mut source).unwrap();
        let mut owner = Connection::open_hol_in_memory(AllowAll).unwrap();
        let matched = persist_and_match(&mut owner, &snapshot);
        assert!(matches!(
            matched.open_as_trusted_state(AllowAll),
            Err(TrustedStateOpenError::IdOverflow("hol_import"))
        ));
        // The owner remains usable and can rematch the same exact evidence after failure.
        let second = persist_and_match(&mut owner, &snapshot);
        assert!(matches!(
            second.open_as_trusted_state(AllowAll),
            Err(TrustedStateOpenError::IdOverflow("hol_import"))
        ));
    }

    #[test]
    fn attestation_id_overflow_rolls_back_partial_child_initialization() {
        let unrelated_kernel = Kernel::ephemeral();
        let mut unrelated = Connection::open_hol_in_memory(AllowAll).unwrap();
        let unrelated_snapshot = unrelated_kernel.export_hol(&mut unrelated).unwrap();
        let unrelated_evidence = authenticated_validated(&unrelated_snapshot);

        let source_kernel = Kernel::ephemeral();
        let mut source = Connection::open_hol_in_memory(AllowAll).unwrap();
        let claim = unrelated_evidence.claim();
        source.trust_snapshot_signer(claim).unwrap();
        source.accept_authenticated_snapshot(claim).unwrap();
        let import = source
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        let trusted = source.accept_trusted_import(import, claim).unwrap();
        source
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "UPDATE hol_trusted_import SET trusted_import_id = ?1
                 WHERE trusted_import_id = ?2",
                [i64::MAX, trusted.get()],
            )
            .unwrap();
        let snapshot = source_kernel.export_hol(&mut source).unwrap();
        let attestation = snapshot.attestation();
        let database = HolDatabaseRef::new(attestation.schema(), attestation.image());
        let neutron = covalence_neutron::Connection::deserialize(
            &covalence_neutron::Bytes::copy_from_slice(snapshot.image().bytes()),
        )
        .unwrap();

        assert!(matches!(
            initialize_trusted_state(
                &neutron,
                database,
                attestation.signer(),
                attestation.public_key(),
                attestation.signature(),
            ),
            Err(TrustedStateOpenError::IdOverflow("hol_trusted_import"))
        ));
        let sqlite = neutron.sqlite();
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM hol_import
                     WHERE schema_hash = ?1 AND image_hash = ?2",
                    sqlite::params![database.schema().as_ref(), database.image().as_ref()],
                    |row| row.get::<_, i64>(0),
                )
                .unwrap(),
            0
        );
        assert_eq!(
            sqlite
                .query_row(
                    "SELECT count(*) FROM temp.sqlite_schema
                     WHERE name IN (
                         'cov_conn_hol_trusted_snapshot_signer',
                         'cov_conn_hol_accepted_snapshot'
                     )",
                    [],
                    |row| row.get::<_, i64>(0),
                )
                .unwrap(),
            0
        );

        // The same public operation exposes no partial child and leaves the owner free to rematch.
        let mut owner = Connection::open_hol_in_memory(AllowAll).unwrap();
        assert!(matches!(
            persist_and_match(&mut owner, &snapshot).open_as_trusted_state(AllowAll),
            Err(TrustedStateOpenError::IdOverflow("hol_trusted_import"))
        ));
        assert!(matches!(
            persist_and_match(&mut owner, &snapshot).open_as_trusted_state(AllowAll),
            Err(TrustedStateOpenError::IdOverflow("hol_trusted_import"))
        ));
    }

    #[test]
    fn existing_attestation_must_match_exact_key_and_signature() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let sqlite = connection.parts_mut().0.sqlite();
        let database = HolDatabaseRef::new(O256::from_bytes(b"schema"), O256::from_bytes(b"image"));
        let import = find_or_insert_import(sqlite, database).unwrap();
        let signer = O256::from_bytes(b"signer");
        sqlite
            .execute(
                "INSERT INTO hol_trusted_import(
                     trusted_import_id, import_id, signer_hash, public_key, signature
                 ) VALUES (0, ?1, ?2, zeroblob(32), zeroblob(64))",
                sqlite::params![import.get(), signer.as_ref()],
            )
            .unwrap();

        assert!(matches!(
            find_or_insert_attestation(sqlite, import, signer, &[1; 32], &[2; 64]),
            Err(TrustedStateOpenError::ConflictingProvenance {
                import: actual,
                signer: actual_signer,
            }) if actual == import && actual_signer == signer
        ));
        assert_eq!(
            sqlite
                .query_row("SELECT count(*) FROM hol_trusted_import", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            1
        );
    }
}
