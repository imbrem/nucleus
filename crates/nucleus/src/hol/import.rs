use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{
    ExportId, Hol, HolSnapshotAttestation, NamespaceError, NamespaceId, Operation, Policy,
};
use crate::Connection;

/// Unverified coordinates for exact bytes under one claimed physical schema.
///
/// This pair alone claims neither existence, validity, authenticity, trust, nor logical truth.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HolDatabaseRef {
    schema: O256,
    image: O256,
}

impl HolDatabaseRef {
    /// Constructs inert schema-qualified database coordinates.
    #[must_use]
    pub const fn new(schema: O256, image: O256) -> Self {
        Self { schema, image }
    }

    /// Returns the claimed exact physical schema.
    #[must_use]
    pub const fn schema(self) -> O256 {
        self.schema
    }

    /// Returns the content address of the claimed exact bytes.
    #[must_use]
    pub const fn image(self) -> O256 {
        self.image
    }
}

impl From<&HolSnapshotAttestation> for HolDatabaseRef {
    fn from(attestation: &HolSnapshotAttestation) -> Self {
        Self::new(attestation.schema(), attestation.image())
    }
}

/// Database-local identity of one inert import-directory reference.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImportId(i64);

impl ImportId {
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

/// Whether one local namespace row stores local exports or aliases an external namespace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NamespaceSource {
    /// Ordinary local namespace.
    Local,
    /// Inert alias of one complete external namespace.
    Imported {
        /// Local import-directory reference.
        import: ImportId,
        /// Namespace ID in the unfetched source database.
        source_namespace: i64,
    },
}

/// Read-only view of one inert import-directory row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImportView {
    /// Schema-qualified database coordinates.
    pub database: HolDatabaseRef,
}

/// Opaque coordinates for an export in an unfetched external namespace.
///
/// This value has deliberately no HOL sort and establishes neither remote existence nor a local
/// syntax/proof capability.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ExternalExportRef {
    database: HolDatabaseRef,
    source_namespace: i64,
    export: ExportId,
}

impl ExternalExportRef {
    /// Returns the external database coordinates.
    #[must_use]
    pub const fn database(self) -> HolDatabaseRef {
        self.database
    }

    /// Returns the source database's namespace ID.
    #[must_use]
    pub const fn source_namespace(self) -> i64 {
        self.source_namespace
    }

    /// Returns the source namespace's numeric export coordinate.
    #[must_use]
    pub const fn export(self) -> ExportId {
        self.export
    }
}

impl<P: Policy> Connection<Hol<P>> {
    /// Registers inert schema-qualified database coordinates without fetching them.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies registration, IDs are exhausted, or `SQLite` rejects the
    /// transaction.
    pub fn register_import(&mut self, database: HolDatabaseRef) -> Result<ImportId, ImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::RegisterImport)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        if let Some(id) = find_import(&transaction, database)? {
            transaction.commit()?;
            return Ok(id);
        }
        let maximum =
            transaction.query_row("SELECT max(import_id) FROM hol_import", [], |row| {
                row.get::<_, Option<i64>>(0)
            })?;
        let id = ImportId(
            maximum
                .unwrap_or(-1)
                .checked_add(1)
                .ok_or(ImportError::IdOverflow)?,
        );
        transaction.execute(
            "INSERT INTO hol_import(import_id, schema_hash, image_hash) VALUES (?1, ?2, ?3)",
            sqlite::params![
                id.get(),
                database.schema().as_ref(),
                database.image().as_ref()
            ],
        )?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads one inert import-directory reference.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is absent/corrupt, or `SQLite` rejects
    /// the query.
    pub fn import_reference(&mut self, id: ImportId) -> Result<ImportView, ImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadImport)?;
        read_import(neutron.sqlite(), id)
    }

    /// Defines an inert alias of one complete external namespace without fetching it.
    ///
    /// Named aliases are idempotent only for the exact same source. Anonymous aliases are fresh.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the operation, the import/parent/source/name is invalid,
    /// a named path has another source, or `SQLite` rejects the transaction.
    pub fn create_imported_namespace(
        &mut self,
        parent: Option<NamespaceId>,
        name: Option<&str>,
        import: ImportId,
        source_namespace: i64,
    ) -> Result<NamespaceId, ImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::DefineImportedNamespace)?;
        super::namespace::validate_name(name)?;
        if source_namespace < 0 {
            return Err(ImportError::InvalidSourceNamespace(source_namespace));
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_import(&transaction, import)?;
        if let Some(parent) = parent {
            match super::namespace::namespace_source(&transaction, parent) {
                Ok(NamespaceSource::Local) => {}
                Ok(NamespaceSource::Imported { .. }) => {
                    return Err(NamespaceError::ImportedParent(parent).into());
                }
                Err(NamespaceError::UnknownNamespace(_)) => {
                    return Err(NamespaceError::UnknownParent(parent).into());
                }
                Err(error) => return Err(error.into()),
            }
        }
        let expected = NamespaceSource::Imported {
            import,
            source_namespace,
        };
        if let Some((namespace, source_import, source_namespace)) = name
            .map(|name| {
                transaction
                    .query_row(
                        "SELECT namespace_id, source_import_id, source_namespace_id
                         FROM hol_namespace
                         WHERE parent_namespace_id IS ?1 AND name = ?2",
                        sqlite::params![parent.map(NamespaceId::get), name],
                        |row| {
                            Ok((
                                NamespaceId::from_i64(row.get(0)?),
                                row.get::<_, Option<i64>>(1)?,
                                row.get::<_, Option<i64>>(2)?,
                            ))
                        },
                    )
                    .optional()
            })
            .transpose()?
            .flatten()
        {
            let actual = decode_source(namespace, source_import, source_namespace)?;
            if actual == expected {
                transaction.commit()?;
                return Ok(namespace);
            }
            return Err(NamespaceError::SourceConflict {
                namespace,
                expected,
                actual,
            }
            .into());
        }
        let namespace = NamespaceId::from_i64(super::namespace::next_id(
            &transaction,
            "hol_namespace",
            "namespace_id",
        )?);
        transaction.execute(
            "INSERT INTO hol_namespace(
                 namespace_id, parent_namespace_id, name,
                 source_import_id, source_namespace_id
             ) VALUES (?1, ?2, ?3, ?4, ?5)",
            sqlite::params![
                namespace.get(),
                parent.map(NamespaceId::get),
                name,
                import.get(),
                source_namespace
            ],
        )?;
        transaction.commit()?;
        Ok(namespace)
    }

    /// Reads the source discriminator of one namespace.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the namespace is absent/corrupt, or `SQLite`
    /// rejects the query.
    pub fn namespace_source(
        &mut self,
        namespace: NamespaceId,
    ) -> Result<NamespaceSource, ImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadImportedNamespace)?;
        super::namespace::namespace_source(neutron.sqlite(), namespace).map_err(Into::into)
    }

    /// Constructs inert external coordinates through a full namespace alias.
    ///
    /// No source bytes are fetched and no export existence or sort is claimed.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the namespace is local/absent/corrupt, the
    /// export ID is negative, or `SQLite` rejects the query.
    pub fn external_export_ref(
        &mut self,
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<ExternalExportRef, ImportError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadImportedNamespace)?;
        if export.get() < 0 {
            return Err(ImportError::InvalidExportId(export));
        }
        match super::namespace::namespace_source(neutron.sqlite(), namespace)? {
            NamespaceSource::Local => Err(ImportError::LocalNamespace(namespace)),
            NamespaceSource::Imported {
                import,
                source_namespace,
            } => Ok(ExternalExportRef {
                database: read_import(neutron.sqlite(), import)?.database,
                source_namespace,
                export,
            }),
        }
    }
}

fn find_import(
    connection: &sqlite::Connection,
    database: HolDatabaseRef,
) -> Result<Option<ImportId>, ImportError> {
    connection
        .query_row(
            "SELECT import_id FROM hol_import WHERE schema_hash = ?1 AND image_hash = ?2",
            sqlite::params![database.schema().as_ref(), database.image().as_ref()],
            |row| row.get::<_, i64>(0).map(ImportId),
        )
        .optional()
        .map_err(Into::into)
}

pub(super) fn read_import(
    connection: &sqlite::Connection,
    id: ImportId,
) -> Result<ImportView, ImportError> {
    let row = connection
        .query_row(
            "SELECT schema_hash, image_hash FROM hol_import WHERE import_id = ?1",
            [id.get()],
            |row| Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, Vec<u8>>(1)?)),
        )
        .optional()?
        .ok_or(ImportError::UnknownImport(id))?;
    let schema = <[u8; 32]>::try_from(row.0).map_err(|_| ImportError::CorruptImport(id))?;
    let image = <[u8; 32]>::try_from(row.1).map_err(|_| ImportError::CorruptImport(id))?;
    Ok(ImportView {
        database: HolDatabaseRef::new(O256::from_array(schema), O256::from_array(image)),
    })
}

fn decode_source(
    namespace: NamespaceId,
    import: Option<i64>,
    source_namespace: Option<i64>,
) -> Result<NamespaceSource, ImportError> {
    match (import, source_namespace) {
        (None, None) => Ok(NamespaceSource::Local),
        (Some(import), Some(source_namespace)) if import >= 0 && source_namespace >= 0 => {
            Ok(NamespaceSource::Imported {
                import: ImportId(import),
                source_namespace,
            })
        }
        _ => Err(NamespaceError::CorruptSource(namespace).into()),
    }
}

fn authorize(policy: &mut impl Policy, operation: Operation) -> Result<(), ImportError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(ImportError::Denied(operation))
    }
}

/// Failure to record or inspect inert external database coordinates.
#[derive(Debug)]
pub enum ImportError {
    /// Policy denied the operation.
    Denied(Operation),
    /// Import-directory ID is absent.
    UnknownImport(ImportId),
    /// Namespace processing failed.
    Namespace(NamespaceError),
    /// The source namespace coordinate must be non-negative.
    InvalidSourceNamespace(i64),
    /// The export coordinate must be non-negative.
    InvalidExportId(ExportId),
    /// External coordinates were requested through a local namespace.
    LocalNamespace(NamespaceId),
    /// A stored import hash has the wrong representation.
    CorruptImport(ImportId),
    /// No further non-negative import ID can be allocated.
    IdOverflow,
    /// `SQLite` rejected the operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for ImportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownImport(id) => write!(formatter, "unknown import reference {}", id.get()),
            Self::Namespace(error) => error.fmt(formatter),
            Self::InvalidSourceNamespace(id) => {
                write!(formatter, "invalid source namespace ID {id}")
            }
            Self::InvalidExportId(id) => {
                write!(formatter, "invalid external export ID {}", id.get())
            }
            Self::LocalNamespace(id) => write!(formatter, "namespace {} is local", id.get()),
            Self::CorruptImport(id) => {
                write!(formatter, "import reference {} is corrupt", id.get())
            }
            Self::IdOverflow => formatter.write_str("import ID overflow"),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for ImportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Namespace(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<NamespaceError> for ImportError {
    fn from(error: NamespaceError) -> Self {
        Self::Namespace(error)
    }
}

impl From<sqlite::Error> for ImportError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::{
        AllowAll, ExportError, HolImageValidationError, HolSchema, Kind, MetadataTable,
        MetadataTarget, MetadataType, MetadataValue, NamespaceExport, ValidatedHolImage,
    };

    fn database(seed: &[u8]) -> HolDatabaseRef {
        HolDatabaseRef::new(
            O256::from_bytes([b"schema", seed].concat()),
            O256::from_bytes(seed),
        )
    }

    #[derive(Default)]
    struct TogglePolicy {
        allow: bool,
        operations: Vec<Operation>,
    }

    impl Policy for TogglePolicy {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            self.allow
        }
    }

    #[test]
    fn import_identity_is_the_exact_schema_image_pair_without_fetching() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let first = database(b"missing bytes are fine");
        let id = connection.register_import(first).unwrap();
        assert_eq!(connection.register_import(first).unwrap(), id);
        assert_eq!(connection.import_reference(id).unwrap().database, first);

        let same_image_other_schema =
            HolDatabaseRef::new(O256::from_bytes(b"other"), first.image());
        let other = connection.register_import(same_image_other_schema).unwrap();
        assert_ne!(id, other);
        assert_eq!(
            connection.import_reference(other).unwrap().database,
            same_image_other_schema
        );
    }

    #[test]
    fn denied_idempotent_operations_do_not_probe_or_write() {
        let mut connection = Connection::open_hol_in_memory(TogglePolicy {
            allow: true,
            operations: Vec::new(),
        })
        .unwrap();
        let database = database(b"policy");
        let import = connection.register_import(database).unwrap();
        connection.parts_mut().1.policy.allow = false;
        assert!(matches!(
            connection.register_import(database),
            Err(ImportError::Denied(Operation::RegisterImport))
        ));
        assert!(matches!(
            connection.create_imported_namespace(None, Some("denied"), import, 0),
            Err(ImportError::Denied(Operation::DefineImportedNamespace))
        ));
        let (neutron, hol) = connection.parts_mut();
        assert_eq!(
            neutron
                .sqlite()
                .query_row("SELECT count(*) FROM hol_import", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            1
        );
        assert_eq!(
            neutron
                .sqlite()
                .query_row("SELECT count(*) FROM hol_namespace", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            1
        );
        assert_eq!(
            hol.policy.operations,
            [
                Operation::RegisterImport,
                Operation::RegisterImport,
                Operation::DefineImportedNamespace,
            ]
        );
    }

    #[test]
    fn full_namespace_aliases_are_idempotent_inert_coordinates() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let database = database(b"unfetched");
        let import = connection.register_import(database).unwrap();
        let namespace = connection
            .create_imported_namespace(Some(NamespaceId::root()), Some("remote"), import, i64::MAX)
            .unwrap();
        assert_eq!(
            connection
                .create_imported_namespace(
                    Some(NamespaceId::root()),
                    Some("remote"),
                    import,
                    i64::MAX,
                )
                .unwrap(),
            namespace
        );
        assert_eq!(
            connection.namespace_source(namespace).unwrap(),
            NamespaceSource::Imported {
                import,
                source_namespace: i64::MAX,
            }
        );
        let external = connection
            .external_export_ref(namespace, ExportId::from_i64(999_999))
            .unwrap();
        assert_eq!(external.database(), database);
        assert_eq!(external.source_namespace(), i64::MAX);
        assert_eq!(external.export(), ExportId::from_i64(999_999));
    }

    #[test]
    fn local_and_imported_namespaces_cannot_be_overlaid() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let import = connection.register_import(database(b"remote")).unwrap();
        let local = connection
            .create_namespace(Some(NamespaceId::root()), Some("local"))
            .unwrap();
        assert!(matches!(
            connection.create_imported_namespace(
                Some(NamespaceId::root()),
                Some("local"),
                import,
                0,
            ),
            Err(ImportError::Namespace(
                NamespaceError::SourceConflict { .. }
            ))
        ));
        let remote = connection
            .create_imported_namespace(Some(NamespaceId::root()), Some("remote"), import, 0)
            .unwrap();
        assert!(matches!(
            connection.create_namespace(Some(NamespaceId::root()), Some("remote")),
            Err(NamespaceError::SourceConflict { .. })
        ));
        assert!(matches!(
            connection.create_namespace(Some(remote), Some("child")),
            Err(NamespaceError::ImportedParent(_))
        ));
        let star = connection.insert_kind(&Kind::Star).unwrap();
        assert!(matches!(
            connection.export_value(
                remote,
                ExportId::from_i64(0),
                NamespaceExport::Kind(star),
                None,
            ),
            Err(ExportError::ImportedNamespace(_))
        ));
        assert_eq!(
            connection.namespace_source(local).unwrap(),
            NamespaceSource::Local
        );
    }

    #[test]
    fn imports_and_aliases_accept_user_metadata_and_validate_detached() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::Import, "purpose", MetadataType::Text)
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::Import,
                "hol_import_purpose",
                ["purpose"],
                false,
            )
            .unwrap();
        schema
            .add_column_to(MetadataTable::Namespace, "mount_note", MetadataType::Text)
            .unwrap();
        let mut connection =
            Connection::open_hol_in_memory_with_schema(AllowAll, schema.clone()).unwrap();
        let import = connection.register_import(database(b"metadata")).unwrap();
        let namespace = connection
            .create_imported_namespace(None, Some("remote"), import, 7)
            .unwrap();
        connection
            .set_metadata(
                MetadataTarget::import(import),
                &[("purpose", MetadataValue::Text("hypothetical".to_owned()))],
            )
            .unwrap();
        connection
            .set_metadata(
                MetadataTarget::namespace(namespace),
                &[("mount_note", MetadataValue::Text("no fetch".to_owned()))],
            )
            .unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();
        let validated = ValidatedHolImage::validate_with_schema(&bytes, &schema).unwrap();
        assert_eq!(validated.counts().import_references, 1);
        assert_eq!(validated.counts().imported_namespaces, 1);
    }

    #[test]
    fn detached_validation_rejects_import_overlays_and_malformed_hashes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();
        let corrupt = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt
            .sqlite()
            .execute(
                "INSERT INTO hol_import VALUES (0, zeroblob(32), zeroblob(32))",
                [],
            )
            .unwrap();
        corrupt
            .sqlite()
            .execute(
                "INSERT INTO hol_namespace VALUES (1, 0, 'remote', 0, 0)",
                [],
            )
            .unwrap();
        corrupt
            .sqlite()
            .execute(
                "INSERT INTO hol_namespace_export VALUES (1, 0, 'kind', 1, NULL)",
                [],
            )
            .unwrap();
        let overlay = corrupt.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&overlay),
            Err(HolImageValidationError::ImportedNamespaceHasLocalExport { .. })
        ));

        let corrupt = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt
            .sqlite()
            .execute_batch("PRAGMA ignore_check_constraints = ON")
            .unwrap();
        corrupt
            .sqlite()
            .execute("INSERT INTO hol_import VALUES (0, x'00', zeroblob(32))", [])
            .unwrap();
        let malformed = corrupt.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&malformed),
            Err(HolImageValidationError::Integrity(_)
                | HolImageValidationError::MalformedImportHash(_))
        ));
    }
}
