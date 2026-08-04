use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_crypto::ed25519::VerifyingKey;
use covalence_lib_hash::{O256, o256_path};
use covalence_lib_sqlite as sqlite;

use super::{
    BOOL_TYPE_ID, ContextError, ContextId, ExportId, HolDatabaseRef, HolSchema,
    HolSchemaDescriptor, ImportId, KindError, KindId, KindView, NamespaceId, SCHEMA, STAR_ID,
    TermError, TermId, TrustedImportId, TypeError, TypeId, TypeView, ValidatedTerm,
    install_metadata_schema, kind_rank, read_context_members, read_kind, read_type,
    validate_term_inner,
};
use crate::{
    AuthenticatedSnapshot, AuthenticatedSnapshotClaim, Ed25519Verifier, Verifier as _,
    ed25519_key_id, schema_valid_snapshot_statement,
};

const MAX_GRAPH_DEPTH: usize = 512;
const STLC_BOOL_EQ_V1_SPEC: &[u8] = include_bytes!("semantics-v1.txt");

/// Returns the content hash of version one of the normative `hol-common-v2` semantics.
#[must_use]
pub fn stlc_bool_eq_v1_semantics() -> O256 {
    o256_path!(::nucleus.hol.protocol.stlc_bool_eq.v1).tag(STLC_BOOL_EQ_V1_SPEC)
}

/// Derives the signed schema identity from semantic and exact physical commitments.
#[must_use]
pub fn stlc_bool_eq_v1_schema_id(physical_schema: O256) -> O256 {
    let mut commitments = [0_u8; 64];
    commitments[..32].copy_from_slice(stlc_bool_eq_v1_semantics().as_ref());
    commitments[32..].copy_from_slice(physical_schema.as_ref());
    o256_path!(::nucleus.hol.protocol.stlc_bool_eq.sqlite_schema.v1).tag(commitments)
}

/// Counts established while validating one complete HOL database image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolImageCounts {
    /// Universal kind/type/term nodes.
    pub nodes: u64,
    /// Immutable context headers.
    pub contexts: u64,
    /// Context membership pairs.
    pub members: u64,
    /// Structurally well-formed untrusted judgement rows.
    pub untrusted_judgement_rows: u64,
    /// Structurally well-formed untrusted context-implication rows.
    pub untrusted_context_implication_rows: u64,
    /// Independently rechecked exact structural context unions.
    pub context_exact_unions: u64,
    /// Validated local namespace headers.
    pub namespaces: u64,
    /// Validated local namespace exports.
    pub namespace_exports: u64,
    /// Inert schema-qualified external database references.
    pub import_references: u64,
    /// Local namespace handles aliasing complete external namespaces.
    pub imported_namespaces: u64,
    /// Cryptographically coherent but externally untrusted persistent import assumptions.
    pub untrusted_trusted_import_rows: u64,
}

/// Exact bytes admitted as one expected tagged-node HOL physical schema.
///
/// This evidence establishes `SQLite` integrity, exact physical and semantic schema, syntax
/// typing, binder closure invariants, context well-formedness, and judgement
/// row shape. It deliberately does not establish that imported judgements are
/// true merely because their rows or optional rule labels exist. Hash-first
/// import references are checked only as inert coordinates: validation does
/// not fetch them or establish their existence, authenticity, trust, or truth.
pub struct ValidatedHolImage {
    hash: O256,
    schema: O256,
    physical_schema: O256,
    bytes: covalence_neutron::Bytes,
    counts: HolImageCounts,
}

/// Conjoined evidence that exact received bytes are authenticated and structurally valid.
///
/// This does not establish that the signer is trusted, that imported judgement rows are true, or
/// that any connection has accepted the snapshot.
pub struct AuthenticatedValidatedHolImage {
    image: ValidatedHolImage,
    claim: AuthenticatedSnapshotClaim,
}

impl AuthenticatedValidatedHolImage {
    /// Validates an authenticated snapshot against one checked portable metadata schema.
    ///
    /// The descriptor is an untrusted reconstruction witness. Exact manifest validation derives
    /// the composite schema identity independently and compares it with the authenticated claim.
    ///
    /// # Errors
    ///
    /// Returns an error if detached validation fails or the independently computed image/schema
    /// coordinates differ from the authenticated claim.
    pub fn validate_with_descriptor(
        snapshot: AuthenticatedSnapshot,
        descriptor: &HolSchemaDescriptor,
    ) -> Result<Self, AuthenticatedHolImageValidationError> {
        if descriptor.schema_id() != snapshot.schema() {
            return Err(AuthenticatedHolImageValidationError::SchemaMismatch {
                claimed: snapshot.schema(),
                actual: descriptor.schema_id(),
            });
        }
        Self::validate_with_schema(snapshot, descriptor.schema())
    }

    /// Validates an authenticated snapshot against the exact zero-metadata HOL schema.
    ///
    /// Validation uses the existing disposable-connection boundary and additionally requires the
    /// validated interpretation-qualified schema to equal the signed schema coordinate.
    ///
    /// # Errors
    ///
    /// Returns an error if detached default-schema validation fails or its independently computed
    /// image/schema coordinates differ from the authenticated claim.
    pub fn validate_default(
        snapshot: AuthenticatedSnapshot,
    ) -> Result<Self, AuthenticatedHolImageValidationError> {
        Self::validate_with_schema(snapshot, &HolSchema::new())
    }

    fn validate_with_schema(
        snapshot: AuthenticatedSnapshot,
        schema: &HolSchema,
    ) -> Result<Self, AuthenticatedHolImageValidationError> {
        let image = ValidatedHolImage::validate_with_schema(snapshot.bytes(), schema)?;
        if image.hash() != snapshot.image() {
            return Err(AuthenticatedHolImageValidationError::ImageMismatch {
                claimed: snapshot.image(),
                actual: image.hash(),
            });
        }
        if image.schema() != snapshot.schema() {
            return Err(AuthenticatedHolImageValidationError::SchemaMismatch {
                claimed: snapshot.schema(),
                actual: image.schema(),
            });
        }
        Ok(Self {
            image,
            claim: snapshot.into_claim(),
        })
    }

    /// Returns the detached structural validation evidence and exact owned bytes.
    #[must_use]
    pub const fn image(&self) -> &ValidatedHolImage {
        &self.image
    }

    /// Returns the independently authenticated exact claim.
    #[must_use]
    pub const fn claim(&self) -> &AuthenticatedSnapshotClaim {
        &self.claim
    }

    /// Consumes the conjunction and returns its independent evidence components.
    #[must_use]
    pub fn into_parts(self) -> (ValidatedHolImage, AuthenticatedSnapshotClaim) {
        (self.image, self.claim)
    }
}

impl ValidatedHolImage {
    /// Opens `bytes` only in a disposable connection and validates the full
    /// default HOL schema.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are not an `SQLite` image, integrity or
    /// exact-schema checks fail, or any structural HOL invariant is invalid.
    pub fn validate(bytes: &[u8]) -> Result<Self, HolImageValidationError> {
        Self::validate_with_schema(bytes, &HolSchema::new())
    }

    /// Validates bytes against one exact user-declared physical schema.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes fail integrity, differ from the expected
    /// core plus metadata schema, or violate any structural HOL invariant.
    pub fn validate_with_schema(
        bytes: &[u8],
        expected_schema: &HolSchema,
    ) -> Result<Self, HolImageValidationError> {
        let hash = O256::from_bytes(bytes);
        let owned = covalence_neutron::Bytes::copy_from_slice(bytes);
        let disposable = covalence_neutron::Connection::deserialize(&owned)
            .map_err(HolImageValidationError::Image)?;
        validate_integrity(disposable.sqlite())?;
        let physical_schema = validate_schema(disposable.sqlite(), expected_schema)?;
        let schema = stlc_bool_eq_v1_schema_id(physical_schema);
        let counts = validate_contents(disposable.sqlite())?;
        Ok(Self {
            hash,
            schema,
            physical_schema,
            bytes: owned,
            counts,
        })
    }

    /// Returns the content address of the exact owned bytes.
    #[must_use]
    pub const fn hash(&self) -> O256 {
        self.hash
    }

    /// Returns the signed composite semantic and physical schema identifier.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.schema
    }

    /// Returns the interpretation-qualified schema identity signed by snapshots.
    #[must_use]
    pub const fn semantic_schema(&self) -> O256 {
        self.schema
    }

    /// Returns the exact physical `SQLite` manifest identifier.
    #[must_use]
    pub const fn physical_schema(&self) -> O256 {
        self.physical_schema
    }

    /// Returns the exact domain-separated `SQLite` schema-manifest identifier.
    #[must_use]
    pub const fn physical_schema_manifest(&self) -> O256 {
        self.physical_schema
    }

    /// Returns the admitted exact bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns counts established by the validator.
    #[must_use]
    pub const fn counts(&self) -> HolImageCounts {
        self.counts
    }

    /// Consumes the evidence and returns the exact admitted bytes.
    #[must_use]
    pub fn into_bytes(self) -> covalence_neutron::Bytes {
        self.bytes
    }
}

fn validate_integrity(connection: &sqlite::Connection) -> Result<(), HolImageValidationError> {
    let results = connection
        .prepare("PRAGMA integrity_check")?
        .query_map([], |row| row.get::<_, String>(0))?
        .collect::<Result<Vec<_>, _>>()?;
    if results == ["ok"] {
        Ok(())
    } else {
        Err(HolImageValidationError::Integrity(results))
    }
}

type SchemaObject = (String, String, String, String);

fn schema_manifest(connection: &sqlite::Connection) -> Result<Vec<SchemaObject>, sqlite::Error> {
    connection
        .prepare(
            "SELECT type, name, tbl_name, sql
             FROM main.sqlite_schema
             WHERE name NOT LIKE 'sqlite_%' AND sql IS NOT NULL
             ORDER BY type COLLATE BINARY, name COLLATE BINARY,
                      tbl_name COLLATE BINARY, sql COLLATE BINARY",
        )?
        .query_map([], |row| {
            Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
        })?
        .collect()
}

fn validate_schema(
    connection: &sqlite::Connection,
    schema: &HolSchema,
) -> Result<O256, HolImageValidationError> {
    let expected = covalence_neutron::Connection::open_in_memory()
        .map_err(HolImageValidationError::Connection)?;
    expected.sqlite().execute_batch(SCHEMA)?;
    install_metadata_schema(expected.sqlite(), schema)?;
    let expected_manifest = schema_manifest(expected.sqlite())?;
    if schema_manifest(connection)? != expected_manifest {
        return Err(HolImageValidationError::SchemaMismatch);
    }
    let identity = connection.query_row(
        "SELECT version, representation FROM hol_schema",
        [],
        |row| Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?)),
    )?;
    if identity == (8, "tagged-node".to_owned()) {
        Ok(schema_manifest_id(&expected_manifest))
    } else {
        Err(HolImageValidationError::SchemaMismatch)
    }
}

pub(super) fn expected_composite_schema_id(
    schema: &HolSchema,
) -> Result<O256, HolImageValidationError> {
    let expected = covalence_neutron::Connection::open_in_memory()
        .map_err(HolImageValidationError::Connection)?;
    expected.sqlite().execute_batch(SCHEMA)?;
    install_metadata_schema(expected.sqlite(), schema)?;
    Ok(stlc_bool_eq_v1_schema_id(schema_manifest_id(
        &schema_manifest(expected.sqlite())?,
    )))
}

fn schema_manifest_id(manifest: &[SchemaObject]) -> O256 {
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&(manifest.len() as u64).to_le_bytes());
    for object in manifest {
        for field in [&object.0, &object.1, &object.2, &object.3] {
            encoded.extend_from_slice(&(field.len() as u64).to_le_bytes());
            encoded.extend_from_slice(field.as_bytes());
        }
    }
    o256_path!(::nucleus.sqlite.schema_manifest.v0).tag(&encoded)
}

#[allow(clippy::too_many_lines)]
fn validate_contents(
    connection: &sqlite::Connection,
) -> Result<HolImageCounts, HolImageValidationError> {
    let nodes = connection
        .prepare("SELECT node_id, tag, lhs, rhs, ty FROM hol_node ORDER BY node_id")?
        .query_map([], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, Option<i64>>(2)?,
                row.get::<_, Option<i64>>(3)?,
                row.get::<_, Option<i64>>(4)?,
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    validate_graph_depth(&nodes)?;
    validate_reserved_primitives(connection)?;
    let mut kind_memo = HashMap::new();
    let mut type_memo = HashSet::new();
    let mut term_memo = HashMap::new();
    for (id, tag, _, _, _) in &nodes {
        match tag.as_bytes().first() {
            Some(b'K') => {
                kind_rank(connection, KindId(*id), &mut HashSet::new(), &mut kind_memo)?;
            }
            Some(b'T') => {
                validate_type_graph(connection, TypeId(*id), &mut HashSet::new(), &mut type_memo)?;
            }
            Some(b'M') => {
                validate_term_inner(connection, TermId(*id), &mut HashSet::new(), &mut term_memo)?;
            }
            _ => return Err(HolImageValidationError::UnknownTag(tag.clone())),
        }
    }

    let contexts = connection
        .prepare("SELECT ctx_id FROM hol_context ORDER BY ctx_id")?
        .query_map([], |row| row.get::<_, i64>(0).map(ContextId))?
        .collect::<Result<Vec<_>, _>>()?;
    if !contexts.contains(&ContextId::empty()) {
        return Err(HolImageValidationError::MissingEmptyContext);
    }
    let mut member_count = 0_u64;
    let mut canonical_contexts = HashMap::new();
    for context in &contexts {
        let members = read_context_members(connection, *context)?;
        if let Some(first) = canonical_contexts.insert(members.clone(), *context) {
            return Err(HolImageValidationError::DuplicateContext {
                first,
                second: *context,
            });
        }
        member_count = member_count
            .checked_add(u64::try_from(members.len()).unwrap_or(u64::MAX))
            .ok_or(HolImageValidationError::CountOverflow)?;
        if *context == ContextId::empty() && !members.is_empty() {
            return Err(HolImageValidationError::NonemptyReservedContext);
        }
        for member in members {
            let validation = validate_term_cached(connection, member, &mut term_memo)?;
            if validation.ty != BOOL_TYPE_ID || !validation.boundary.is_empty() {
                return Err(HolImageValidationError::InvalidContextMember {
                    context: *context,
                    term: member,
                });
            }
        }
    }
    let orphan_members = connection.query_row(
        "SELECT count(*) FROM hol_context_member AS member
         WHERE NOT EXISTS (SELECT 1 FROM hol_context WHERE ctx_id = member.ctx_id)",
        [],
        |row| row.get::<_, i64>(0),
    )?;
    if orphan_members != 0 {
        return Err(HolImageValidationError::OrphanContextMember);
    }

    let judgements = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")?
        .query_map([], |row| Ok((ContextId(row.get(0)?), TermId(row.get(1)?))))?
        .collect::<Result<Vec<_>, _>>()?;
    for (context, term) in &judgements {
        if !contexts.contains(context) {
            return Err(HolImageValidationError::OrphanJudgement(*context, *term));
        }
        let validation = validate_term_cached(connection, *term, &mut term_memo)?;
        if validation.ty != BOOL_TYPE_ID || !validation.boundary.is_empty() {
            return Err(HolImageValidationError::InvalidJudgement(*context, *term));
        }
    }

    let implication_count = validate_context_implications(connection, &contexts)?;
    let context_union_count = validate_context_unions(connection, &contexts)?;
    let (
        namespace_count,
        namespace_export_count,
        import_count,
        imported_namespace_count,
        trusted_import_count,
    ) = validate_namespaces(connection, &nodes, &contexts.iter().copied().collect())?;

    Ok(HolImageCounts {
        nodes: u64::try_from(nodes.len()).map_err(|_| HolImageValidationError::CountOverflow)?,
        contexts: u64::try_from(contexts.len())
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        members: member_count,
        untrusted_judgement_rows: u64::try_from(judgements.len())
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        untrusted_context_implication_rows: u64::try_from(implication_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        context_exact_unions: u64::try_from(context_union_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        namespaces: u64::try_from(namespace_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        namespace_exports: u64::try_from(namespace_export_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        import_references: u64::try_from(import_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        imported_namespaces: u64::try_from(imported_namespace_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        untrusted_trusted_import_rows: u64::try_from(trusted_import_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
    })
}

#[allow(clippy::too_many_lines)]
fn validate_namespaces(
    connection: &sqlite::Connection,
    nodes: &[NodeRow],
    contexts: &HashSet<ContextId>,
) -> Result<(usize, usize, usize, usize, usize), HolImageValidationError> {
    let imports = connection
        .prepare("SELECT import_id, schema_hash, image_hash FROM hol_import ORDER BY import_id")?
        .query_map([], |row| {
            Ok((
                ImportId::from_i64(row.get(0)?),
                row.get::<_, Vec<u8>>(1)?,
                row.get::<_, Vec<u8>>(2)?,
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    let mut import_databases = HashMap::new();
    for (import, schema, image) in &imports {
        let schema = <[u8; 32]>::try_from(schema.as_slice())
            .map(O256::from_array)
            .map_err(|_| HolImageValidationError::MalformedImportHash(*import))?;
        let image = <[u8; 32]>::try_from(image.as_slice())
            .map(O256::from_array)
            .map_err(|_| HolImageValidationError::MalformedImportHash(*import))?;
        import_databases.insert(*import, HolDatabaseRef::new(schema, image));
    }
    let import_ids = import_databases.keys().copied().collect::<HashSet<_>>();
    let trusted_import_count = validate_trusted_imports(connection, &import_databases)?;
    let namespaces = connection
        .prepare(
            "SELECT namespace_id, parent_namespace_id, name,
                    source_import_id, source_namespace_id
             FROM hol_namespace ORDER BY namespace_id",
        )?
        .query_map([], |row| {
            Ok((
                NamespaceId::from_i64(row.get(0)?),
                row.get::<_, Option<i64>>(1)?.map(NamespaceId::from_i64),
                row.get::<_, Option<String>>(2)?,
                row.get::<_, Option<i64>>(3)?.map(ImportId::from_i64),
                row.get::<_, Option<i64>>(4)?,
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    let parents = namespaces
        .iter()
        .map(|(id, parent, _, _, _)| (*id, *parent))
        .collect::<HashMap<_, _>>();
    let sources = namespaces
        .iter()
        .map(|(id, _, _, import, source)| (*id, (*import, *source)))
        .collect::<HashMap<_, _>>();
    if parents.get(&NamespaceId::root()) != Some(&None)
        || namespaces
            .iter()
            .find(|(id, _, _, _, _)| *id == NamespaceId::root())
            .is_none_or(|(_, _, name, import, source)| {
                name.is_some() || import.is_some() || source.is_some()
            })
    {
        return Err(HolImageValidationError::InvalidRootNamespace);
    }
    let mut imported_namespaces = HashSet::new();
    for (namespace, (source_import, source_namespace)) in &sources {
        match (source_import, source_namespace) {
            (None, None) => {}
            (Some(import), Some(source_namespace))
                if import_ids.contains(import) && *source_namespace >= 0 =>
            {
                imported_namespaces.insert(*namespace);
            }
            (Some(import), Some(_)) if !import_ids.contains(import) => {
                return Err(HolImageValidationError::OrphanNamespaceImport {
                    namespace: *namespace,
                    import: *import,
                });
            }
            _ => {
                return Err(HolImageValidationError::MalformedNamespaceSource(
                    *namespace,
                ));
            }
        }
    }
    for (namespace, parent, _, _, _) in &namespaces {
        if let Some(parent) = parent
            && !parents.contains_key(parent)
        {
            return Err(HolImageValidationError::OrphanNamespaceParent {
                namespace: *namespace,
                parent: *parent,
            });
        }
        if let Some(parent) = parent
            && imported_namespaces.contains(parent)
        {
            return Err(HolImageValidationError::ImportedNamespaceHasChild {
                namespace: *namespace,
                parent: *parent,
            });
        }
    }
    let mut complete = HashSet::new();
    for root in parents.keys().copied() {
        let mut active = HashSet::new();
        let mut current = Some(root);
        while let Some(namespace) = current {
            if complete.contains(&namespace) {
                break;
            }
            if !active.insert(namespace) {
                return Err(HolImageValidationError::CyclicNamespace(namespace));
            }
            current = parents.get(&namespace).copied().flatten();
        }
        complete.extend(active);
    }

    let kinds = nodes
        .iter()
        .filter(|(_, tag, _, _, _)| tag.starts_with('K'))
        .map(|(id, _, _, _, _)| *id)
        .collect::<HashSet<_>>();
    let types = nodes
        .iter()
        .filter(|(_, tag, _, _, _)| tag.starts_with('T'))
        .map(|(id, _, _, _, _)| *id)
        .collect::<HashSet<_>>();
    let terms = nodes
        .iter()
        .filter(|(_, tag, _, _, _)| tag.starts_with('M'))
        .map(|(id, _, _, _, _)| *id)
        .collect::<HashSet<_>>();
    let exports = connection
        .prepare(
            "SELECT namespace_id, export_id, sort, local_id
             FROM hol_namespace_export ORDER BY namespace_id, export_id",
        )?
        .query_map([], |row| {
            Ok((
                NamespaceId::from_i64(row.get(0)?),
                ExportId::from_i64(row.get(1)?),
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)?,
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    for (namespace, export, sort, local_id) in &exports {
        if !parents.contains_key(namespace) {
            return Err(HolImageValidationError::OrphanNamespaceExport {
                namespace: *namespace,
                export: *export,
            });
        }
        if imported_namespaces.contains(namespace) {
            return Err(HolImageValidationError::ImportedNamespaceHasLocalExport {
                namespace: *namespace,
                export: *export,
            });
        }
        let valid = match sort.as_str() {
            "kind" => kinds.contains(local_id),
            "type" => types.contains(local_id),
            "term" => terms.contains(local_id),
            "context" => contexts.contains(&ContextId::from_i64(*local_id)),
            _ => false,
        };
        if !valid {
            return Err(HolImageValidationError::InvalidNamespaceExport {
                namespace: *namespace,
                export: *export,
                sort: sort.clone(),
                local_id: *local_id,
            });
        }
    }
    Ok((
        namespaces.len(),
        exports.len(),
        imports.len(),
        imported_namespaces.len(),
        trusted_import_count,
    ))
}

fn validate_trusted_imports(
    connection: &sqlite::Connection,
    imports: &HashMap<ImportId, HolDatabaseRef>,
) -> Result<usize, HolImageValidationError> {
    let rows = connection
        .prepare(
            "SELECT trusted_import_id, import_id, signer_hash, public_key, signature
             FROM hol_trusted_import ORDER BY trusted_import_id",
        )?
        .query_map([], |row| {
            Ok((
                TrustedImportId::from_i64(row.get(0)?),
                ImportId::from_i64(row.get(1)?),
                row.get::<_, Vec<u8>>(2)?,
                row.get::<_, Vec<u8>>(3)?,
                row.get::<_, Vec<u8>>(4)?,
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    for (id, import, signer, public_key, signature) in &rows {
        let database = imports
            .get(import)
            .ok_or(HolImageValidationError::OrphanTrustedImport {
                trusted_import: *id,
                import: *import,
            })?;
        let signer = <[u8; 32]>::try_from(signer.as_slice())
            .map(O256::from_array)
            .map_err(|_| HolImageValidationError::MalformedTrustedImport(*id))?;
        let public_key = <[u8; 32]>::try_from(public_key.as_slice())
            .map_err(|_| HolImageValidationError::MalformedTrustedImport(*id))?;
        if signature.len() != 64 {
            return Err(HolImageValidationError::MalformedTrustedImport(*id));
        }
        if ed25519_key_id(&public_key) != signer {
            return Err(HolImageValidationError::TrustedImportSignerMismatch(*id));
        }
        let verifying_key = VerifyingKey::from_bytes(&public_key)
            .map_err(|_| HolImageValidationError::MalformedTrustedImport(*id))?;
        Ed25519Verifier::new(verifying_key)
            .verify(
                signer,
                schema_valid_snapshot_statement(database.schema(), database.image()),
                signature,
            )
            .map_err(|_| HolImageValidationError::InvalidTrustedImportSignature(*id))?;
    }
    Ok(rows.len())
}

fn validate_reserved_primitives(
    connection: &sqlite::Connection,
) -> Result<(), HolImageValidationError> {
    if matches!(read_kind(connection, STAR_ID), Ok(KindView::Star))
        && matches!(read_type(connection, BOOL_TYPE_ID), Ok(TypeView::Bool))
    {
        Ok(())
    } else {
        Err(HolImageValidationError::MissingReservedPrimitive)
    }
}

fn validate_context_implications(
    connection: &sqlite::Connection,
    contexts: &[ContextId],
) -> Result<usize, HolImageValidationError> {
    let implications = connection
        .prepare(
            "SELECT antecedent_ctx_id, consequent_ctx_id
             FROM hol_context_implication
             ORDER BY antecedent_ctx_id, consequent_ctx_id",
        )?
        .query_map([], |row| {
            Ok((ContextId(row.get(0)?), ContextId(row.get(1)?)))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    for (antecedent, consequent) in &implications {
        if !contexts.contains(antecedent) || !contexts.contains(consequent) {
            return Err(HolImageValidationError::OrphanContextImplication {
                antecedent: *antecedent,
                consequent: *consequent,
            });
        }
    }
    Ok(implications.len())
}

fn validate_context_unions(
    connection: &sqlite::Connection,
    contexts: &[ContextId],
) -> Result<usize, HolImageValidationError> {
    let unions = connection
        .prepare(
            "SELECT left_ctx_id, right_ctx_id, result_ctx_id
             FROM hol_context_exact_union
             ORDER BY left_ctx_id, right_ctx_id",
        )?
        .query_map([], |row| {
            Ok((
                ContextId(row.get(0)?),
                ContextId(row.get(1)?),
                ContextId(row.get(2)?),
            ))
        })?
        .collect::<Result<Vec<_>, _>>()?;
    for (left, right, result) in &unions {
        if !contexts.contains(left) || !contexts.contains(right) || !contexts.contains(result) {
            return Err(HolImageValidationError::OrphanContextUnion {
                left: *left,
                right: *right,
                result: *result,
            });
        }
        let mut expected = read_context_members(connection, *left)?;
        expected.extend(read_context_members(connection, *right)?);
        expected.sort_unstable();
        expected.dedup();
        if read_context_members(connection, *result)? != expected {
            return Err(HolImageValidationError::InvalidContextUnion {
                left: *left,
                right: *right,
                result: *result,
            });
        }
    }
    Ok(unions.len())
}

type NodeRow = (i64, String, Option<i64>, Option<i64>, Option<i64>);

fn validate_graph_depth(nodes: &[NodeRow]) -> Result<(), HolImageValidationError> {
    let edges = nodes
        .iter()
        .map(|(id, tag, lhs, rhs, ty)| {
            let children = match tag.as_str() {
                "KARR" => vec![*lhs, *rhs],
                "TBOOL" | "TBASE" | "MBOOL" | "MFV" | "MCONST" | "MBV" => vec![*ty],
                "TARR" | "MAPP" | "MLAM" | "MEQ" => vec![*lhs, *rhs, *ty],
                _ => Vec::new(),
            }
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
            (*id, children)
        })
        .collect::<HashMap<_, _>>();
    let mut complete = HashSet::new();
    for root in edges.keys().copied() {
        if complete.contains(&root) {
            continue;
        }
        let mut active = HashSet::new();
        let mut stack = vec![(root, 0_usize, false)];
        while let Some((node, depth, exiting)) = stack.pop() {
            if exiting {
                active.remove(&node);
                complete.insert(node);
                continue;
            }
            if complete.contains(&node) {
                continue;
            }
            if depth > MAX_GRAPH_DEPTH {
                return Err(HolImageValidationError::GraphTooDeep {
                    node,
                    limit: MAX_GRAPH_DEPTH,
                });
            }
            if !active.insert(node) {
                return Err(HolImageValidationError::CyclicNodeGraph(node));
            }
            stack.push((node, depth, true));
            if let Some(children) = edges.get(&node) {
                for child in children.iter().rev() {
                    if active.contains(child) {
                        return Err(HolImageValidationError::CyclicNodeGraph(*child));
                    }
                    stack.push((*child, depth + 1, false));
                }
            }
        }
    }
    Ok(())
}

fn validate_term_cached(
    connection: &sqlite::Connection,
    id: TermId,
    memo: &mut HashMap<TermId, ValidatedTerm>,
) -> Result<ValidatedTerm, TermError> {
    validate_term_inner(connection, id, &mut HashSet::new(), memo)
}

fn validate_type_graph(
    connection: &sqlite::Connection,
    id: TypeId,
    active: &mut HashSet<TypeId>,
    memo: &mut HashSet<TypeId>,
) -> Result<(), TypeError> {
    if memo.contains(&id) {
        return Ok(());
    }
    if !active.insert(id) {
        return Err(TypeError::CorruptType(id));
    }
    match read_type(connection, id)? {
        TypeView::Bool | TypeView::Base { .. } => {}
        TypeView::Arrow { domain, codomain } => {
            validate_type_graph(connection, domain, active, memo)?;
            validate_type_graph(connection, codomain, active, memo)?;
        }
    }
    active.remove(&id);
    memo.insert(id);
    Ok(())
}

/// Failure to conjoin authenticated coordinates with detached default-schema validation.
#[derive(Debug)]
pub enum AuthenticatedHolImageValidationError {
    /// Detached HOL validation rejected the received bytes.
    Validation(HolImageValidationError),
    /// The validator independently derived a different image hash.
    ImageMismatch { claimed: O256, actual: O256 },
    /// The validator independently derived a different interpretation-qualified schema.
    SchemaMismatch { claimed: O256, actual: O256 },
}

impl fmt::Display for AuthenticatedHolImageValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Validation(error) => error.fmt(formatter),
            Self::ImageMismatch { claimed, actual } => write!(
                formatter,
                "authenticated HOL image hash {claimed} differs from validated hash {actual}"
            ),
            Self::SchemaMismatch { claimed, actual } => write!(
                formatter,
                "authenticated HOL schema {claimed} differs from validated schema {actual}"
            ),
        }
    }
}

impl StdError for AuthenticatedHolImageValidationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Validation(error) => Some(error),
            Self::ImageMismatch { .. } | Self::SchemaMismatch { .. } => None,
        }
    }
}

impl From<HolImageValidationError> for AuthenticatedHolImageValidationError {
    fn from(error: HolImageValidationError) -> Self {
        Self::Validation(error)
    }
}

/// Failure to validate an untrusted complete HOL `SQLite` image.
#[derive(Debug)]
pub enum HolImageValidationError {
    /// The image could not be installed in a disposable connection.
    Image(covalence_neutron::ImageError),
    /// The expected disposable connection could not be opened.
    Connection(covalence_neutron::ConnectionError),
    /// `SQLite` rejected an integrity, schema, or content query.
    Sqlite(sqlite::Error),
    /// `SQLite` integrity checking returned diagnostics.
    Integrity(Vec<String>),
    /// The physical schema or identity row differs from the default HOL schema.
    SchemaMismatch,
    /// A reserved primitive node is absent or has the wrong constructor.
    MissingReservedPrimitive,
    /// A node uses an unknown sort/tag family.
    UnknownTag(String),
    /// The universal node graph contains a cycle.
    CyclicNodeGraph(i64),
    /// A node graph exceeds the recursion bound used by the MVP validator.
    GraphTooDeep { node: i64, limit: usize },
    /// A kind graph is invalid.
    Kind(KindError),
    /// A type graph is invalid.
    Type(TypeError),
    /// A term graph is invalid.
    Term(TermError),
    /// A context could not be read from the image.
    Context(ContextError),
    /// Context zero is absent.
    MissingEmptyContext,
    /// Reserved context zero has members.
    NonemptyReservedContext,
    /// Two context IDs denote the same member set.
    DuplicateContext { first: ContextId, second: ContextId },
    /// A context member is non-Boolean or locally open.
    InvalidContextMember { context: ContextId, term: TermId },
    /// A membership row names no context.
    OrphanContextMember,
    /// A judgement row names no context.
    OrphanJudgement(ContextId, TermId),
    /// A judgement conclusion is non-Boolean or locally open.
    InvalidJudgement(ContextId, TermId),
    /// A context implication names an absent context.
    OrphanContextImplication {
        antecedent: ContextId,
        consequent: ContextId,
    },
    /// An exact context union names an absent context.
    OrphanContextUnion {
        left: ContextId,
        right: ContextId,
        result: ContextId,
    },
    /// An exact context union's result has the wrong member set.
    InvalidContextUnion {
        left: ContextId,
        right: ContextId,
        result: ContextId,
    },
    /// Reserved namespace zero is missing or has a non-root shape.
    InvalidRootNamespace,
    /// A namespace names an absent parent.
    OrphanNamespaceParent {
        namespace: NamespaceId,
        parent: NamespaceId,
    },
    /// The namespace parent relation contains a cycle.
    CyclicNamespace(NamespaceId),
    /// An export names an absent namespace.
    OrphanNamespaceExport {
        namespace: NamespaceId,
        export: ExportId,
    },
    /// An export's local ID does not inhabit its declared sort.
    InvalidNamespaceExport {
        namespace: NamespaceId,
        export: ExportId,
        sort: String,
        local_id: i64,
    },
    /// An import-directory row has a malformed hash representation.
    MalformedImportHash(ImportId),
    /// A persistent accepted-import row names no import reference.
    OrphanTrustedImport {
        trusted_import: TrustedImportId,
        import: ImportId,
    },
    /// A persistent accepted-import row has malformed key/signature representation.
    MalformedTrustedImport(TrustedImportId),
    /// A persistent accepted-import signer hash does not identify its public key.
    TrustedImportSignerMismatch(TrustedImportId),
    /// A persistent accepted-import signature does not authenticate the referenced coordinates.
    InvalidTrustedImportSignature(TrustedImportId),
    /// A namespace source names an absent import-directory row.
    OrphanNamespaceImport {
        namespace: NamespaceId,
        import: ImportId,
    },
    /// A namespace has only half of its imported-source discriminator.
    MalformedNamespaceSource(NamespaceId),
    /// Imported aliases cannot contain local child paths in v0.
    ImportedNamespaceHasChild {
        namespace: NamespaceId,
        parent: NamespaceId,
    },
    /// Imported aliases cannot contain local export rows.
    ImportedNamespaceHasLocalExport {
        namespace: NamespaceId,
        export: ExportId,
    },
    /// A diagnostic count exceeded its representation.
    CountOverflow,
}

impl fmt::Display for HolImageValidationError {
    #[allow(clippy::too_many_lines)]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Image(error) => error.fmt(formatter),
            Self::Connection(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
            Self::Integrity(results) => {
                write!(formatter, "SQLite integrity check failed: {results:?}")
            }
            Self::SchemaMismatch => formatter.write_str("HOL physical schema mismatch"),
            Self::MissingReservedPrimitive => {
                formatter.write_str("reserved HOL primitive is missing or corrupt")
            }
            Self::UnknownTag(tag) => write!(formatter, "unknown HOL node tag {tag:?}"),
            Self::CyclicNodeGraph(node) => {
                write!(formatter, "HOL node graph is cyclic at node {node}")
            }
            Self::GraphTooDeep { node, limit } => {
                write!(
                    formatter,
                    "HOL node {node} exceeds graph depth limit {limit}"
                )
            }
            Self::Kind(error) => error.fmt(formatter),
            Self::Type(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::Context(error) => error.fmt(formatter),
            Self::MissingEmptyContext => formatter.write_str("reserved empty context is missing"),
            Self::NonemptyReservedContext => {
                formatter.write_str("reserved empty context has members")
            }
            Self::DuplicateContext { first, second } => write!(
                formatter,
                "contexts {} and {} have identical members",
                first.get(),
                second.get()
            ),
            Self::InvalidContextMember { context, term } => write!(
                formatter,
                "term {} is not a closed Boolean member of context {}",
                term.get(),
                context.get()
            ),
            Self::OrphanContextMember => formatter.write_str("context member names no context"),
            Self::OrphanJudgement(context, term) => write!(
                formatter,
                "judgement ({}, {}) names no context",
                context.get(),
                term.get()
            ),
            Self::InvalidJudgement(context, term) => write!(
                formatter,
                "judgement ({}, {}) has an invalid conclusion",
                context.get(),
                term.get()
            ),
            Self::OrphanContextImplication {
                antecedent,
                consequent,
            } => write!(
                formatter,
                "context implication ({} => {}) names an absent context",
                antecedent.get(),
                consequent.get()
            ),
            Self::OrphanContextUnion {
                left,
                right,
                result,
            } => write!(
                formatter,
                "context union ({}, {}) -> {} names an absent context",
                left.get(),
                right.get(),
                result.get()
            ),
            Self::InvalidContextUnion {
                left,
                right,
                result,
            } => write!(
                formatter,
                "context union ({}, {}) -> {} has the wrong member set",
                left.get(),
                right.get(),
                result.get()
            ),
            Self::InvalidRootNamespace => {
                formatter.write_str("reserved root namespace is missing or corrupt")
            }
            Self::OrphanNamespaceParent { namespace, parent } => write!(
                formatter,
                "namespace {} names absent parent {}",
                namespace.get(),
                parent.get()
            ),
            Self::CyclicNamespace(namespace) => {
                write!(formatter, "namespace parent cycle at {}", namespace.get())
            }
            Self::OrphanNamespaceExport { namespace, export } => write!(
                formatter,
                "export {} names absent namespace {}",
                export.get(),
                namespace.get()
            ),
            Self::InvalidNamespaceExport {
                namespace,
                export,
                sort,
                local_id,
            } => write!(
                formatter,
                "export {} in namespace {} has invalid {sort} local ID {local_id}",
                export.get(),
                namespace.get()
            ),
            Self::MalformedImportHash(import) => {
                write!(
                    formatter,
                    "import reference {} has a malformed hash",
                    import.get()
                )
            }
            Self::OrphanTrustedImport {
                trusted_import,
                import,
            } => write!(
                formatter,
                "trusted-import assumption {} names absent import {}",
                trusted_import.get(),
                import.get()
            ),
            Self::MalformedTrustedImport(id) => write!(
                formatter,
                "trusted-import assumption {} has malformed evidence",
                id.get()
            ),
            Self::TrustedImportSignerMismatch(id) => write!(
                formatter,
                "trusted-import assumption {} has mismatched signer identity",
                id.get()
            ),
            Self::InvalidTrustedImportSignature(id) => write!(
                formatter,
                "trusted-import assumption {} has an invalid signature",
                id.get()
            ),
            Self::OrphanNamespaceImport { namespace, import } => write!(
                formatter,
                "namespace {} names absent import reference {}",
                namespace.get(),
                import.get()
            ),
            Self::MalformedNamespaceSource(namespace) => write!(
                formatter,
                "namespace {} has a malformed source discriminator",
                namespace.get()
            ),
            Self::ImportedNamespaceHasChild { namespace, parent } => write!(
                formatter,
                "namespace {} is a local child of imported namespace {}",
                namespace.get(),
                parent.get()
            ),
            Self::ImportedNamespaceHasLocalExport { namespace, export } => write!(
                formatter,
                "imported namespace {} contains local export {}",
                namespace.get(),
                export.get()
            ),
            Self::CountOverflow => formatter.write_str("HOL validation count overflow"),
        }
    }
}

impl StdError for HolImageValidationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Image(error) => Some(error),
            Self::Connection(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            Self::Kind(error) => Some(error),
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Context(error) => Some(error),
            _ => None,
        }
    }
}

impl From<sqlite::Error> for HolImageValidationError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

impl From<KindError> for HolImageValidationError {
    fn from(error: KindError) -> Self {
        Self::Kind(error)
    }
}

impl From<TypeError> for HolImageValidationError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<TermError> for HolImageValidationError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ContextError> for HolImageValidationError {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::{AllowAll, MetadataType, TermView};
    use crate::{
        Connection, Kernel, SignedSnapshotEnvelope, Signer as _, schema_valid_snapshot_statement,
    };

    fn sample_image() -> covalence_neutron::Bytes {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_beta(ContextId::empty(), identity, truth)?;
                proof.persist_theorem(&theorem)
            })
            .unwrap();
        connection.parts_mut().0.serialize().unwrap()
    }

    #[test]
    fn conjoins_authentication_with_detached_default_schema_validation() {
        let kernel = Kernel::ephemeral();
        let mut connection = kernel.open_hol(AllowAll).unwrap();
        connection.insert_bool_term(true).unwrap();
        let exported = kernel.export_hol(&mut connection).unwrap();
        let attestation = exported.attestation();
        let authenticated = SignedSnapshotEnvelope::new(
            exported.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap();

        let admitted = AuthenticatedValidatedHolImage::validate_default(authenticated).unwrap();
        assert_eq!(admitted.image().hash(), attestation.image());
        assert_eq!(admitted.image().schema(), attestation.schema());
        assert_eq!(admitted.claim().signer(), attestation.signer());
        assert_eq!(admitted.claim().signature(), attestation.signature());
    }

    #[test]
    fn authenticated_coordinates_must_match_default_detached_validation() {
        let kernel = Kernel::ephemeral();
        let bytes = sample_image();
        let image = O256::from_bytes(&bytes);
        let wrong_schema = O256::from_bytes(b"wrong HOL schema");
        let signature = kernel
            .signer()
            .sign(
                kernel.key_id(),
                schema_valid_snapshot_statement(wrong_schema, image),
            )
            .unwrap();
        let authenticated = SignedSnapshotEnvelope::new(
            &bytes,
            wrong_schema,
            image,
            kernel.key_id(),
            *kernel.verifying_key().as_bytes(),
            &signature,
        )
        .authenticate()
        .unwrap();
        assert!(matches!(
            AuthenticatedValidatedHolImage::validate_default(authenticated),
            Err(AuthenticatedHolImageValidationError::SchemaMismatch { .. })
        ));

        let malformed = b"not a SQLite database";
        let image = O256::from_bytes(malformed);
        let schema = ValidatedHolImage::validate(&bytes).unwrap().schema();
        let signature = kernel
            .signer()
            .sign(
                kernel.key_id(),
                schema_valid_snapshot_statement(schema, image),
            )
            .unwrap();
        let authenticated = SignedSnapshotEnvelope::new(
            malformed,
            schema,
            image,
            kernel.key_id(),
            *kernel.verifying_key().as_bytes(),
            &signature,
        )
        .authenticate()
        .unwrap();
        assert!(matches!(
            AuthenticatedValidatedHolImage::validate_default(authenticated),
            Err(AuthenticatedHolImageValidationError::Validation(_))
        ));
    }

    #[test]
    fn default_authenticated_validation_explicitly_rejects_custom_metadata_schema() {
        let kernel = Kernel::ephemeral();
        let mut schema = HolSchema::new();
        schema.add_column("note", MetadataType::Text).unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(AllowAll, schema).unwrap();
        let exported = kernel.export_hol(&mut connection).unwrap();
        let attestation = exported.attestation();
        let authenticated = SignedSnapshotEnvelope::new(
            exported.image().bytes(),
            attestation.schema(),
            attestation.image(),
            attestation.signer(),
            *attestation.public_key(),
            attestation.signature(),
        )
        .authenticate()
        .unwrap();

        assert!(matches!(
            AuthenticatedValidatedHolImage::validate_default(authenticated),
            Err(AuthenticatedHolImageValidationError::Validation(
                HolImageValidationError::SchemaMismatch
            ))
        ));
    }

    #[test]
    fn validates_exact_owned_bytes_without_trusting_judgement_truth() {
        let bytes = sample_image();
        let validated = ValidatedHolImage::validate(&bytes).unwrap();
        assert_eq!(validated.hash(), O256::from_bytes(&bytes));
        let expected = covalence_neutron::Connection::open_in_memory().unwrap();
        expected.sqlite().execute_batch(SCHEMA).unwrap();
        let physical = schema_manifest_id(&schema_manifest(expected.sqlite()).unwrap());
        assert_eq!(
            stlc_bool_eq_v1_semantics(),
            O256::from_hex("8bcd46ee221fbedcb3feca5d32cf137b1502873bd69094615fecab49780af5a5")
                .unwrap()
        );
        assert_eq!(
            physical,
            O256::from_hex("56858da836ea998df43c79c0a11fc203fb57eab38b32f887079e57730c200b0d")
                .unwrap()
        );
        assert_eq!(
            stlc_bool_eq_v1_schema_id(physical),
            O256::from_hex("5e5cfa1574f0c6474e4e41738813508a4c3941de3712cb50f0f03a79dffbe7a7")
                .unwrap()
        );
        assert_eq!(validated.physical_schema(), physical);
        assert_eq!(validated.schema(), stlc_bool_eq_v1_schema_id(physical));
        assert_ne!(validated.schema(), validated.physical_schema());
        assert_ne!(validated.schema(), stlc_bool_eq_v1_semantics());
        assert_eq!(validated.bytes(), bytes.as_ref());
        assert_eq!(
            validated.counts(),
            HolImageCounts {
                nodes: 8,
                contexts: 1,
                members: 0,
                untrusted_judgement_rows: 1,
                untrusted_context_implication_rows: 0,
                context_exact_unions: 0,
                namespaces: 1,
                namespace_exports: 0,
                import_references: 0,
                imported_namespaces: 0,
                untrusted_trusted_import_rows: 0,
            }
        );

        let restored = covalence_neutron::Connection::deserialize(&validated.into_bytes()).unwrap();
        let conclusion = restored
            .sqlite()
            .query_row("SELECT term_id FROM hol_judgement", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        let (view, _) = super::super::read_term(restored.sqlite(), TermId(conclusion)).unwrap();
        assert!(matches!(view, TermView::Equality { .. }));

        let untrusted = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        untrusted
            .sqlite()
            .execute(
                "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MBOOL', 0, 2)",
                [],
            )
            .unwrap();
        let falsehood = untrusted.sqlite().last_insert_rowid();
        untrusted
            .sqlite()
            .execute(
                "INSERT INTO hol_judgement(ctx_id, term_id) VALUES (0, ?1)",
                [falsehood],
            )
            .unwrap();
        untrusted
            .sqlite()
            .execute(
                "INSERT INTO hol_proof_event(ctx_id, term_id, rule)
                 VALUES (999, 999, 'forged diagnostics')",
                [],
            )
            .unwrap();
        untrusted
            .sqlite()
            .execute(
                "INSERT INTO hol_context_implication(
                     antecedent_ctx_id, consequent_ctx_id
                 ) VALUES (0, 0)",
                [],
            )
            .unwrap();
        untrusted
            .sqlite()
            .execute(
                "INSERT INTO hol_context_exact_union(
                     left_ctx_id, right_ctx_id, result_ctx_id
                 ) VALUES (0, 0, 0)",
                [],
            )
            .unwrap();
        let untrusted = untrusted.serialize().unwrap();
        let counts = ValidatedHolImage::validate(&untrusted).unwrap().counts();
        assert_eq!(counts.untrusted_judgement_rows, 2);
        assert_eq!(counts.untrusted_context_implication_rows, 1);
        assert_eq!(counts.context_exact_unions, 1);
    }

    #[test]
    fn rejects_schema_extensions_and_semantically_corrupt_terms() {
        let bytes = sample_image();
        let extended = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        extended
            .sqlite()
            .execute("CREATE TABLE extra(value INTEGER)", [])
            .unwrap();
        let extended = extended.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&extended),
            Err(HolImageValidationError::SchemaMismatch)
        ));

        let corrupt = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        let application = corrupt
            .sqlite()
            .query_row(
                "SELECT node_id FROM hol_node WHERE tag = 'MAPP'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        corrupt
            .sqlite()
            .execute(
                "UPDATE hol_node SET lhs = rhs WHERE node_id = ?1",
                [application],
            )
            .unwrap();
        let corrupt = corrupt.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&corrupt),
            Err(HolImageValidationError::Term(_))
        ));
    }

    #[test]
    fn detached_validation_rechecks_opaque_signature_declarations() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let base = connection.insert_base_type(100).unwrap();
        let constant = connection.insert_constant(200, base).unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();

        let corrupt_constant = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt_constant
            .sqlite()
            .execute(
                "UPDATE hol_node SET ty = 999 WHERE node_id = ?1",
                [constant.get()],
            )
            .unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&corrupt_constant.serialize().unwrap()),
            Err(HolImageValidationError::Term(TermError::Type(
                TypeError::UnknownType(_)
            )))
        ));

        let corrupt_base = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt_base
            .sqlite()
            .execute_batch("PRAGMA ignore_check_constraints = ON")
            .unwrap();
        corrupt_base
            .sqlite()
            .execute(
                "UPDATE hol_node SET ty = 2 WHERE node_id = ?1",
                [base.get()],
            )
            .unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&corrupt_base.serialize().unwrap()),
            Err(HolImageValidationError::Integrity(_)
                | HolImageValidationError::Type(TypeError::CorruptType(_)))
        ));
    }

    #[test]
    fn rejects_non_sqlite_bytes() {
        assert!(ValidatedHolImage::validate(b"not sqlite").is_err());
    }

    #[test]
    fn physical_schema_rejects_null_payloads_and_moved_primitives() {
        let connection = covalence_neutron::Connection::open_in_memory().unwrap();
        connection.sqlite().execute_batch(SCHEMA).unwrap();
        assert!(
            connection
                .sqlite()
                .execute(
                    "INSERT INTO hol_node(node_id, tag, ty) VALUES (99, 'MBOOL', 2)",
                    [],
                )
                .is_err()
        );
        assert!(
            connection
                .sqlite()
                .execute(
                    "INSERT INTO hol_node(node_id, tag, ty) VALUES (99, 'TBOOL', 1)",
                    [],
                )
                .is_err()
        );
    }

    #[test]
    fn validates_only_the_exact_declared_metadata_schema() {
        let mut schema = HolSchema::new();
        schema.add_column("source", MetadataType::Text).unwrap();
        schema.add_index("hol_source", ["source"], false).unwrap();
        let mut connection =
            Connection::open_hol_in_memory_with_schema(AllowAll, schema.clone()).unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();

        assert!(matches!(
            ValidatedHolImage::validate(&bytes),
            Err(HolImageValidationError::SchemaMismatch)
        ));
        let validated = ValidatedHolImage::validate_with_schema(&bytes, &schema).unwrap();
        assert_eq!(validated.bytes(), bytes.as_ref());
        assert_eq!(
            validated.semantic_schema(),
            stlc_bool_eq_v1_schema_id(validated.physical_schema_manifest())
        );
        let default = ValidatedHolImage::validate(&sample_image()).unwrap();
        assert_ne!(
            validated.physical_schema_manifest(),
            default.physical_schema_manifest()
        );
        assert_ne!(validated.semantic_schema(), default.semantic_schema());
    }

    #[test]
    fn rejects_missing_primitives_and_duplicate_contexts() {
        let bytes = sample_image();
        let missing = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        missing
            .sqlite()
            .execute("DELETE FROM hol_node WHERE node_id IN (1, 2)", [])
            .unwrap();
        let missing = missing.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&missing),
            Err(HolImageValidationError::MissingReservedPrimitive)
        ));

        let duplicate = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        duplicate
            .sqlite()
            .execute("INSERT INTO hol_context(ctx_id) VALUES (1)", [])
            .unwrap();
        let duplicate = duplicate.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&duplicate),
            Err(HolImageValidationError::DuplicateContext { .. })
        ));

        let orphan = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        orphan
            .sqlite()
            .execute(
                "INSERT INTO hol_context_implication(
                     antecedent_ctx_id, consequent_ctx_id
                 ) VALUES (0, 999)",
                [],
            )
            .unwrap();
        let orphan = orphan.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&orphan),
            Err(HolImageValidationError::OrphanContextImplication { .. })
        ));
    }

    #[test]
    fn detached_validation_rechecks_exact_context_unions() {
        let bytes = sample_image();
        let orphan = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        orphan
            .sqlite()
            .execute(
                "INSERT INTO hol_context_exact_union(
                     left_ctx_id, right_ctx_id, result_ctx_id
                 ) VALUES (0, 0, 999)",
                [],
            )
            .unwrap();
        let orphan = orphan.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&orphan),
            Err(HolImageValidationError::OrphanContextUnion { .. })
        ));

        let invalid = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        invalid
            .sqlite()
            .execute(
                "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MBOOL', 0, 2)",
                [],
            )
            .unwrap();
        let falsehood = invalid.sqlite().last_insert_rowid();
        invalid
            .sqlite()
            .execute("INSERT INTO hol_context(ctx_id) VALUES (1)", [])
            .unwrap();
        invalid
            .sqlite()
            .execute(
                "INSERT INTO hol_context_member(ctx_id, term_id) VALUES (1, ?1)",
                [falsehood],
            )
            .unwrap();
        invalid
            .sqlite()
            .execute(
                "INSERT INTO hol_context_exact_union(
                     left_ctx_id, right_ctx_id, result_ctx_id
                 ) VALUES (1, 0, 0)",
                [],
            )
            .unwrap();
        let invalid = invalid.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&invalid),
            Err(HolImageValidationError::InvalidContextUnion { .. })
        ));
    }
}
