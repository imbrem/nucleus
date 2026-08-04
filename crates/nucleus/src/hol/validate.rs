use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use super::{
    BOOL_TYPE_ID, ContextError, ContextId, HolSchema, KindError, KindId, KindView, SCHEMA, STAR_ID,
    TermError, TermId, TypeError, TypeId, TypeView, ValidatedTerm, install_metadata_schema,
    kind_rank, read_context_members, read_kind, read_type, validate_term_inner,
};

const MAX_GRAPH_DEPTH: usize = 512;

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
}

/// Exact bytes admitted as one expected tagged-node HOL physical schema.
///
/// This evidence establishes `SQLite` integrity, exact physical schema, syntax
/// typing, binder closure invariants, context well-formedness, and judgement
/// row shape. It deliberately does not establish that imported judgements are
/// true merely because their rows or optional rule labels exist.
pub struct ValidatedHolImage {
    hash: O256,
    schema: O256,
    bytes: covalence_neutron::Bytes,
    counts: HolImageCounts,
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
        let schema = validate_schema(disposable.sqlite(), expected_schema)?;
        let counts = validate_contents(disposable.sqlite())?;
        Ok(Self {
            hash,
            schema,
            bytes: owned,
            counts,
        })
    }

    /// Returns the content address of the exact owned bytes.
    #[must_use]
    pub const fn hash(&self) -> O256 {
        self.hash
    }

    /// Returns the physical schema identifier used for this validation.
    #[must_use]
    pub const fn schema(&self) -> O256 {
        self.schema
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
             ORDER BY type, name",
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
    if identity == (2, "tagged-node".to_owned()) {
        Ok(schema_manifest_id(&expected_manifest))
    } else {
        Err(HolImageValidationError::SchemaMismatch)
    }
}

fn schema_manifest_id(manifest: &[SchemaObject]) -> O256 {
    let mut encoded = Vec::new();
    for object in manifest {
        for field in [&object.0, &object.1, &object.2, &object.3] {
            encoded.extend_from_slice(&(field.len() as u64).to_le_bytes());
            encoded.extend_from_slice(field.as_bytes());
        }
    }
    O256::from_bytes(&encoded)
}

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

    Ok(HolImageCounts {
        nodes: u64::try_from(nodes.len()).map_err(|_| HolImageValidationError::CountOverflow)?,
        contexts: u64::try_from(contexts.len())
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        members: member_count,
        untrusted_judgement_rows: u64::try_from(judgements.len())
            .map_err(|_| HolImageValidationError::CountOverflow)?,
        untrusted_context_implication_rows: u64::try_from(implication_count)
            .map_err(|_| HolImageValidationError::CountOverflow)?,
    })
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

type NodeRow = (i64, String, Option<i64>, Option<i64>, Option<i64>);

fn validate_graph_depth(nodes: &[NodeRow]) -> Result<(), HolImageValidationError> {
    let edges = nodes
        .iter()
        .map(|(id, tag, lhs, rhs, ty)| {
            let children = match tag.as_str() {
                "KARR" => vec![*lhs, *rhs],
                "TBOOL" | "MBOOL" | "MFV" | "MBV" => vec![*ty],
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
        TypeView::Bool => {}
        TypeView::Arrow { domain, codomain } => {
            validate_type_graph(connection, domain, active, memo)?;
            validate_type_graph(connection, codomain, active, memo)?;
        }
    }
    active.remove(&id);
    memo.insert(id);
    Ok(())
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
    /// A diagnostic count exceeded its representation.
    CountOverflow,
}

impl fmt::Display for HolImageValidationError {
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
    use crate::Connection;
    use crate::hol::{AllowAll, MetadataType, TermView};

    fn sample_image() -> covalence_neutron::Bytes {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        connection
            .with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), identity, truth)
                    .map(|_| ())
            })
            .unwrap();
        connection.parts_mut().0.serialize().unwrap()
    }

    #[test]
    fn validates_exact_owned_bytes_without_trusting_judgement_truth() {
        let bytes = sample_image();
        let validated = ValidatedHolImage::validate(&bytes).unwrap();
        assert_eq!(validated.hash(), O256::from_bytes(&bytes));
        let expected = covalence_neutron::Connection::open_in_memory().unwrap();
        expected.sqlite().execute_batch(SCHEMA).unwrap();
        assert_eq!(
            validated.schema(),
            schema_manifest_id(&schema_manifest(expected.sqlite()).unwrap())
        );
        assert_eq!(validated.bytes(), bytes.as_ref());
        assert_eq!(
            validated.counts(),
            HolImageCounts {
                nodes: 8,
                contexts: 1,
                members: 0,
                untrusted_judgement_rows: 1,
                untrusted_context_implication_rows: 0,
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
        let untrusted = untrusted.serialize().unwrap();
        let counts = ValidatedHolImage::validate(&untrusted).unwrap().counts();
        assert_eq!(counts.untrusted_judgement_rows, 2);
        assert_eq!(counts.untrusted_context_implication_rows, 1);
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
}
