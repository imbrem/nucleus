//! Minimal HOL-omega protocol, beginning with canonical kinds.

use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use crate::Connection;

const SCHEMA: &str = include_str!("hol/schema.sql");
const STAR_ID: KindId = KindId(1);

/// A HOL-omega kind expression accepted by the representation-independent API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind {
    /// The kind of ordinary types.
    Star,
    /// A type-operator kind.
    Arrow(Box<Self>, Box<Self>),
}

impl Kind {
    /// Constructs a type-operator kind.
    #[must_use]
    pub fn arrow(domain: Self, codomain: Self) -> Self {
        Self::Arrow(Box::new(domain), Box::new(codomain))
    }
}

/// Database-local identity of an admitted kind.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KindId(i64);

impl KindId {
    /// Creates a database-local lookup handle from its stored integer.
    ///
    /// Operations still validate that the ID names a kind in their connection.
    #[must_use]
    pub const fn from_i64(id: i64) -> Self {
        Self(id)
    }

    /// Returns the integer stored in the HOL database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One admitted kind row, independent of its physical representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KindView {
    /// The canonical kind of ordinary types.
    Star,
    /// A canonical type-operator kind.
    Arrow {
        /// Kind accepted by the operator.
        domain: KindId,
        /// Kind returned by the operator.
        codomain: KindId,
    },
}

/// A policy-visible trusted HOL operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    /// Read a kind constructor or its derived rank.
    ReadKind,
    /// Validate and canonically intern a kind.
    InsertKind,
    /// Read user-declared metadata attached to an admitted node.
    ReadMetadata,
    /// Write user-declared metadata attached to an admitted node.
    WriteMetadata,
}

/// `SQLite` storage class of a user-declared metadata column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MetadataType {
    /// Signed 64-bit integer metadata.
    Integer,
    /// IEEE-754 binary64 metadata.
    Real,
    /// UTF-8 text metadata.
    Text,
    /// Arbitrary byte-string metadata.
    Blob,
    /// Any `SQLite` value, preserving its storage class.
    Any,
}

impl MetadataType {
    const fn sql(self) -> &'static str {
        match self {
            Self::Integer => "INTEGER",
            Self::Real => "REAL",
            Self::Text => "TEXT",
            Self::Blob => "BLOB",
            Self::Any => "ANY",
        }
    }
}

/// A value read from or written to a user metadata column.
#[derive(Clone, Debug, PartialEq)]
pub enum MetadataValue {
    /// SQL NULL.
    Null,
    /// Signed 64-bit integer.
    Integer(i64),
    /// IEEE-754 binary64 value.
    Real(f64),
    /// UTF-8 text.
    Text(String),
    /// Arbitrary bytes.
    Blob(Vec<u8>),
}

impl From<MetadataValue> for sqlite::types::Value {
    fn from(value: MetadataValue) -> Self {
        match value {
            MetadataValue::Null => Self::Null,
            MetadataValue::Integer(value) => Self::Integer(value),
            MetadataValue::Real(value) => Self::Real(value),
            MetadataValue::Text(value) => Self::Text(value),
            MetadataValue::Blob(value) => Self::Blob(value),
        }
    }
}

impl From<sqlite::types::Value> for MetadataValue {
    fn from(value: sqlite::types::Value) -> Self {
        match value {
            sqlite::types::Value::Null => Self::Null,
            sqlite::types::Value::Integer(value) => Self::Integer(value),
            sqlite::types::Value::Real(value) => Self::Real(value),
            sqlite::types::Value::Text(value) => Self::Text(value),
            sqlite::types::Value::Blob(value) => Self::Blob(value),
        }
    }
}

#[derive(Clone, Debug)]
struct MetadataColumn {
    name: String,
    storage: MetadataType,
}

#[derive(Clone, Debug)]
struct MetadataIndex {
    name: String,
    columns: Vec<String>,
    unique: bool,
}

/// User-selected physical metadata columns and ordinary `SQLite` indexes.
///
/// Metadata never participates in canonical HOL node identity.
#[derive(Clone, Debug, Default)]
pub struct HolSchema {
    columns: Vec<MetadataColumn>,
    indexes: Vec<MetadataIndex>,
}

impl HolSchema {
    /// Creates the zero-metadata schema.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            columns: Vec::new(),
            indexes: Vec::new(),
        }
    }

    /// Adds a nullable user metadata column to `hol_node`.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reserved, NUL-containing, or duplicate
    /// identifier.
    pub fn add_column(
        &mut self,
        name: impl Into<String>,
        storage: MetadataType,
    ) -> Result<(), MetadataSchemaError> {
        let name = name.into();
        validate_identifier(&name)?;
        if is_core_column(&name)
            || self
                .columns
                .iter()
                .any(|column| column.name.eq_ignore_ascii_case(&name))
        {
            return Err(MetadataSchemaError::DuplicateOrReservedColumn(name));
        }
        self.columns.push(MetadataColumn { name, storage });
        Ok(())
    }

    /// Adds an index over one or more declared metadata columns.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid/duplicate index name, an empty column
    /// list, or a column which has not been declared on this schema.
    pub fn add_index<I, S>(
        &mut self,
        name: impl Into<String>,
        columns: I,
        unique: bool,
    ) -> Result<(), MetadataSchemaError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let name = name.into();
        validate_identifier(&name)?;
        if self
            .indexes
            .iter()
            .any(|index| index.name.eq_ignore_ascii_case(&name))
        {
            return Err(MetadataSchemaError::DuplicateIndex(name));
        }
        let columns: Vec<String> = columns.into_iter().map(Into::into).collect();
        if columns.is_empty() {
            return Err(MetadataSchemaError::EmptyIndex(name));
        }
        for column in &columns {
            if !self
                .columns
                .iter()
                .any(|declared| declared.name.eq_ignore_ascii_case(column))
            {
                return Err(MetadataSchemaError::UnknownColumn(column.clone()));
            }
        }
        self.indexes.push(MetadataIndex {
            name,
            columns,
            unique,
        });
        Ok(())
    }

    fn column(&self, name: &str) -> Option<&MetadataColumn> {
        self.columns
            .iter()
            .find(|column| column.name.eq_ignore_ascii_case(name))
    }

    /// Returns the declared storage class of a metadata column.
    #[must_use]
    pub fn metadata_type(&self, name: &str) -> Option<MetadataType> {
        self.column(name).map(|column| column.storage)
    }
}

/// Connection-local permission and operation-recording policy.
pub trait Policy {
    /// Returns whether this operation is permitted.
    ///
    /// Implementations may record the operation before returning.
    fn allows(&mut self, operation: Operation) -> bool;
}

/// A policy which permits every currently implemented HOL operation.
#[derive(Clone, Copy, Debug, Default)]
pub struct AllowAll;

impl Policy for AllowAll {
    fn allows(&mut self, _operation: Operation) -> bool {
        true
    }
}

/// HOL protocol state carried by [`Connection`].
pub struct Hol<P> {
    policy: P,
    schema: HolSchema,
}

impl<P> Hol<P> {
    /// Returns this connection's policy state.
    #[must_use]
    pub const fn policy(&self) -> &P {
        &self.policy
    }

    /// Returns the connection's declared metadata schema.
    #[must_use]
    pub const fn schema(&self) -> &HolSchema {
        &self.schema
    }
}

impl<P: Policy> Connection<Hol<P>> {
    /// Opens a new in-memory HOL-omega store and installs schema version zero.
    ///
    /// # Errors
    ///
    /// Returns an error if the Neutron connection or HOL schema cannot be
    /// opened.
    pub fn open_hol_in_memory(policy: P) -> Result<Self, HolOpenError> {
        Self::open_hol_in_memory_with_schema(policy, HolSchema::new())
    }

    /// Opens an in-memory store with user metadata columns and indexes.
    ///
    /// # Errors
    ///
    /// Returns an error if the Neutron connection or complete physical schema
    /// cannot be installed atomically.
    pub fn open_hol_in_memory_with_schema(
        policy: P,
        schema: HolSchema,
    ) -> Result<Self, HolOpenError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        transaction.execute_batch(SCHEMA)?;
        install_metadata_schema(&transaction, &schema)?;
        transaction.commit()?;
        Ok(Self::from_neutron(neutron, Hol { policy, schema }))
    }

    /// Validates and canonically interns a kind.
    ///
    /// The normative rank convention is `rank(star) = 0` and
    /// `rank(K -> L) = max(rank(K) + 1, rank(L))`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies insertion or the store rejects the
    /// transaction.
    pub fn insert_kind(&mut self, kind: &Kind) -> Result<KindId, KindError> {
        self.insert_kind_with_metadata(kind, &[])
    }

    /// Interns a kind and sets declared metadata on its canonical root row.
    ///
    /// If the kind already exists, supplied metadata replaces the selected
    /// single-valued columns. Metadata is not part of canonical identity.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies either operation, a column is unknown
    /// or repeated, or `SQLite` rejects the atomic transaction.
    pub fn insert_kind_with_metadata(
        &mut self,
        kind: &Kind,
        metadata: &[(&str, MetadataValue)],
    ) -> Result<KindId, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::InsertKind)?;
        if !metadata.is_empty() {
            authorize(&mut hol.policy, Operation::WriteMetadata)?;
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let id = intern_kind(&transaction, kind)?;
        write_metadata(&transaction, &hol.schema, id, metadata)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Canonically interns a kind arrow from already-admitted child IDs.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies insertion, either child is not an
    /// admitted kind, or the store rejects the transaction.
    pub fn insert_kind_arrow(
        &mut self,
        domain: KindId,
        codomain: KindId,
    ) -> Result<KindId, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::InsertKind)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_kind(&transaction, domain)?;
        read_kind(&transaction, codomain)?;
        let id = intern_kind_arrow(&transaction, domain, codomain)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads the constructor of an admitted kind.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is unknown, or the
    /// universal node row is corrupt.
    pub fn kind(&mut self, id: KindId) -> Result<KindView, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadKind)?;
        read_kind(neutron.sqlite(), id)
    }

    /// Derives the rank of an admitted kind from its node graph.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is unknown, the node
    /// graph is malformed or cyclic, or the derived rank overflows.
    pub fn kind_rank(&mut self, id: KindId) -> Result<u32, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadKind)?;
        kind_rank(
            neutron.sqlite(),
            id,
            &mut HashSet::new(),
            &mut HashMap::new(),
        )
    }

    /// Reads selected user metadata columns from an admitted kind.
    ///
    /// Values are returned in the requested order.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, a column is undeclared, the
    /// kind is unknown/corrupt, or `SQLite` rejects the query.
    pub fn kind_metadata(
        &mut self,
        id: KindId,
        columns: &[&str],
    ) -> Result<Vec<MetadataValue>, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadMetadata)?;
        read_kind(neutron.sqlite(), id)?;
        read_metadata(neutron.sqlite(), &hol.schema, id, columns)
    }
}

fn install_metadata_schema(
    connection: &sqlite::Connection,
    schema: &HolSchema,
) -> Result<(), sqlite::Error> {
    for column in &schema.columns {
        connection.execute_batch(&format!(
            "ALTER TABLE hol_node ADD COLUMN {} {}",
            quote_identifier(&column.name),
            column.storage.sql()
        ))?;
    }
    for index in &schema.indexes {
        let columns = index
            .columns
            .iter()
            .map(|column| quote_identifier(column))
            .collect::<Vec<_>>()
            .join(", ");
        connection.execute_batch(&format!(
            "CREATE {}INDEX {} ON hol_node({columns})",
            if index.unique { "UNIQUE " } else { "" },
            quote_identifier(&index.name),
        ))?;
    }
    Ok(())
}

fn write_metadata(
    connection: &sqlite::Connection,
    schema: &HolSchema,
    id: KindId,
    metadata: &[(&str, MetadataValue)],
) -> Result<(), KindError> {
    if metadata.is_empty() {
        return Ok(());
    }
    let mut seen = HashSet::new();
    let mut assignments = Vec::with_capacity(metadata.len());
    let mut values = Vec::with_capacity(metadata.len() + 1);
    for (name, value) in metadata {
        let column = schema
            .column(name)
            .ok_or_else(|| KindError::UnknownMetadataColumn((*name).to_owned()))?;
        let folded = column.name.to_ascii_lowercase();
        if !seen.insert(folded) {
            return Err(KindError::DuplicateMetadataColumn((*name).to_owned()));
        }
        assignments.push(format!("{} = ?", quote_identifier(&column.name)));
        values.push(sqlite::types::Value::from(value.clone()));
    }
    values.push(sqlite::types::Value::Integer(id.0));
    let sql = format!(
        "UPDATE hol_node SET {} WHERE node_id = ?",
        assignments.join(", ")
    );
    connection.execute(&sql, sqlite::params_from_iter(values.iter()))?;
    Ok(())
}

fn read_metadata(
    connection: &sqlite::Connection,
    schema: &HolSchema,
    id: KindId,
    columns: &[&str],
) -> Result<Vec<MetadataValue>, KindError> {
    if columns.is_empty() {
        return Ok(Vec::new());
    }
    let columns = columns
        .iter()
        .map(|name| {
            schema
                .column(name)
                .map(|column| quote_identifier(&column.name))
                .ok_or_else(|| KindError::UnknownMetadataColumn((*name).to_owned()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let sql = format!(
        "SELECT {} FROM hol_node WHERE node_id = ?1",
        columns.join(", ")
    );
    connection
        .query_row(&sql, [id.0], |row| {
            (0..columns.len())
                .map(|index| row.get::<_, sqlite::types::Value>(index))
                .collect::<Result<Vec<_>, _>>()
        })?
        .into_iter()
        .map(|value| Ok(MetadataValue::from(value)))
        .collect()
}

fn validate_identifier(identifier: &str) -> Result<(), MetadataSchemaError> {
    if identifier.is_empty() || identifier.contains('\0') {
        Err(MetadataSchemaError::InvalidIdentifier(
            identifier.to_owned(),
        ))
    } else {
        Ok(())
    }
}

fn is_core_column(name: &str) -> bool {
    ["node_id", "tag", "lhs", "rhs", "ty"]
        .iter()
        .any(|core| core.eq_ignore_ascii_case(name))
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

fn authorize(policy: &mut impl Policy, operation: Operation) -> Result<(), KindError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(KindError::Denied(operation))
    }
}

fn intern_kind(connection: &sqlite::Connection, kind: &Kind) -> Result<KindId, KindError> {
    let Kind::Arrow(domain, codomain) = kind else {
        return Ok(STAR_ID);
    };
    let domain = intern_kind(connection, domain)?;
    let codomain = intern_kind(connection, codomain)?;
    intern_kind_arrow(connection, domain, codomain)
}

fn intern_kind_arrow(
    connection: &sqlite::Connection,
    domain: KindId,
    codomain: KindId,
) -> Result<KindId, KindError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'KARR' AND lhs = ?1 AND rhs = ?2 AND ty IS NULL",
            [domain.0, codomain.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(KindId(id));
    }

    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs) VALUES ('KARR', ?1, ?2)",
        [domain.0, codomain.0],
    )?;
    let id = KindId(connection.last_insert_rowid());
    Ok(id)
}

fn read_kind(connection: &sqlite::Connection, id: KindId) -> Result<KindView, KindError> {
    let row = connection
        .query_row(
            "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
            [id.0],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, Option<i64>>(1)?,
                    row.get::<_, Option<i64>>(2)?,
                    row.get::<_, Option<i64>>(3)?,
                ))
            },
        )
        .optional()?
        .ok_or(KindError::UnknownKind(id))?;
    match row {
        (tag, None, None, None) if tag == "KSTAR" => Ok(KindView::Star),
        (tag, Some(domain), Some(codomain), None) if tag == "KARR" => Ok(KindView::Arrow {
            domain: KindId(domain),
            codomain: KindId(codomain),
        }),
        _ => Err(KindError::CorruptKind(id)),
    }
}

fn kind_rank(
    connection: &sqlite::Connection,
    id: KindId,
    active: &mut HashSet<KindId>,
    memo: &mut HashMap<KindId, u32>,
) -> Result<u32, KindError> {
    if let Some(rank) = memo.get(&id) {
        return Ok(*rank);
    }
    if !active.insert(id) {
        return Err(KindError::CorruptKind(id));
    }
    let result: Result<u32, KindError> = match read_kind(connection, id)? {
        KindView::Star => Ok(0),
        KindView::Arrow { domain, codomain } => {
            let domain = kind_rank(connection, domain, active, memo)?;
            let codomain = kind_rank(connection, codomain, active, memo)?;
            Ok(domain
                .checked_add(1)
                .ok_or(KindError::RankOverflow)?
                .max(codomain))
        }
    };
    active.remove(&id);
    let rank = result?;
    memo.insert(id, rank);
    Ok(rank)
}

/// Failure to open a HOL connection.
#[derive(Debug)]
pub enum HolOpenError {
    /// The raw connection could not be opened.
    Connection(covalence_neutron::ConnectionError),
    /// The schema could not be installed.
    Schema(sqlite::Error),
}

impl fmt::Display for HolOpenError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Connection(error) => write!(formatter, "could not open HOL connection: {error}"),
            Self::Schema(error) => write!(formatter, "could not install HOL schema: {error}"),
        }
    }
}

impl StdError for HolOpenError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Connection(error) => Some(error),
            Self::Schema(error) => Some(error),
        }
    }
}

impl From<covalence_neutron::ConnectionError> for HolOpenError {
    fn from(error: covalence_neutron::ConnectionError) -> Self {
        Self::Connection(error)
    }
}

impl From<sqlite::Error> for HolOpenError {
    fn from(error: sqlite::Error) -> Self {
        Self::Schema(error)
    }
}

/// Invalid user metadata schema declaration.
#[derive(Debug, Eq, PartialEq)]
pub enum MetadataSchemaError {
    /// `SQLite` cannot represent this identifier.
    InvalidIdentifier(String),
    /// A column duplicates another metadata column or a fixed core column.
    DuplicateOrReservedColumn(String),
    /// An index duplicates an earlier user index name.
    DuplicateIndex(String),
    /// An index has no columns.
    EmptyIndex(String),
    /// An index names a column not declared as metadata.
    UnknownColumn(String),
}

impl fmt::Display for MetadataSchemaError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidIdentifier(name) => {
                write!(formatter, "invalid SQLite identifier {name:?}")
            }
            Self::DuplicateOrReservedColumn(name) => {
                write!(formatter, "duplicate or reserved metadata column {name:?}")
            }
            Self::DuplicateIndex(name) => write!(formatter, "duplicate metadata index {name:?}"),
            Self::EmptyIndex(name) => write!(formatter, "metadata index {name:?} has no columns"),
            Self::UnknownColumn(name) => write!(formatter, "unknown metadata column {name:?}"),
        }
    }
}

impl StdError for MetadataSchemaError {}

/// Failure to insert or inspect an admitted kind.
#[derive(Debug)]
pub enum KindError {
    /// Policy denied the operation.
    Denied(Operation),
    /// No kind has the requested ID.
    UnknownKind(KindId),
    /// A universal node has an invalid kind shape or constructor.
    CorruptKind(KindId),
    /// The normative rank does not fit in `SQLite`'s integer representation.
    RankOverflow,
    /// A metadata operation names a column absent from this connection.
    UnknownMetadataColumn(String),
    /// One metadata update names the same column more than once.
    DuplicateMetadataColumn(String),
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for KindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownKind(id) => write!(formatter, "unknown kind {}", id.get()),
            Self::CorruptKind(id) => write!(formatter, "kind {} is structurally corrupt", id.get()),
            Self::RankOverflow => formatter.write_str("kind rank overflow"),
            Self::UnknownMetadataColumn(name) => {
                write!(formatter, "unknown HOL metadata column {name:?}")
            }
            Self::DuplicateMetadataColumn(name) => {
                write!(formatter, "duplicate HOL metadata column {name:?}")
            }
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for KindError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::UnknownKind(_)
            | Self::CorruptKind(_)
            | Self::RankOverflow
            | Self::UnknownMetadataColumn(_)
            | Self::DuplicateMetadataColumn(_) => None,
        }
    }
}

impl From<sqlite::Error> for KindError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct RecordingPolicy {
        allowed: bool,
        operations: Vec<Operation>,
    }

    impl Policy for RecordingPolicy {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            self.allowed
        }
    }

    #[test]
    fn canonically_interns_kinds_and_computes_order_rank() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let star = connection.insert_kind(&Kind::Star).unwrap();
        let unary = connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        let higher = connection
            .insert_kind(&Kind::arrow(
                Kind::arrow(Kind::Star, Kind::Star),
                Kind::Star,
            ))
            .unwrap();

        assert_eq!(star, STAR_ID);
        assert_eq!(
            unary,
            connection
                .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
                .unwrap()
        );
        assert_eq!(connection.kind(star).unwrap(), KindView::Star);
        assert_eq!(
            connection.kind(unary).unwrap(),
            KindView::Arrow {
                domain: star,
                codomain: star,
            }
        );
        assert_eq!(connection.kind_rank(star).unwrap(), 0);
        assert_eq!(connection.kind_rank(unary).unwrap(), 1);
        assert_eq!(connection.kind_rank(higher).unwrap(), 2);
    }

    #[test]
    fn policy_controls_and_records_every_public_operation() {
        let mut connection = Connection::open_hol_in_memory(RecordingPolicy::default()).unwrap();
        assert!(matches!(
            connection.insert_kind(&Kind::Star),
            Err(KindError::Denied(Operation::InsertKind))
        ));
        assert!(matches!(
            connection.kind(STAR_ID),
            Err(KindError::Denied(Operation::ReadKind))
        ));
        assert_eq!(
            connection.protocol().policy().operations,
            [Operation::InsertKind, Operation::ReadKind]
        );
    }

    #[test]
    fn detects_invalid_constructor_tags() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let arrow = connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch("PRAGMA ignore_check_constraints = ON")
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "UPDATE hol_node SET tag = 'NOPE' WHERE node_id = ?1",
                [arrow.0],
            )
            .unwrap();
        assert!(matches!(
            connection.kind(arrow),
            Err(KindError::CorruptKind(id)) if id == arrow
        ));
    }

    #[test]
    fn stores_every_kind_as_one_tagged_node_row() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        let rows = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*), count(DISTINCT node_id), count(DISTINCT tag) FROM hol_node",
                [],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(rows, (2, 2, 2));
    }

    #[test]
    fn user_metadata_columns_are_typed_indexed_and_not_canonical_identity() {
        let mut schema = HolSchema::new();
        schema
            .add_column("source label", MetadataType::Text)
            .unwrap();
        schema
            .add_column("priority", MetadataType::Integer)
            .unwrap();
        schema
            .add_index("by source", ["source label"], false)
            .unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(
            RecordingPolicy {
                allowed: true,
                operations: Vec::new(),
            },
            schema,
        )
        .unwrap();

        let first = connection
            .insert_kind_with_metadata(
                &Kind::Star,
                &[
                    ("source label", MetadataValue::Text("first".to_owned())),
                    ("priority", MetadataValue::Integer(7)),
                ],
            )
            .unwrap();
        let second = connection
            .insert_kind_with_metadata(
                &Kind::Star,
                &[("source label", MetadataValue::Text("second".to_owned()))],
            )
            .unwrap();

        assert_eq!(first, second);
        assert_eq!(
            connection
                .kind_metadata(first, &["source label", "priority"])
                .unwrap(),
            [
                MetadataValue::Text("second".to_owned()),
                MetadataValue::Integer(7)
            ]
        );
        assert_eq!(
            connection.protocol().schema().metadata_type("SOURCE LABEL"),
            Some(MetadataType::Text)
        );
        let index_exists = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT EXISTS(SELECT 1 FROM pragma_index_list('hol_node') WHERE name = 'by source')",
                [],
                |row| row.get::<_, bool>(0),
            )
            .unwrap();
        assert!(index_exists);
        assert_eq!(
            connection.protocol().policy().operations,
            [
                Operation::InsertKind,
                Operation::WriteMetadata,
                Operation::InsertKind,
                Operation::WriteMetadata,
                Operation::ReadMetadata,
            ]
        );
    }

    #[test]
    fn metadata_schema_rejects_ambiguous_declarations() {
        let mut schema = HolSchema::new();
        assert_eq!(
            schema.add_column("TAG", MetadataType::Text),
            Err(MetadataSchemaError::DuplicateOrReservedColumn(
                "TAG".to_owned()
            ))
        );
        schema.add_column("origin", MetadataType::Text).unwrap();
        assert_eq!(
            schema.add_column("ORIGIN", MetadataType::Blob),
            Err(MetadataSchemaError::DuplicateOrReservedColumn(
                "ORIGIN".to_owned()
            ))
        );
        assert_eq!(
            schema.add_index("bad", ["missing"], false),
            Err(MetadataSchemaError::UnknownColumn("missing".to_owned()))
        );
    }

    #[test]
    fn metadata_failure_rolls_back_new_canonical_nodes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        assert!(matches!(
            connection.insert_kind_with_metadata(
                &Kind::arrow(Kind::Star, Kind::Star),
                &[("missing", MetadataValue::Integer(1))],
            ),
            Err(KindError::UnknownMetadataColumn(name)) if name == "missing"
        ));
        let count = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(count, 1);
    }
}
