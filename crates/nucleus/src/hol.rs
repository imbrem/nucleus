//! Minimal HOL-omega protocol, beginning with canonical kinds.

mod validate;

pub use validate::{HolImageCounts, HolImageValidationError, ValidatedHolImage};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;
use std::marker::PhantomData;

use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use crate::Connection;

const SCHEMA: &str = include_str!("hol/schema.sql");
const STAR_ID: KindId = KindId(1);
const BOOL_TYPE_ID: TypeId = TypeId(2);

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

/// Database-local identity of an admitted HOL type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeId(i64);

impl TypeId {
    /// Creates a database-local lookup handle from its stored integer.
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

/// One admitted type in the settled closed Boolean/function fragment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeView {
    /// The primitive Boolean type.
    Bool,
    /// A function type.
    Arrow {
        /// Argument type.
        domain: TypeId,
        /// Result type.
        codomain: TypeId,
    },
}

/// Database-local identity of an admitted HOL term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermId(i64);

impl TermId {
    /// Creates a database-local lookup handle from its stored integer.
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

/// One external de Bruijn variable required to type an open term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnboundVariable {
    /// Root-relative external index.
    pub index: u32,
    /// Type required for that index.
    pub ty: TypeId,
}

/// One admitted term in the settled simply typed binding fragment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermView {
    /// A primitive Boolean literal.
    Bool(bool),
    /// A closed free symbol with a declared type.
    Free {
        /// Connection-local symbol identity.
        symbol: i64,
    },
    /// A de Bruijn occurrence, annotated with its admitted type.
    Bound {
        /// Zero-based distance to its binder.
        index: u32,
    },
    /// A well-typed application.
    Application {
        /// Function term.
        function: TermId,
        /// Argument term.
        argument: TermId,
    },
    /// A typed term abstraction.
    Lambda {
        /// Type of the newly bound variable.
        parameter_type: TypeId,
        /// Body, which may be open before this binder is applied.
        body: TermId,
    },
    /// Propositional equality between terms of one type.
    Equality {
        /// Left operand.
        left: TermId,
        /// Right operand.
        right: TermId,
    },
}

/// Database-local identity of an immutable Boolean assumption context.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContextId(i64);

impl ContextId {
    /// Returns the reserved empty context.
    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Creates a database-local lookup handle from its stored integer.
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

type Invariant<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

/// A generative proof scope borrowing one HOL connection.
pub struct ProofSession<'brand, P> {
    connection: &'brand mut Connection<Hol<P>>,
    brand: Invariant<'brand>,
}

/// A proved judgement branded by one generative proof session.
pub struct Theorem<'brand> {
    context: ContextId,
    conclusion: TermId,
    brand: Invariant<'brand>,
}

impl Theorem<'_> {
    /// Returns the theorem's immutable assumption context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the theorem's Boolean conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }
}

/// A policy-visible trusted HOL operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    /// Read a kind constructor or its derived rank.
    ReadKind,
    /// Validate and canonically intern a kind.
    InsertKind,
    /// Read an admitted type or its kind.
    ReadType,
    /// Validate and canonically intern a type.
    InsertType,
    /// Read an admitted term or its type.
    ReadTerm,
    /// Validate and canonically intern a term.
    InsertTerm,
    /// Define an immutable finite set of closed Boolean assumptions.
    DefineContext,
    /// Read context membership.
    ReadContext,
    /// Apply the hypothesis rule.
    ProveHypothesis,
    /// Apply the primitive truth rule.
    ProveTruth,
    /// Apply equality reflexivity.
    ProveReflexivity,
    /// Apply closed beta reduction.
    ProveBeta,
    /// Query whether a judgement has already been proved.
    ReadTheorem,
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
    table: MetadataTable,
    name: String,
    storage: MetadataType,
}

#[derive(Clone, Debug)]
struct MetadataIndex {
    table: MetadataTable,
    name: String,
    columns: Vec<String>,
    unique: bool,
}

/// Core HOL table extended by a user metadata column or index.
///
/// These additions are physical annotations only: no metadata column is part
/// of syntax identity, context membership, or judgement validity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MetadataTable {
    /// The universal kind/type/term node table.
    Node,
    /// Immutable context headers.
    Context,
    /// Pairs asserting membership in an immutable context.
    ContextMember,
    /// Persisted proved judgements.
    Judgement,
}

/// One existing row which may carry user metadata.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MetadataTarget {
    /// A universal syntax node.
    Node(i64),
    /// An immutable context header.
    Context(ContextId),
    /// A context-membership pair.
    ContextMember {
        /// Immutable context.
        context: ContextId,
        /// Boolean member.
        term: TermId,
    },
    /// An authoritative persisted judgement.
    Judgement {
        /// Assumption context.
        context: ContextId,
        /// Boolean conclusion.
        term: TermId,
    },
}

impl MetadataTarget {
    /// Selects a context-membership row.
    #[must_use]
    pub const fn context_member(context: ContextId, term: TermId) -> Self {
        Self::ContextMember { context, term }
    }

    /// Selects an authoritative persisted judgement.
    #[must_use]
    pub const fn judgement(context: ContextId, term: TermId) -> Self {
        Self::Judgement { context, term }
    }

    const fn table(self) -> MetadataTable {
        match self {
            Self::Node(_) => MetadataTable::Node,
            Self::Context(_) => MetadataTable::Context,
            Self::ContextMember { .. } => MetadataTable::ContextMember,
            Self::Judgement { .. } => MetadataTable::Judgement,
        }
    }
}

impl From<KindId> for MetadataTarget {
    fn from(id: KindId) -> Self {
        Self::Node(id.get())
    }
}

impl From<TypeId> for MetadataTarget {
    fn from(id: TypeId) -> Self {
        Self::Node(id.get())
    }
}

impl From<TermId> for MetadataTarget {
    fn from(id: TermId) -> Self {
        Self::Node(id.get())
    }
}

impl From<ContextId> for MetadataTarget {
    fn from(id: ContextId) -> Self {
        Self::Context(id)
    }
}

impl MetadataTable {
    const fn sql(self) -> &'static str {
        match self {
            Self::Node => "hol_node",
            Self::Context => "hol_context",
            Self::ContextMember => "hol_context_member",
            Self::Judgement => "hol_judgement",
        }
    }

    fn is_core_column(self, name: &str) -> bool {
        let columns: &[&str] = match self {
            Self::Node => &["node_id", "tag", "lhs", "rhs", "ty"],
            Self::Context => &["ctx_id"],
            Self::ContextMember | Self::Judgement => &["ctx_id", "term_id"],
        };
        columns.iter().any(|core| core.eq_ignore_ascii_case(name))
    }
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
        self.add_column_to(MetadataTable::Node, name, storage)
    }

    /// Adds a nullable user metadata column to a selected core table.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, reserved, NUL-containing, or duplicate
    /// identifier on that table.
    pub fn add_column_to(
        &mut self,
        table: MetadataTable,
        name: impl Into<String>,
        storage: MetadataType,
    ) -> Result<(), MetadataSchemaError> {
        let name = name.into();
        validate_identifier(&name)?;
        if table.is_core_column(&name)
            || self
                .columns
                .iter()
                .any(|column| column.table == table && column.name.eq_ignore_ascii_case(&name))
        {
            return Err(MetadataSchemaError::DuplicateOrReservedColumn(name));
        }
        self.columns.push(MetadataColumn {
            table,
            name,
            storage,
        });
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
        self.add_index_on(MetadataTable::Node, name, columns, unique)
    }

    /// Adds an index over declared metadata columns on a selected core table.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid/duplicate index name, an empty column
    /// list, or a column not declared as metadata on `table`.
    pub fn add_index_on<I, S>(
        &mut self,
        table: MetadataTable,
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
            if !self.columns.iter().any(|declared| {
                declared.table == table && declared.name.eq_ignore_ascii_case(column)
            }) {
                return Err(MetadataSchemaError::UnknownColumn(column.clone()));
            }
        }
        self.indexes.push(MetadataIndex {
            table,
            name,
            columns,
            unique,
        });
        Ok(())
    }

    fn column(&self, name: &str) -> Option<&MetadataColumn> {
        self.column_on(MetadataTable::Node, name)
    }

    fn column_on(&self, table: MetadataTable, name: &str) -> Option<&MetadataColumn> {
        self.columns
            .iter()
            .find(|column| column.table == table && column.name.eq_ignore_ascii_case(name))
    }

    /// Returns the declared storage class of a metadata column.
    #[must_use]
    pub fn metadata_type(&self, name: &str) -> Option<MetadataType> {
        self.column(name).map(|column| column.storage)
    }

    /// Returns the storage class of metadata declared on `table`.
    #[must_use]
    pub fn metadata_type_on(&self, table: MetadataTable, name: &str) -> Option<MetadataType> {
        self.column_on(table, name).map(|column| column.storage)
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
        write_metadata(&transaction, &hol.schema, id.0, metadata)?;
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

    /// Returns the canonical Boolean type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies type admission.
    pub fn insert_bool_type(&mut self) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        read_type(neutron.sqlite(), BOOL_TYPE_ID)?;
        Ok(BOOL_TYPE_ID)
    }

    /// Canonically interns a closed function type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, either child is not an
    /// admitted star-kinded type, or `SQLite` rejects the transaction.
    pub fn insert_arrow_type(
        &mut self,
        domain: TypeId,
        codomain: TypeId,
    ) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_type(&transaction, domain)?;
        read_type(&transaction, codomain)?;
        let id = intern_type_arrow(&transaction, domain, codomain)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads an admitted type constructor.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the node is unknown or
    /// malformed.
    pub fn type_view(&mut self, id: TypeId) -> Result<TypeView, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::ReadType)?;
        read_type(neutron.sqlite(), id)
    }

    /// Returns the admitted kind of a type.
    ///
    /// Every type in this initial closed fragment has kind `star`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the type is unknown or
    /// malformed.
    pub fn type_kind(&mut self, id: TypeId) -> Result<KindId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::ReadType)?;
        read_type(neutron.sqlite(), id)?;
        Ok(STAR_ID)
    }

    /// Canonically interns a Boolean literal term.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission or `SQLite` rejects it.
    pub fn insert_bool_term(&mut self, value: bool) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        intern_bool_term(neutron.sqlite(), value)
    }

    /// Canonically interns a closed free symbol at an admitted type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, the type is invalid, or
    /// `SQLite` rejects the transaction.
    pub fn insert_free_term(&mut self, symbol: i64, ty: TypeId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_type(&transaction, ty)?;
        let id = intern_free_term(&transaction, symbol, ty)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Canonically interns an explicitly typed de Bruijn occurrence.
    ///
    /// The resulting term may be locally open. A later lambda validates the
    /// type of every occurrence it captures.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, the type is invalid, or
    /// `SQLite` rejects the transaction.
    pub fn insert_bound_term(&mut self, index: u32, ty: TypeId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_type(&transaction, ty)?;
        let id = intern_bound_term(&transaction, index, ty)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Checks and canonically interns a term application.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, either term is invalid,
    /// the function does not have an arrow type, the argument type differs, or
    /// `SQLite` rejects the transaction.
    pub fn insert_application(
        &mut self,
        function: TermId,
        argument: TermId,
    ) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let function_validation = validate_term(&transaction, function)?;
        let argument_validation = validate_term(&transaction, argument)?;
        let function_type = function_validation.ty;
        let argument_type = argument_validation.ty;
        let TypeView::Arrow { domain, codomain } = read_type(&transaction, function_type)? else {
            return Err(TermError::NotFunction(function_type));
        };
        if domain != argument_type {
            return Err(TermError::ApplicationTypeMismatch {
                expected: domain,
                actual: argument_type,
            });
        }
        let id = intern_application(&transaction, function, argument, codomain)?;
        validate_term(&transaction, id)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Checks and canonically interns a typed term abstraction.
    ///
    /// Every de Bruijn occurrence captured by the new binder must carry the
    /// binder's type annotation. Occurrences referring outside the new lambda
    /// remain open and can be captured by a surrounding lambda.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, either child is invalid,
    /// a captured occurrence has the wrong type, or `SQLite` rejects the
    /// transaction.
    pub fn insert_lambda(
        &mut self,
        parameter_type: TypeId,
        body: TermId,
    ) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        authorize_type(&mut hol.policy, Operation::InsertType).map_err(TermError::Type)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        read_type(&transaction, parameter_type)?;
        let body_type = validate_term(&transaction, body)?.ty;
        let function_type = intern_type_arrow(&transaction, parameter_type, body_type)?;
        let id = intern_lambda(&transaction, parameter_type, body, function_type)?;
        validate_term(&transaction, id)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Checks and canonically interns propositional equality.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, either operand is invalid,
    /// their types differ, their external environments conflict, or `SQLite`
    /// rejects the transaction.
    pub fn insert_equality(&mut self, left: TermId, right: TermId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let left_validation = validate_term(&transaction, left)?;
        let right_validation = validate_term(&transaction, right)?;
        if left_validation.ty != right_validation.ty {
            return Err(TermError::EqualityTypeMismatch {
                left: left_validation.ty,
                right: right_validation.ty,
            });
        }
        merge_term_boundaries(left_validation.boundary, right_validation.boundary)?;
        let equality = intern_equality(&transaction, left, right)?;
        validate_term(&transaction, equality)?;
        transaction.commit()?;
        Ok(equality)
    }

    /// Reads an admitted term constructor.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term is unknown or
    /// malformed.
    pub fn term(&mut self, id: TermId) -> Result<TermView, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        read_term(neutron.sqlite(), id).map(|(term, _)| term)
    }

    /// Returns the admitted type of a term.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term/type is invalid.
    pub fn term_type(&mut self, id: TermId) -> Result<TypeId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        read_term(neutron.sqlite(), id).map(|(_, ty)| ty)
    }

    /// Returns the free symbol IDs reachable from a term in ascending order.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the root is invalid, or the
    /// recursive query fails.
    pub fn term_free_variables(&mut self, id: TermId) -> Result<Vec<i64>, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        read_term(neutron.sqlite(), id)?;
        free_term_symbols(neutron.sqlite(), id)
    }

    /// Reports whether a term is locally closed.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term is invalid.
    pub fn term_is_locally_closed(&mut self, id: TermId) -> Result<bool, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        Ok(validate_term(neutron.sqlite(), id)?.boundary.is_empty())
    }

    /// Returns unbound de Bruijn variables reachable from this term.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term is invalid.
    pub fn term_unbound_variables(
        &mut self,
        id: TermId,
    ) -> Result<Vec<UnboundVariable>, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        Ok(validate_term(neutron.sqlite(), id)?
            .boundary
            .into_iter()
            .map(|(index, ty)| UnboundVariable { index, ty })
            .collect())
    }

    /// Defines an immutable finite set of closed Boolean assumptions.
    ///
    /// Members are sorted and deduplicated. Repeating the same set returns the
    /// same context ID, independent of input order.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies definition, a member is invalid or
    /// non-Boolean, or `SQLite` rejects the transaction.
    pub fn define_context(
        &mut self,
        members: impl IntoIterator<Item = TermId>,
    ) -> Result<ContextId, ContextError> {
        let (neutron, hol) = self.parts_mut();
        authorize_context(&mut hol.policy, Operation::DefineContext)?;
        let mut members: Vec<TermId> = members.into_iter().collect();
        members.sort_unstable();
        members.dedup();
        let transaction = neutron.sqlite().unchecked_transaction()?;
        for member in &members {
            let validation = validate_term(&transaction, *member)?;
            if validation.ty != BOOL_TYPE_ID {
                return Err(ContextError::NonBooleanMember {
                    term: *member,
                    ty: validation.ty,
                });
            }
            if !validation.boundary.is_empty() {
                return Err(ContextError::OpenMember(*member));
            }
        }
        if let Some(context) = find_context(&transaction, &members)? {
            transaction.commit()?;
            return Ok(context);
        }
        transaction.execute("INSERT INTO hol_context DEFAULT VALUES", [])?;
        let context = ContextId(transaction.last_insert_rowid());
        for member in members {
            transaction.execute(
                "INSERT INTO hol_context_member(ctx_id, term_id) VALUES (?1, ?2)",
                [context.0, member.0],
            )?;
        }
        transaction.commit()?;
        Ok(context)
    }

    /// Returns an immutable context's members in ascending term-ID order.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the context is unknown, or
    /// `SQLite` rejects the query.
    pub fn context_members(&mut self, id: ContextId) -> Result<Vec<TermId>, ContextError> {
        let (neutron, hol) = self.parts_mut();
        authorize_context(&mut hol.policy, Operation::ReadContext)?;
        require_context(neutron.sqlite(), id)?;
        read_context_members(neutron.sqlite(), id)
    }

    /// Runs a generative proof session which may hold several theorem handles.
    ///
    /// The session brand cannot escape this closure or be shared with another
    /// connection. Plain context and term IDs may be returned as ordinary
    /// database-local data.
    ///
    /// ```compile_fail
    /// use covalence_nucleus::{AllowAll, Connection, ContextId};
    ///
    /// let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
    /// let theorem = connection.with_proof_session(|mut proof| {
    ///     proof.prove_truth(ContextId::empty()).unwrap()
    /// });
    /// # let _ = theorem;
    /// ```
    pub fn with_proof_session<R>(
        &mut self,
        run: impl for<'brand> FnOnce(ProofSession<'brand, P>) -> R,
    ) -> R {
        run(ProofSession {
            connection: self,
            brand: PhantomData,
        })
    }
}

impl<'brand, P: Policy> ProofSession<'brand, P> {
    /// Applies the hypothesis rule and persists the resulting judgement.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context is unknown, the
    /// term is not a member, or persistence fails.
    pub fn prove_hypothesis(
        &mut self,
        context: ContextId,
        term: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveHypothesis)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let member = transaction.query_row(
            "SELECT EXISTS(
                 SELECT 1 FROM hol_context_member WHERE ctx_id = ?1 AND term_id = ?2
             )",
            [context.0, term.0],
            |row| row.get::<_, bool>(0),
        )?;
        if !member {
            return Err(ProofError::NotMember { context, term });
        }
        persist_judgement(&transaction, context, term, "hypothesis")?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: term,
            brand: PhantomData,
        })
    }

    /// Applies primitive truth in an existing context and persists it.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context is unknown, or
    /// persistence fails.
    pub fn prove_truth(&mut self, context: ContextId) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveTruth)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let truth = intern_bool_term(&transaction, true)?;
        persist_judgement(&transaction, context, truth, "truth")?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: truth,
            brand: PhantomData,
        })
    }

    /// Applies equality reflexivity in an existing context and persists it.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context or term is
    /// invalid, the term is locally open, or persistence fails.
    pub fn prove_reflexivity(
        &mut self,
        context: ContextId,
        term: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveReflexivity)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let validation = validate_term(&transaction, term)?;
        if !validation.boundary.is_empty() {
            return Err(ProofError::OpenConclusion(term));
        }
        let equality = intern_equality(&transaction, term, term)?;
        validate_term(&transaction, equality)?;
        persist_judgement(&transaction, context, equality, "reflexivity")?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            brand: PhantomData,
        })
    }

    /// Proves one beta reduction with a closed abstraction and argument.
    ///
    /// Keeping this primitive rule closed makes capture avoidance explicit and
    /// small: substitution never needs to shift the replacement term.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context or terms are
    /// invalid, either input is open, the first term is not a lambda, the
    /// argument type differs, substitution fails, or persistence fails.
    pub fn prove_beta(
        &mut self,
        context: ContextId,
        abstraction: TermId,
        argument: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveBeta)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let abstraction_validation = validate_term(&transaction, abstraction)?;
        if !abstraction_validation.boundary.is_empty() {
            return Err(ProofError::OpenConclusion(abstraction));
        }
        let TermView::Lambda {
            parameter_type,
            body,
        } = abstraction_validation.view
        else {
            return Err(ProofError::NotLambda(abstraction));
        };
        let argument_validation = validate_term(&transaction, argument)?;
        if !argument_validation.boundary.is_empty() {
            return Err(ProofError::OpenConclusion(argument));
        }
        if argument_validation.ty != parameter_type {
            return Err(ProofError::BetaTypeMismatch {
                expected: parameter_type,
                actual: argument_validation.ty,
            });
        }
        let reduct = substitute_closed(&transaction, body, argument, 0)?;
        let TypeView::Arrow { codomain, .. } =
            read_type(&transaction, abstraction_validation.ty).map_err(TermError::Type)?
        else {
            return Err(ProofError::NotLambda(abstraction));
        };
        let application = intern_application(&transaction, abstraction, argument, codomain)?;
        validate_term(&transaction, application)?;
        let equality = intern_equality(&transaction, application, reduct)?;
        validate_term(&transaction, equality)?;
        persist_judgement(&transaction, context, equality, "beta")?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            brand: PhantomData,
        })
    }

    /// Loads one already persisted local judgement as a session capability.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the context or conclusion
    /// is invalid, or `SQLite` rejects the query.
    pub fn load_theorem(
        &mut self,
        context: ContextId,
        conclusion: TermId,
    ) -> Result<Option<Theorem<'brand>>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadTheorem)?;
        require_context(neutron.sqlite(), context)?;
        let validation = validate_term(neutron.sqlite(), conclusion)?;
        if validation.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConclusion {
                term: conclusion,
                ty: validation.ty,
            });
        }
        if !validation.boundary.is_empty() {
            return Err(ProofError::OpenConclusion(conclusion));
        }
        let exists = neutron.sqlite().query_row(
            "SELECT EXISTS(
                 SELECT 1 FROM hol_judgement WHERE ctx_id = ?1 AND term_id = ?2
             )",
            [context.0, conclusion.0],
            |row| row.get::<_, bool>(0),
        )?;
        Ok(exists.then_some(Theorem {
            context,
            conclusion,
            brand: PhantomData,
        }))
    }
}

impl<P: Policy> Connection<Hol<P>> {
    /// Reports whether a Boolean judgement is in the append-only proof table.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the context/term is invalid,
    /// the term is not Boolean, or `SQLite` rejects the query.
    pub fn proved_judgement(
        &mut self,
        context: ContextId,
        term: TermId,
    ) -> Result<bool, ProofError> {
        let (neutron, hol) = self.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadTheorem)?;
        require_context(neutron.sqlite(), context)?;
        let validation = validate_term(neutron.sqlite(), term)?;
        if validation.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConclusion {
                term,
                ty: validation.ty,
            });
        }
        if !validation.boundary.is_empty() {
            return Err(ProofError::OpenConclusion(term));
        }
        neutron
            .sqlite()
            .query_row(
                "SELECT EXISTS(
                     SELECT 1 FROM hol_judgement WHERE ctx_id = ?1 AND term_id = ?2
                 )",
                [context.0, term.0],
                |row| row.get(0),
            )
            .map_err(Into::into)
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
        read_metadata(neutron.sqlite(), &hol.schema, id.0, columns)
    }

    /// Reads selected user metadata from an existing structural row.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the target or a column is
    /// unknown, or `SQLite` rejects the query.
    pub fn metadata(
        &mut self,
        target: MetadataTarget,
        columns: &[&str],
    ) -> Result<Vec<MetadataValue>, MetadataError> {
        let (neutron, hol) = self.parts_mut();
        authorize_metadata(&mut hol.policy, Operation::ReadMetadata)?;
        read_target_metadata(neutron.sqlite(), &hol.schema, target, columns)
    }

    /// Replaces selected user metadata on an existing structural row.
    ///
    /// Metadata is never consulted by syntax admission or proof rules.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the write, the target or a column is
    /// unknown, a column is repeated, or `SQLite` rejects the atomic update.
    pub fn set_metadata(
        &mut self,
        target: MetadataTarget,
        metadata: &[(&str, MetadataValue)],
    ) -> Result<(), MetadataError> {
        let (neutron, hol) = self.parts_mut();
        authorize_metadata(&mut hol.policy, Operation::WriteMetadata)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_metadata_target(&transaction, target)?;
        if !metadata.is_empty() {
            let table = target.table();
            let mut seen = HashSet::new();
            let mut assignments = Vec::with_capacity(metadata.len());
            let mut values = Vec::with_capacity(metadata.len() + 2);
            for (name, value) in metadata {
                let column = hol
                    .schema
                    .column_on(table, name)
                    .ok_or_else(|| MetadataError::UnknownColumn((*name).to_owned()))?;
                if !seen.insert(column.name.to_ascii_lowercase()) {
                    return Err(MetadataError::DuplicateColumn((*name).to_owned()));
                }
                assignments.push(format!("{} = ?", quote_identifier(&column.name)));
                values.push(sqlite::types::Value::from(value.clone()));
            }
            let (predicate, keys) = metadata_target_predicate(target, values.len() + 1);
            values.extend(keys.into_iter().map(sqlite::types::Value::Integer));
            transaction.execute(
                &format!(
                    "UPDATE {} SET {} WHERE {predicate}",
                    table.sql(),
                    assignments.join(", ")
                ),
                sqlite::params_from_iter(values.iter()),
            )?;
        }
        transaction.commit()?;
        Ok(())
    }
}

fn authorize_metadata(policy: &mut impl Policy, operation: Operation) -> Result<(), MetadataError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(MetadataError::Denied(operation))
    }
}

fn metadata_target_predicate(target: MetadataTarget, first_parameter: usize) -> (String, Vec<i64>) {
    match target {
        MetadataTarget::Node(id) => (format!("node_id = ?{first_parameter}"), vec![id]),
        MetadataTarget::Context(context) => {
            (format!("ctx_id = ?{first_parameter}"), vec![context.get()])
        }
        MetadataTarget::ContextMember { context, term }
        | MetadataTarget::Judgement { context, term } => (
            format!(
                "ctx_id = ?{first_parameter} AND term_id = ?{}",
                first_parameter + 1
            ),
            vec![context.get(), term.get()],
        ),
    }
}

fn require_metadata_target(
    connection: &sqlite::Connection,
    target: MetadataTarget,
) -> Result<(), MetadataError> {
    let (predicate, keys) = metadata_target_predicate(target, 1);
    let exists = connection.query_row(
        &format!(
            "SELECT EXISTS(SELECT 1 FROM {} WHERE {predicate})",
            target.table().sql()
        ),
        sqlite::params_from_iter(keys.iter()),
        |row| row.get::<_, bool>(0),
    )?;
    if exists {
        Ok(())
    } else {
        Err(MetadataError::UnknownTarget(target))
    }
}

fn read_target_metadata(
    connection: &sqlite::Connection,
    schema: &HolSchema,
    target: MetadataTarget,
    columns: &[&str],
) -> Result<Vec<MetadataValue>, MetadataError> {
    require_metadata_target(connection, target)?;
    if columns.is_empty() {
        return Ok(Vec::new());
    }
    let table = target.table();
    let columns = columns
        .iter()
        .map(|name| {
            schema
                .column_on(table, name)
                .map(|column| quote_identifier(&column.name))
                .ok_or_else(|| MetadataError::UnknownColumn((*name).to_owned()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (predicate, keys) = metadata_target_predicate(target, 1);
    connection
        .query_row(
            &format!(
                "SELECT {} FROM {} WHERE {predicate}",
                columns.join(", "),
                table.sql()
            ),
            sqlite::params_from_iter(keys.iter()),
            |row| {
                (0..columns.len())
                    .map(|index| row.get::<_, sqlite::types::Value>(index))
                    .collect::<Result<Vec<_>, _>>()
            },
        )?
        .into_iter()
        .map(|value| Ok(MetadataValue::from(value)))
        .collect()
}

fn install_metadata_schema(
    connection: &sqlite::Connection,
    schema: &HolSchema,
) -> Result<(), sqlite::Error> {
    for column in &schema.columns {
        connection.execute_batch(&format!(
            "ALTER TABLE {} ADD COLUMN {} {}",
            column.table.sql(),
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
            "CREATE {}INDEX {} ON {}({columns})",
            if index.unique { "UNIQUE " } else { "" },
            quote_identifier(&index.name),
            index.table.sql(),
        ))?;
    }
    Ok(())
}

fn write_metadata(
    connection: &sqlite::Connection,
    schema: &HolSchema,
    id: i64,
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
    values.push(sqlite::types::Value::Integer(id));
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
    id: i64,
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
        .query_row(&sql, [id], |row| {
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

fn authorize_type(policy: &mut impl Policy, operation: Operation) -> Result<(), TypeError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(TypeError::Denied(operation))
    }
}

fn authorize_term(policy: &mut impl Policy, operation: Operation) -> Result<(), TermError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(TermError::Denied(operation))
    }
}

fn authorize_context(policy: &mut impl Policy, operation: Operation) -> Result<(), ContextError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(ContextError::Denied(operation))
    }
}

fn authorize_proof(policy: &mut impl Policy, operation: Operation) -> Result<(), ProofError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(ProofError::Denied(operation))
    }
}

fn require_context(connection: &sqlite::Connection, id: ContextId) -> Result<(), ContextError> {
    let exists = connection.query_row(
        "SELECT EXISTS(SELECT 1 FROM hol_context WHERE ctx_id = ?1)",
        [id.0],
        |row| row.get::<_, bool>(0),
    )?;
    if exists {
        Ok(())
    } else {
        Err(ContextError::UnknownContext(id))
    }
}

fn read_context_members(
    connection: &sqlite::Connection,
    id: ContextId,
) -> Result<Vec<TermId>, ContextError> {
    let mut statement = connection
        .prepare("SELECT term_id FROM hol_context_member WHERE ctx_id = ?1 ORDER BY term_id")?;
    let rows = statement.query_map([id.0], |row| row.get::<_, i64>(0).map(TermId))?;
    rows.collect::<Result<Vec<_>, _>>().map_err(Into::into)
}

fn find_context(
    connection: &sqlite::Connection,
    members: &[TermId],
) -> Result<Option<ContextId>, ContextError> {
    let mut statement = connection.prepare(
        "SELECT ctx_id FROM hol_context
         WHERE (SELECT count(*) FROM hol_context_member
                WHERE hol_context_member.ctx_id = hol_context.ctx_id) = ?1
         ORDER BY ctx_id",
    )?;
    let candidates = statement
        .query_map([i64::try_from(members.len()).unwrap_or(i64::MAX)], |row| {
            row.get::<_, i64>(0).map(ContextId)
        })?
        .collect::<Result<Vec<_>, _>>()?;
    for candidate in candidates {
        if read_context_members(connection, candidate)? == members {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

fn persist_judgement(
    connection: &sqlite::Connection,
    context: ContextId,
    term: TermId,
    rule: &str,
) -> Result<(), sqlite::Error> {
    connection.execute(
        "INSERT OR IGNORE INTO hol_judgement(ctx_id, term_id) VALUES (?1, ?2)",
        (context.0, term.0),
    )?;
    connection.execute(
        "INSERT INTO hol_proof_event(ctx_id, term_id, rule) VALUES (?1, ?2, ?3)",
        (context.0, term.0, rule),
    )?;
    Ok(())
}

fn intern_type_arrow(
    connection: &sqlite::Connection,
    domain: TypeId,
    codomain: TypeId,
) -> Result<TypeId, TypeError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'TARR' AND lhs = ?1 AND rhs = ?2 AND ty = ?3",
            (domain.0, codomain.0, STAR_ID.0),
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TypeId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs, ty) VALUES ('TARR', ?1, ?2, ?3)",
        (domain.0, codomain.0, STAR_ID.0),
    )?;
    Ok(TypeId(connection.last_insert_rowid()))
}

fn read_type(connection: &sqlite::Connection, id: TypeId) -> Result<TypeView, TypeError> {
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
        .ok_or(TypeError::UnknownType(id))?;
    match row {
        (tag, None, None, Some(kind)) if tag == "TBOOL" && kind == STAR_ID.0 => Ok(TypeView::Bool),
        (tag, Some(domain), Some(codomain), Some(kind)) if tag == "TARR" && kind == STAR_ID.0 => {
            Ok(TypeView::Arrow {
                domain: TypeId(domain),
                codomain: TypeId(codomain),
            })
        }
        _ => Err(TypeError::CorruptType(id)),
    }
}

fn intern_bool_term(connection: &sqlite::Connection, value: bool) -> Result<TermId, TermError> {
    let immediate = i64::from(value);
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MBOOL' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [immediate, BOOL_TYPE_ID.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MBOOL', ?1, ?2)",
        [immediate, BOOL_TYPE_ID.0],
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_free_term(
    connection: &sqlite::Connection,
    symbol: i64,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MFV' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [symbol, ty.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MFV', ?1, ?2)",
        [symbol, ty.0],
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_bound_term(
    connection: &sqlite::Connection,
    index: u32,
    ty: TypeId,
) -> Result<TermId, TermError> {
    let index = i64::from(index);
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MBV' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [index, ty.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MBV', ?1, ?2)",
        [index, ty.0],
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_application(
    connection: &sqlite::Connection,
    function: TermId,
    argument: TermId,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MAPP' AND lhs = ?1 AND rhs = ?2 AND ty = ?3",
            (function.0, argument.0, ty.0),
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs, ty) VALUES ('MAPP', ?1, ?2, ?3)",
        (function.0, argument.0, ty.0),
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_lambda(
    connection: &sqlite::Connection,
    parameter_type: TypeId,
    body: TermId,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MLAM' AND lhs = ?1 AND rhs = ?2 AND ty = ?3",
            (parameter_type.0, body.0, ty.0),
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs, ty) VALUES ('MLAM', ?1, ?2, ?3)",
        (parameter_type.0, body.0, ty.0),
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_equality(
    connection: &sqlite::Connection,
    left: TermId,
    right: TermId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MEQ' AND lhs = ?1 AND rhs = ?2 AND ty = ?3",
            (left.0, right.0, BOOL_TYPE_ID.0),
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs, ty) VALUES ('MEQ', ?1, ?2, ?3)",
        (left.0, right.0, BOOL_TYPE_ID.0),
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn read_term_node(
    connection: &sqlite::Connection,
    id: TermId,
) -> Result<(TermView, TypeId), TermError> {
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
        .ok_or(TermError::UnknownTerm(id))?;
    let (term, ty) = match row {
        (tag, Some(value @ 0..=1), None, Some(ty)) if tag == "MBOOL" => {
            (TermView::Bool(value == 1), TypeId(ty))
        }
        (tag, Some(symbol), None, Some(ty)) if tag == "MFV" => {
            (TermView::Free { symbol }, TypeId(ty))
        }
        (tag, Some(index), None, Some(ty))
            if tag == "MBV" && (0..=i64::from(u32::MAX)).contains(&index) =>
        {
            (
                TermView::Bound {
                    index: u32::try_from(index).map_err(|_| TermError::CorruptTerm(id))?,
                },
                TypeId(ty),
            )
        }
        (tag, Some(function), Some(argument), Some(ty)) if tag == "MAPP" => (
            TermView::Application {
                function: TermId(function),
                argument: TermId(argument),
            },
            TypeId(ty),
        ),
        (tag, Some(parameter_type), Some(body), Some(ty)) if tag == "MLAM" => (
            TermView::Lambda {
                parameter_type: TypeId(parameter_type),
                body: TermId(body),
            },
            TypeId(ty),
        ),
        (tag, Some(left), Some(right), Some(ty)) if tag == "MEQ" => (
            TermView::Equality {
                left: TermId(left),
                right: TermId(right),
            },
            TypeId(ty),
        ),
        _ => return Err(TermError::CorruptTerm(id)),
    };
    read_type(connection, ty)?;
    if matches!(term, TermView::Bool(_)) && ty != BOOL_TYPE_ID {
        return Err(TermError::CorruptTerm(id));
    }
    Ok((term, ty))
}

#[derive(Clone)]
struct ValidatedTerm {
    view: TermView,
    ty: TypeId,
    boundary: BTreeMap<u32, TypeId>,
}

fn read_term(connection: &sqlite::Connection, id: TermId) -> Result<(TermView, TypeId), TermError> {
    let validated = validate_term(connection, id)?;
    Ok((validated.view, validated.ty))
}

fn validate_term(connection: &sqlite::Connection, id: TermId) -> Result<ValidatedTerm, TermError> {
    validate_term_inner(connection, id, &mut HashSet::new(), &mut HashMap::new())
}

fn validate_term_inner(
    connection: &sqlite::Connection,
    id: TermId,
    active: &mut HashSet<TermId>,
    memo: &mut HashMap<TermId, ValidatedTerm>,
) -> Result<ValidatedTerm, TermError> {
    if let Some(validated) = memo.get(&id) {
        return Ok(validated.clone());
    }
    if !active.insert(id) {
        return Err(TermError::CyclicTerm(id));
    }
    let (view, ty) = read_term_node(connection, id)?;
    let boundary = match view {
        TermView::Bool(_) | TermView::Free { .. } => BTreeMap::new(),
        TermView::Bound { index } => BTreeMap::from([(index, ty)]),
        TermView::Application { function, argument } => {
            let function = validate_term_inner(connection, function, active, memo)?;
            let argument = validate_term_inner(connection, argument, active, memo)?;
            let TypeView::Arrow { domain, codomain } = read_type(connection, function.ty)? else {
                return Err(TermError::NotFunction(function.ty));
            };
            if domain != argument.ty {
                return Err(TermError::ApplicationTypeMismatch {
                    expected: domain,
                    actual: argument.ty,
                });
            }
            if codomain != ty {
                return Err(TermError::CorruptTerm(id));
            }
            merge_term_boundaries(function.boundary, argument.boundary)?
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            read_type(connection, parameter_type)?;
            let body = validate_term_inner(connection, body, active, memo)?;
            match read_type(connection, ty)? {
                TypeView::Arrow { domain, codomain }
                    if domain == parameter_type && codomain == body.ty => {}
                _ => return Err(TermError::CorruptTerm(id)),
            }
            close_term_boundary(body.boundary, parameter_type)?
        }
        TermView::Equality { left, right } => {
            if ty != BOOL_TYPE_ID {
                return Err(TermError::CorruptTerm(id));
            }
            let left = validate_term_inner(connection, left, active, memo)?;
            let right = validate_term_inner(connection, right, active, memo)?;
            if left.ty != right.ty {
                return Err(TermError::EqualityTypeMismatch {
                    left: left.ty,
                    right: right.ty,
                });
            }
            merge_term_boundaries(left.boundary, right.boundary)?
        }
    };
    active.remove(&id);
    let validated = ValidatedTerm { view, ty, boundary };
    memo.insert(id, validated.clone());
    Ok(validated)
}

fn merge_term_boundaries(
    mut left: BTreeMap<u32, TypeId>,
    right: BTreeMap<u32, TypeId>,
) -> Result<BTreeMap<u32, TypeId>, TermError> {
    for (index, ty) in right {
        if let Some(first) = left.insert(index, ty)
            && first != ty
        {
            return Err(TermError::InconsistentUnboundVariable {
                index,
                first,
                second: ty,
            });
        }
    }
    Ok(left)
}

fn close_term_boundary(
    mut body: BTreeMap<u32, TypeId>,
    binder: TypeId,
) -> Result<BTreeMap<u32, TypeId>, TermError> {
    if let Some(actual) = body.remove(&0)
        && actual != binder
    {
        return Err(TermError::BoundVariableTypeMismatch {
            expected: binder,
            actual,
        });
    }
    Ok(body
        .into_iter()
        .map(|(index, ty)| (index - 1, ty))
        .collect())
}

fn substitute_closed(
    connection: &sqlite::Connection,
    body: TermId,
    replacement: TermId,
    depth: u32,
) -> Result<TermId, TermError> {
    let result =
        substitute_closed_inner(connection, body, replacement, depth, &mut HashMap::new())?;
    validate_term(connection, result)?;
    Ok(result)
}

fn substitute_closed_inner(
    connection: &sqlite::Connection,
    term: TermId,
    replacement: TermId,
    depth: u32,
    memo: &mut HashMap<(TermId, u32), TermId>,
) -> Result<TermId, TermError> {
    if let Some(result) = memo.get(&(term, depth)) {
        return Ok(*result);
    }
    let (view, ty) = read_term_node(connection, term)?;
    let result = match view {
        TermView::Bound { index } if index == depth => replacement,
        TermView::Bound { index } if index > depth => intern_bound_term(connection, index - 1, ty)?,
        TermView::Bool(_) | TermView::Free { .. } | TermView::Bound { .. } => term,
        TermView::Application { function, argument } => {
            let function = substitute_closed_inner(connection, function, replacement, depth, memo)?;
            let argument = substitute_closed_inner(connection, argument, replacement, depth, memo)?;
            intern_application(connection, function, argument, ty)?
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            let body = substitute_closed_inner(
                connection,
                body,
                replacement,
                depth
                    .checked_add(1)
                    .ok_or(TermError::SubstitutionDepthOverflow)?,
                memo,
            )?;
            intern_lambda(connection, parameter_type, body, ty)?
        }
        TermView::Equality { left, right } => {
            let left = substitute_closed_inner(connection, left, replacement, depth, memo)?;
            let right = substitute_closed_inner(connection, right, replacement, depth, memo)?;
            intern_equality(connection, left, right)?
        }
    };
    memo.insert((term, depth), result);
    Ok(result)
}

fn free_term_symbols(connection: &sqlite::Connection, root: TermId) -> Result<Vec<i64>, TermError> {
    let mut statement = connection.prepare(
        "WITH RECURSIVE
         edge(parent, child) AS (
             SELECT node_id, lhs FROM hol_node WHERE tag = 'MAPP'
             UNION ALL
             SELECT node_id, rhs FROM hol_node WHERE tag = 'MAPP'
             UNION ALL
             SELECT node_id, rhs FROM hol_node WHERE tag = 'MLAM'
             UNION ALL
             SELECT node_id, lhs FROM hol_node WHERE tag = 'MEQ'
             UNION ALL
             SELECT node_id, rhs FROM hol_node WHERE tag = 'MEQ'
         ),
         reachable(node_id) AS (
             SELECT ?1
             UNION
             SELECT edge.child FROM edge JOIN reachable ON edge.parent = reachable.node_id
         )
         SELECT DISTINCT node.lhs
         FROM hol_node AS node JOIN reachable USING (node_id)
         WHERE node.tag = 'MFV'
         ORDER BY node.lhs",
    )?;
    let rows = statement.query_map([root.0], |row| row.get::<_, i64>(0))?;
    rows.collect::<Result<Vec<_>, _>>().map_err(Into::into)
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

/// Failure to read or update user metadata.
#[derive(Debug)]
pub enum MetadataError {
    /// Policy denied the metadata operation.
    Denied(Operation),
    /// The selected structural row does not exist.
    UnknownTarget(MetadataTarget),
    /// The selected table has no declared metadata column with this name.
    UnknownColumn(String),
    /// One update names a metadata column more than once.
    DuplicateColumn(String),
    /// `SQLite` rejected the operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for MetadataError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownTarget(target) => write!(formatter, "unknown metadata target {target:?}"),
            Self::UnknownColumn(name) => write!(formatter, "unknown HOL metadata column {name:?}"),
            Self::DuplicateColumn(name) => {
                write!(formatter, "duplicate HOL metadata column {name:?}")
            }
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for MetadataError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::UnknownTarget(_)
            | Self::UnknownColumn(_)
            | Self::DuplicateColumn(_) => None,
        }
    }
}

impl From<sqlite::Error> for MetadataError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to insert or inspect an admitted type.
#[derive(Debug)]
pub enum TypeError {
    /// Policy denied the operation.
    Denied(Operation),
    /// No type has the requested ID.
    UnknownType(TypeId),
    /// A tagged node has an invalid type shape or classifier.
    CorruptType(TypeId),
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownType(id) => write!(formatter, "unknown type {}", id.get()),
            Self::CorruptType(id) => write!(formatter, "type {} is structurally corrupt", id.get()),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TypeError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            Self::Denied(_) | Self::UnknownType(_) | Self::CorruptType(_) => None,
        }
    }
}

impl From<sqlite::Error> for TypeError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to insert or inspect an admitted term.
#[derive(Debug)]
pub enum TermError {
    /// Policy denied the operation.
    Denied(Operation),
    /// No term has the requested ID.
    UnknownTerm(TermId),
    /// A tagged node has an invalid term shape or classifier.
    CorruptTerm(TermId),
    /// The function position does not have a function type.
    NotFunction(TypeId),
    /// An application's argument type differs from its function domain.
    ApplicationTypeMismatch {
        /// Required argument type.
        expected: TypeId,
        /// Actual argument type.
        actual: TypeId,
    },
    /// Equality operands have different types.
    EqualityTypeMismatch {
        /// Left operand type.
        left: TypeId,
        /// Right operand type.
        right: TypeId,
    },
    /// One external de Bruijn index has incompatible type annotations.
    InconsistentUnboundVariable {
        /// External index.
        index: u32,
        /// First observed type.
        first: TypeId,
        /// Conflicting type.
        second: TypeId,
    },
    /// A lambda captures an occurrence annotated with a different type.
    BoundVariableTypeMismatch {
        /// Binder type.
        expected: TypeId,
        /// Captured occurrence type.
        actual: TypeId,
    },
    /// The term graph contains a cycle.
    CyclicTerm(TermId),
    /// A binder nesting depth exceeds the supported de Bruijn index range.
    SubstitutionDepthOverflow,
    /// A referenced type is invalid.
    Type(TypeError),
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TermError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownTerm(id) => write!(formatter, "unknown term {}", id.get()),
            Self::CorruptTerm(id) => write!(formatter, "term {} is structurally corrupt", id.get()),
            Self::NotFunction(ty) => write!(formatter, "type {} is not a function type", ty.get()),
            Self::ApplicationTypeMismatch { expected, actual } => write!(
                formatter,
                "application expected type {}, got {}",
                expected.get(),
                actual.get()
            ),
            Self::EqualityTypeMismatch { left, right } => write!(
                formatter,
                "equality operands have different types {} and {}",
                left.get(),
                right.get()
            ),
            Self::InconsistentUnboundVariable {
                index,
                first,
                second,
            } => write!(
                formatter,
                "unbound index {index} has incompatible types {} and {}",
                first.get(),
                second.get()
            ),
            Self::BoundVariableTypeMismatch { expected, actual } => write!(
                formatter,
                "lambda binder has type {}, but captured occurrence has type {}",
                expected.get(),
                actual.get()
            ),
            Self::CyclicTerm(id) => write!(formatter, "term {} contains a cycle", id.get()),
            Self::SubstitutionDepthOverflow => formatter.write_str("substitution depth overflow"),
            Self::Type(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TermError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Type(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::UnknownTerm(_)
            | Self::CorruptTerm(_)
            | Self::NotFunction(_)
            | Self::ApplicationTypeMismatch { .. }
            | Self::EqualityTypeMismatch { .. }
            | Self::InconsistentUnboundVariable { .. }
            | Self::BoundVariableTypeMismatch { .. }
            | Self::CyclicTerm(_)
            | Self::SubstitutionDepthOverflow => None,
        }
    }
}

impl From<TypeError> for TermError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<sqlite::Error> for TermError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to define or inspect an immutable assumption context.
#[derive(Debug)]
pub enum ContextError {
    /// Policy denied the operation.
    Denied(Operation),
    /// No context has the requested ID.
    UnknownContext(ContextId),
    /// A proposed context member is not Boolean.
    NonBooleanMember {
        /// Proposed member.
        term: TermId,
        /// Its admitted non-Boolean type.
        ty: TypeId,
    },
    /// A proposed context member has unbound de Bruijn variables.
    OpenMember(TermId),
    /// A member term is invalid.
    Term(TermError),
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for ContextError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownContext(id) => write!(formatter, "unknown context {}", id.get()),
            Self::NonBooleanMember { term, ty } => write!(
                formatter,
                "context member term {} has non-Boolean type {}",
                term.get(),
                ty.get()
            ),
            Self::OpenMember(term) => {
                write!(
                    formatter,
                    "context member term {} is not locally closed",
                    term.get()
                )
            }
            Self::Term(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for ContextError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Term(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::UnknownContext(_)
            | Self::NonBooleanMember { .. }
            | Self::OpenMember(_) => None,
        }
    }
}

impl From<TermError> for ContextError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<sqlite::Error> for ContextError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to apply or inspect a trusted HOL proof rule.
#[derive(Debug)]
pub enum ProofError {
    /// Policy denied the operation/rule.
    Denied(Operation),
    /// The context is invalid.
    Context(ContextError),
    /// The conclusion/member term is invalid.
    Term(TermError),
    /// The hypothesis rule was requested for a non-member.
    NotMember {
        /// Assumption context.
        context: ContextId,
        /// Proposed hypothesis.
        term: TermId,
    },
    /// A proposed conclusion is not Boolean.
    NonBooleanConclusion {
        /// Proposed conclusion.
        term: TermId,
        /// Its admitted type.
        ty: TypeId,
    },
    /// A proposed theorem conclusion has external de Bruijn variables.
    OpenConclusion(TermId),
    /// Beta reduction was requested for a non-lambda term.
    NotLambda(TermId),
    /// A beta argument has the wrong type.
    BetaTypeMismatch {
        /// Lambda parameter type.
        expected: TypeId,
        /// Argument type.
        actual: TypeId,
    },
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::Context(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::NotMember { context, term } => write!(
                formatter,
                "term {} is not a member of context {}",
                term.get(),
                context.get()
            ),
            Self::NonBooleanConclusion { term, ty } => write!(
                formatter,
                "conclusion term {} has non-Boolean type {}",
                term.get(),
                ty.get()
            ),
            Self::OpenConclusion(term) => {
                write!(
                    formatter,
                    "conclusion term {} is not locally closed",
                    term.get()
                )
            }
            Self::NotLambda(term) => write!(formatter, "term {} is not a lambda", term.get()),
            Self::BetaTypeMismatch { expected, actual } => write!(
                formatter,
                "beta argument has type {}, expected {}",
                actual.get(),
                expected.get()
            ),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for ProofError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Context(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::NotMember { .. }
            | Self::NonBooleanConclusion { .. }
            | Self::OpenConclusion(_)
            | Self::NotLambda(_)
            | Self::BetaTypeMismatch { .. } => None,
        }
    }
}

impl From<ContextError> for ProofError {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
    }
}

impl From<TermError> for ProofError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<sqlite::Error> for ProofError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

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

    fn theorem_conclusion(theorem: Result<Theorem<'_>, ProofError>) -> Result<TermId, ProofError> {
        theorem.map(|theorem| theorem.conclusion())
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
                "SELECT count(*), count(DISTINCT node_id), count(DISTINCT tag)
                 FROM hol_node WHERE tag LIKE 'K%'",
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
    fn admits_closed_boolean_function_types_and_typed_applications() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(10, function_type).unwrap();
        let argument = connection.insert_free_term(11, bool_type).unwrap();
        let application = connection.insert_application(function, argument).unwrap();
        let literal = connection.insert_bool_term(true).unwrap();

        assert_eq!(bool_type, BOOL_TYPE_ID);
        assert_eq!(connection.type_view(bool_type).unwrap(), TypeView::Bool);
        assert_eq!(
            connection.type_view(function_type).unwrap(),
            TypeView::Arrow {
                domain: bool_type,
                codomain: bool_type,
            }
        );
        assert_eq!(connection.type_kind(function_type).unwrap(), STAR_ID);
        assert_eq!(
            connection.term(application).unwrap(),
            TermView::Application { function, argument }
        );
        assert_eq!(connection.term(literal).unwrap(), TermView::Bool(true));
        assert_eq!(connection.term_type(application).unwrap(), bool_type);
        assert_eq!(
            connection.term_free_variables(application).unwrap(),
            [10, 11]
        );
        assert!(connection.term_is_locally_closed(application).unwrap());
        assert!(
            connection
                .term_unbound_variables(application)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            application,
            connection.insert_application(function, argument).unwrap()
        );
    }

    #[test]
    fn rejects_ill_typed_applications_atomically() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(20, function_type).unwrap();
        let wrong_argument = connection.insert_free_term(21, function_type).unwrap();

        assert!(matches!(
            connection.insert_application(function, wrong_argument),
            Err(TermError::ApplicationTypeMismatch { expected, actual })
                if expected == bool_type && actual == function_type
        ));
        let applications = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*) FROM hol_node WHERE tag = 'MAPP'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(applications, 0);
    }

    #[test]
    fn admits_typed_de_bruijn_variables_and_closed_lambdas() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        assert_eq!(
            connection.term(variable).unwrap(),
            TermView::Bound { index: 0 }
        );
        assert_eq!(
            connection.term_unbound_variables(variable).unwrap(),
            [UnboundVariable {
                index: 0,
                ty: bool_type
            }]
        );
        assert!(!connection.term_is_locally_closed(variable).unwrap());

        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        assert_eq!(
            connection.term(identity).unwrap(),
            TermView::Lambda {
                parameter_type: bool_type,
                body: variable
            }
        );
        let identity_type = connection.term_type(identity).unwrap();
        assert_eq!(
            connection.type_view(identity_type).unwrap(),
            TypeView::Arrow {
                domain: bool_type,
                codomain: bool_type
            }
        );
        assert!(connection.term_is_locally_closed(identity).unwrap());
        assert!(
            connection
                .term_unbound_variables(identity)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            identity,
            connection.insert_lambda(bool_type, variable).unwrap()
        );

        let outer_variable = connection.insert_bound_term(1, bool_type).unwrap();
        let inner = connection.insert_lambda(bool_type, outer_variable).unwrap();
        assert_eq!(
            connection.term_unbound_variables(inner).unwrap(),
            [UnboundVariable {
                index: 0,
                ty: bool_type
            }]
        );
        let nested = connection.insert_lambda(bool_type, inner).unwrap();
        assert!(connection.term_is_locally_closed(nested).unwrap());
    }

    #[test]
    fn open_application_requires_one_coherent_boundary_environment() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_bound_term(0, function_type).unwrap();
        let argument = connection.insert_bound_term(0, bool_type).unwrap();

        assert!(matches!(
            connection.insert_application(function, argument),
            Err(TermError::InconsistentUnboundVariable {
                index: 0,
                first,
                second
            }) if first == function_type && second == bool_type
        ));
        let applications = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*) FROM hol_node WHERE tag = 'MAPP'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(applications, 0);
    }

    #[test]
    fn lambda_rejects_a_mistyped_capture_atomically() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();

        assert!(matches!(
            connection.insert_lambda(function_type, variable),
            Err(TermError::BoundVariableTypeMismatch { expected, actual })
                if expected == function_type && actual == bool_type
        ));
        let lambdas = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*) FROM hol_node WHERE tag = 'MLAM'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(lambdas, 0);
    }

    #[test]
    fn contexts_reject_open_boolean_terms() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        assert!(matches!(
            connection.define_context([variable]),
            Err(ContextError::OpenMember(term)) if term == variable
        ));
    }

    #[test]
    fn recursive_term_validation_detects_cycles() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let lambda = connection.insert_lambda(bool_type, variable).unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "UPDATE hol_node SET rhs = ?1 WHERE node_id = ?1",
                [lambda.get()],
            )
            .unwrap();
        assert!(matches!(
            connection.term(lambda),
            Err(TermError::CyclicTerm(id)) if id == lambda
        ));
    }

    #[test]
    fn sqlite_rejects_malformed_bound_term_shapes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let result = connection.parts_mut().0.sqlite().execute(
            "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MBV', -1, 2)",
            [],
        );
        assert!(result.is_err());
    }

    #[test]
    fn lambda_admission_exposes_both_term_and_derived_type_footprints() {
        let mut connection = Connection::open_hol_in_memory(RecordingPolicy {
            allowed: true,
            operations: Vec::new(),
        })
        .unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        connection.insert_lambda(bool_type, variable).unwrap();
        assert_eq!(
            connection.protocol().policy().operations,
            [
                Operation::InsertType,
                Operation::InsertTerm,
                Operation::InsertTerm,
                Operation::InsertType,
            ]
        );
    }

    #[test]
    fn equality_is_typed_canonical_and_preserves_boundaries() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let equality = connection.insert_equality(variable, variable).unwrap();
        assert_eq!(
            connection.term(equality).unwrap(),
            TermView::Equality {
                left: variable,
                right: variable
            }
        );
        assert_eq!(connection.term_type(equality).unwrap(), bool_type);
        assert_eq!(
            connection.term_unbound_variables(equality).unwrap(),
            [UnboundVariable {
                index: 0,
                ty: bool_type
            }]
        );
        assert_eq!(
            equality,
            connection.insert_equality(variable, variable).unwrap()
        );

        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        assert!(matches!(
            connection.insert_equality(variable, identity),
            Err(TermError::EqualityTypeMismatch { left, right })
                if left == bool_type && right != bool_type
        ));
    }

    #[test]
    fn reflexivity_proves_a_closed_identity_lambda() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let conclusion = connection
            .with_proof_session(|mut proof| {
                proof
                    .prove_reflexivity(ContextId::empty(), identity)
                    .map(|theorem| theorem.conclusion())
            })
            .unwrap();
        assert_eq!(
            connection.term(conclusion).unwrap(),
            TermView::Equality {
                left: identity,
                right: identity
            }
        );
        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
        connection
            .with_proof_session(|mut proof| {
                proof
                    .prove_reflexivity(ContextId::empty(), identity)
                    .map(|_| ())
            })
            .unwrap();
        let counts = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT
                     (SELECT count(*) FROM hol_judgement),
                     (SELECT count(*) FROM hol_proof_event)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(counts, (1, 2));
        let rule = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT rule FROM hol_proof_event WHERE ctx_id = 0 AND term_id = ?1",
                [conclusion.get()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(rule, "reflexivity");
    }

    #[test]
    fn reflexivity_rejects_open_terms_without_persisting() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                proof
                    .prove_reflexivity(ContextId::empty(), variable)
                    .map(|_| ())
            }),
            Err(ProofError::OpenConclusion(term)) if term == variable
        ));
        let rows = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_judgement", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 0);
    }

    #[test]
    fn beta_proves_identity_application() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let conclusion = connection
            .with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), identity, truth)
                    .map(|theorem| theorem.conclusion())
            })
            .unwrap();
        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("beta conclusion is not equality");
        };
        assert_eq!(right, truth);
        assert_eq!(
            connection.term(left).unwrap(),
            TermView::Application {
                function: identity,
                argument: truth
            }
        );
        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
    }

    #[test]
    fn beta_substitution_avoids_nested_binder_capture() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let outer_variable = connection.insert_bound_term(1, bool_type).unwrap();
        let inner = connection.insert_lambda(bool_type, outer_variable).unwrap();
        let abstraction = connection.insert_lambda(bool_type, inner).unwrap();
        let falsehood = connection.insert_bool_term(false).unwrap();
        let conclusion = connection
            .with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), abstraction, falsehood)
                    .map(|theorem| theorem.conclusion())
            })
            .unwrap();
        let TermView::Equality { right, .. } = connection.term(conclusion).unwrap() else {
            panic!("beta conclusion is not equality");
        };
        assert_eq!(
            connection.term(right).unwrap(),
            TermView::Lambda {
                parameter_type: bool_type,
                body: falsehood
            }
        );
        assert!(connection.term_is_locally_closed(right).unwrap());
    }

    #[test]
    fn beta_rejects_open_or_mistyped_arguments() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), identity, variable)
                    .map(|_| ())
            }),
            Err(ProofError::OpenConclusion(term)) if term == variable
        ));
        let function = connection.insert_free_term(7, function_type).unwrap();
        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), identity, function)
                    .map(|_| ())
            }),
            Err(ProofError::BetaTypeMismatch { expected, actual })
                if expected == bool_type && actual == function_type
        ));
        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                proof
                    .prove_beta(ContextId::empty(), function, identity)
                    .map(|_| ())
            }),
            Err(ProofError::NotLambda(term)) if term == function
        ));
    }

    #[test]
    fn policy_observes_type_and_term_operations() {
        let mut connection = Connection::open_hol_in_memory(RecordingPolicy {
            allowed: true,
            operations: Vec::new(),
        })
        .unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let literal = connection.insert_bool_term(false).unwrap();
        connection.type_view(bool_type).unwrap();
        connection.term_type(literal).unwrap();
        assert_eq!(
            connection.protocol().policy().operations,
            [
                Operation::InsertType,
                Operation::InsertTerm,
                Operation::ReadType,
                Operation::ReadTerm,
            ]
        );
    }

    #[test]
    fn contexts_are_immutable_canonical_boolean_sets() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let falsehood = connection.insert_bool_term(false).unwrap();
        let context = connection
            .define_context([truth, falsehood, truth])
            .unwrap();
        let reordered = connection.define_context([falsehood, truth]).unwrap();

        assert_eq!(context, reordered);
        assert_eq!(
            connection.context_members(context).unwrap(),
            [truth.min(falsehood), truth.max(falsehood)]
        );
        assert_eq!(connection.context_members(ContextId::empty()).unwrap(), []);

        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(44, function_type).unwrap();
        assert!(matches!(
            connection.define_context([function]),
            Err(ContextError::NonBooleanMember { term, ty })
                if term == function && ty == function_type
        ));
    }

    #[test]
    fn hypothesis_and_truth_are_the_only_judgement_insertion_paths() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let assumption = connection.insert_bool_term(false).unwrap();
        let context = connection.define_context([assumption]).unwrap();

        let (hypothesis_context, hypothesis_conclusion, truth_context, truth_id) = connection
            .with_proof_session(|mut proof| {
                let hypothesis = proof.prove_hypothesis(context, assumption)?;
                let truth = proof.prove_truth(ContextId::empty())?;
                Ok::<_, ProofError>((
                    hypothesis.context(),
                    hypothesis.conclusion(),
                    truth.context(),
                    truth.conclusion(),
                ))
            })
            .unwrap();
        assert_eq!(hypothesis_context, context);
        assert_eq!(hypothesis_conclusion, assumption);
        assert!(connection.proved_judgement(context, assumption).unwrap());

        assert_eq!(truth_context, ContextId::empty());
        assert_eq!(connection.term(truth_id).unwrap(), TermView::Bool(true));
        assert!(
            connection
                .proved_judgement(ContextId::empty(), truth_id)
                .unwrap()
        );
        assert!(
            !connection
                .proved_judgement(ContextId::empty(), assumption)
                .unwrap()
        );

        let reloaded = connection
            .with_proof_session(|mut proof| {
                let hypothesis = proof.load_theorem(context, assumption)?.unwrap();
                let truth = proof.load_theorem(ContextId::empty(), truth_id)?.unwrap();
                Ok::<_, ProofError>((hypothesis.conclusion(), truth.conclusion()))
            })
            .unwrap();
        assert_eq!(reloaded, (assumption, truth_id));

        let rules = connection
            .parts_mut()
            .0
            .sqlite()
            .prepare("SELECT rule FROM hol_proof_event ORDER BY event_id")
            .unwrap()
            .query_map([], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(rules, ["hypothesis", "truth"]);
    }

    #[test]
    fn hypothesis_rejects_nonmembers_without_persisting() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let term = connection.insert_bool_term(false).unwrap();
        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                proof
                    .prove_hypothesis(ContextId::empty(), term)
                    .map(|_| ())
            }),
            Err(ProofError::NotMember { context, term: rejected })
                if context == ContextId::empty() && rejected == term
        ));
        assert!(
            !connection
                .proved_judgement(ContextId::empty(), term)
                .unwrap()
        );
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
    fn metadata_columns_and_indexes_can_target_context_relations() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::Context, "label", MetadataType::Text)
            .unwrap();
        schema
            .add_column_to(MetadataTable::ContextMember, "label", MetadataType::Text)
            .unwrap();
        schema
            .add_column_to(MetadataTable::Judgement, "cost", MetadataType::Integer)
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::ContextMember,
                "context member label",
                ["label"],
                false,
            )
            .unwrap();
        schema
            .add_index_on(MetadataTable::Judgement, "judgement cost", ["cost"], false)
            .unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(AllowAll, schema).unwrap();

        let term = connection.insert_bool_term(false).unwrap();
        let context = connection.define_context([term]).unwrap();
        let conclusion = connection
            .with_proof_session(|mut proof| {
                theorem_conclusion(proof.prove_hypothesis(context, term))
            })
            .unwrap();
        connection
            .set_metadata(
                context.into(),
                &[("label", MetadataValue::Text("assumptions".to_owned()))],
            )
            .unwrap();
        connection
            .set_metadata(
                MetadataTarget::context_member(context, term),
                &[("label", MetadataValue::Text("given".to_owned()))],
            )
            .unwrap();
        connection
            .set_metadata(
                MetadataTarget::judgement(context, conclusion),
                &[("cost", MetadataValue::Integer(1))],
            )
            .unwrap();
        assert_eq!(
            connection.metadata(context.into(), &["label"]).unwrap(),
            [MetadataValue::Text("assumptions".to_owned())]
        );
        assert_eq!(
            connection
                .metadata(MetadataTarget::context_member(context, term), &["label"])
                .unwrap(),
            [MetadataValue::Text("given".to_owned())]
        );
        assert_eq!(
            connection
                .metadata(MetadataTarget::judgement(context, conclusion), &["cost"])
                .unwrap(),
            [MetadataValue::Integer(1)]
        );

        assert_eq!(
            connection
                .protocol()
                .schema()
                .metadata_type_on(MetadataTable::Context, "LABEL"),
            Some(MetadataType::Text)
        );
        let (neutron, _) = connection.parts_mut();
        for (table, column) in [
            ("hol_context", "label"),
            ("hol_context_member", "label"),
            ("hol_judgement", "cost"),
        ] {
            let exists = neutron
                .sqlite()
                .query_row(
                    &format!(
                        "SELECT EXISTS(SELECT 1 FROM pragma_table_info('{table}') WHERE name = ?1)"
                    ),
                    [column],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap();
            assert!(exists);
        }
        for index in ["context member label", "judgement cost"] {
            let exists = neutron
                .sqlite()
                .query_row(
                    "SELECT EXISTS(SELECT 1 FROM sqlite_schema WHERE type = 'index' AND name = ?1)",
                    [index],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap();
            assert!(exists);
        }
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
        assert_eq!(count, 2);
    }
}
