//! Minimal HOL-omega protocol, beginning with canonical kinds.

mod export;
mod import;
mod namespace;
mod reader;
mod schema_descriptor;
mod trust;
mod validate;

pub use export::{HolExportError, HolSnapshotAttestation, SignedHolSnapshot};
pub use import::{
    ExternalExportRef, HolDatabaseRef, ImportError, ImportId, ImportView, NamespaceSource,
};
pub use namespace::{
    ExportError, ExportId, ExportSort, ExportView, NamespaceError, NamespaceExport, NamespaceId,
    NamespaceView,
};
pub use reader::{
    ImportedContextId, ImportedExport, ImportedHolReader, ImportedKindId, ImportedReaderError,
    ImportedTermId, ImportedTermView, ImportedTheorem, ImportedTypeId, ImportedTypeView,
};
pub use schema_descriptor::{HolSchemaDescriptor, HolSchemaDescriptorError};
pub use trust::{
    MatchedTrustedHolImage, SnapshotTrustError, TrustedImportError, TrustedImportId,
    TrustedImportImageError, TrustedImportView,
};
pub use validate::{
    AuthenticatedHolImageValidationError, AuthenticatedValidatedHolImage, HolImageCounts,
    HolImageValidationError, ValidatedHolImage, stlc_bool_eq_v1_schema_id,
    stlc_bool_eq_v1_semantics, stlc_bool_eq_v2_schema_id, stlc_bool_eq_v2_semantics,
    stlc_bool_eq_v3_schema_id, stlc_bool_eq_v3_semantics, stlc_bool_eq_v4_schema_id,
    stlc_bool_eq_v4_semantics, stlc_bool_eq_v5_schema_id, stlc_bool_eq_v5_semantics,
    stlc_bool_eq_v6_schema_id, stlc_bool_eq_v6_semantics, stlc_bool_eq_v7_schema_id,
    stlc_bool_eq_v7_semantics, stlc_bool_eq_v8_schema_id, stlc_bool_eq_v8_semantics,
};

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

/// One admitted type in the settled rank-zero schematic fragment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeView {
    /// The primitive Boolean type.
    Bool,
    /// An opaque, connection-local base-type declaration.
    Base {
        /// Declaration symbol interpreted by the surrounding signature.
        symbol: i64,
    },
    /// A free rank-zero schematic type variable.
    Free {
        /// Connection-local symbol identity.
        symbol: i64,
    },
    /// A rank-zero de Bruijn type occurrence.
    Bound {
        /// Zero-based distance to its enclosing universal type binder.
        index: u32,
    },
    /// An object-level universal type binding one rank-zero type variable.
    Forall {
        /// Body, possibly open before this binder is applied.
        body: TypeId,
    },
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

/// One exact free-variable replacement for simultaneous theorem instantiation.
///
/// `variable` must identify an admitted `MFV` node. Matching is by its exact
/// database-local [`TermId`], not merely by its user-facing symbol.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TermInstantiation {
    /// Exact free-variable node to replace.
    pub variable: TermId,
    /// Locally closed, same-typed replacement term.
    pub replacement: TermId,
}

/// One exact free-type-variable replacement for simultaneous theorem instantiation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TypeInstantiation {
    /// Exact admitted `TFV` node to replace.
    pub variable: TypeId,
    /// Well-formed star-kinded replacement, copied without recursive substitution.
    pub replacement: TypeId,
}

/// One external de Bruijn variable required to type an open term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnboundVariable {
    /// Root-relative external index.
    pub index: u32,
    /// Type required for that index.
    pub ty: TypeId,
}

/// One external de Bruijn type variable required by an open type or term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnboundTypeVariable {
    /// Root-relative external index.
    pub index: u32,
    /// Required kind; version eight always records `star`.
    pub kind: KindId,
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
    /// A closed opaque constant declaration.
    Constant {
        /// Declaration symbol interpreted by the surrounding signature.
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
    /// Hilbert choice applied to a Boolean-valued predicate.
    Epsilon {
        /// Predicate of type `A -> bool`; the epsilon term has type `A`.
        predicate: TermId,
    },
    /// Object-level type abstraction over one rank-zero type variable.
    TypeLambda {
        /// Body checked in an empty external term environment.
        body: TermId,
    },
    /// Object-level type application.
    TypeApplication {
        /// Term of universal type.
        function: TermId,
        /// Rank-zero type argument.
        argument: TypeId,
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
    origin: Option<TheoremOrigin>,
    brand: Invariant<'brand>,
}

/// A checked definitional equality between two terms in one proof session.
///
/// The endpoints have the same type and the same typed external de Bruijn
/// boundary.  Consequently an open conversion cannot directly become a
/// theorem, but it can be closed by [`ProofSession::conversion_lambda`].
pub struct Conversion<'brand> {
    left: TermId,
    right: TermId,
    ty: TypeId,
    term_boundary: BTreeMap<u32, TypeId>,
    type_boundary: BTreeMap<u32, KindId>,
    brand: Invariant<'brand>,
}

impl Conversion<'_> {
    /// Returns the left endpoint.
    #[must_use]
    pub const fn left(&self) -> TermId {
        self.left
    }

    /// Returns the right endpoint.
    #[must_use]
    pub const fn right(&self) -> TermId {
        self.right
    }

    /// Returns the common endpoint type.
    #[must_use]
    pub const fn ty(&self) -> TypeId {
        self.ty
    }

    /// Returns whether both endpoints are locally closed.
    #[must_use]
    pub fn is_closed(&self) -> bool {
        self.term_boundary.is_empty() && self.type_boundary.is_empty()
    }
}

#[derive(Clone, Copy)]
enum TheoremOrigin {
    Hypothesis,
    Truth,
    Reflexivity,
    Beta,
    Weakening,
    EqualityModusPonens,
    EqualitySubstitution,
    DeductionAntisymmetry,
    TermInstantiation,
    TypeInstantiation,
    Abstraction,
    Choice,
    ConversionEquality,
    Conversion,
}

impl TheoremOrigin {
    const fn label(self) -> &'static str {
        match self {
            Self::Hypothesis => "hypothesis",
            Self::Truth => "truth",
            Self::Reflexivity => "reflexivity",
            Self::Beta => "beta",
            Self::Weakening => "weakening",
            Self::EqualityModusPonens => "equality_modus_ponens",
            Self::EqualitySubstitution => "equality_substitution",
            Self::DeductionAntisymmetry => "deduction_antisymmetry",
            Self::TermInstantiation => "term_instantiation",
            Self::TypeInstantiation => "type_instantiation",
            Self::Abstraction => "abstraction",
            Self::Choice => "choice",
            Self::ConversionEquality => "conversion_equality",
            Self::Conversion => "conversion",
        }
    }
}

/// A proved implication between two contexts in one proof session.
///
/// `antecedent ⇒ consequent` means every member of `consequent` is proved
/// under `antecedent`.
pub struct ContextImplication<'brand> {
    antecedent: ContextId,
    consequent: ContextId,
    origin: Option<ImplicationOrigin>,
    brand: Invariant<'brand>,
}

#[derive(Clone, Copy)]
enum ImplicationOrigin {
    Introduction,
    Reflexivity,
    Transitivity,
}

impl ImplicationOrigin {
    const fn label(self) -> &'static str {
        match self {
            Self::Introduction => "introduction",
            Self::Reflexivity => "reflexivity",
            Self::Transitivity => "transitivity",
        }
    }
}

/// A checked exact structural union of immutable context member sets.
pub struct ContextUnion<'brand> {
    left: ContextId,
    right: ContextId,
    result: ContextId,
    brand: Invariant<'brand>,
}

/// Two oppositely directed context implications in one proof session.
///
/// This is a derived capability only. It has no authoritative table of its
/// own and carries no union-find or search result.
pub struct ContextEquivalence<'brand> {
    left: ContextId,
    right: ContextId,
    brand: Invariant<'brand>,
}

impl ContextEquivalence<'_> {
    /// Returns the left endpoint.
    #[must_use]
    pub const fn left(&self) -> ContextId {
        self.left
    }

    /// Returns the right endpoint.
    #[must_use]
    pub const fn right(&self) -> ContextId {
        self.right
    }
}

impl ContextUnion<'_> {
    /// Returns the left input context.
    #[must_use]
    pub const fn left(&self) -> ContextId {
        self.left
    }

    /// Returns the right input context.
    #[must_use]
    pub const fn right(&self) -> ContextId {
        self.right
    }

    /// Returns the context whose members are exactly the input union.
    #[must_use]
    pub const fn result(&self) -> ContextId {
        self.result
    }
}

impl ContextImplication<'_> {
    /// Returns the context under which all target assumptions were proved.
    #[must_use]
    pub const fn antecedent(&self) -> ContextId {
        self.antecedent
    }

    /// Returns the context whose assumptions were discharged.
    #[must_use]
    pub const fn consequent(&self) -> ContextId {
        self.consequent
    }
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
    /// Extend the opaque base-type signature.
    DeclareBaseType,
    /// Read an admitted term or its type.
    ReadTerm,
    /// Validate and canonically intern a term.
    InsertTerm,
    /// Extend the opaque typed-constant signature.
    DeclareConstant,
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
    /// Introduce conversion reflexivity.
    ProveConversionReflexivity,
    /// Reverse a conversion.
    ProveConversionSymmetry,
    /// Compose two conversions.
    ProveConversionTransitivity,
    /// Apply conversion congruence to a function and argument.
    ProveConversionApplication,
    /// Close a common-boundary conversion beneath a lambda.
    ProveConversionLambda,
    /// Apply closed beta conversion.
    ProveConversionBeta,
    /// Apply closed eta conversion.
    ProveConversionEta,
    /// Apply conversion congruence beneath Hilbert choice.
    ProveConversionEpsilon,
    /// Turn a closed conversion into a theorem of equality.
    ProveConversionEquality,
    /// Transport a Boolean theorem along a conversion.
    ProveTheoremConversion,
    /// Query whether a judgement has already been proved.
    ReadTheorem,
    /// Persist a branded theorem as authoritative connection state.
    PersistJudgement,
    /// Introduce a context implication from theorem witnesses.
    ProveContextImplication,
    /// Compose an explicit path of proved context implications.
    ProveContextImplicationPath,
    /// Weaken a theorem along a context implication.
    ProveWeakening,
    /// Apply equality modus ponens to two branded premises.
    ProveEqualityModusPonens,
    /// Substitute equals through one closed typed Boolean predicate.
    ProveEqualitySubstitution,
    /// Discharge opposite conclusions through deduction antisymmetry.
    ProveDeductionAntisymmetry,
    /// Simultaneously instantiate exact free variables throughout a theorem.
    ProveTermInstantiation,
    /// Simultaneously instantiate exact free type variables throughout a theorem.
    ProveTypeInstantiation,
    /// Abstract one exact free variable from both sides of a proved equality.
    ProveAbstraction,
    /// Select a witness for one proved inhabited predicate.
    ProveChoice,
    /// Load or inspect a persisted context implication.
    ReadContextImplication,
    /// Persist a branded context implication as authoritative connection state.
    PersistContextImplication,
    /// Serialize and sign the complete persistent HOL database state.
    ExportSignedSnapshot,
    /// Define one local hierarchical namespace.
    DefineNamespace,
    /// Read one local namespace.
    ReadNamespace,
    /// Publish a local HOL value under a namespace export ID.
    ExportNamespaceValue,
    /// Read one namespace export.
    ReadNamespaceExport,
    /// Register an unfetched schema-qualified database reference.
    RegisterImport,
    /// Read an unfetched database reference.
    ReadImport,
    /// Define a full external namespace alias without fetching it.
    DefineImportedNamespace,
    /// Read an external namespace alias.
    ReadImportedNamespace,
    /// Trust one authenticated signer for schema-qualified snapshot assertions on this connection.
    TrustSnapshotSigner,
    /// Read connection-local snapshot-signer trust.
    ReadTrustedSnapshotSigner,
    /// Explicitly accept one authenticated snapshot assertion from a trusted signer.
    AcceptAuthenticatedSnapshot,
    /// Read connection-local acceptance of an exact authenticated snapshot assertion.
    ReadAcceptedSnapshot,
    /// Persist an auditable accepted assumption for one exact registered import.
    AcceptTrustedImport,
    /// Read a persistent accepted-import assumption.
    ReadTrustedImport,
    /// Match authenticated, structurally validated bytes to one persistent accepted import.
    MatchTrustedImportImage,
    /// Open a matched image through an internally verified immutable VFS.
    OpenTrustedImportReader,
    /// Read namespace/export structure from a scoped imported image.
    ReadImportedImageNamespace,
    /// Read type structure from a scoped imported image.
    ReadImportedImageType,
    /// Read term structure from a scoped imported image.
    ReadImportedImageTerm,
    /// Read an exact persisted judgement from a scoped imported image.
    ReadImportedImageTheorem,
    /// Check and persist one exact structural context union.
    ProveContextUnion,
    /// Load and recheck one exact structural context union.
    ReadContextUnion,
    /// Package two opposite implication witnesses as context equivalence.
    ProveContextEquivalence,
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

/// Logical HOL row family extended by a user metadata column or index.
///
/// These additions are physical annotations only: no metadata column is part
/// of syntax identity, context membership, or judgement validity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MetadataTable {
    /// The shared kind/type/term syntax-node metadata anchor.
    Node,
    /// Immutable context headers.
    Context,
    /// Pairs asserting membership in an immutable context.
    ContextMember,
    /// Persisted proved judgements.
    Judgement,
    /// Persisted proved implications between contexts.
    ContextImplication,
    /// Checked exact structural unions of context member sets.
    ContextUnion,
    /// Local hierarchical namespace headers.
    Namespace,
    /// Published local values in a namespace-wide export-ID space.
    NamespaceExport,
    /// Schema-qualified unfetched database references.
    Import,
    /// Persisted accepted attestations for exact import references.
    TrustedImport,
}

/// One existing row which may carry user metadata.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MetadataTarget {
    /// A kind, type, or term syntax node.
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
    /// An authoritative persisted context implication.
    ContextImplication {
        /// Context proving every assumption of `consequent`.
        antecedent: ContextId,
        /// Context whose assumptions are discharged.
        consequent: ContextId,
    },
    /// An exact structural union keyed by its ordered input pair.
    ContextUnion {
        /// Left input context.
        left: ContextId,
        /// Right input context.
        right: ContextId,
    },
    /// A local namespace header.
    Namespace(NamespaceId),
    /// One published local value.
    NamespaceExport {
        /// Namespace containing the export.
        namespace: NamespaceId,
        /// Namespace-wide export ID.
        export: ExportId,
    },
    /// An unfetched schema-qualified database reference.
    Import(ImportId),
    /// A persisted accepted import attestation.
    TrustedImport(TrustedImportId),
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

    /// Selects an authoritative persisted context implication.
    #[must_use]
    pub const fn context_implication(antecedent: ContextId, consequent: ContextId) -> Self {
        Self::ContextImplication {
            antecedent,
            consequent,
        }
    }

    /// Selects an exact structural context-union row.
    #[must_use]
    pub const fn context_union(left: ContextId, right: ContextId) -> Self {
        Self::ContextUnion { left, right }
    }

    /// Selects a local namespace row.
    #[must_use]
    pub const fn namespace(namespace: NamespaceId) -> Self {
        Self::Namespace(namespace)
    }

    /// Selects one namespace export row.
    #[must_use]
    pub const fn namespace_export(namespace: NamespaceId, export: ExportId) -> Self {
        Self::NamespaceExport { namespace, export }
    }

    /// Selects an import-directory row.
    #[must_use]
    pub const fn import(import: ImportId) -> Self {
        Self::Import(import)
    }

    /// Selects a persisted accepted import attestation.
    #[must_use]
    pub const fn trusted_import(trusted_import: TrustedImportId) -> Self {
        Self::TrustedImport(trusted_import)
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

impl From<NamespaceId> for MetadataTarget {
    fn from(id: NamespaceId) -> Self {
        Self::Namespace(id)
    }
}

impl From<ImportId> for MetadataTarget {
    fn from(id: ImportId) -> Self {
        Self::Import(id)
    }
}

impl From<TrustedImportId> for MetadataTarget {
    fn from(id: TrustedImportId) -> Self {
        Self::TrustedImport(id)
    }
}

#[derive(Clone, Copy)]
struct MetadataBinding {
    table: &'static str,
    core_columns: &'static [&'static str],
}

fn metadata_binding(table: MetadataTable) -> MetadataBinding {
    match table {
        MetadataTable::Node => MetadataBinding {
            table: "hol_node",
            core_columns: &["node_id", "tag", "lhs", "rhs", "ty"],
        },
        MetadataTable::Context => MetadataBinding {
            table: "hol_context",
            core_columns: &["ctx_id"],
        },
        MetadataTable::ContextMember => MetadataBinding {
            table: "hol_context_member",
            core_columns: &["ctx_id", "term_id"],
        },
        MetadataTable::Judgement => MetadataBinding {
            table: "hol_judgement",
            core_columns: &["ctx_id", "term_id"],
        },
        MetadataTable::ContextImplication => MetadataBinding {
            table: "hol_context_implication",
            core_columns: &["antecedent_ctx_id", "consequent_ctx_id"],
        },
        MetadataTable::ContextUnion => MetadataBinding {
            table: "hol_context_exact_union",
            core_columns: &["left_ctx_id", "right_ctx_id", "result_ctx_id"],
        },
        MetadataTable::Namespace => MetadataBinding {
            table: "hol_namespace",
            core_columns: &[
                "namespace_id",
                "parent_namespace_id",
                "name",
                "source_import_id",
                "source_namespace_id",
            ],
        },
        MetadataTable::NamespaceExport => MetadataBinding {
            table: "hol_namespace_export",
            core_columns: &["namespace_id", "export_id", "sort", "local_id", "name"],
        },
        MetadataTable::Import => MetadataBinding {
            table: "hol_import",
            core_columns: &["import_id", "schema_hash", "image_hash"],
        },
        MetadataTable::TrustedImport => MetadataBinding {
            table: "hol_trusted_import",
            core_columns: &[
                "trusted_import_id",
                "import_id",
                "signer_hash",
                "public_key",
                "signature",
            ],
        },
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

    /// Adds a nullable user metadata column to the syntax-node metadata anchor.
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
        if metadata_binding(table)
            .core_columns
            .iter()
            .any(|core| core.eq_ignore_ascii_case(&name))
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
        trust::install_connection_trust_schema(&transaction)?;
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
        write_target_metadata(&transaction, &hol.schema, id.into(), metadata)
            .map_err(|error| kind_metadata_error(id, error))?;
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

    /// Declares an opaque nonempty base type under a connection-local symbol.
    ///
    /// Repeating the same symbol returns the same canonical type. This operation
    /// asserts no property such as infinitude and introduces no theorem.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies signature extension/type insertion or
    /// `SQLite` rejects the transaction.
    pub fn insert_base_type(&mut self, symbol: i64) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::DeclareBaseType)?;
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        let id = intern_base_type(neutron.sqlite(), symbol)?;
        Ok(id)
    }

    /// Canonically interns a free rank-zero schematic type variable.
    ///
    /// This is logical syntax rather than a signature declaration. The variable
    /// has kind `star` and is locally closed.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies type insertion or `SQLite` rejects it.
    pub fn insert_free_type(&mut self, symbol: i64) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        intern_free_type(neutron.sqlite(), symbol)
    }

    /// Canonically interns a rank-zero de Bruijn type occurrence.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission or `SQLite` rejects it.
    pub fn insert_bound_type(&mut self, index: u32) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        intern_bound_type(neutron.sqlite(), index)
    }

    /// Closes one rank-zero type binder around a type body.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, the body is invalid, or insertion fails.
    pub fn insert_forall_type(&mut self, body: TypeId) -> Result<TypeId, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::InsertType)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        validate_type(&transaction, body)?;
        let result = intern_forall_type(&transaction, body)?;
        validate_type(&transaction, result)?;
        transaction.commit()?;
        Ok(result)
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
        validate_type(&transaction, domain)?;
        validate_type(&transaction, codomain)?;
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
        Ok(validate_type(neutron.sqlite(), id)?.view)
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
        validate_type(neutron.sqlite(), id)?;
        Ok(STAR_ID)
    }

    /// Returns exact free-type-variable IDs reachable from a type in ascending order.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the type graph is invalid.
    pub fn type_free_variables(&mut self, id: TypeId) -> Result<Vec<TypeId>, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::ReadType)?;
        collect_type_free_variables(neutron.sqlite(), id)
    }

    /// Reports whether a type is locally closed.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the type graph is invalid.
    pub fn type_is_locally_closed(&mut self, id: TypeId) -> Result<bool, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::ReadType)?;
        Ok(validate_type(neutron.sqlite(), id)?.boundary.is_empty())
    }

    /// Returns external rank-zero de Bruijn variables required by a type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the type graph is invalid.
    pub fn type_unbound_variables(
        &mut self,
        id: TypeId,
    ) -> Result<Vec<UnboundTypeVariable>, TypeError> {
        let (neutron, hol) = self.parts_mut();
        authorize_type(&mut hol.policy, Operation::ReadType)?;
        Ok(validate_type(neutron.sqlite(), id)?
            .boundary
            .into_iter()
            .map(|(index, kind)| UnboundTypeVariable { index, kind })
            .collect())
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
        validate_type(&transaction, ty)?;
        let id = intern_free_term(&transaction, symbol, ty)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Declares one closed opaque constant at an admitted type.
    ///
    /// A symbol has one canonical declared type. Redeclaring it at another type
    /// fails atomically. Declaration introduces no equation or theorem.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies signature extension/term insertion,
    /// the type is invalid, the symbol already has another type, or `SQLite`
    /// rejects the transaction.
    pub fn insert_constant(&mut self, symbol: i64, ty: TypeId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::DeclareConstant)?;
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let validation = validate_type(&transaction, ty)?;
        if type_contains_free_variable(&transaction, ty)? {
            return Err(TermError::PolymorphicConstantType { symbol, ty });
        }
        if !validation.boundary.is_empty() {
            return Err(TermError::OpenConstantType { symbol, ty });
        }
        let id = intern_constant(&transaction, symbol, ty)?;
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
        validate_type(&transaction, ty)?;
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

    /// Checks and canonically interns Hilbert choice for one predicate.
    ///
    /// If `predicate` has type `A -> bool`, the resulting term has type `A`.
    /// Its external de Bruijn boundary is exactly the predicate's boundary, so
    /// open epsilon syntax can be closed by an enclosing lambda.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies admission, the predicate is invalid,
    /// is not a function, does not return Boolean, or `SQLite` rejects the
    /// atomic insertion.
    pub fn insert_epsilon(&mut self, predicate: TermId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let predicate_validation = validate_term(&transaction, predicate)?;
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, predicate_validation.ty)?
        else {
            return Err(TermError::NotFunction(predicate_validation.ty));
        };
        if codomain != BOOL_TYPE_ID {
            return Err(TermError::EpsilonPredicateNonBoolean {
                predicate,
                codomain,
            });
        }
        let id = intern_epsilon(&transaction, predicate, domain)?;
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
        validate_type(&transaction, parameter_type)?;
        let body_type = validate_term(&transaction, body)?.ty;
        let function_type = intern_type_arrow(&transaction, parameter_type, body_type)?;
        let id = intern_lambda(&transaction, parameter_type, body, function_type)?;
        validate_term(&transaction, id)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Closes one rank-zero type binder around a term with no external term environment.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies insertion, the body is invalid or has a forbidden
    /// external term environment, or atomic insertion fails.
    pub fn insert_type_lambda(&mut self, body: TermId) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        authorize_type(&mut hol.policy, Operation::InsertType).map_err(TermError::Type)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let body_validation = validate_term(&transaction, body)?;
        if !body_validation.term_boundary.is_empty() {
            return Err(TermError::TypeLambdaOpenTermBody(body));
        }
        if body_validation.has_mfv {
            return Err(TermError::TypeLambdaFreeTermBody(body));
        }
        let ty = intern_forall_type(&transaction, body_validation.ty)?;
        let id = intern_type_lambda(&transaction, body, ty)?;
        validate_term(&transaction, id)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Instantiates one rank-zero universal term at an admitted type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies insertion, either operand is invalid, the function is
    /// not universal, substitution overflows, or atomic insertion fails.
    pub fn insert_type_application(
        &mut self,
        function: TermId,
        argument: TypeId,
    ) -> Result<TermId, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::InsertTerm)?;
        authorize_type(&mut hol.policy, Operation::InsertType).map_err(TermError::Type)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let function_validation = validate_term(&transaction, function)?;
        validate_type(&transaction, argument)?;
        let TypeView::Forall { body } = read_type(&transaction, function_validation.ty)? else {
            return Err(TermError::NotUniversal(function_validation.ty));
        };
        let ty = substitute_bound_type(&transaction, body, argument)?;
        let id = intern_type_application(&transaction, function, argument, ty)?;
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
        merge_term_boundaries(
            left_validation.term_boundary,
            right_validation.term_boundary,
        )?;
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

    /// Returns exact free type variables occurring anywhere in a term graph.
    ///
    /// This inspects every reachable term annotation, including lambda parameter
    /// types and internal types which need not occur in the root result type.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term/type graph is invalid.
    pub fn term_free_type_variables(&mut self, id: TermId) -> Result<Vec<TypeId>, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        collect_term_free_type_variables(neutron.sqlite(), id)
    }

    /// Reports whether a term is locally closed.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term is invalid.
    pub fn term_is_locally_closed(&mut self, id: TermId) -> Result<bool, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        Ok(validate_term(neutron.sqlite(), id)?.is_closed())
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
            .term_boundary
            .into_iter()
            .map(|(index, ty)| UnboundVariable { index, ty })
            .collect())
    }

    /// Returns external rank-zero de Bruijn type variables required by a term.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or the term/type graph is invalid.
    pub fn term_unbound_type_variables(
        &mut self,
        id: TermId,
    ) -> Result<Vec<UnboundTypeVariable>, TermError> {
        let (neutron, hol) = self.parts_mut();
        authorize_term(&mut hol.policy, Operation::ReadTerm)?;
        Ok(validate_term(neutron.sqlite(), id)?
            .type_boundary
            .into_iter()
            .map(|(index, kind)| UnboundTypeVariable { index, kind })
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
        let context = intern_context(&transaction, &members)?;
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
    /// Applies the hypothesis rule and returns a session capability.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context is unknown, the
    /// term is not a member, or `SQLite` rejects the membership check.
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
        Ok(Theorem {
            context,
            conclusion: term,
            origin: Some(TheoremOrigin::Hypothesis),
            brand: PhantomData,
        })
    }

    /// Applies primitive truth in an existing context.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule or syntax insertion, the
    /// context is unknown, or `SQLite` rejects syntax interning.
    pub fn prove_truth(&mut self, context: ContextId) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveTruth)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let truth = intern_bool_term(&transaction, true)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: truth,
            origin: Some(TheoremOrigin::Truth),
            brand: PhantomData,
        })
    }

    /// Introduces reflexive conversion for an admitted term.
    ///
    /// Unlike theorem reflexivity, this rule admits an open term.  Its typed
    /// boundary is retained in the capability and must be closed before the
    /// conversion can produce a theorem.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule or the term is invalid.
    pub fn conversion_reflexivity(
        &mut self,
        term: TermId,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionReflexivity)?;
        let validated = validate_term(neutron.sqlite(), term)?;
        Ok(Conversion {
            left: term,
            right: term,
            ty: validated.ty,
            term_boundary: validated.term_boundary,
            type_boundary: validated.type_boundary,
            brand: PhantomData,
        })
    }

    /// Reverses a checked conversion.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule.
    pub fn conversion_symmetry(
        &mut self,
        conversion: &Conversion<'brand>,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (_, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionSymmetry)?;
        Ok(Conversion {
            left: conversion.right,
            right: conversion.left,
            ty: conversion.ty,
            term_boundary: conversion.term_boundary.clone(),
            type_boundary: conversion.type_boundary.clone(),
            brand: PhantomData,
        })
    }

    /// Composes conversions whose middle endpoints are exactly identical.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule or the endpoints differ.
    pub fn conversion_transitivity(
        &mut self,
        first: &Conversion<'brand>,
        second: &Conversion<'brand>,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (_, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionTransitivity)?;
        if first.right != second.left
            || first.ty != second.ty
            || first.term_boundary != second.term_boundary
            || first.type_boundary != second.type_boundary
        {
            return Err(ProofError::ConversionChainMismatch {
                first_right: first.right,
                second_left: second.left,
            });
        }
        Ok(Conversion {
            left: first.left,
            right: second.right,
            ty: first.ty,
            term_boundary: first.term_boundary.clone(),
            type_boundary: first.type_boundary.clone(),
            brand: PhantomData,
        })
    }

    /// Applies congruence to checked function and argument conversions.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, types or open
    /// boundaries are incompatible, or syntax interning fails.
    pub fn conversion_application(
        &mut self,
        function: &Conversion<'brand>,
        argument: &Conversion<'brand>,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionApplication)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, function.ty).map_err(TermError::Type)?
        else {
            return Err(TermError::NotFunction(function.ty).into());
        };
        if domain != argument.ty {
            return Err(TermError::ApplicationTypeMismatch {
                expected: domain,
                actual: argument.ty,
            }
            .into());
        }
        merge_term_boundaries(
            function.term_boundary.clone(),
            argument.term_boundary.clone(),
        )?;
        let left = intern_application(&transaction, function.left, argument.left, codomain)?;
        let right = intern_application(&transaction, function.right, argument.right, codomain)?;
        let conversion = checked_conversion(&transaction, left, right)?;
        transaction.commit()?;
        Ok(conversion)
    }

    /// Closes one binder in both endpoints of a common-boundary conversion.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, the binder type
    /// is invalid, its capture annotations differ, or syntax interning fails.
    pub fn conversion_lambda(
        &mut self,
        parameter_type: TypeId,
        body: &Conversion<'brand>,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionLambda)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        authorize_proof(&mut hol.policy, Operation::InsertType)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        validate_type(&transaction, parameter_type).map_err(TermError::Type)?;
        // Check the capture type before writing either endpoint.
        close_term_boundary(body.term_boundary.clone(), parameter_type)?;
        let function_type =
            intern_type_arrow(&transaction, parameter_type, body.ty).map_err(TermError::Type)?;
        let left = intern_lambda(&transaction, parameter_type, body.left, function_type)?;
        let right = intern_lambda(&transaction, parameter_type, body.right, function_type)?;
        let conversion = checked_conversion(&transaction, left, right)?;
        transaction.commit()?;
        Ok(conversion)
    }

    /// Produces the definitional conversion `(λx. body) argument ≡ body[argument/x]`.
    ///
    /// Both the abstraction and argument must be closed, so substitution does
    /// not require a general shifting operation.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, either input is
    /// open or invalid, types differ, or substitution/interning fails.
    pub fn conversion_beta(
        &mut self,
        abstraction: TermId,
        argument: TermId,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionBeta)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let abstraction_validation = validate_term(&transaction, abstraction)?;
        if !abstraction_validation.is_closed() {
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
        if !argument_validation.is_closed() {
            return Err(ProofError::OpenConclusion(argument));
        }
        if argument_validation.ty != parameter_type {
            return Err(ProofError::BetaTypeMismatch {
                expected: parameter_type,
                actual: argument_validation.ty,
            });
        }
        let TypeView::Arrow { codomain, .. } =
            read_type(&transaction, abstraction_validation.ty).map_err(TermError::Type)?
        else {
            return Err(ProofError::NotLambda(abstraction));
        };
        let left = intern_application(&transaction, abstraction, argument, codomain)?;
        let right = substitute_closed(&transaction, body, argument, 0)?;
        let conversion = checked_conversion(&transaction, left, right)?;
        transaction.commit()?;
        Ok(conversion)
    }

    /// Produces the restricted closed eta conversion `λx. f x ≡ f`.
    ///
    /// Requiring `f` to be closed is the exact condition which lets this
    /// fragment place it beneath a binder without a shifting primitive.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, `f` is open or
    /// not a valid function, or syntax interning fails.
    pub fn conversion_eta(&mut self, function: TermId) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionEta)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let validated = validate_term(&transaction, function)?;
        if !validated.is_closed() {
            return Err(ProofError::OpenConclusion(function));
        }
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, validated.ty).map_err(TermError::Type)?
        else {
            return Err(TermError::NotFunction(validated.ty).into());
        };
        let variable = intern_bound_term(&transaction, 0, domain)?;
        let body = intern_application(&transaction, function, variable, codomain)?;
        let left = intern_lambda(&transaction, domain, body, validated.ty)?;
        let conversion = checked_conversion(&transaction, left, function)?;
        transaction.commit()?;
        Ok(conversion)
    }

    /// Applies definitional-conversion congruence beneath Hilbert choice.
    ///
    /// From `p ≡ q` at type `A -> bool`, derives `εp ≡ εq`. Open
    /// predicate conversions are supported and retain their exact common
    /// external de Bruijn boundary.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, the conversion is
    /// not between Boolean-valued predicates, or atomic interning fails.
    pub fn conversion_epsilon(
        &mut self,
        predicate: &Conversion<'brand>,
    ) -> Result<Conversion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionEpsilon)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, predicate.ty).map_err(TermError::Type)?
        else {
            return Err(TermError::NotFunction(predicate.ty).into());
        };
        if codomain != BOOL_TYPE_ID {
            return Err(TermError::EpsilonPredicateNonBoolean {
                predicate: predicate.left,
                codomain,
            }
            .into());
        }
        let left = intern_epsilon(&transaction, predicate.left, domain)?;
        let right = intern_epsilon(&transaction, predicate.right, domain)?;
        let conversion = checked_conversion(&transaction, left, right)?;
        transaction.commit()?;
        Ok(conversion)
    }

    /// Turns a closed conversion into a theorem `Γ ⊢ left = right`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, the conversion is
    /// open, the context is invalid, or equality interning fails.
    pub fn prove_conversion_equality(
        &mut self,
        context: ContextId,
        conversion: &Conversion<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveConversionEquality)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        if !conversion.is_closed() {
            return Err(ProofError::OpenConclusion(conversion.left));
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let equality = intern_equality(&transaction, conversion.left, conversion.right)?;
        validate_term(&transaction, equality)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            origin: Some(TheoremOrigin::ConversionEquality),
            brand: PhantomData,
        })
    }

    /// Transports `Γ ⊢ left` along a closed Boolean conversion `left ≡ right`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the conversion is open or
    /// non-Boolean, or the premise conclusion is not its left endpoint.
    pub fn convert_theorem(
        &mut self,
        theorem: &Theorem<'brand>,
        conversion: &Conversion<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (_, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveTheoremConversion)?;
        if !conversion.is_closed() {
            return Err(ProofError::OpenConclusion(conversion.left));
        }
        if conversion.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConversion {
                term: conversion.left,
                ty: conversion.ty,
            });
        }
        if theorem.conclusion != conversion.left {
            return Err(ProofError::ConversionPremiseMismatch {
                expected: conversion.left,
                actual: theorem.conclusion,
            });
        }
        Ok(Theorem {
            context: theorem.context,
            conclusion: conversion.right,
            origin: Some(TheoremOrigin::Conversion),
            brand: PhantomData,
        })
    }

    /// Applies equality reflexivity in an existing context.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the context or term is
    /// invalid, the term is locally open, or syntax interning fails.
    pub fn prove_reflexivity(
        &mut self,
        context: ContextId,
        term: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveReflexivity)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let validation = validate_term(&transaction, term)?;
        if !validation.is_closed() {
            return Err(ProofError::OpenConclusion(term));
        }
        let equality = intern_equality(&transaction, term, term)?;
        validate_term(&transaction, equality)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            origin: Some(TheoremOrigin::Reflexivity),
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
    /// argument type differs, substitution or syntax interning fails.
    pub fn prove_beta(
        &mut self,
        context: ContextId,
        abstraction: TermId,
        argument: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveBeta)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, context)?;
        let abstraction_validation = validate_term(&transaction, abstraction)?;
        if !abstraction_validation.is_closed() {
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
        if !argument_validation.is_closed() {
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
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            origin: Some(TheoremOrigin::Beta),
            brand: PhantomData,
        })
    }

    /// Persists one branded theorem as an authoritative judgement row.
    ///
    /// A freshly derived capability also appends its fixed observational rule
    /// label. Re-persisting a capability loaded from the database is an
    /// idempotent row insertion and creates no invented provenance event.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies persistence or `SQLite` rejects it.
    pub fn persist_theorem(&mut self, theorem: &Theorem<'brand>) -> Result<(), ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::PersistJudgement)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        persist_judgement(
            &transaction,
            theorem.context,
            theorem.conclusion,
            theorem.origin.map(TheoremOrigin::label),
        )?;
        transaction.commit()?;
        Ok(())
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
        if !validation.is_closed() {
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
            origin: None,
            brand: PhantomData,
        }))
    }

    /// Proves `antecedent ⇒ consequent` from an exact set of theorem witnesses.
    ///
    /// Each member of `consequent` must occur exactly once as the conclusion of
    /// a witness proved under `antecedent`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, either context is unknown,
    /// witnesses have the wrong context, or their conclusions do not exactly
    /// cover the consequent context.
    pub fn prove_context_implication(
        &mut self,
        antecedent: ContextId,
        consequent: ContextId,
        witnesses: &[Theorem<'brand>],
    ) -> Result<ContextImplication<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveContextImplication)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, antecedent)?;
        require_context(&transaction, consequent)?;
        let expected = read_context_members(&transaction, consequent)?;
        let mut actual = Vec::with_capacity(witnesses.len());
        let mut seen = HashSet::new();
        for witness in witnesses {
            if witness.context != antecedent {
                return Err(ProofError::WrongImplicationWitnessContext {
                    expected: antecedent,
                    actual: witness.context,
                    conclusion: witness.conclusion,
                });
            }
            if !seen.insert(witness.conclusion) {
                return Err(ProofError::DuplicateImplicationWitness(witness.conclusion));
            }
            actual.push(witness.conclusion);
        }
        actual.sort_unstable();
        if let Some(term) = expected.iter().find(|term| !seen.contains(term)) {
            return Err(ProofError::MissingImplicationWitness {
                consequent,
                term: *term,
            });
        }
        if let Some(term) = actual
            .iter()
            .find(|term| expected.binary_search(term).is_err())
        {
            return Err(ProofError::UnexpectedImplicationWitness {
                consequent,
                term: *term,
            });
        }
        Ok(ContextImplication {
            antecedent,
            consequent,
            origin: Some(ImplicationOrigin::Introduction),
            brand: PhantomData,
        })
    }

    /// Loads one exact persisted context implication as a session capability.
    ///
    /// This performs no transitive search.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, either context is unknown,
    /// or `SQLite` rejects the exact lookup.
    pub fn load_context_implication(
        &mut self,
        antecedent: ContextId,
        consequent: ContextId,
    ) -> Result<Option<ContextImplication<'brand>>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadContextImplication)?;
        require_context(neutron.sqlite(), antecedent)?;
        require_context(neutron.sqlite(), consequent)?;
        let exists = neutron.sqlite().query_row(
            "SELECT EXISTS(
                 SELECT 1 FROM hol_context_implication
                 WHERE antecedent_ctx_id = ?1 AND consequent_ctx_id = ?2
             )",
            [antecedent.0, consequent.0],
            |row| row.get::<_, bool>(0),
        )?;
        Ok(exists.then_some(ContextImplication {
            antecedent,
            consequent,
            origin: None,
            brand: PhantomData,
        }))
    }

    /// Composes one explicit path of authoritative implication edges.
    ///
    /// A singleton path establishes context reflexivity. Longer paths are
    /// checked edge-by-edge with exact primary-key lookups; this method never
    /// searches for a path.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies composition, the path is empty, a
    /// context is unknown, or an adjacent persisted edge is absent.
    pub fn prove_context_implication_path(
        &mut self,
        path: &[ContextId],
    ) -> Result<ContextImplication<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveContextImplicationPath)?;
        let Some(antecedent) = path.first().copied() else {
            return Err(ProofError::EmptyImplicationPath);
        };
        let consequent = path.last().copied().unwrap_or(antecedent);
        let transaction = neutron.sqlite().unchecked_transaction()?;
        for context in path {
            require_context(&transaction, *context)?;
        }
        for edge in path.windows(2) {
            let exists = transaction.query_row(
                "SELECT EXISTS(
                     SELECT 1 FROM hol_context_implication
                     WHERE antecedent_ctx_id = ?1 AND consequent_ctx_id = ?2
                 )",
                [edge[0].0, edge[1].0],
                |row| row.get::<_, bool>(0),
            )?;
            if !exists {
                return Err(ProofError::MissingContextImplicationEdge {
                    antecedent: edge[0],
                    consequent: edge[1],
                });
            }
        }
        Ok(ContextImplication {
            antecedent,
            consequent,
            origin: Some(if path.len() == 1 {
                ImplicationOrigin::Reflexivity
            } else {
                ImplicationOrigin::Transitivity
            }),
            brand: PhantomData,
        })
    }

    /// Persists one branded implication as an authoritative directed edge.
    ///
    /// Fresh derivations append their fixed observational rule label. A
    /// capability loaded from the database adds no new provenance event.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies persistence or `SQLite` rejects it.
    pub fn persist_context_implication(
        &mut self,
        implication: &ContextImplication<'brand>,
    ) -> Result<(), ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::PersistContextImplication)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        persist_context_implication(
            &transaction,
            implication.antecedent,
            implication.consequent,
            implication.origin.map(ImplicationOrigin::label),
        )?;
        transaction.commit()?;
        Ok(())
    }

    /// Checks and records that `result` has exactly the members of `left ∪ right`.
    ///
    /// This is a decidable structural relation over concrete immutable
    /// contexts, not the future logical notion of an opaque context merely
    /// equivalent to a union.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the check, a context is unknown, the
    /// result member set differs, an existing ordered pair names another
    /// result, or persistence fails.
    pub fn prove_context_union(
        &mut self,
        left: ContextId,
        right: ContextId,
        result: ContextId,
    ) -> Result<ContextUnion<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveContextUnion)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, left)?;
        require_context(&transaction, right)?;
        require_context(&transaction, result)?;
        check_context_union_members(&transaction, left, right, result)?;
        if let Some(stored_result) = transaction
            .query_row(
                "SELECT result_ctx_id FROM hol_context_exact_union
                 WHERE left_ctx_id = ?1 AND right_ctx_id = ?2",
                (left.0, right.0),
                |row| row.get::<_, i64>(0).map(ContextId),
            )
            .optional()?
            && stored_result != result
        {
            return Err(ProofError::ContextUnionConflict {
                left,
                right,
                stored_result,
                requested_result: result,
            });
        }
        persist_context_union(&transaction, left, right, result)?;
        transaction.commit()?;
        Ok(ContextUnion {
            left,
            right,
            result,
            brand: PhantomData,
        })
    }

    /// Loads and structurally rechecks one exact ordered context union.
    ///
    /// This performs one primary-key lookup and never searches for a matching
    /// result context.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, an input or stored result is
    /// unknown, the stored structural fact is false, or `SQLite` rejects it.
    pub fn load_context_union(
        &mut self,
        left: ContextId,
        right: ContextId,
    ) -> Result<Option<ContextUnion<'brand>>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadContextUnion)?;
        require_context(neutron.sqlite(), left)?;
        require_context(neutron.sqlite(), right)?;
        let Some(result) = neutron
            .sqlite()
            .query_row(
                "SELECT result_ctx_id FROM hol_context_exact_union
                 WHERE left_ctx_id = ?1 AND right_ctx_id = ?2",
                (left.0, right.0),
                |row| row.get::<_, i64>(0).map(ContextId),
            )
            .optional()?
        else {
            return Ok(None);
        };
        require_context(neutron.sqlite(), result)?;
        check_context_union_members(neutron.sqlite(), left, right, result)?;
        Ok(Some(ContextUnion {
            left,
            right,
            result,
            brand: PhantomData,
        }))
    }

    /// Packages implication witnesses in both directions as equivalence.
    ///
    /// This checks only that the endpoints are exact opposites. Candidate path
    /// search and path checking happen before this method produces a pair.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the operation or the two implications
    /// do not have reversed endpoints.
    pub fn prove_context_equivalence(
        &mut self,
        forward: &ContextImplication<'brand>,
        backward: &ContextImplication<'brand>,
    ) -> Result<ContextEquivalence<'brand>, ProofError> {
        let (_, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveContextEquivalence)?;
        if forward.antecedent != backward.consequent || forward.consequent != backward.antecedent {
            return Err(ProofError::ContextEquivalenceMismatch {
                forward_antecedent: forward.antecedent,
                forward_consequent: forward.consequent,
                backward_antecedent: backward.antecedent,
                backward_consequent: backward.consequent,
            });
        }
        Ok(ContextEquivalence {
            left: forward.antecedent,
            right: forward.consequent,
            brand: PhantomData,
        })
    }

    /// Transports a theorem from an implied context to its antecedent.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies weakening or the theorem is not proved
    /// under the implication's consequent.
    pub fn weaken(
        &mut self,
        implication: &ContextImplication<'brand>,
        theorem: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (_, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveWeakening)?;
        if theorem.context != implication.consequent {
            return Err(ProofError::WeakeningContextMismatch {
                expected: implication.consequent,
                actual: theorem.context,
            });
        }
        Ok(Theorem {
            context: implication.antecedent,
            conclusion: theorem.conclusion,
            origin: Some(TheoremOrigin::Weakening),
            brand: PhantomData,
        })
    }

    /// Applies typed Leibniz substitution.
    ///
    /// From `Γ ⊢ left = right` and `Γ ⊢ predicate left`, where `predicate` is
    /// a closed term of type `type(left) -> bool`, this derives
    /// `Γ ⊢ predicate right`. The premise application must match exactly;
    /// this rule performs no conversion, shifting, or binder manipulation.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, the premises have
    /// different contexts, the first premise is not equality, the predicate is
    /// open or has the wrong type, the second premise is not the exact expected
    /// application, or checked term insertion fails.
    pub fn equality_substitution(
        &mut self,
        equality: &Theorem<'brand>,
        predicate: TermId,
        premise: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveEqualitySubstitution)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        if equality.context != premise.context {
            return Err(ProofError::EqualitySubstitutionContextMismatch {
                equality: equality.context,
                premise: premise.context,
            });
        }

        let transaction = neutron.sqlite().unchecked_transaction()?;
        let (equality_view, _) = read_term(&transaction, equality.conclusion)?;
        let TermView::Equality { left, right } = equality_view else {
            return Err(ProofError::ExpectedEquality(equality.conclusion));
        };
        let left_validation = validate_term(&transaction, left)?;
        let predicate_validation = validate_term(&transaction, predicate)?;
        if !predicate_validation.is_closed() {
            return Err(ProofError::OpenEqualityPredicate(predicate));
        }
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, predicate_validation.ty).map_err(TermError::Type)?
        else {
            return Err(ProofError::EqualityPredicateNotFunction {
                predicate,
                ty: predicate_validation.ty,
            });
        };
        if domain != left_validation.ty {
            return Err(ProofError::EqualityPredicateDomainMismatch {
                predicate,
                expected: left_validation.ty,
                actual: domain,
            });
        }
        if codomain != BOOL_TYPE_ID {
            return Err(ProofError::EqualityPredicateNonBoolean {
                predicate,
                codomain,
            });
        }
        let (premise_view, _) = read_term(&transaction, premise.conclusion)?;
        if premise_view
            != (TermView::Application {
                function: predicate,
                argument: left,
            })
        {
            return Err(ProofError::EqualitySubstitutionPremiseMismatch {
                predicate,
                argument: left,
                actual: premise.conclusion,
            });
        }
        let conclusion = intern_application(&transaction, predicate, right, BOOL_TYPE_ID)?;
        validate_term(&transaction, conclusion)?;
        transaction.commit()?;
        Ok(Theorem {
            context: equality.context,
            conclusion,
            origin: Some(TheoremOrigin::EqualitySubstitution),
            brand: PhantomData,
        })
    }

    /// Applies deduction antisymmetry to two Boolean theorems.
    ///
    /// From `Γ ⊢ p` and `Δ ⊢ q`, this derives
    /// `(Γ ∖ {q}) ∪ (Δ ∖ {p}) ⊢ p = q`. Context subtraction and union
    /// use the canonical finite-set representation; the equality and exact
    /// result context are interned atomically.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, term insertion, or context
    /// construction; either premise or context is corrupt; or `SQLite` rejects
    /// the atomic construction.
    pub fn deduction_antisymmetry(
        &mut self,
        first: &Theorem<'brand>,
        second: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveDeductionAntisymmetry)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        authorize_context(&mut hol.policy, Operation::DefineContext)?;

        let transaction = neutron.sqlite().unchecked_transaction()?;
        let first_validation = validate_term(&transaction, first.conclusion)?;
        let second_validation = validate_term(&transaction, second.conclusion)?;
        if first_validation.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConclusion {
                term: first.conclusion,
                ty: first_validation.ty,
            });
        }
        if second_validation.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConclusion {
                term: second.conclusion,
                ty: second_validation.ty,
            });
        }
        if !first_validation.is_closed() {
            return Err(ProofError::OpenConclusion(first.conclusion));
        }
        if !second_validation.is_closed() {
            return Err(ProofError::OpenConclusion(second.conclusion));
        }

        require_context(&transaction, first.context)?;
        require_context(&transaction, second.context)?;
        let mut members = read_context_members(&transaction, first.context)?;
        members.retain(|member| *member != second.conclusion);
        members.extend(
            read_context_members(&transaction, second.context)?
                .into_iter()
                .filter(|member| *member != first.conclusion),
        );
        members.sort_unstable();
        members.dedup();

        let equality = intern_equality(&transaction, first.conclusion, second.conclusion)?;
        validate_term(&transaction, equality)?;
        let context = intern_context(&transaction, &members)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion: equality,
            origin: Some(TheoremOrigin::DeductionAntisymmetry),
            brand: PhantomData,
        })
    }

    /// Simultaneously instantiates exact free variables throughout a theorem.
    ///
    /// Every key must be an `MFV` node, keys must be distinct, and each
    /// replacement must be locally closed and have the key's type. The
    /// substitution is simultaneous: replacement terms are copied unchanged,
    /// including beneath lambdas. Both the conclusion and every assumption in
    /// the theorem's context are transformed, then canonically interned.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, term insertion, or context
    /// construction; the theorem graph or context is invalid; an
    /// instantiation key is not an exact free-variable node or is duplicated;
    /// or a replacement is open or has the wrong type.
    pub fn instantiate_terms(
        &mut self,
        theorem: &Theorem<'brand>,
        instantiations: &[TermInstantiation],
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveTermInstantiation)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        authorize_context(&mut hol.policy, Operation::DefineContext)?;

        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, theorem.context)?;
        let members = read_context_members(&transaction, theorem.context)?;

        // Validate every root before walking and interning any transformed graph.
        validate_term(&transaction, theorem.conclusion)?;
        for member in &members {
            validate_term(&transaction, *member)?;
        }
        let mut replacements = HashMap::with_capacity(instantiations.len());
        for instantiation in instantiations {
            let variable = validate_term(&transaction, instantiation.variable)?;
            if !matches!(variable.view, TermView::Free { .. }) {
                return Err(ProofError::InstantiationKeyNotFree(instantiation.variable));
            }
            if replacements
                .insert(instantiation.variable, instantiation.replacement)
                .is_some()
            {
                return Err(ProofError::DuplicateTermInstantiation(
                    instantiation.variable,
                ));
            }
            let replacement = validate_term(&transaction, instantiation.replacement)?;
            if variable.ty != replacement.ty {
                return Err(ProofError::TermInstantiationTypeMismatch {
                    variable: instantiation.variable,
                    replacement: instantiation.replacement,
                    expected: variable.ty,
                    actual: replacement.ty,
                });
            }
            if !replacement.is_closed() {
                return Err(ProofError::OpenTermInstantiationReplacement(
                    instantiation.replacement,
                ));
            }
        }

        let mut memo = HashMap::new();
        let conclusion = instantiate_free_terms_inner(
            &transaction,
            theorem.conclusion,
            &replacements,
            &mut memo,
        )?;
        let mut transformed_members = members
            .into_iter()
            .map(|member| {
                instantiate_free_terms_inner(&transaction, member, &replacements, &mut memo)
            })
            .collect::<Result<Vec<_>, _>>()?;
        transformed_members.sort_unstable();
        transformed_members.dedup();
        validate_term(&transaction, conclusion)?;
        let context = intern_context(&transaction, &transformed_members)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion,
            origin: Some(TheoremOrigin::TermInstantiation),
            brand: PhantomData,
        })
    }

    /// Simultaneously instantiates exact free type variables throughout a theorem.
    ///
    /// Replacements are copied unchanged, so the substitution is simultaneous rather
    /// than recursively composed. Both the conclusion and every assumption are rebuilt.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies any required insertion/context operation, a
    /// key is not an exact `TFV`, a key is duplicated, or any source graph is invalid.
    pub fn instantiate_types(
        &mut self,
        theorem: &Theorem<'brand>,
        instantiations: &[TypeInstantiation],
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveTypeInstantiation)?;
        authorize_proof(&mut hol.policy, Operation::InsertType)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        authorize_context(&mut hol.policy, Operation::DefineContext)?;

        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, theorem.context)?;
        let members = read_context_members(&transaction, theorem.context)?;
        validate_term(&transaction, theorem.conclusion)?;
        for member in &members {
            validate_term(&transaction, *member)?;
        }

        let mut replacements = HashMap::with_capacity(instantiations.len());
        for instantiation in instantiations {
            validate_type(&transaction, instantiation.variable).map_err(TermError::Type)?;
            if !matches!(
                read_type(&transaction, instantiation.variable).map_err(TermError::Type)?,
                TypeView::Free { .. }
            ) {
                return Err(ProofError::TypeInstantiationKeyNotFree(
                    instantiation.variable,
                ));
            }
            let replacement =
                validate_type(&transaction, instantiation.replacement).map_err(TermError::Type)?;
            if !replacement.boundary.is_empty() {
                return Err(ProofError::OpenTypeInstantiationReplacement(
                    instantiation.replacement,
                ));
            }
            if replacements
                .insert(instantiation.variable, instantiation.replacement)
                .is_some()
            {
                return Err(ProofError::DuplicateTypeInstantiation(
                    instantiation.variable,
                ));
            }
        }

        let mut type_memo = HashMap::new();
        let mut term_memo = HashMap::new();
        let conclusion = instantiate_term_types_inner(
            &transaction,
            theorem.conclusion,
            &replacements,
            &mut type_memo,
            &mut term_memo,
        )?;
        let mut transformed_members = members
            .into_iter()
            .map(|member| {
                instantiate_term_types_inner(
                    &transaction,
                    member,
                    &replacements,
                    &mut type_memo,
                    &mut term_memo,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        transformed_members.sort_unstable();
        transformed_members.dedup();
        validate_term(&transaction, conclusion)?;
        let context = intern_context(&transaction, &transformed_members)?;
        transaction.commit()?;
        Ok(Theorem {
            context,
            conclusion,
            origin: Some(TheoremOrigin::TypeInstantiation),
            brand: PhantomData,
        })
    }

    /// Applies the standard HOL abstraction rule to one exact free-variable node.
    ///
    /// From `Γ ⊢ left = right`, this derives `Γ ⊢ (λx. left) = (λx. right)`
    /// when the exact `MFV` node `variable` does not occur in any assumption in
    /// `Γ`. Occurrences under existing lambdas are replaced by the corresponding
    /// typed de Bruijn index; existing bound variables are left unchanged.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule or required syntax insertion,
    /// the premise is not a closed equality, `variable` is not an exact `MFV`
    /// node, it occurs in an assumption, or checked atomic interning fails.
    pub fn abstraction(
        &mut self,
        theorem: &Theorem<'brand>,
        variable: TermId,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveAbstraction)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        authorize_proof(&mut hol.policy, Operation::InsertType)?;

        let transaction = neutron.sqlite().unchecked_transaction()?;
        let variable_validation = validate_term(&transaction, variable)?;
        if !matches!(variable_validation.view, TermView::Free { .. }) {
            return Err(ProofError::AbstractionKeyNotFree(variable));
        }
        let conclusion_validation = validate_term(&transaction, theorem.conclusion)?;
        if !conclusion_validation.is_closed() {
            return Err(ProofError::OpenConclusion(theorem.conclusion));
        }
        let TermView::Equality { left, right } = conclusion_validation.view else {
            return Err(ProofError::ExpectedEquality(theorem.conclusion));
        };
        require_context(&transaction, theorem.context)?;
        for assumption in read_context_members(&transaction, theorem.context)? {
            validate_term(&transaction, assumption)?;
            if term_contains_exact(&transaction, assumption, variable, &mut HashMap::new())? {
                return Err(ProofError::AbstractionVariableFreeInAssumption {
                    variable,
                    assumption,
                });
            }
        }

        let mut memo = HashMap::new();
        let left = abstract_free_term_inner(
            &transaction,
            left,
            variable,
            variable_validation.ty,
            0,
            &mut memo,
        )?;
        let right = abstract_free_term_inner(
            &transaction,
            right,
            variable,
            variable_validation.ty,
            0,
            &mut memo,
        )?;
        let endpoint_type = validate_term(&transaction, left)?.ty;
        let function_type = intern_type_arrow(&transaction, variable_validation.ty, endpoint_type)
            .map_err(TermError::Type)?;
        let left = intern_lambda(&transaction, variable_validation.ty, left, function_type)?;
        let right = intern_lambda(&transaction, variable_validation.ty, right, function_type)?;
        let conclusion = intern_equality(&transaction, left, right)?;
        validate_term(&transaction, conclusion)?;
        transaction.commit()?;
        Ok(Theorem {
            context: theorem.context,
            conclusion,
            origin: Some(TheoremOrigin::Abstraction),
            brand: PhantomData,
        })
    }

    /// Applies Hilbert choice to one proved predicate application.
    ///
    /// From an exact premise `Γ ⊢ predicate witness`, this derives
    /// `Γ ⊢ predicate (ε predicate)`. The predicate and witness are
    /// inferred from the premise's canonical application node, avoiding any
    /// redundant caller-supplied coordinates.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule/insertion, the premise is
    /// invalid, open, non-Boolean, not an application, or atomic interning
    /// fails.
    pub fn choice(&mut self, premise: &Theorem<'brand>) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveChoice)?;
        authorize_proof(&mut hol.policy, Operation::InsertTerm)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_context(&transaction, premise.context)?;
        let conclusion = validate_term(&transaction, premise.conclusion)?;
        if conclusion.ty != BOOL_TYPE_ID {
            return Err(ProofError::NonBooleanConclusion {
                term: premise.conclusion,
                ty: conclusion.ty,
            });
        }
        if !conclusion.is_closed() {
            return Err(ProofError::OpenConclusion(premise.conclusion));
        }
        let TermView::Application {
            function: predicate,
            argument: _,
        } = conclusion.view
        else {
            return Err(ProofError::ChoicePremiseNotApplication(premise.conclusion));
        };
        let predicate_validation = validate_term(&transaction, predicate)?;
        let TypeView::Arrow { domain, codomain } =
            read_type(&transaction, predicate_validation.ty).map_err(TermError::Type)?
        else {
            return Err(TermError::NotFunction(predicate_validation.ty).into());
        };
        if codomain != BOOL_TYPE_ID {
            return Err(TermError::EpsilonPredicateNonBoolean {
                predicate,
                codomain,
            }
            .into());
        }
        let epsilon = intern_epsilon(&transaction, predicate, domain)?;
        let conclusion = intern_application(&transaction, predicate, epsilon, BOOL_TYPE_ID)?;
        validate_term(&transaction, conclusion)?;
        transaction.commit()?;
        Ok(Theorem {
            context: premise.context,
            conclusion,
            origin: Some(TheoremOrigin::Choice),
            brand: PhantomData,
        })
    }

    /// Applies equality modus ponens: `Γ ⊢ p = q` and `Γ ⊢ p` yield `Γ ⊢ q`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the rule, the premises have different
    /// contexts, the first conclusion is not equality, its left side is not
    /// the premise conclusion, or its stored term graph is invalid.
    pub fn equality_modus_ponens(
        &mut self,
        equality: &Theorem<'brand>,
        premise: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let (neutron, hol) = self.connection.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ProveEqualityModusPonens)?;
        if equality.context != premise.context {
            return Err(ProofError::MismatchedTheoremContexts {
                expected: equality.context,
                actual: premise.context,
            });
        }
        let (view, _) = read_term(neutron.sqlite(), equality.conclusion)?;
        let TermView::Equality { left, right } = view else {
            return Err(ProofError::ExpectedEquality(equality.conclusion));
        };
        if premise.conclusion != left {
            return Err(ProofError::EqualityPremiseMismatch {
                expected: left,
                actual: premise.conclusion,
            });
        }
        Ok(Theorem {
            context: equality.context,
            conclusion: right,
            origin: Some(TheoremOrigin::EqualityModusPonens),
            brand: PhantomData,
        })
    }
}

impl<P: Policy> Connection<Hol<P>> {
    /// Returns every direct authoritative implication edge in key order.
    ///
    /// This ordinary read API is intended for untrusted candidate generators;
    /// the returned IDs are not proof capabilities.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read or `SQLite` rejects it.
    pub fn context_implication_edges(&mut self) -> Result<Vec<(ContextId, ContextId)>, ProofError> {
        let (neutron, hol) = self.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadContextImplication)?;
        let mut statement = neutron.sqlite().prepare(
            "SELECT antecedent_ctx_id, consequent_ctx_id
             FROM hol_context_implication
             ORDER BY antecedent_ctx_id, consequent_ctx_id",
        )?;
        statement
            .query_map([], |row| {
                Ok((ContextId(row.get(0)?), ContextId(row.get(1)?)))
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(Into::into)
    }

    /// Reports whether one exact context implication has been proved locally.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, either context is unknown,
    /// or `SQLite` rejects the exact lookup.
    pub fn proved_context_implication(
        &mut self,
        antecedent: ContextId,
        consequent: ContextId,
    ) -> Result<bool, ProofError> {
        let (neutron, hol) = self.parts_mut();
        authorize_proof(&mut hol.policy, Operation::ReadContextImplication)?;
        require_context(neutron.sqlite(), antecedent)?;
        require_context(neutron.sqlite(), consequent)?;
        neutron
            .sqlite()
            .query_row(
                "SELECT EXISTS(
                     SELECT 1 FROM hol_context_implication
                     WHERE antecedent_ctx_id = ?1 AND consequent_ctx_id = ?2
                 )",
                [antecedent.0, consequent.0],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

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
        if !validation.is_closed() {
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
        read_target_metadata(neutron.sqlite(), &hol.schema, id.into(), columns)
            .map_err(|error| kind_metadata_error(id, error))
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
        write_target_metadata(&transaction, &hol.schema, target, metadata)?;
        transaction.commit()?;
        Ok(())
    }
}

pub(super) fn write_target_metadata(
    connection: &sqlite::Connection,
    schema: &HolSchema,
    target: MetadataTarget,
    metadata: &[(&str, MetadataValue)],
) -> Result<(), MetadataError> {
    require_metadata_target(connection, target)?;
    if metadata.is_empty() {
        return Ok(());
    }
    let key = metadata_target_key(target);
    let binding = metadata_binding(key.table);
    let mut seen = HashSet::new();
    let mut assignments = Vec::with_capacity(metadata.len());
    let mut values = Vec::with_capacity(metadata.len() + 2);
    for (name, value) in metadata {
        let column = schema
            .column_on(key.table, name)
            .ok_or_else(|| MetadataError::UnknownColumn((*name).to_owned()))?;
        if !seen.insert(column.name.to_ascii_lowercase()) {
            return Err(MetadataError::DuplicateColumn((*name).to_owned()));
        }
        assignments.push(format!("{} = ?", quote_identifier(&column.name)));
        values.push(sqlite::types::Value::from(value.clone()));
    }
    let predicate = key.predicate(values.len() + 1);
    values.extend(
        key.values
            .iter()
            .copied()
            .map(sqlite::types::Value::Integer),
    );
    connection.execute(
        &format!(
            "UPDATE {} SET {} WHERE {predicate}",
            binding.table,
            assignments.join(", ")
        ),
        sqlite::params_from_iter(values.iter()),
    )?;
    Ok(())
}

fn authorize_metadata(policy: &mut impl Policy, operation: Operation) -> Result<(), MetadataError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(MetadataError::Denied(operation))
    }
}

struct MetadataTargetKey {
    table: MetadataTable,
    columns: &'static [&'static str],
    values: Vec<i64>,
}

impl MetadataTargetKey {
    fn predicate(&self, first_parameter: usize) -> String {
        self.columns
            .iter()
            .enumerate()
            .map(|(offset, column)| format!("{column} = ?{}", first_parameter + offset))
            .collect::<Vec<_>>()
            .join(" AND ")
    }
}

fn metadata_target_key(target: MetadataTarget) -> MetadataTargetKey {
    let (table, columns, values) = match target {
        MetadataTarget::Node(id) => (MetadataTable::Node, &["node_id"][..], vec![id]),
        MetadataTarget::Context(context) => {
            (MetadataTable::Context, &["ctx_id"][..], vec![context.get()])
        }
        MetadataTarget::ContextMember { context, term }
        | MetadataTarget::Judgement { context, term } => {
            let table = if matches!(target, MetadataTarget::ContextMember { .. }) {
                MetadataTable::ContextMember
            } else {
                MetadataTable::Judgement
            };
            (
                table,
                &["ctx_id", "term_id"][..],
                vec![context.get(), term.get()],
            )
        }
        MetadataTarget::ContextImplication {
            antecedent,
            consequent,
        } => (
            MetadataTable::ContextImplication,
            &["antecedent_ctx_id", "consequent_ctx_id"][..],
            vec![antecedent.get(), consequent.get()],
        ),
        MetadataTarget::ContextUnion { left, right } => (
            MetadataTable::ContextUnion,
            &["left_ctx_id", "right_ctx_id"][..],
            vec![left.get(), right.get()],
        ),
        MetadataTarget::Namespace(namespace) => (
            MetadataTable::Namespace,
            &["namespace_id"][..],
            vec![namespace.get()],
        ),
        MetadataTarget::NamespaceExport { namespace, export } => (
            MetadataTable::NamespaceExport,
            &["namespace_id", "export_id"][..],
            vec![namespace.get(), export.get()],
        ),
        MetadataTarget::Import(import) => (
            MetadataTable::Import,
            &["import_id"][..],
            vec![import.get()],
        ),
        MetadataTarget::TrustedImport(trusted_import) => (
            MetadataTable::TrustedImport,
            &["trusted_import_id"][..],
            vec![trusted_import.get()],
        ),
    };
    MetadataTargetKey {
        table,
        columns,
        values,
    }
}

fn require_metadata_target(
    connection: &sqlite::Connection,
    target: MetadataTarget,
) -> Result<(), MetadataError> {
    let key = metadata_target_key(target);
    let predicate = key.predicate(1);
    let exists = connection.query_row(
        &format!(
            "SELECT EXISTS(SELECT 1 FROM {} WHERE {predicate})",
            metadata_binding(key.table).table
        ),
        sqlite::params_from_iter(key.values.iter()),
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
    let key = metadata_target_key(target);
    let binding = metadata_binding(key.table);
    let columns = columns
        .iter()
        .map(|name| {
            schema
                .column_on(key.table, name)
                .map(|column| quote_identifier(&column.name))
                .ok_or_else(|| MetadataError::UnknownColumn((*name).to_owned()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let predicate = key.predicate(1);
    connection
        .query_row(
            &format!(
                "SELECT {} FROM {} WHERE {predicate}",
                columns.join(", "),
                binding.table
            ),
            sqlite::params_from_iter(key.values.iter()),
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
        let binding = metadata_binding(column.table);
        connection.execute_batch(&format!(
            "ALTER TABLE {} ADD COLUMN {} {}",
            binding.table,
            quote_identifier(&column.name),
            column.storage.sql()
        ))?;
    }
    for index in &schema.indexes {
        let binding = metadata_binding(index.table);
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
            binding.table,
        ))?;
    }
    Ok(())
}

fn kind_metadata_error(id: KindId, error: MetadataError) -> KindError {
    match error {
        MetadataError::Denied(operation) => KindError::Denied(operation),
        MetadataError::UnknownTarget(_) => KindError::UnknownKind(id),
        MetadataError::UnknownColumn(name) => KindError::UnknownMetadataColumn(name),
        MetadataError::DuplicateColumn(name) => KindError::DuplicateMetadataColumn(name),
        MetadataError::Sqlite(error) => KindError::Sqlite(error),
    }
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

fn check_context_union_members(
    connection: &sqlite::Connection,
    left: ContextId,
    right: ContextId,
    result: ContextId,
) -> Result<(), ProofError> {
    let mut expected = read_context_members(connection, left)?;
    expected.extend(read_context_members(connection, right)?);
    expected.sort_unstable();
    expected.dedup();
    let actual = read_context_members(connection, result)?;
    if let Some(term) = expected
        .iter()
        .find(|term| actual.binary_search(term).is_err())
    {
        return Err(ProofError::ContextUnionMissingMember {
            left,
            right,
            result,
            term: *term,
        });
    }
    if let Some(term) = actual
        .iter()
        .find(|term| expected.binary_search(term).is_err())
    {
        return Err(ProofError::ContextUnionUnexpectedMember {
            left,
            right,
            result,
            term: *term,
        });
    }
    Ok(())
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

fn intern_context(
    connection: &sqlite::Connection,
    members: &[TermId],
) -> Result<ContextId, ContextError> {
    for member in members {
        let validation = validate_term(connection, *member)?;
        if validation.ty != BOOL_TYPE_ID {
            return Err(ContextError::NonBooleanMember {
                term: *member,
                ty: validation.ty,
            });
        }
        if !validation.is_closed() {
            return Err(ContextError::OpenMember(*member));
        }
    }
    if let Some(context) = find_context(connection, members)? {
        return Ok(context);
    }
    connection.execute("INSERT INTO hol_context DEFAULT VALUES", [])?;
    let context = ContextId(connection.last_insert_rowid());
    for member in members {
        connection.execute(
            "INSERT INTO hol_context_member(ctx_id, term_id) VALUES (?1, ?2)",
            [context.0, member.0],
        )?;
    }
    Ok(context)
}

fn persist_judgement(
    connection: &sqlite::Connection,
    context: ContextId,
    term: TermId,
    rule: Option<&str>,
) -> Result<(), sqlite::Error> {
    connection.execute(
        "INSERT OR IGNORE INTO hol_judgement(ctx_id, term_id) VALUES (?1, ?2)",
        (context.0, term.0),
    )?;
    if let Some(rule) = rule {
        connection.execute(
            "INSERT INTO hol_proof_event(ctx_id, term_id, rule) VALUES (?1, ?2, ?3)",
            (context.0, term.0, rule),
        )?;
    }
    Ok(())
}

fn persist_context_implication(
    connection: &sqlite::Connection,
    antecedent: ContextId,
    consequent: ContextId,
    rule: Option<&str>,
) -> Result<(), sqlite::Error> {
    connection.execute(
        "INSERT OR IGNORE INTO hol_context_implication(
             antecedent_ctx_id, consequent_ctx_id
         ) VALUES (?1, ?2)",
        (antecedent.0, consequent.0),
    )?;
    if let Some(rule) = rule {
        connection.execute(
            "INSERT INTO hol_context_implication_event(
                 antecedent_ctx_id, consequent_ctx_id, rule
             ) VALUES (?1, ?2, ?3)",
            (antecedent.0, consequent.0, rule),
        )?;
    }
    Ok(())
}

fn persist_context_union(
    connection: &sqlite::Connection,
    left: ContextId,
    right: ContextId,
    result: ContextId,
) -> Result<(), sqlite::Error> {
    connection.execute(
        "INSERT OR IGNORE INTO hol_context_exact_union(
             left_ctx_id, right_ctx_id, result_ctx_id
         ) VALUES (?1, ?2, ?3)",
        (left.0, right.0, result.0),
    )?;
    connection.execute(
        "INSERT INTO hol_context_exact_union_event(
             left_ctx_id, right_ctx_id, result_ctx_id, rule
         ) VALUES (?1, ?2, ?3, 'exact-membership')",
        (left.0, right.0, result.0),
    )?;
    Ok(())
}

fn intern_base_type(connection: &sqlite::Connection, symbol: i64) -> Result<TypeId, TypeError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'TBASE' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [symbol, STAR_ID.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TypeId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('TBASE', ?1, ?2)",
        [symbol, STAR_ID.0],
    )?;
    Ok(TypeId(connection.last_insert_rowid()))
}

fn intern_free_type(connection: &sqlite::Connection, symbol: i64) -> Result<TypeId, TypeError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'TFV' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [symbol, STAR_ID.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TypeId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('TFV', ?1, ?2)",
        [symbol, STAR_ID.0],
    )?;
    Ok(TypeId(connection.last_insert_rowid()))
}

fn intern_bound_type(connection: &sqlite::Connection, index: u32) -> Result<TypeId, TypeError> {
    let index = i64::from(index);
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'TBV' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [index, STAR_ID.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TypeId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('TBV', ?1, ?2)",
        [index, STAR_ID.0],
    )?;
    Ok(TypeId(connection.last_insert_rowid()))
}

fn intern_forall_type(connection: &sqlite::Connection, body: TypeId) -> Result<TypeId, TypeError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'TALL' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [body.0, STAR_ID.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TypeId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('TALL', ?1, ?2)",
        [body.0, STAR_ID.0],
    )?;
    Ok(TypeId(connection.last_insert_rowid()))
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
        (tag, Some(symbol), None, Some(kind)) if tag == "TBASE" && kind == STAR_ID.0 => {
            Ok(TypeView::Base { symbol })
        }
        (tag, Some(symbol), None, Some(kind)) if tag == "TFV" && kind == STAR_ID.0 => {
            Ok(TypeView::Free { symbol })
        }
        (tag, Some(index), None, Some(kind))
            if tag == "TBV" && kind == STAR_ID.0 && (0..=i64::from(u32::MAX)).contains(&index) =>
        {
            Ok(TypeView::Bound {
                index: u32::try_from(index).map_err(|_| TypeError::CorruptType(id))?,
            })
        }
        (tag, Some(body), None, Some(kind)) if tag == "TALL" && kind == STAR_ID.0 => {
            Ok(TypeView::Forall { body: TypeId(body) })
        }
        (tag, Some(domain), Some(codomain), Some(kind)) if tag == "TARR" && kind == STAR_ID.0 => {
            Ok(TypeView::Arrow {
                domain: TypeId(domain),
                codomain: TypeId(codomain),
            })
        }
        _ => Err(TypeError::CorruptType(id)),
    }
}

#[derive(Clone)]
struct ValidatedType {
    view: TypeView,
    boundary: BTreeMap<u32, KindId>,
}

fn validate_type(
    connection: &sqlite::Connection,
    root: TypeId,
) -> Result<ValidatedType, TypeError> {
    fn walk(
        connection: &sqlite::Connection,
        id: TypeId,
        active: &mut HashSet<TypeId>,
        memo: &mut HashMap<TypeId, ValidatedType>,
    ) -> Result<ValidatedType, TypeError> {
        if let Some(validated) = memo.get(&id) {
            return Ok(validated.clone());
        }
        if !active.insert(id) {
            return Err(TypeError::CorruptType(id));
        }
        let view = read_type(connection, id)?;
        let boundary = match view {
            TypeView::Bound { index } => BTreeMap::from([(index, STAR_ID)]),
            TypeView::Forall { body } => {
                close_type_boundary(walk(connection, body, active, memo)?.boundary)
            }
            TypeView::Arrow { domain, codomain } => merge_type_boundaries(
                walk(connection, domain, active, memo)?.boundary,
                walk(connection, codomain, active, memo)?.boundary,
            )?,
            TypeView::Bool | TypeView::Base { .. } | TypeView::Free { .. } => BTreeMap::new(),
        };
        active.remove(&id);
        let validated = ValidatedType { view, boundary };
        memo.insert(id, validated.clone());
        Ok(validated)
    }
    walk(connection, root, &mut HashSet::new(), &mut HashMap::new())
}

fn merge_type_boundaries(
    mut left: BTreeMap<u32, KindId>,
    right: BTreeMap<u32, KindId>,
) -> Result<BTreeMap<u32, KindId>, TypeError> {
    for (index, kind) in right {
        if let Some(first) = left.insert(index, kind)
            && first != kind
        {
            return Err(TypeError::InconsistentUnboundVariable {
                index,
                first,
                second: kind,
            });
        }
    }
    Ok(left)
}

fn close_type_boundary(mut boundary: BTreeMap<u32, KindId>) -> BTreeMap<u32, KindId> {
    boundary.remove(&0);
    boundary
        .into_iter()
        .map(|(index, kind)| (index - 1, kind))
        .collect()
}

fn shift_bound_type(
    connection: &sqlite::Connection,
    ty: TypeId,
    amount: u32,
    cutoff: u32,
    memo: &mut HashMap<(TypeId, u32, u32), TypeId>,
) -> Result<TypeId, TypeError> {
    if amount == 0 {
        return Ok(ty);
    }
    if let Some(result) = memo.get(&(ty, amount, cutoff)) {
        return Ok(*result);
    }
    let result = match read_type(connection, ty)? {
        TypeView::Bound { index } if index >= cutoff => intern_bound_type(
            connection,
            index
                .checked_add(amount)
                .ok_or(TypeError::SubstitutionDepthOverflow)?,
        )?,
        TypeView::Bool | TypeView::Base { .. } | TypeView::Free { .. } | TypeView::Bound { .. } => {
            ty
        }
        TypeView::Arrow { domain, codomain } => {
            let domain = shift_bound_type(connection, domain, amount, cutoff, memo)?;
            let codomain = shift_bound_type(connection, codomain, amount, cutoff, memo)?;
            intern_type_arrow(connection, domain, codomain)?
        }
        TypeView::Forall { body } => {
            let body = shift_bound_type(
                connection,
                body,
                amount,
                cutoff
                    .checked_add(1)
                    .ok_or(TypeError::SubstitutionDepthOverflow)?,
                memo,
            )?;
            intern_forall_type(connection, body)?
        }
    };
    memo.insert((ty, amount, cutoff), result);
    Ok(result)
}

fn substitute_bound_type(
    connection: &sqlite::Connection,
    body: TypeId,
    replacement: TypeId,
) -> Result<TypeId, TypeError> {
    fn walk(
        connection: &sqlite::Connection,
        ty: TypeId,
        replacement: TypeId,
        depth: u32,
        memo: &mut HashMap<(TypeId, u32), TypeId>,
        shift_memo: &mut HashMap<(TypeId, u32, u32), TypeId>,
    ) -> Result<TypeId, TypeError> {
        if let Some(result) = memo.get(&(ty, depth)) {
            return Ok(*result);
        }
        let result = match read_type(connection, ty)? {
            TypeView::Bound { index } if index == depth => {
                shift_bound_type(connection, replacement, depth, 0, shift_memo)?
            }
            TypeView::Bound { index } if index > depth => intern_bound_type(connection, index - 1)?,
            TypeView::Bool
            | TypeView::Base { .. }
            | TypeView::Free { .. }
            | TypeView::Bound { .. } => ty,
            TypeView::Arrow { domain, codomain } => {
                let domain = walk(connection, domain, replacement, depth, memo, shift_memo)?;
                let codomain = walk(connection, codomain, replacement, depth, memo, shift_memo)?;
                intern_type_arrow(connection, domain, codomain)?
            }
            TypeView::Forall { body } => {
                let body = walk(
                    connection,
                    body,
                    replacement,
                    depth
                        .checked_add(1)
                        .ok_or(TypeError::SubstitutionDepthOverflow)?,
                    memo,
                    shift_memo,
                )?;
                intern_forall_type(connection, body)?
            }
        };
        memo.insert((ty, depth), result);
        Ok(result)
    }

    validate_type(connection, body)?;
    validate_type(connection, replacement)?;
    let result = walk(
        connection,
        body,
        replacement,
        0,
        &mut HashMap::new(),
        &mut HashMap::new(),
    )?;
    validate_type(connection, result)?;
    Ok(result)
}

fn collect_type_free_variables(
    connection: &sqlite::Connection,
    root: TypeId,
) -> Result<Vec<TypeId>, TypeError> {
    fn walk(
        connection: &sqlite::Connection,
        id: TypeId,
        active: &mut HashSet<TypeId>,
        complete: &mut HashSet<TypeId>,
        variables: &mut HashSet<TypeId>,
    ) -> Result<(), TypeError> {
        if complete.contains(&id) {
            return Ok(());
        }
        if !active.insert(id) {
            return Err(TypeError::CorruptType(id));
        }
        match read_type(connection, id)? {
            TypeView::Free { .. } => {
                variables.insert(id);
            }
            TypeView::Arrow { domain, codomain } => {
                walk(connection, domain, active, complete, variables)?;
                walk(connection, codomain, active, complete, variables)?;
            }
            TypeView::Forall { body } => {
                walk(connection, body, active, complete, variables)?;
            }
            TypeView::Bool | TypeView::Base { .. } | TypeView::Bound { .. } => {}
        }
        active.remove(&id);
        complete.insert(id);
        Ok(())
    }
    let mut variables = HashSet::new();
    walk(
        connection,
        root,
        &mut HashSet::new(),
        &mut HashSet::new(),
        &mut variables,
    )?;
    let mut variables = variables.into_iter().collect::<Vec<_>>();
    variables.sort_unstable();
    Ok(variables)
}

fn type_contains_free_variable(
    connection: &sqlite::Connection,
    root: TypeId,
) -> Result<bool, TypeError> {
    Ok(!collect_type_free_variables(connection, root)?.is_empty())
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

fn intern_constant(
    connection: &sqlite::Connection,
    symbol: i64,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some((id, existing)) = connection
        .query_row(
            "SELECT node_id, ty FROM hol_node
             WHERE tag = 'MCONST' AND lhs = ?1 AND rhs IS NULL",
            [symbol],
            |row| Ok((row.get::<_, i64>(0)?, TypeId(row.get::<_, i64>(1)?))),
        )
        .optional()?
    {
        if existing != ty {
            return Err(TermError::ConstantTypeConflict {
                symbol,
                existing,
                requested: ty,
            });
        }
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MCONST', ?1, ?2)",
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

fn intern_epsilon(
    connection: &sqlite::Connection,
    predicate: TermId,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MEPS' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [predicate.0, ty.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MEPS', ?1, ?2)",
        [predicate.0, ty.0],
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_type_lambda(
    connection: &sqlite::Connection,
    body: TermId,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MTYLAM' AND lhs = ?1 AND rhs IS NULL AND ty = ?2",
            [body.0, ty.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, ty) VALUES ('MTYLAM', ?1, ?2)",
        [body.0, ty.0],
    )?;
    Ok(TermId(connection.last_insert_rowid()))
}

fn intern_type_application(
    connection: &sqlite::Connection,
    function: TermId,
    argument: TypeId,
    ty: TypeId,
) -> Result<TermId, TermError> {
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'MTYAPP' AND lhs = ?1 AND rhs = ?2 AND ty = ?3",
            (function.0, argument.0, ty.0),
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(TermId(id));
    }
    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs, ty) VALUES ('MTYAPP', ?1, ?2, ?3)",
        (function.0, argument.0, ty.0),
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
        (tag, Some(symbol), None, Some(ty)) if tag == "MCONST" => {
            (TermView::Constant { symbol }, TypeId(ty))
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
        (tag, Some(predicate), None, Some(ty)) if tag == "MEPS" => (
            TermView::Epsilon {
                predicate: TermId(predicate),
            },
            TypeId(ty),
        ),
        (tag, Some(body), None, Some(ty)) if tag == "MTYLAM" => {
            (TermView::TypeLambda { body: TermId(body) }, TypeId(ty))
        }
        (tag, Some(function), Some(argument), Some(ty)) if tag == "MTYAPP" => (
            TermView::TypeApplication {
                function: TermId(function),
                argument: TypeId(argument),
            },
            TypeId(ty),
        ),
        _ => return Err(TermError::CorruptTerm(id)),
    };
    validate_type(connection, ty)?;
    if matches!(term, TermView::Bool(_)) && ty != BOOL_TYPE_ID {
        return Err(TermError::CorruptTerm(id));
    }
    Ok((term, ty))
}

#[derive(Clone)]
struct ValidatedTerm {
    view: TermView,
    ty: TypeId,
    term_boundary: BTreeMap<u32, TypeId>,
    type_boundary: BTreeMap<u32, KindId>,
    has_mfv: bool,
}

impl ValidatedTerm {
    fn is_closed(&self) -> bool {
        self.term_boundary.is_empty() && self.type_boundary.is_empty()
    }
}

fn read_term(connection: &sqlite::Connection, id: TermId) -> Result<(TermView, TypeId), TermError> {
    let validated = validate_term(connection, id)?;
    Ok((validated.view, validated.ty))
}

fn validate_term(connection: &sqlite::Connection, id: TermId) -> Result<ValidatedTerm, TermError> {
    validate_term_inner(connection, id, &mut HashSet::new(), &mut HashMap::new())
}

#[allow(clippy::too_many_lines)]
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
    let own_type_boundary = validate_type(connection, ty)?.boundary;
    let (term_boundary, type_boundary, has_mfv) = match view {
        TermView::Bool(_) => (BTreeMap::new(), own_type_boundary, false),
        TermView::Free { .. } => (BTreeMap::new(), own_type_boundary, true),
        TermView::Constant { symbol } => {
            if type_contains_free_variable(connection, ty)? {
                return Err(TermError::PolymorphicConstantType { symbol, ty });
            }
            if !own_type_boundary.is_empty() {
                return Err(TermError::OpenConstantType { symbol, ty });
            }
            (BTreeMap::new(), BTreeMap::new(), false)
        }
        TermView::Bound { index } => (BTreeMap::from([(index, ty)]), own_type_boundary, false),
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
            let term_boundary =
                merge_term_boundaries(function.term_boundary, argument.term_boundary)?;
            let type_boundary = merge_type_boundaries(
                merge_type_boundaries(function.type_boundary, argument.type_boundary)
                    .map_err(TermError::Type)?,
                own_type_boundary,
            )
            .map_err(TermError::Type)?;
            (
                term_boundary,
                type_boundary,
                function.has_mfv || argument.has_mfv,
            )
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            let parameter_type_boundary = validate_type(connection, parameter_type)?.boundary;
            let body = validate_term_inner(connection, body, active, memo)?;
            match read_type(connection, ty)? {
                TypeView::Arrow { domain, codomain }
                    if domain == parameter_type && codomain == body.ty => {}
                _ => return Err(TermError::CorruptTerm(id)),
            }
            let term_boundary = close_term_boundary(body.term_boundary, parameter_type)?;
            let type_boundary = merge_type_boundaries(
                merge_type_boundaries(body.type_boundary, parameter_type_boundary)
                    .map_err(TermError::Type)?,
                own_type_boundary,
            )
            .map_err(TermError::Type)?;
            (term_boundary, type_boundary, body.has_mfv)
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
            let term_boundary = merge_term_boundaries(left.term_boundary, right.term_boundary)?;
            let type_boundary = merge_type_boundaries(
                merge_type_boundaries(left.type_boundary, right.type_boundary)
                    .map_err(TermError::Type)?,
                own_type_boundary,
            )
            .map_err(TermError::Type)?;
            (term_boundary, type_boundary, left.has_mfv || right.has_mfv)
        }
        TermView::Epsilon { predicate } => {
            let predicate_validation = validate_term_inner(connection, predicate, active, memo)?;
            let TypeView::Arrow { domain, codomain } =
                read_type(connection, predicate_validation.ty)?
            else {
                return Err(TermError::NotFunction(predicate_validation.ty));
            };
            if codomain != BOOL_TYPE_ID {
                return Err(TermError::EpsilonPredicateNonBoolean {
                    predicate,
                    codomain,
                });
            }
            if domain != ty {
                return Err(TermError::CorruptTerm(id));
            }
            let type_boundary =
                merge_type_boundaries(predicate_validation.type_boundary, own_type_boundary)
                    .map_err(TermError::Type)?;
            (
                predicate_validation.term_boundary,
                type_boundary,
                predicate_validation.has_mfv,
            )
        }
        TermView::TypeLambda { body } => {
            let body = validate_term_inner(connection, body, active, memo)?;
            if !body.term_boundary.is_empty() {
                return Err(TermError::TypeLambdaOpenTermBody(id));
            }
            if body.has_mfv {
                return Err(TermError::TypeLambdaFreeTermBody(id));
            }
            let TypeView::Forall {
                body: expected_body,
            } = read_type(connection, ty)?
            else {
                return Err(TermError::CorruptTerm(id));
            };
            if expected_body != body.ty {
                return Err(TermError::CorruptTerm(id));
            }
            let type_boundary =
                merge_type_boundaries(close_type_boundary(body.type_boundary), own_type_boundary)
                    .map_err(TermError::Type)?;
            (BTreeMap::new(), type_boundary, false)
        }
        TermView::TypeApplication { function, argument } => {
            let function = validate_term_inner(connection, function, active, memo)?;
            let argument_boundary = validate_type(connection, argument)?.boundary;
            let TypeView::Forall { body } = read_type(connection, function.ty)? else {
                return Err(TermError::NotUniversal(function.ty));
            };
            let expected = substitute_bound_type(connection, body, argument)?;
            if expected != ty {
                return Err(TermError::CorruptTerm(id));
            }
            let type_boundary = merge_type_boundaries(
                merge_type_boundaries(function.type_boundary, argument_boundary)
                    .map_err(TermError::Type)?,
                own_type_boundary,
            )
            .map_err(TermError::Type)?;
            (function.term_boundary, type_boundary, function.has_mfv)
        }
    };
    active.remove(&id);
    let validated = ValidatedTerm {
        view,
        ty,
        term_boundary,
        type_boundary,
        has_mfv,
    };
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

fn checked_conversion<'brand>(
    connection: &sqlite::Connection,
    left: TermId,
    right: TermId,
) -> Result<Conversion<'brand>, ProofError> {
    let left_validation = validate_term(connection, left)?;
    let right_validation = validate_term(connection, right)?;
    if left_validation.ty != right_validation.ty {
        return Err(TermError::EqualityTypeMismatch {
            left: left_validation.ty,
            right: right_validation.ty,
        }
        .into());
    }
    if left_validation.term_boundary != right_validation.term_boundary
        || left_validation.type_boundary != right_validation.type_boundary
    {
        return Err(ProofError::ConversionBoundaryMismatch { left, right });
    }
    Ok(Conversion {
        left,
        right,
        ty: left_validation.ty,
        term_boundary: left_validation.term_boundary,
        type_boundary: left_validation.type_boundary,
        brand: PhantomData,
    })
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
        TermView::Bool(_)
        | TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::Bound { .. } => term,
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
        TermView::Epsilon { predicate } => {
            let predicate =
                substitute_closed_inner(connection, predicate, replacement, depth, memo)?;
            intern_epsilon(connection, predicate, ty)?
        }
        TermView::TypeLambda { body } => {
            let body = substitute_closed_inner(connection, body, replacement, depth, memo)?;
            intern_type_lambda(connection, body, ty)?
        }
        TermView::TypeApplication { function, argument } => {
            let function = substitute_closed_inner(connection, function, replacement, depth, memo)?;
            intern_type_application(connection, function, argument, ty)?
        }
    };
    memo.insert((term, depth), result);
    Ok(result)
}

fn instantiate_free_terms_inner(
    connection: &sqlite::Connection,
    term: TermId,
    replacements: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, TermError> {
    if let Some(replacement) = replacements.get(&term) {
        return Ok(*replacement);
    }
    if let Some(result) = memo.get(&term) {
        return Ok(*result);
    }
    let (view, ty) = read_term_node(connection, term)?;
    let result = match view {
        TermView::Bool(_)
        | TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::Bound { .. } => term,
        TermView::Application { function, argument } => {
            let function = instantiate_free_terms_inner(connection, function, replacements, memo)?;
            let argument = instantiate_free_terms_inner(connection, argument, replacements, memo)?;
            intern_application(connection, function, argument, ty)?
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            let body = instantiate_free_terms_inner(connection, body, replacements, memo)?;
            intern_lambda(connection, parameter_type, body, ty)?
        }
        TermView::Equality { left, right } => {
            let left = instantiate_free_terms_inner(connection, left, replacements, memo)?;
            let right = instantiate_free_terms_inner(connection, right, replacements, memo)?;
            intern_equality(connection, left, right)?
        }
        TermView::Epsilon { predicate } => {
            let predicate =
                instantiate_free_terms_inner(connection, predicate, replacements, memo)?;
            intern_epsilon(connection, predicate, ty)?
        }
        TermView::TypeLambda { body } => {
            let body = instantiate_free_terms_inner(connection, body, replacements, memo)?;
            intern_type_lambda(connection, body, ty)?
        }
        TermView::TypeApplication { function, argument } => {
            let function = instantiate_free_terms_inner(connection, function, replacements, memo)?;
            intern_type_application(connection, function, argument, ty)?
        }
    };
    memo.insert(term, result);
    Ok(result)
}

fn instantiate_type_inner(
    connection: &sqlite::Connection,
    ty: TypeId,
    replacements: &HashMap<TypeId, TypeId>,
    memo: &mut HashMap<TypeId, TypeId>,
) -> Result<TypeId, TypeError> {
    if let Some(replacement) = replacements.get(&ty) {
        return Ok(*replacement);
    }
    if let Some(result) = memo.get(&ty) {
        return Ok(*result);
    }
    let result = match read_type(connection, ty)? {
        TypeView::Bool | TypeView::Base { .. } | TypeView::Free { .. } | TypeView::Bound { .. } => {
            ty
        }
        TypeView::Arrow { domain, codomain } => {
            let domain = instantiate_type_inner(connection, domain, replacements, memo)?;
            let codomain = instantiate_type_inner(connection, codomain, replacements, memo)?;
            intern_type_arrow(connection, domain, codomain)?
        }
        TypeView::Forall { body } => {
            let body = instantiate_type_inner(connection, body, replacements, memo)?;
            intern_forall_type(connection, body)?
        }
    };
    memo.insert(ty, result);
    Ok(result)
}

fn instantiate_term_types_inner(
    connection: &sqlite::Connection,
    term: TermId,
    replacements: &HashMap<TypeId, TypeId>,
    type_memo: &mut HashMap<TypeId, TypeId>,
    term_memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, TermError> {
    if let Some(result) = term_memo.get(&term) {
        return Ok(*result);
    }
    let (view, ty) = read_term_node(connection, term)?;
    let transformed_type = instantiate_type_inner(connection, ty, replacements, type_memo)?;
    let result = match view {
        TermView::Bool(_) | TermView::Constant { .. } => term,
        TermView::Free { symbol } => intern_free_term(connection, symbol, transformed_type)?,
        TermView::Bound { index } => intern_bound_term(connection, index, transformed_type)?,
        TermView::Application { function, argument } => {
            let function = instantiate_term_types_inner(
                connection,
                function,
                replacements,
                type_memo,
                term_memo,
            )?;
            let argument = instantiate_term_types_inner(
                connection,
                argument,
                replacements,
                type_memo,
                term_memo,
            )?;
            intern_application(connection, function, argument, transformed_type)?
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            let parameter_type =
                instantiate_type_inner(connection, parameter_type, replacements, type_memo)?;
            let body =
                instantiate_term_types_inner(connection, body, replacements, type_memo, term_memo)?;
            intern_lambda(connection, parameter_type, body, transformed_type)?
        }
        TermView::Equality { left, right } => {
            let left =
                instantiate_term_types_inner(connection, left, replacements, type_memo, term_memo)?;
            let right = instantiate_term_types_inner(
                connection,
                right,
                replacements,
                type_memo,
                term_memo,
            )?;
            intern_equality(connection, left, right)?
        }
        TermView::Epsilon { predicate } => {
            let predicate = instantiate_term_types_inner(
                connection,
                predicate,
                replacements,
                type_memo,
                term_memo,
            )?;
            intern_epsilon(connection, predicate, transformed_type)?
        }
        TermView::TypeLambda { body } => {
            let body =
                instantiate_term_types_inner(connection, body, replacements, type_memo, term_memo)?;
            intern_type_lambda(connection, body, transformed_type)?
        }
        TermView::TypeApplication { function, argument } => {
            let function = instantiate_term_types_inner(
                connection,
                function,
                replacements,
                type_memo,
                term_memo,
            )?;
            let argument = instantiate_type_inner(connection, argument, replacements, type_memo)?;
            intern_type_application(connection, function, argument, transformed_type)?
        }
    };
    term_memo.insert(term, result);
    Ok(result)
}

fn term_contains_exact(
    connection: &sqlite::Connection,
    term: TermId,
    needle: TermId,
    memo: &mut HashMap<TermId, bool>,
) -> Result<bool, TermError> {
    if term == needle {
        return Ok(true);
    }
    if let Some(result) = memo.get(&term) {
        return Ok(*result);
    }
    let (view, _) = read_term_node(connection, term)?;
    let result = match view {
        TermView::Bool(_)
        | TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::Bound { .. } => false,
        TermView::Application { function, argument } => {
            term_contains_exact(connection, function, needle, memo)?
                || term_contains_exact(connection, argument, needle, memo)?
        }
        TermView::Lambda { body, .. } | TermView::TypeLambda { body } => {
            term_contains_exact(connection, body, needle, memo)?
        }
        TermView::Equality { left, right } => {
            term_contains_exact(connection, left, needle, memo)?
                || term_contains_exact(connection, right, needle, memo)?
        }
        TermView::Epsilon { predicate } => {
            term_contains_exact(connection, predicate, needle, memo)?
        }
        TermView::TypeApplication { function, .. } => {
            term_contains_exact(connection, function, needle, memo)?
        }
    };
    memo.insert(term, result);
    Ok(result)
}

fn abstract_free_term_inner(
    connection: &sqlite::Connection,
    term: TermId,
    variable: TermId,
    variable_type: TypeId,
    depth: u32,
    memo: &mut HashMap<(TermId, u32), TermId>,
) -> Result<TermId, TermError> {
    if term == variable {
        return intern_bound_term(connection, depth, variable_type);
    }
    if let Some(result) = memo.get(&(term, depth)) {
        return Ok(*result);
    }
    let (view, ty) = read_term_node(connection, term)?;
    let result = match view {
        TermView::Bool(_)
        | TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::Bound { .. } => term,
        TermView::Application { function, argument } => {
            let function = abstract_free_term_inner(
                connection,
                function,
                variable,
                variable_type,
                depth,
                memo,
            )?;
            let argument = abstract_free_term_inner(
                connection,
                argument,
                variable,
                variable_type,
                depth,
                memo,
            )?;
            intern_application(connection, function, argument, ty)?
        }
        TermView::Lambda {
            parameter_type,
            body,
        } => {
            let body = abstract_free_term_inner(
                connection,
                body,
                variable,
                variable_type,
                depth
                    .checked_add(1)
                    .ok_or(TermError::SubstitutionDepthOverflow)?,
                memo,
            )?;
            intern_lambda(connection, parameter_type, body, ty)?
        }
        TermView::Equality { left, right } => {
            let left =
                abstract_free_term_inner(connection, left, variable, variable_type, depth, memo)?;
            let right =
                abstract_free_term_inner(connection, right, variable, variable_type, depth, memo)?;
            intern_equality(connection, left, right)?
        }
        TermView::Epsilon { predicate } => {
            let predicate = abstract_free_term_inner(
                connection,
                predicate,
                variable,
                variable_type,
                depth,
                memo,
            )?;
            intern_epsilon(connection, predicate, ty)?
        }
        TermView::TypeLambda { body } => {
            let body =
                abstract_free_term_inner(connection, body, variable, variable_type, depth, memo)?;
            intern_type_lambda(connection, body, ty)?
        }
        TermView::TypeApplication { function, argument } => {
            let function = abstract_free_term_inner(
                connection,
                function,
                variable,
                variable_type,
                depth,
                memo,
            )?;
            intern_type_application(connection, function, argument, ty)?
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
             UNION ALL
             SELECT node_id, lhs FROM hol_node WHERE tag = 'MEPS'
             UNION ALL
             SELECT node_id, lhs FROM hol_node WHERE tag = 'MTYLAM'
             UNION ALL
             SELECT node_id, lhs FROM hol_node WHERE tag = 'MTYAPP'
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

fn collect_term_free_type_variables(
    connection: &sqlite::Connection,
    root: TermId,
) -> Result<Vec<TypeId>, TermError> {
    validate_term(connection, root)?;
    let mut pending = vec![root];
    let mut seen_terms = HashSet::new();
    let mut variables = HashSet::new();
    while let Some(term) = pending.pop() {
        if !seen_terms.insert(term) {
            continue;
        }
        let (view, ty) = read_term_node(connection, term)?;
        variables.extend(collect_type_free_variables(connection, ty)?);
        match view {
            TermView::Bool(_)
            | TermView::Free { .. }
            | TermView::Constant { .. }
            | TermView::Bound { .. } => {}
            TermView::Application { function, argument } => {
                pending.push(function);
                pending.push(argument);
            }
            TermView::Lambda {
                parameter_type,
                body,
            } => {
                variables.extend(collect_type_free_variables(connection, parameter_type)?);
                pending.push(body);
            }
            TermView::Equality { left, right } => {
                pending.push(left);
                pending.push(right);
            }
            TermView::Epsilon { predicate } => pending.push(predicate),
            TermView::TypeLambda { body } => pending.push(body),
            TermView::TypeApplication { function, argument } => {
                pending.push(function);
                variables.extend(collect_type_free_variables(connection, argument)?);
            }
        }
    }
    let mut variables = variables.into_iter().collect::<Vec<_>>();
    variables.sort_unstable();
    Ok(variables)
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
    /// One external type index has incompatible kind annotations.
    InconsistentUnboundVariable {
        /// External index.
        index: u32,
        /// First observed kind.
        first: KindId,
        /// Conflicting kind.
        second: KindId,
    },
    /// A binder nesting depth exceeds the supported de Bruijn index range.
    SubstitutionDepthOverflow,
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for TypeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownType(id) => write!(formatter, "unknown type {}", id.get()),
            Self::CorruptType(id) => write!(formatter, "type {} is structurally corrupt", id.get()),
            Self::InconsistentUnboundVariable {
                index,
                first,
                second,
            } => write!(
                formatter,
                "unbound type index {index} has incompatible kinds {} and {}",
                first.get(),
                second.get()
            ),
            Self::SubstitutionDepthOverflow => {
                formatter.write_str("type substitution depth overflow")
            }
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for TypeError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            Self::Denied(_)
            | Self::UnknownType(_)
            | Self::CorruptType(_)
            | Self::InconsistentUnboundVariable { .. }
            | Self::SubstitutionDepthOverflow => None,
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
    /// One constant symbol was already declared at another type.
    ConstantTypeConflict {
        /// Connection-local declaration symbol.
        symbol: i64,
        /// Previously declared type.
        existing: TypeId,
        /// Newly requested type.
        requested: TypeId,
    },
    /// A monomorphic constant declaration contains a schematic type variable.
    PolymorphicConstantType {
        /// Connection-local declaration symbol.
        symbol: i64,
        /// Rejected schematic type.
        ty: TypeId,
    },
    /// A constant declaration contains an unbound rank-zero type variable.
    OpenConstantType { symbol: i64, ty: TypeId },
    /// A type abstraction body has an external term de Bruijn environment.
    TypeLambdaOpenTermBody(TermId),
    /// A type abstraction body contains a schematic free term variable.
    TypeLambdaFreeTermBody(TermId),
    /// Type application was requested for a non-universal term.
    NotUniversal(TypeId),
    /// The function position does not have a function type.
    NotFunction(TypeId),
    /// An application's argument type differs from its function domain.
    ApplicationTypeMismatch {
        /// Required argument type.
        expected: TypeId,
        /// Actual argument type.
        actual: TypeId,
    },
    /// Hilbert choice was requested for a predicate with non-Boolean codomain.
    EpsilonPredicateNonBoolean {
        /// Proposed predicate term.
        predicate: TermId,
        /// Its actual result type.
        codomain: TypeId,
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
            Self::ConstantTypeConflict {
                symbol,
                existing,
                requested,
            } => write!(
                formatter,
                "constant symbol {symbol} has type {}, not requested type {}",
                existing.get(),
                requested.get()
            ),
            Self::PolymorphicConstantType { symbol, ty } => write!(
                formatter,
                "constant symbol {symbol} cannot be declared at schematic type {}",
                ty.get()
            ),
            Self::OpenConstantType { symbol, ty } => write!(
                formatter,
                "constant symbol {symbol} cannot be declared at open type {}",
                ty.get()
            ),
            Self::TypeLambdaOpenTermBody(term) => write!(
                formatter,
                "type abstraction body {} has an external term environment",
                term.get()
            ),
            Self::TypeLambdaFreeTermBody(term) => write!(
                formatter,
                "type abstraction body {} contains a schematic free term variable",
                term.get()
            ),
            Self::NotUniversal(ty) => write!(formatter, "type {} is not universal", ty.get()),
            Self::NotFunction(ty) => write!(formatter, "type {} is not a function type", ty.get()),
            Self::ApplicationTypeMismatch { expected, actual } => write!(
                formatter,
                "application expected type {}, got {}",
                expected.get(),
                actual.get()
            ),
            Self::EpsilonPredicateNonBoolean {
                predicate,
                codomain,
            } => write!(
                formatter,
                "epsilon predicate {} has non-Boolean codomain {}",
                predicate.get(),
                codomain.get()
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
            | Self::ConstantTypeConflict { .. }
            | Self::PolymorphicConstantType { .. }
            | Self::OpenConstantType { .. }
            | Self::TypeLambdaOpenTermBody(_)
            | Self::TypeLambdaFreeTermBody(_)
            | Self::NotUniversal(_)
            | Self::NotFunction(_)
            | Self::ApplicationTypeMismatch { .. }
            | Self::EpsilonPredicateNonBoolean { .. }
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
    /// An implication witness was proved under the wrong context.
    WrongImplicationWitnessContext {
        /// Required witness context.
        expected: ContextId,
        /// Actual witness context.
        actual: ContextId,
        /// Witness conclusion.
        conclusion: TermId,
    },
    /// A consequent member has no theorem witness.
    MissingImplicationWitness {
        /// Context whose members must be covered.
        consequent: ContextId,
        /// Missing member.
        term: TermId,
    },
    /// A witness conclusion is not a consequent member.
    UnexpectedImplicationWitness {
        /// Context whose members must be covered.
        consequent: ContextId,
        /// Unexpected conclusion.
        term: TermId,
    },
    /// The same witness conclusion occurs more than once.
    DuplicateImplicationWitness(TermId),
    /// An implication path contains no context.
    EmptyImplicationPath,
    /// One adjacent edge in an explicit implication path is absent.
    MissingContextImplicationEdge {
        antecedent: ContextId,
        consequent: ContextId,
    },
    /// The proposed exact-union result omits an input member.
    ContextUnionMissingMember {
        left: ContextId,
        right: ContextId,
        result: ContextId,
        term: TermId,
    },
    /// The proposed exact-union result contains a non-input member.
    ContextUnionUnexpectedMember {
        left: ContextId,
        right: ContextId,
        result: ContextId,
        term: TermId,
    },
    /// One ordered input pair was already recorded with another result.
    ContextUnionConflict {
        left: ContextId,
        right: ContextId,
        stored_result: ContextId,
        requested_result: ContextId,
    },
    /// Two implication witnesses do not have exactly reversed endpoints.
    ContextEquivalenceMismatch {
        forward_antecedent: ContextId,
        forward_consequent: ContextId,
        backward_antecedent: ContextId,
        backward_consequent: ContextId,
    },
    /// Weakening was given a theorem under the wrong context.
    WeakeningContextMismatch {
        /// Implication consequent required by the rule.
        expected: ContextId,
        /// Actual theorem context.
        actual: ContextId,
    },
    /// Two theorem premises were derived under different contexts.
    MismatchedTheoremContexts {
        expected: ContextId,
        actual: ContextId,
    },
    /// Equality substitution received premises from different contexts.
    EqualitySubstitutionContextMismatch {
        equality: ContextId,
        premise: ContextId,
    },
    /// Equality modus ponens received a non-equality first conclusion.
    ExpectedEquality(TermId),
    /// Equality modus ponens' premise does not match the equality's left side.
    EqualityPremiseMismatch { expected: TermId, actual: TermId },
    /// Equality substitution's predicate is not locally closed.
    OpenEqualityPredicate(TermId),
    /// Equality substitution's predicate does not have a function type.
    EqualityPredicateNotFunction { predicate: TermId, ty: TypeId },
    /// Equality substitution's predicate has the wrong domain.
    EqualityPredicateDomainMismatch {
        predicate: TermId,
        expected: TypeId,
        actual: TypeId,
    },
    /// Equality substitution's predicate does not return Boolean propositions.
    EqualityPredicateNonBoolean { predicate: TermId, codomain: TypeId },
    /// Equality substitution's premise is not the exact expected application.
    EqualitySubstitutionPremiseMismatch {
        predicate: TermId,
        argument: TermId,
        actual: TermId,
    },
    /// A theorem-instantiation key is not an exact `MFV` node.
    InstantiationKeyNotFree(TermId),
    /// The same exact free-variable key occurs more than once.
    DuplicateTermInstantiation(TermId),
    /// A theorem-instantiation replacement has a different type from its key.
    TermInstantiationTypeMismatch {
        variable: TermId,
        replacement: TermId,
        expected: TypeId,
        actual: TypeId,
    },
    /// A theorem-instantiation replacement is not locally closed.
    OpenTermInstantiationReplacement(TermId),
    /// A theorem type-instantiation key is not an exact `TFV` node.
    TypeInstantiationKeyNotFree(TypeId),
    /// The same exact free-type-variable key occurs more than once.
    DuplicateTypeInstantiation(TypeId),
    /// A theorem type-instantiation replacement is not locally closed.
    OpenTypeInstantiationReplacement(TypeId),
    /// The abstraction key is not an exact `MFV` node.
    AbstractionKeyNotFree(TermId),
    /// The abstraction key occurs in one undischarged assumption.
    AbstractionVariableFreeInAssumption {
        variable: TermId,
        assumption: TermId,
    },
    /// Hilbert choice requires a premise whose conclusion is an application.
    ChoicePremiseNotApplication(TermId),
    /// Two conversions cannot compose because their middle terms differ.
    ConversionChainMismatch {
        first_right: TermId,
        second_left: TermId,
    },
    /// Constructed conversion endpoints do not have one common open boundary.
    ConversionBoundaryMismatch { left: TermId, right: TermId },
    /// Boolean theorem conversion was requested at a non-Boolean type.
    NonBooleanConversion { term: TermId, ty: TypeId },
    /// The theorem conclusion is not the conversion's left endpoint.
    ConversionPremiseMismatch { expected: TermId, actual: TermId },
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(result) = format_delegated_proof_error(self, formatter) {
            return result;
        }
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
            Self::OpenConclusion(term) => write!(
                formatter,
                "conclusion term {} is not locally closed",
                term.get()
            ),
            Self::NotLambda(term) => write!(formatter, "term {} is not a lambda", term.get()),
            Self::BetaTypeMismatch { expected, actual } => write!(
                formatter,
                "beta argument has type {}, expected {}",
                actual.get(),
                expected.get()
            ),
            Self::WrongImplicationWitnessContext {
                expected,
                actual,
                conclusion,
            } => write!(
                formatter,
                "implication witness {} has context {}, expected {}",
                conclusion.get(),
                actual.get(),
                expected.get()
            ),
            Self::MissingImplicationWitness { consequent, term } => write!(
                formatter,
                "context {} member {} has no implication witness",
                consequent.get(),
                term.get()
            ),
            Self::UnexpectedImplicationWitness { consequent, term } => write!(
                formatter,
                "implication witness {} is not a member of context {}",
                term.get(),
                consequent.get()
            ),
            Self::DuplicateImplicationWitness(term) => {
                write!(formatter, "duplicate implication witness {}", term.get())
            }
            Self::EmptyImplicationPath => formatter.write_str("context implication path is empty"),
            Self::MissingContextImplicationEdge {
                antecedent,
                consequent,
            } => write!(
                formatter,
                "context implication edge {} => {} is absent",
                antecedent.get(),
                consequent.get()
            ),
            Self::ContextUnionMissingMember { .. }
            | Self::ContextUnionUnexpectedMember { .. }
            | Self::ContextUnionConflict { .. }
            | Self::ContextEquivalenceMismatch { .. }
            | Self::WeakeningContextMismatch { .. }
            | Self::MismatchedTheoremContexts { .. }
            | Self::EqualitySubstitutionContextMismatch { .. }
            | Self::ExpectedEquality(_)
            | Self::EqualityPremiseMismatch { .. }
            | Self::OpenEqualityPredicate(_)
            | Self::EqualityPredicateNotFunction { .. }
            | Self::EqualityPredicateDomainMismatch { .. }
            | Self::EqualityPredicateNonBoolean { .. }
            | Self::EqualitySubstitutionPremiseMismatch { .. }
            | Self::InstantiationKeyNotFree(_)
            | Self::DuplicateTermInstantiation(_)
            | Self::TermInstantiationTypeMismatch { .. }
            | Self::OpenTermInstantiationReplacement(_)
            | Self::TypeInstantiationKeyNotFree(_)
            | Self::DuplicateTypeInstantiation(_)
            | Self::OpenTypeInstantiationReplacement(_)
            | Self::AbstractionKeyNotFree(_)
            | Self::AbstractionVariableFreeInAssumption { .. }
            | Self::ChoicePremiseNotApplication(_)
            | Self::ConversionChainMismatch { .. }
            | Self::ConversionBoundaryMismatch { .. }
            | Self::NonBooleanConversion { .. }
            | Self::ConversionPremiseMismatch { .. } => unreachable!("handled above"),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

fn format_delegated_proof_error(
    error: &ProofError,
    formatter: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    if let Some(result) = format_instantiation_proof_error(error, formatter) {
        return Some(result);
    }
    if let Some(result) = format_substitution_proof_error(error, formatter) {
        return Some(result);
    }
    if let Some(result) = format_relational_proof_error(error, formatter) {
        return Some(result);
    }
    format_conversion_proof_error(error, formatter)
}

fn format_conversion_proof_error(
    error: &ProofError,
    formatter: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    match error {
        ProofError::ConversionChainMismatch {
            first_right,
            second_left,
        } => Some(write!(
            formatter,
            "conversion chain has middle terms {} and {}",
            first_right.get(),
            second_left.get()
        )),
        ProofError::ConversionBoundaryMismatch { left, right } => Some(write!(
            formatter,
            "conversion endpoints {} and {} have different open boundaries",
            left.get(),
            right.get()
        )),
        ProofError::NonBooleanConversion { term, ty } => Some(write!(
            formatter,
            "conversion endpoint {} has non-Boolean type {}",
            term.get(),
            ty.get()
        )),
        ProofError::ConversionPremiseMismatch { expected, actual } => Some(write!(
            formatter,
            "theorem conclusion {} does not match conversion endpoint {}",
            actual.get(),
            expected.get()
        )),
        _ => None,
    }
}

fn format_relational_proof_error(
    error: &ProofError,
    formatter: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    match error {
        ProofError::ContextUnionMissingMember {
            left,
            right,
            result,
            term,
        } => Some(format_context_union_member_error(
            formatter, *left, *right, *result, *term, "omits",
        )),
        ProofError::ContextUnionUnexpectedMember {
            left,
            right,
            result,
            term,
        } => Some(format_context_union_member_error(
            formatter,
            *left,
            *right,
            *result,
            *term,
            "has unexpected",
        )),
        ProofError::ContextUnionConflict {
            left,
            right,
            stored_result,
            requested_result,
        } => Some(format_context_union_conflict_error(
            formatter,
            *left,
            *right,
            *stored_result,
            *requested_result,
        )),
        ProofError::ContextEquivalenceMismatch {
            forward_antecedent,
            forward_consequent,
            backward_antecedent,
            backward_consequent,
        } => Some(write!(
            formatter,
            "context implications {} => {} and {} => {} are not opposites",
            forward_antecedent.get(),
            forward_consequent.get(),
            backward_antecedent.get(),
            backward_consequent.get()
        )),
        ProofError::WeakeningContextMismatch { expected, actual } => Some(write!(
            formatter,
            "weakening theorem has context {}, expected {}",
            actual.get(),
            expected.get()
        )),
        ProofError::MismatchedTheoremContexts { expected, actual } => Some(write!(
            formatter,
            "theorem context {} does not match {}",
            actual.get(),
            expected.get()
        )),
        ProofError::ExpectedEquality(term) => Some(write!(
            formatter,
            "term {} is not an equality conclusion",
            term.get()
        )),
        ProofError::EqualityPremiseMismatch { expected, actual } => Some(write!(
            formatter,
            "equality premise is {}, expected {}",
            actual.get(),
            expected.get()
        )),
        _ => None,
    }
}

fn format_substitution_proof_error(
    error: &ProofError,
    formatter: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    match error {
        ProofError::EqualitySubstitutionContextMismatch { equality, premise } => Some(write!(
            formatter,
            "equality substitution premise context {} does not match equality context {}",
            premise.get(),
            equality.get()
        )),
        ProofError::OpenEqualityPredicate(predicate) => Some(write!(
            formatter,
            "equality substitution predicate {} is not locally closed",
            predicate.get()
        )),
        ProofError::EqualityPredicateNotFunction { predicate, ty } => Some(write!(
            formatter,
            "equality substitution predicate {} has non-function type {}",
            predicate.get(),
            ty.get()
        )),
        ProofError::EqualityPredicateDomainMismatch {
            predicate,
            expected,
            actual,
        } => Some(write!(
            formatter,
            "equality substitution predicate {} has domain {}, expected {}",
            predicate.get(),
            actual.get(),
            expected.get()
        )),
        ProofError::EqualityPredicateNonBoolean {
            predicate,
            codomain,
        } => Some(write!(
            formatter,
            "equality substitution predicate {} has non-Boolean codomain {}",
            predicate.get(),
            codomain.get()
        )),
        ProofError::EqualitySubstitutionPremiseMismatch {
            predicate,
            argument,
            actual,
        } => Some(write!(
            formatter,
            "equality substitution premise {} is not application {} {}",
            actual.get(),
            predicate.get(),
            argument.get()
        )),
        ProofError::AbstractionKeyNotFree(variable) => Some(write!(
            formatter,
            "term {} is not an exact free-variable abstraction key",
            variable.get()
        )),
        ProofError::AbstractionVariableFreeInAssumption {
            variable,
            assumption,
        } => Some(write!(
            formatter,
            "free variable {} occurs in assumption {}",
            variable.get(),
            assumption.get()
        )),
        ProofError::ChoicePremiseNotApplication(conclusion) => Some(write!(
            formatter,
            "choice premise {} is not a predicate application",
            conclusion.get()
        )),
        _ => None,
    }
}

fn format_instantiation_proof_error(
    error: &ProofError,
    formatter: &mut fmt::Formatter<'_>,
) -> Option<fmt::Result> {
    match error {
        ProofError::InstantiationKeyNotFree(variable) => Some(write!(
            formatter,
            "term {} is not an exact free-variable instantiation key",
            variable.get()
        )),
        ProofError::DuplicateTermInstantiation(variable) => Some(write!(
            formatter,
            "free-variable instantiation key {} occurs more than once",
            variable.get()
        )),
        ProofError::TermInstantiationTypeMismatch {
            variable,
            replacement,
            expected,
            actual,
        } => Some(write!(
            formatter,
            "replacement {} for free variable {} has type {}, expected {}",
            replacement.get(),
            variable.get(),
            actual.get(),
            expected.get()
        )),
        ProofError::OpenTermInstantiationReplacement(replacement) => Some(write!(
            formatter,
            "free-term instantiation replacement {} is not locally closed",
            replacement.get()
        )),
        ProofError::TypeInstantiationKeyNotFree(variable) => Some(write!(
            formatter,
            "type {} is not an exact free-type-variable instantiation key",
            variable.get()
        )),
        ProofError::DuplicateTypeInstantiation(variable) => Some(write!(
            formatter,
            "free-type-variable instantiation key {} occurs more than once",
            variable.get()
        )),
        ProofError::OpenTypeInstantiationReplacement(replacement) => Some(write!(
            formatter,
            "free-type-variable instantiation replacement {} is not locally closed",
            replacement.get()
        )),
        _ => None,
    }
}

fn format_context_union_member_error(
    formatter: &mut fmt::Formatter<'_>,
    left: ContextId,
    right: ContextId,
    result: ContextId,
    term: TermId,
    relation: &str,
) -> fmt::Result {
    write!(
        formatter,
        "context union ({}, {}) result {} {relation} member {}",
        left.get(),
        right.get(),
        result.get(),
        term.get()
    )
}

fn format_context_union_conflict_error(
    formatter: &mut fmt::Formatter<'_>,
    left: ContextId,
    right: ContextId,
    stored_result: ContextId,
    requested_result: ContextId,
) -> fmt::Result {
    write!(
        formatter,
        "context union ({}, {}) is stored as {}, not {}",
        left.get(),
        right.get(),
        stored_result.get(),
        requested_result.get()
    )
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
            | Self::BetaTypeMismatch { .. }
            | Self::WrongImplicationWitnessContext { .. }
            | Self::MissingImplicationWitness { .. }
            | Self::UnexpectedImplicationWitness { .. }
            | Self::DuplicateImplicationWitness(_)
            | Self::EmptyImplicationPath
            | Self::MissingContextImplicationEdge { .. }
            | Self::ContextUnionMissingMember { .. }
            | Self::ContextUnionUnexpectedMember { .. }
            | Self::ContextUnionConflict { .. }
            | Self::ContextEquivalenceMismatch { .. }
            | Self::WeakeningContextMismatch { .. }
            | Self::MismatchedTheoremContexts { .. }
            | Self::EqualitySubstitutionContextMismatch { .. }
            | Self::ExpectedEquality(_)
            | Self::EqualityPremiseMismatch { .. }
            | Self::OpenEqualityPredicate(_)
            | Self::EqualityPredicateNotFunction { .. }
            | Self::EqualityPredicateDomainMismatch { .. }
            | Self::EqualityPredicateNonBoolean { .. }
            | Self::EqualitySubstitutionPremiseMismatch { .. }
            | Self::InstantiationKeyNotFree(_)
            | Self::DuplicateTermInstantiation(_)
            | Self::TermInstantiationTypeMismatch { .. }
            | Self::OpenTermInstantiationReplacement(_)
            | Self::TypeInstantiationKeyNotFree(_)
            | Self::DuplicateTypeInstantiation(_)
            | Self::OpenTypeInstantiationReplacement(_)
            | Self::AbstractionKeyNotFree(_)
            | Self::AbstractionVariableFreeInAssumption { .. }
            | Self::ChoicePremiseNotApplication(_)
            | Self::ConversionChainMismatch { .. }
            | Self::ConversionBoundaryMismatch { .. }
            | Self::NonBooleanConversion { .. }
            | Self::ConversionPremiseMismatch { .. } => None,
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
    use std::cell::Cell;
    use std::rc::Rc;

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

    #[derive(Default)]
    struct DenyPersistence {
        operations: Vec<Operation>,
    }

    impl Policy for DenyPersistence {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            !matches!(
                operation,
                Operation::PersistJudgement | Operation::PersistContextImplication
            )
        }
    }

    #[derive(Default)]
    struct DenyEqualitySubstitution {
        operations: Vec<Operation>,
    }

    #[derive(Default)]
    struct DenyDeductionAntisymmetry {
        operations: Vec<Operation>,
    }

    impl Policy for DenyDeductionAntisymmetry {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            operation != Operation::ProveDeductionAntisymmetry
        }
    }

    struct ArmedDenial {
        operation: Operation,
        armed: Rc<Cell<bool>>,
    }

    impl Policy for ArmedDenial {
        fn allows(&mut self, operation: Operation) -> bool {
            !self.armed.get() || operation != self.operation
        }
    }

    impl Policy for DenyEqualitySubstitution {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            operation != Operation::ProveEqualitySubstitution
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
    fn opaque_signature_declarations_are_canonical_typed_and_closed() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(100).unwrap();
        let same_ind = connection.insert_base_type(100).unwrap();
        let zero = connection.insert_constant(200, ind).unwrap();
        let same_zero = connection.insert_constant(200, ind).unwrap();

        assert_eq!(ind, same_ind);
        assert_eq!(zero, same_zero);
        assert_eq!(
            connection.type_view(ind).unwrap(),
            TypeView::Base { symbol: 100 }
        );
        assert_eq!(connection.type_kind(ind).unwrap(), STAR_ID);
        assert_eq!(
            connection.term(zero).unwrap(),
            TermView::Constant { symbol: 200 }
        );
        assert_eq!(connection.term_type(zero).unwrap(), ind);
        assert!(connection.term_is_locally_closed(zero).unwrap());
        assert!(connection.term_free_variables(zero).unwrap().is_empty());

        assert!(matches!(
            connection.insert_constant(200, BOOL_TYPE_ID),
            Err(TermError::ConstantTypeConflict {
                symbol: 200,
                existing,
                requested
            }) if existing == ind && requested == BOOL_TYPE_ID
        ));
        let declarations = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*) FROM hol_node WHERE tag = 'MCONST' AND lhs = 200",
                [],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(declarations, 1);
    }

    #[test]
    fn signature_extension_is_separately_policy_visible_and_atomic() {
        let mut denied = Connection::open_hol_in_memory(RecordingPolicy::default()).unwrap();
        assert!(matches!(
            denied.insert_base_type(100),
            Err(TypeError::Denied(Operation::DeclareBaseType))
        ));
        assert_eq!(
            denied
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT count(*) FROM hol_node WHERE tag = 'TBASE'",
                    [],
                    |row| { row.get::<_, i64>(0) }
                )
                .unwrap(),
            0
        );

        let mut allowed = Connection::open_hol_in_memory(RecordingPolicy {
            allowed: true,
            operations: Vec::new(),
        })
        .unwrap();
        let base = allowed.insert_base_type(100).unwrap();
        allowed.insert_constant(200, base).unwrap();
        assert_eq!(
            allowed.protocol().policy().operations,
            [
                Operation::DeclareBaseType,
                Operation::InsertType,
                Operation::DeclareConstant,
                Operation::InsertTerm,
            ]
        );
    }

    #[test]
    fn closed_beta_over_opaque_ind_uses_only_conversion_rules() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(100).unwrap();
        let zero = connection.insert_constant(200, ind).unwrap();
        let ind_to_ind = connection.insert_arrow_type(ind, ind).unwrap();
        let succ = connection.insert_constant(201, ind_to_ind).unwrap();
        let variable = connection.insert_bound_term(0, ind).unwrap();
        let succ_variable = connection.insert_application(succ, variable).unwrap();
        let abstraction = connection.insert_lambda(ind, succ_variable).unwrap();
        let succ_zero = connection.insert_application(succ, zero).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let conversion = proof.conversion_beta(abstraction, zero)?;
                assert_eq!(conversion.right(), succ_zero);
                let theorem = proof.prove_conversion_equality(ContextId::empty(), &conversion)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .unwrap();

        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
        assert!(
            connection
                .term_free_variables(conclusion)
                .unwrap()
                .is_empty()
        );
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
                let theorem = proof.prove_reflexivity(ContextId::empty(), identity)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
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
                let theorem = proof.prove_reflexivity(ContextId::empty(), identity)?;
                proof.persist_theorem(&theorem)
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
                let theorem = proof.prove_beta(ContextId::empty(), identity, truth)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
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
    fn equality_modus_ponens_composes_branded_premises_before_persistence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let application = connection.insert_application(identity, truth).unwrap();
        let context = connection.define_context([application]).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let premise = proof.prove_hypothesis(context, application)?;
                let equality = proof.prove_beta(context, identity, truth)?;
                let wrong_context = proof.prove_truth(ContextId::empty())?;
                assert!(matches!(
                    proof.equality_modus_ponens(&equality, &wrong_context),
                    Err(ProofError::MismatchedTheoremContexts { .. })
                ));
                assert!(matches!(
                    proof.equality_modus_ponens(&premise, &premise),
                    Err(ProofError::ExpectedEquality(term)) if term == application
                ));
                let wrong_premise = proof.prove_truth(context)?;
                assert!(matches!(
                    proof.equality_modus_ponens(&equality, &wrong_premise),
                    Err(ProofError::EqualityPremiseMismatch { .. })
                ));
                let theorem = proof.equality_modus_ponens(&equality, &premise)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .unwrap();
        assert_eq!(conclusion, truth);
        let (judgements, rule) = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT
                     (SELECT count(*) FROM hol_judgement),
                     (SELECT rule FROM hol_proof_event LIMIT 1)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?)),
            )
            .unwrap();
        assert_eq!(judgements, 1);
        assert_eq!(rule, "equality_modus_ponens");
    }

    #[test]
    fn typed_equality_substitution_proves_succ_congruence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(100).unwrap();
        let ind_to_ind = connection.insert_arrow_type(ind, ind).unwrap();
        let x = connection.insert_constant(200, ind).unwrap();
        let y = connection.insert_constant(201, ind).unwrap();
        let succ = connection.insert_constant(202, ind_to_ind).unwrap();
        let x_equals_y = connection.insert_equality(x, y).unwrap();
        let context = connection.define_context([x_equals_y]).unwrap();

        let succ_x = connection.insert_application(succ, x).unwrap();
        let variable = connection.insert_bound_term(0, ind).unwrap();
        let succ_variable = connection.insert_application(succ, variable).unwrap();
        let predicate_body = connection.insert_equality(succ_x, succ_variable).unwrap();
        let predicate = connection.insert_lambda(ind, predicate_body).unwrap();
        let succ_y = connection.insert_application(succ, y).unwrap();
        let expected = connection.insert_equality(succ_x, succ_y).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let equality = proof.prove_hypothesis(context, x_equals_y)?;
                let reflexive = proof.prove_reflexivity(context, succ_x)?;

                let beta_x = proof.conversion_beta(predicate, x)?;
                let reverse_beta_x = proof.conversion_symmetry(&beta_x)?;
                let predicate_x = proof.convert_theorem(&reflexive, &reverse_beta_x)?;

                let predicate_y =
                    proof.equality_substitution(&equality, predicate, &predicate_x)?;
                proof.persist_theorem(&predicate_y)?;
                let beta_y = proof.conversion_beta(predicate, y)?;
                let theorem = proof.convert_theorem(&predicate_y, &beta_y)?;
                assert_eq!(theorem.conclusion(), expected);
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(theorem.conclusion())
            })
            .unwrap();

        assert_eq!(conclusion, expected);
        assert!(connection.proved_judgement(context, expected).unwrap());
        let mut rules = connection
            .parts_mut()
            .0
            .sqlite()
            .prepare("SELECT rule FROM hol_proof_event WHERE ctx_id = ?1 ORDER BY event_id")
            .unwrap();
        let rules = rules
            .query_map([context.get()], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(rules, ["equality_substitution", "conversion"]);
    }

    #[test]
    fn equality_substitution_rejects_inexact_or_ill_typed_predicates() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let falsehood = connection.insert_bool_term(false).unwrap();
        let equality_term = connection.insert_equality(truth, falsehood).unwrap();
        let context = connection.define_context([equality_term, truth]).unwrap();
        let other_context = connection.define_context([truth]).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let open_predicate = connection.insert_bound_term(0, bool_to_bool).unwrap();
        let ind = connection.insert_base_type(300).unwrap();
        let wrong_domain = connection.insert_lambda(ind, truth).unwrap();
        let non_boolean = connection.insert_lambda(bool_type, identity).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let equality = proof.prove_hypothesis(context, equality_term)?;
                let premise = proof.prove_hypothesis(context, truth)?;
                let other = proof.prove_hypothesis(other_context, truth)?;
                assert!(matches!(
                    proof.equality_substitution(&premise, identity, &premise),
                    Err(ProofError::ExpectedEquality(term)) if term == truth
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, identity, &other),
                    Err(ProofError::EqualitySubstitutionContextMismatch { .. })
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, open_predicate, &premise),
                    Err(ProofError::OpenEqualityPredicate(term)) if term == open_predicate
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, truth, &premise),
                    Err(ProofError::EqualityPredicateNotFunction { predicate, .. })
                        if predicate == truth
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, wrong_domain, &premise),
                    Err(ProofError::EqualityPredicateDomainMismatch { predicate, .. })
                        if predicate == wrong_domain
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, non_boolean, &premise),
                    Err(ProofError::EqualityPredicateNonBoolean { predicate, .. })
                        if predicate == non_boolean
                ));
                assert!(matches!(
                    proof.equality_substitution(&equality, identity, &premise),
                    Err(ProofError::EqualitySubstitutionPremiseMismatch { actual, .. })
                        if actual == truth
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn equality_substitution_has_a_distinct_policy_gate() {
        let mut connection =
            Connection::open_hol_in_memory(DenyEqualitySubstitution::default()).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let equality_term = connection.insert_equality(truth, truth).unwrap();
        let context = connection.define_context([equality_term, truth]).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();

        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                let equality = proof.prove_hypothesis(context, equality_term)?;
                let premise = proof.prove_hypothesis(context, truth)?;
                proof
                    .equality_substitution(&equality, identity, &premise)
                    .map(|_| ())
            }),
            Err(ProofError::Denied(Operation::ProveEqualitySubstitution))
        ));
        let operations = &connection.protocol().policy().operations;
        assert_eq!(
            operations.last(),
            Some(&Operation::ProveEqualitySubstitution)
        );
        assert!(
            !operations.ends_with(&[Operation::ProveEqualitySubstitution, Operation::InsertTerm])
        );
    }

    #[test]
    fn term_instantiation_is_simultaneous_and_transforms_the_context() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(700, bool_type).unwrap();
        let y = connection.insert_free_term(701, bool_type).unwrap();
        let z = connection.insert_free_term(702, bool_type).unwrap();
        let context = connection.define_context([x, y]).unwrap();

        let (simultaneous_context, collapsed_context, conclusion) = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, x)?;
                let simultaneous = proof.instantiate_terms(
                    &theorem,
                    &[
                        TermInstantiation {
                            variable: x,
                            replacement: y,
                        },
                        TermInstantiation {
                            variable: y,
                            replacement: z,
                        },
                    ],
                )?;
                assert_eq!(simultaneous.conclusion(), y);
                let collapsed = proof.instantiate_terms(
                    &theorem,
                    &[
                        TermInstantiation {
                            variable: x,
                            replacement: z,
                        },
                        TermInstantiation {
                            variable: y,
                            replacement: z,
                        },
                    ],
                )?;
                proof.persist_theorem(&simultaneous)?;
                Ok::<_, ProofError>((
                    simultaneous.context(),
                    collapsed.context(),
                    simultaneous.conclusion(),
                ))
            })
            .unwrap();

        assert_eq!(conclusion, y);
        assert_eq!(
            connection.context_members(simultaneous_context).unwrap(),
            [y, z]
        );
        assert_eq!(connection.context_members(collapsed_context).unwrap(), [z]);
        let rule = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT rule FROM hol_proof_event WHERE ctx_id = ?1 AND term_id = ?2",
                [simultaneous_context.get(), y.get()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(rule, "term_instantiation");
    }

    #[test]
    fn empty_and_identity_term_instantiations_preserve_canonical_ids() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(705, bool_type).unwrap();
        let context = connection.define_context([x]).unwrap();

        let results = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, x)?;
                let empty = proof.instantiate_terms(&theorem, &[])?;
                let identity = proof.instantiate_terms(
                    &theorem,
                    &[TermInstantiation {
                        variable: x,
                        replacement: x,
                    }],
                )?;
                Ok::<_, ProofError>([
                    (empty.context(), empty.conclusion()),
                    (identity.context(), identity.conclusion()),
                ])
            })
            .unwrap();
        assert_eq!(results, [(context, x), (context, x)]);
    }

    #[test]
    fn term_instantiation_copies_closed_replacements_unchanged_beneath_lambdas() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(710, bool_to_bool).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let application = connection.insert_application(function, bound).unwrap();
        let abstraction = connection.insert_lambda(bool_type, application).unwrap();
        let proposition = connection
            .insert_equality(abstraction, abstraction)
            .unwrap();
        let context = connection.define_context([proposition]).unwrap();

        let identity_body = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, identity_body).unwrap();
        let expected_application = connection.insert_application(identity, bound).unwrap();
        let expected_abstraction = connection
            .insert_lambda(bool_type, expected_application)
            .unwrap();
        let expected = connection
            .insert_equality(expected_abstraction, expected_abstraction)
            .unwrap();

        let (result_context, conclusion) = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, proposition)?;
                let result = proof.instantiate_terms(
                    &theorem,
                    &[TermInstantiation {
                        variable: function,
                        replacement: identity,
                    }],
                )?;
                Ok::<_, ProofError>((result.context(), result.conclusion()))
            })
            .unwrap();
        assert_eq!(conclusion, expected);
        assert_eq!(
            connection.context_members(result_context).unwrap(),
            [expected]
        );
        let TermView::Equality { left, .. } = connection.term(conclusion).unwrap() else {
            panic!("instantiated conclusion is not equality")
        };
        let TermView::Lambda { body, .. } = connection.term(left).unwrap() else {
            panic!("instantiated operand is not a lambda")
        };
        let TermView::Application {
            function: copied, ..
        } = connection.term(body).unwrap()
        else {
            panic!("instantiated lambda body is not an application")
        };
        assert_eq!(copied, identity);
    }

    #[test]
    fn term_instantiation_rejects_invalid_maps_without_writes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let ind = connection.insert_base_type(720).unwrap();
        let x = connection.insert_free_term(721, bool_type).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let constant = connection.insert_constant(722, bool_type).unwrap();
        let wrong_type = connection.insert_constant(723, ind).unwrap();
        let open = connection.insert_bound_term(0, bool_type).unwrap();
        let context = connection.define_context([x]).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();

        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, x)?;
                assert!(matches!(
                    proof.instantiate_terms(
                        &theorem,
                        &[TermInstantiation { variable: constant, replacement: truth }]
                    ),
                    Err(ProofError::InstantiationKeyNotFree(term)) if term == constant
                ));
                assert!(matches!(
                    proof.instantiate_terms(
                        &theorem,
                        &[
                            TermInstantiation { variable: x, replacement: truth },
                            TermInstantiation { variable: x, replacement: truth },
                        ]
                    ),
                    Err(ProofError::DuplicateTermInstantiation(term)) if term == x
                ));
                assert!(matches!(
                    proof.instantiate_terms(
                        &theorem,
                        &[TermInstantiation { variable: x, replacement: wrong_type }]
                    ),
                    Err(ProofError::TermInstantiationTypeMismatch { variable, replacement, .. })
                        if variable == x && replacement == wrong_type
                ));
                assert!(matches!(
                    proof.instantiate_terms(
                        &theorem,
                        &[TermInstantiation { variable: x, replacement: open }]
                    ),
                    Err(ProofError::OpenTermInstantiationReplacement(term)) if term == open
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        let after = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(after, before);
    }

    #[test]
    fn term_instantiation_rolls_back_syntax_when_context_interning_fails() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(725, bool_type).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let proposition = connection.insert_equality(x, x).unwrap();
        let context = connection.define_context([proposition]).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "CREATE TEMP TRIGGER reject_instantiated_context
                 BEFORE INSERT ON hol_context
                 BEGIN
                   SELECT RAISE(ABORT, 'test context rejection');
                 END",
            )
            .unwrap();

        let result = connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_hypothesis(context, proposition)?;
            proof
                .instantiate_terms(
                    &theorem,
                    &[TermInstantiation {
                        variable: x,
                        replacement: truth,
                    }],
                )
                .map(|_| ())
        });
        assert!(matches!(
            result,
            Err(ProofError::Context(ContextError::Sqlite(_)))
        ));
        let after = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(after, before);
        assert!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT NOT EXISTS(
                     SELECT 1 FROM hol_node
                     WHERE tag = 'MEQ' AND lhs = ?1 AND rhs = ?1
                 )",
                    [truth.get()],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap()
        );
    }

    #[test]
    fn term_instantiation_checks_all_policy_gates_before_database_work() {
        for denied in [
            Operation::ProveTermInstantiation,
            Operation::InsertTerm,
            Operation::DefineContext,
        ] {
            let armed = Rc::new(Cell::new(false));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed: Rc::clone(&armed),
            })
            .unwrap();
            let bool_type = connection.insert_bool_type().unwrap();
            let x = connection.insert_free_term(730, bool_type).unwrap();
            let truth = connection.insert_bool_term(true).unwrap();
            let context = connection.define_context([x]).unwrap();
            armed.set(true);

            let result = connection.with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, x)?;
                proof
                    .instantiate_terms(
                        &theorem,
                        &[TermInstantiation {
                            variable: x,
                            replacement: truth,
                        }],
                    )
                    .map(|_| ())
            });
            let expected = match denied {
                Operation::DefineContext => ProofError::Context(ContextError::Denied(denied)),
                _ => ProofError::Denied(denied),
            };
            assert_eq!(result.unwrap_err().to_string(), expected.to_string());
            let counts = connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT (SELECT count(*) FROM hol_judgement),
                            (SELECT count(*) FROM hol_proof_event)",
                    [],
                    |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
                )
                .unwrap();
            assert_eq!(counts, (0, 0));
        }
    }

    #[test]
    fn abstraction_closes_an_honest_beta_equality_and_persists_its_origin() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(800, bool_type).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let beta = proof.prove_beta(ContextId::empty(), identity, x)?;
                let abstracted = proof.abstraction(&beta, x)?;
                assert_eq!(abstracted.context(), ContextId::empty());
                proof.persist_theorem(&abstracted)?;
                Ok::<_, ProofError>(abstracted.conclusion())
            })
            .unwrap();

        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("abstracted theorem is not equality")
        };
        let TermView::Lambda {
            body: left_body, ..
        } = connection.term(left).unwrap()
        else {
            panic!("left endpoint is not a lambda")
        };
        let TermView::Lambda {
            body: right_body, ..
        } = connection.term(right).unwrap()
        else {
            panic!("right endpoint is not a lambda")
        };
        assert!(matches!(
            connection.term(left_body).unwrap(),
            TermView::Application { .. }
        ));
        assert_eq!(
            connection.term(right_body).unwrap(),
            TermView::Bound { index: 0 }
        );
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
        assert_eq!(rule, "abstraction");
    }

    #[test]
    fn abstraction_tracks_nested_binder_depth_and_interacts_exactly_with_instantiation() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(810, bool_type).unwrap();
        let y = connection.insert_free_term(811, bool_type).unwrap();
        let pair_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(812, pair_type).unwrap();
        let existing_bound = connection.insert_bound_term(0, bool_type).unwrap();
        let fx = connection.insert_application(function, x).unwrap();
        let fy = connection.insert_application(function, y).unwrap();
        let free_equality = connection.insert_equality(fx, fy).unwrap();
        let bound_equality = connection
            .insert_equality(existing_bound, existing_bound)
            .unwrap();
        let body = connection
            .insert_equality(free_equality, bound_equality)
            .unwrap();
        let left = connection.insert_lambda(bool_type, body).unwrap();
        let replacement = connection.insert_bool_term(true).unwrap();

        let final_conclusion = connection
            .with_proof_session(|mut proof| {
                let reflexive = proof.prove_reflexivity(ContextId::empty(), left)?;
                let abstracted = proof.abstraction(&reflexive, x)?;
                let instantiated = proof.instantiate_terms(
                    &abstracted,
                    &[
                        TermInstantiation {
                            variable: x,
                            replacement,
                        },
                        TermInstantiation {
                            variable: y,
                            replacement,
                        },
                    ],
                )?;
                Ok::<_, ProofError>(instantiated.conclusion())
            })
            .unwrap();

        let TermView::Equality { left, .. } = connection.term(final_conclusion).unwrap() else {
            panic!("result is not equality")
        };
        let TermView::Lambda { body: outer, .. } = connection.term(left).unwrap() else {
            panic!("missing abstraction lambda")
        };
        let TermView::Lambda { body: inner, .. } = connection.term(outer).unwrap() else {
            panic!("missing existing lambda")
        };
        let TermView::Equality {
            left: free_equality,
            right: bound_equality,
        } = connection.term(inner).unwrap()
        else {
            panic!("missing inner equality")
        };
        let TermView::Equality {
            left: fx,
            right: fy,
        } = connection.term(free_equality).unwrap()
        else {
            panic!("missing free equality")
        };
        let TermView::Application { argument, .. } = connection.term(fx).unwrap() else {
            panic!("missing inner application")
        };
        assert_eq!(
            connection.term(argument).unwrap(),
            TermView::Bound { index: 1 }
        );
        let TermView::Application { argument, .. } = connection.term(fy).unwrap() else {
            panic!("missing instantiated application")
        };
        assert_eq!(argument, replacement);
        let TermView::Equality { left: bv, right } = connection.term(bound_equality).unwrap()
        else {
            panic!("missing bound equality")
        };
        assert_eq!(bv, right);
        assert_eq!(connection.term(bv).unwrap(), TermView::Bound { index: 0 });
    }

    #[test]
    fn abstraction_freshness_is_exact_typed_identity_and_rejection_is_atomic() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let ind = connection.insert_base_type(820).unwrap();
        let x = connection.insert_free_term(821, ind).unwrap();
        let same_symbol_bool = connection.insert_free_term(821, bool_type).unwrap();
        let wrapped_x = connection.insert_lambda(bool_type, x).unwrap();
        let nested_assumption = connection.insert_equality(wrapped_x, wrapped_x).unwrap();
        let clean_context = connection.define_context([same_symbol_bool]).unwrap();
        let dirty_context = connection
            .define_context([same_symbol_bool, nested_assumption])
            .unwrap();
        connection
            .with_proof_session(|mut proof| {
                let clean = proof.prove_reflexivity(clean_context, x)?;
                proof.abstraction(&clean, x)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();
        let before_rejection = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        connection
            .with_proof_session(|mut proof| {
                let dirty = proof.prove_reflexivity(dirty_context, x)?;
                assert!(matches!(
                    proof.abstraction(&dirty, x),
                    Err(ProofError::AbstractionVariableFreeInAssumption { variable, assumption })
                        if variable == x && assumption == nested_assumption
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        let after = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(after, before_rejection);
    }

    #[test]
    fn abstraction_rejects_non_free_keys_and_rolls_back_partial_syntax() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(830, bool_type).unwrap();
        let constant = connection.insert_constant(831, bool_type).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "CREATE TEMP TRIGGER reject_abstraction_lambda
             BEFORE INSERT ON hol_node WHEN NEW.tag = 'MLAM'
             BEGIN SELECT RAISE(ABORT, 'test abstraction rejection'); END",
            )
            .unwrap();

        connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_reflexivity(ContextId::empty(), x)?;
            assert!(matches!(proof.abstraction(&theorem, constant), Err(ProofError::AbstractionKeyNotFree(term)) if term == constant));
            assert!(matches!(proof.abstraction(&theorem, bound), Err(ProofError::AbstractionKeyNotFree(term)) if term == bound));
            assert!(matches!(
                proof.abstraction(&theorem, TermId::from_i64(i64::MAX)),
                Err(ProofError::Term(TermError::UnknownTerm(term))) if term == TermId::from_i64(i64::MAX)
            ));
            assert!(matches!(proof.abstraction(&theorem, x), Err(ProofError::Term(TermError::Sqlite(_)))));
            Ok::<_, ProofError>(())
        }).unwrap();
        let after = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(after, before + 1); // reflexivity's equality commits before the ABS transaction.
        assert!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT NOT EXISTS(
                 SELECT 1 FROM hol_node
                 WHERE tag = 'TARR' AND lhs = ?1 AND rhs = ?1
             )",
                    [bool_type.get()],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap()
        );
    }

    #[test]
    fn abstraction_checks_all_policy_gates_before_database_work() {
        for denied in [
            Operation::ProveAbstraction,
            Operation::InsertTerm,
            Operation::InsertType,
        ] {
            let armed = Rc::new(Cell::new(false));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed: Rc::clone(&armed),
            })
            .unwrap();
            let bool_type = connection.insert_bool_type().unwrap();
            let x = connection.insert_free_term(840, bool_type).unwrap();
            armed.set(true);
            let result = connection.with_proof_session(|mut proof| {
                let theorem = Theorem {
                    context: ContextId::empty(),
                    conclusion: x,
                    origin: None,
                    brand: PhantomData,
                };
                proof.abstraction(&theorem, x).map(|_| ())
            });
            assert!(matches!(result, Err(ProofError::Denied(operation)) if operation == denied));
        }
    }

    #[test]
    fn epsilon_is_canonical_typed_and_inherits_its_predicate_boundary() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let ind = connection.insert_base_type(850).unwrap();
        let bool_predicate_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let epsilon = connection.insert_epsilon(identity).unwrap();
        assert_eq!(connection.insert_epsilon(identity).unwrap(), epsilon);
        assert_eq!(connection.term_type(epsilon).unwrap(), bool_type);
        assert_eq!(
            connection.term(epsilon).unwrap(),
            TermView::Epsilon {
                predicate: identity
            }
        );
        assert!(connection.term_is_locally_closed(epsilon).unwrap());

        let open_predicate = connection
            .insert_bound_term(0, bool_predicate_type)
            .unwrap();
        let open_epsilon = connection.insert_epsilon(open_predicate).unwrap();
        assert_eq!(
            connection.term_unbound_variables(open_epsilon).unwrap(),
            [UnboundVariable {
                index: 0,
                ty: bool_predicate_type
            }]
        );
        let closed = connection
            .insert_lambda(bool_predicate_type, open_epsilon)
            .unwrap();
        assert!(connection.term_is_locally_closed(closed).unwrap());

        let truth = connection.insert_bool_term(true).unwrap();
        assert!(matches!(
            connection.insert_epsilon(truth),
            Err(TermError::NotFunction(ty)) if ty == bool_type
        ));
        let ind_bound = connection.insert_bound_term(0, ind).unwrap();
        let ind_identity = connection.insert_lambda(ind, ind_bound).unwrap();
        assert!(matches!(
            connection.insert_epsilon(ind_identity),
            Err(TermError::EpsilonPredicateNonBoolean { predicate, codomain })
                if predicate == ind_identity && codomain == ind
        ));
    }

    #[test]
    fn epsilon_participates_in_beta_instantiation_abstraction_and_free_variable_queries() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let predicate_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let bool_bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bool_bound).unwrap();
        let predicate_bound = connection.insert_bound_term(0, predicate_type).unwrap();
        let open_epsilon = connection.insert_epsilon(predicate_bound).unwrap();
        let chooser = connection
            .insert_lambda(predicate_type, open_epsilon)
            .unwrap();
        let expected = connection.insert_epsilon(identity).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(chooser, identity)?;
                assert_eq!(beta.right(), expected);
                Ok::<_, ProofError>(())
            })
            .unwrap();

        let free_predicate = connection.insert_free_term(851, predicate_type).unwrap();
        let free_epsilon = connection.insert_epsilon(free_predicate).unwrap();
        assert_eq!(connection.term_free_variables(free_epsilon).unwrap(), [851]);
        let (instantiated_conclusion, abstracted_conclusion) = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(ContextId::empty(), free_epsilon)?;
                let instantiated = proof.instantiate_terms(
                    &theorem,
                    &[TermInstantiation {
                        variable: free_predicate,
                        replacement: identity,
                    }],
                )?;
                let abstracted = proof.abstraction(&theorem, free_predicate)?;
                Ok::<_, ProofError>((instantiated.conclusion(), abstracted.conclusion()))
            })
            .unwrap();
        assert_eq!(
            connection.term(instantiated_conclusion).unwrap(),
            TermView::Equality {
                left: expected,
                right: expected
            }
        );
        let TermView::Equality { left, right } = connection.term(abstracted_conclusion).unwrap()
        else {
            panic!("ABS result is not equality")
        };
        assert_eq!(left, right);
        let TermView::Lambda { body, .. } = connection.term(left).unwrap() else {
            panic!("ABS result endpoint is not lambda")
        };
        let TermView::Epsilon { predicate } = connection.term(body).unwrap() else {
            panic!("ABS did not preserve epsilon")
        };
        assert_eq!(
            connection.term(predicate).unwrap(),
            TermView::Bound { index: 0 }
        );
    }

    #[test]
    fn choice_selects_from_an_exact_proved_application_and_persists_its_origin() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let predicate_bound = connection.insert_bound_term(0, bool_type).unwrap();
        let predicate = connection
            .insert_lambda(bool_type, predicate_bound)
            .unwrap();
        let witness = connection.insert_bool_term(true).unwrap();
        let premise = connection.insert_application(predicate, witness).unwrap();
        let context = connection.define_context([premise]).unwrap();
        let predicate_type = connection.term_type(predicate).unwrap();
        let fake_epsilon_type = connection
            .insert_arrow_type(predicate_type, bool_type)
            .unwrap();
        let fake_epsilon = connection.insert_constant(852, fake_epsilon_type).unwrap();
        let fake_choice = connection
            .insert_application(fake_epsilon, predicate)
            .unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let premise = proof.prove_hypothesis(context, premise)?;
                let theorem = proof.choice(&premise)?;
                assert_eq!(theorem.context(), context);
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(theorem.conclusion())
            })
            .unwrap();
        let TermView::Application { function, argument } = connection.term(conclusion).unwrap()
        else {
            panic!("choice conclusion is not an application")
        };
        assert_eq!(function, predicate);
        assert_ne!(argument, fake_choice);
        assert_eq!(
            connection.term(argument).unwrap(),
            TermView::Epsilon { predicate }
        );
        let rule = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT rule FROM hol_proof_event WHERE ctx_id = ?1 AND term_id = ?2",
                [context.get(), conclusion.get()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(rule, "choice");
    }

    #[test]
    fn choice_rejects_nonapplications_and_all_policy_denials_precede_database_work() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_truth(ContextId::empty())?;
                assert!(matches!(
                    proof.choice(&theorem),
                    Err(ProofError::ChoicePremiseNotApplication(term)) if term == truth
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();

        for denied in [Operation::ProveChoice, Operation::InsertTerm] {
            let armed = Rc::new(Cell::new(false));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed: Rc::clone(&armed),
            })
            .unwrap();
            armed.set(true);
            let result = connection.with_proof_session(|mut proof| {
                let theorem = Theorem {
                    context: ContextId::empty(),
                    conclusion: TermId::from_i64(i64::MAX),
                    origin: None,
                    brand: PhantomData,
                };
                proof.choice(&theorem).map(|_| ())
            });
            assert!(matches!(result, Err(ProofError::Denied(operation)) if operation == denied));
        }
    }

    #[test]
    fn epsilon_conversion_is_congruent_and_preserves_open_boundaries() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let predicate_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let predicate_bound = connection.insert_bound_term(0, predicate_type).unwrap();
        let chooser = connection
            .insert_lambda(predicate_type, predicate_bound)
            .unwrap();
        let bool_bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bool_bound).unwrap();

        let (left, right, open_epsilon) = connection
            .with_proof_session(|mut proof| {
                let predicate_beta = proof.conversion_beta(chooser, identity)?;
                let epsilon = proof.conversion_epsilon(&predicate_beta)?;
                assert!(epsilon.is_closed());
                let open = proof.conversion_reflexivity(predicate_bound)?;
                let open_epsilon = proof.conversion_epsilon(&open)?;
                assert!(!open_epsilon.is_closed());
                assert_eq!(open_epsilon.ty(), bool_type);
                Ok::<_, ProofError>((epsilon.left(), epsilon.right(), open_epsilon.left()))
            })
            .unwrap();
        let TermView::Epsilon {
            predicate: left_predicate,
        } = connection.term(left).unwrap()
        else {
            panic!("left conversion endpoint is not epsilon")
        };
        assert_eq!(
            connection.term(left_predicate).unwrap(),
            TermView::Application {
                function: chooser,
                argument: identity
            }
        );
        assert_eq!(
            connection.term(right).unwrap(),
            TermView::Epsilon {
                predicate: identity
            }
        );
        assert_eq!(
            connection.term(open_epsilon).unwrap(),
            TermView::Epsilon {
                predicate: predicate_bound
            }
        );
        assert_eq!(
            connection.term_unbound_variables(open_epsilon).unwrap(),
            [UnboundVariable {
                index: 0,
                ty: predicate_type
            }]
        );
    }

    #[test]
    fn epsilon_conversion_rejects_wrong_types_and_checks_policy_before_reads() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(853).unwrap();
        let bound = connection.insert_bound_term(0, ind).unwrap();
        let non_boolean_predicate = connection.insert_lambda(ind, bound).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let conversion = proof.conversion_reflexivity(non_boolean_predicate)?;
                assert!(matches!(
                    proof.conversion_epsilon(&conversion),
                    Err(ProofError::Term(TermError::EpsilonPredicateNonBoolean {
                        predicate,
                        codomain
                    })) if predicate == non_boolean_predicate && codomain == ind
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();

        for denied in [Operation::ProveConversionEpsilon, Operation::InsertTerm] {
            let armed = Rc::new(Cell::new(true));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed,
            })
            .unwrap();
            let result = connection.with_proof_session(|mut proof| {
                let invalid = Conversion {
                    left: TermId::from_i64(i64::MAX),
                    right: TermId::from_i64(i64::MAX),
                    ty: TypeId::from_i64(i64::MAX),
                    term_boundary: BTreeMap::new(),
                    type_boundary: BTreeMap::new(),
                    brand: PhantomData,
                };
                proof.conversion_epsilon(&invalid).map(|_| ())
            });
            assert!(matches!(result, Err(ProofError::Denied(operation)) if operation == denied));
        }
    }

    #[test]
    fn choice_rolls_back_epsilon_when_result_insertion_fails() {
        let mut choice_connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = choice_connection.insert_bool_type().unwrap();
        let bound = choice_connection.insert_bound_term(0, bool_type).unwrap();
        let predicate = choice_connection.insert_lambda(bool_type, bound).unwrap();
        let witness = choice_connection.insert_bool_term(true).unwrap();
        let application = choice_connection
            .insert_application(predicate, witness)
            .unwrap();
        let before = choice_connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        choice_connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "CREATE TEMP TRIGGER reject_choice_result
                 BEFORE INSERT ON hol_node WHEN NEW.tag = 'MAPP'
                 BEGIN SELECT RAISE(ABORT, 'test choice result rejection'); END",
            )
            .unwrap();
        let result = choice_connection.with_proof_session(|mut proof| {
            let premise = Theorem {
                context: ContextId::empty(),
                conclusion: application,
                origin: None,
                brand: PhantomData,
            };
            proof.choice(&premise).map(|_| ())
        });
        assert!(matches!(
            result,
            Err(ProofError::Term(TermError::Sqlite(_)))
        ));
        assert_eq!(
            choice_connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_node", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            before
        );
    }

    #[test]
    fn epsilon_conversion_rolls_back_its_first_endpoint_when_the_second_fails() {
        let mut conversion_connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = conversion_connection.insert_bool_type().unwrap();
        let predicate_type = conversion_connection
            .insert_arrow_type(bool_type, bool_type)
            .unwrap();
        let predicate_bound = conversion_connection
            .insert_bound_term(0, predicate_type)
            .unwrap();
        let chooser = conversion_connection
            .insert_lambda(predicate_type, predicate_bound)
            .unwrap();
        let bound = conversion_connection
            .insert_bound_term(0, bool_type)
            .unwrap();
        let predicate = conversion_connection
            .insert_lambda(bool_type, bound)
            .unwrap();
        conversion_connection
            .insert_application(chooser, predicate)
            .unwrap();
        let before = conversion_connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        conversion_connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "CREATE TEMP TABLE rejected_epsilon_predicate(term_id INTEGER NOT NULL) STRICT;
                 CREATE TEMP TRIGGER reject_second_epsilon
                 BEFORE INSERT ON hol_node
                 WHEN NEW.tag = 'MEPS'
                      AND NEW.lhs = (SELECT term_id FROM rejected_epsilon_predicate)
                 BEGIN SELECT RAISE(ABORT, 'test second epsilon rejection'); END",
            )
            .unwrap();
        conversion_connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "INSERT INTO rejected_epsilon_predicate(term_id) VALUES (?1)",
                [predicate.get()],
            )
            .unwrap();
        let result = conversion_connection.with_proof_session(|mut proof| {
            let predicate_conversion = proof.conversion_beta(chooser, predicate)?;
            proof.conversion_epsilon(&predicate_conversion).map(|_| ())
        });
        assert!(matches!(
            result,
            Err(ProofError::Term(TermError::Sqlite(_)))
        ));
        assert_eq!(
            conversion_connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_node", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            before
        );
        assert!(
            conversion_connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT NOT EXISTS(SELECT 1 FROM hol_node WHERE tag = 'MEPS')",
                    [],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap()
        );
    }

    #[test]
    fn deduction_antisymmetry_discharges_opposite_assumptions() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let application = connection.insert_application(identity, truth).unwrap();
        let gamma = connection.define_context([application]).unwrap();
        let delta = connection.define_context([truth]).unwrap();
        let expected = connection.insert_equality(truth, application).unwrap();

        let (context, conclusion) = connection
            .with_proof_session(|mut proof| {
                let first = proof.prove_truth(gamma)?;
                let truth_in_delta = proof.prove_hypothesis(delta, truth)?;
                let beta = proof.conversion_beta(identity, truth)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                let second = proof.convert_theorem(&truth_in_delta, &reverse)?;
                let theorem = proof.deduction_antisymmetry(&first, &second)?;
                assert_eq!(theorem.context(), ContextId::empty());
                assert_eq!(theorem.conclusion(), expected);
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>((theorem.context(), theorem.conclusion()))
            })
            .unwrap();

        assert_eq!(context, ContextId::empty());
        assert_eq!(conclusion, expected);
        assert!(
            connection
                .proved_judgement(ContextId::empty(), expected)
                .unwrap()
        );
        let rule = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT rule FROM hol_proof_event WHERE ctx_id = 0 AND term_id = ?1",
                [expected.get()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(rule, "deduction_antisymmetry");
    }

    #[test]
    fn deduction_antisymmetry_constructs_the_exact_canonical_context() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let p = connection.insert_bool_term(true).unwrap();
        let q = connection.insert_bool_term(false).unwrap();
        let r = connection.insert_equality(p, p).unwrap();
        let s = connection.insert_equality(q, q).unwrap();
        let gamma = connection.define_context([p, q, r]).unwrap();
        let delta = connection.define_context([p, q, s]).unwrap();

        let result = connection
            .with_proof_session(|mut proof| {
                let first = proof.prove_hypothesis(gamma, p)?;
                let second = proof.prove_hypothesis(delta, q)?;
                let theorem = proof.deduction_antisymmetry(&first, &second)?;
                Ok::<_, ProofError>(theorem.context())
            })
            .unwrap();

        // Gamma loses q, Delta loses p, and their remaining members are unioned as a set.
        assert_eq!(connection.context_members(result).unwrap(), [p, q, r, s]);
        assert_eq!(result, connection.define_context([s, r, q, p, p]).unwrap());
    }

    #[test]
    fn deduction_antisymmetry_has_a_distinct_policy_gate() {
        let mut connection =
            Connection::open_hol_in_memory(DenyDeductionAntisymmetry::default()).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let context = connection.define_context([truth]).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();

        assert!(matches!(
            connection.with_proof_session(|mut proof| {
                let first = proof.prove_hypothesis(context, truth)?;
                let second = proof.prove_hypothesis(context, truth)?;
                proof.deduction_antisymmetry(&first, &second).map(|_| ())
            }),
            Err(ProofError::Denied(Operation::ProveDeductionAntisymmetry))
        ));
        assert_eq!(
            connection.protocol().policy().operations.last(),
            Some(&Operation::ProveDeductionAntisymmetry)
        );
        let after = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(after, before);
    }

    #[test]
    fn deduction_antisymmetry_policy_denials_precede_atomic_construction() {
        for denied in [Operation::InsertTerm, Operation::DefineContext] {
            let armed = Rc::new(Cell::new(false));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed: Rc::clone(&armed),
            })
            .unwrap();
            let truth = connection.insert_bool_term(true).unwrap();
            let context = connection.define_context([truth]).unwrap();
            let before = connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                    [],
                    |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
                )
                .unwrap();
            armed.set(true);

            let error = connection
                .with_proof_session(|mut proof| {
                    let first = proof.prove_hypothesis(context, truth)?;
                    let second = proof.prove_hypothesis(context, truth)?;
                    proof.deduction_antisymmetry(&first, &second).map(|_| ())
                })
                .unwrap_err();
            match (denied, error) {
                (Operation::InsertTerm, ProofError::Denied(Operation::InsertTerm))
                | (
                    Operation::DefineContext,
                    ProofError::Context(ContextError::Denied(Operation::DefineContext)),
                ) => {}
                (_, other) => panic!("unexpected deduction policy error: {other}"),
            }
            let after = connection
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT (SELECT count(*) FROM hol_node), (SELECT count(*) FROM hol_context)",
                    [],
                    |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
                )
                .unwrap();
            assert_eq!(after, before);
        }
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
    fn common_boundary_lambda_conversion_becomes_a_closed_equality_theorem() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let body = proof.conversion_reflexivity(variable)?;
                assert!(!body.is_closed());
                let lambda = proof.conversion_lambda(bool_type, &body)?;
                assert!(lambda.is_closed());
                let theorem = proof.prove_conversion_equality(ContextId::empty(), &lambda)?;
                Ok::<_, ProofError>(theorem.conclusion())
            })
            .unwrap();
        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("conversion theorem is not equality");
        };
        assert_eq!(left, right);
        assert!(connection.term_is_locally_closed(left).unwrap());
    }

    #[test]
    fn conversion_rules_compose_beta_congruence_symmetry_and_transitivity() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();

        let (application, reduct, congruent_left) = connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(identity, truth)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                let round_trip = proof.conversion_transitivity(&beta, &reverse)?;
                assert_eq!(round_trip.left(), round_trip.right());

                let function = proof.conversion_reflexivity(identity)?;
                let argument = proof.conversion_reflexivity(truth)?;
                let congruent = proof.conversion_application(&function, &argument)?;
                Ok::<_, ProofError>((beta.left(), beta.right(), congruent.left()))
            })
            .unwrap();
        assert_eq!(application, congruent_left);
        assert_eq!(reduct, truth);
    }

    #[test]
    fn closed_eta_and_boolean_theorem_conversion_are_restricted_and_sound() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let function = connection.insert_free_term(7, function_type).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let application = connection.insert_application(identity, truth).unwrap();
        let context = connection.define_context([application]).unwrap();

        let converted = connection
            .with_proof_session(|mut proof| {
                let eta = proof.conversion_eta(function)?;
                assert!(eta.is_closed());
                assert_eq!(eta.right(), function);

                let premise = proof.prove_hypothesis(context, application)?;
                let beta = proof.conversion_beta(identity, truth)?;
                let theorem = proof.convert_theorem(&premise, &beta)?;
                Ok::<_, ProofError>(theorem.conclusion())
            })
            .unwrap();
        assert_eq!(converted, truth);

        assert!(matches!(
            connection.with_proof_session(|mut proof| proof
                .conversion_eta(variable)
                .map(|_| ())),
            Err(ProofError::OpenConclusion(term)) if term == variable
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
                let result = (
                    hypothesis.context(),
                    hypothesis.conclusion(),
                    truth.context(),
                    truth.conclusion(),
                );
                proof.persist_theorem(&hypothesis)?;
                proof.persist_theorem(&truth)?;
                Ok::<_, ProofError>(result)
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
                let result = (hypothesis.conclusion(), truth.conclusion());
                proof.persist_theorem(&hypothesis)?;
                proof.persist_theorem(&truth)?;
                Ok::<_, ProofError>(result)
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
    fn derivation_capabilities_are_separate_from_persistence_policy() {
        let mut connection = Connection::open_hol_in_memory(DenyPersistence::default()).unwrap();
        let p = connection.insert_bool_term(false).unwrap();
        let context = connection.define_context([p]).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, p)?;
                assert!(proof.load_theorem(context, p)?.is_none());
                assert!(matches!(
                    proof.persist_theorem(&theorem),
                    Err(ProofError::Denied(Operation::PersistJudgement))
                ));
                let implication = proof.prove_context_implication(context, context, &[theorem])?;
                assert!(matches!(
                    proof.persist_context_implication(&implication),
                    Err(ProofError::Denied(Operation::PersistContextImplication))
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        let (neutron, hol) = connection.parts_mut();
        assert_eq!(
            hol.policy.operations,
            [
                Operation::InsertTerm,
                Operation::DefineContext,
                Operation::ProveHypothesis,
                Operation::ReadTheorem,
                Operation::PersistJudgement,
                Operation::ProveContextImplication,
                Operation::PersistContextImplication,
            ]
        );
        let counts = neutron
            .sqlite()
            .query_row(
                "SELECT
                     (SELECT count(*) FROM hol_judgement),
                     (SELECT count(*) FROM hol_proof_event),
                     (SELECT count(*) FROM hol_context_implication),
                     (SELECT count(*) FROM hol_context_implication_event)",
                [],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, i64>(3)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(counts, (0, 0, 0, 0));
    }

    #[test]
    fn context_implication_weakens_a_branded_theorem() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let p = connection.insert_free_term(10, bool_type).unwrap();
        let q = connection.insert_free_term(11, bool_type).unwrap();
        let consequent = connection.define_context([p]).unwrap();
        let antecedent = connection.define_context([p, q]).unwrap();

        let (equality, weakened) = connection
            .with_proof_session(|mut proof| {
                let witness = proof.prove_hypothesis(antecedent, p)?;
                let equality = proof.prove_reflexivity(consequent, p)?;
                let implication =
                    proof.prove_context_implication(antecedent, consequent, &[witness])?;
                assert_eq!(implication.antecedent(), antecedent);
                assert_eq!(implication.consequent(), consequent);
                let wrong_context = proof.prove_hypothesis(antecedent, p)?;
                assert!(matches!(
                    proof.weaken(&implication, &wrong_context),
                    Err(ProofError::WeakeningContextMismatch { .. })
                ));
                let weakened = proof.weaken(&implication, &equality)?;
                let result = (equality.conclusion(), weakened.conclusion());
                proof.persist_context_implication(&implication)?;
                proof.persist_theorem(&weakened)?;
                Ok::<_, ProofError>(result)
            })
            .unwrap();

        assert_eq!(weakened, equality);
        assert!(
            connection
                .proved_context_implication(antecedent, consequent)
                .unwrap()
        );
        assert!(connection.proved_judgement(antecedent, equality).unwrap());
        connection
            .with_proof_session(|mut proof| {
                assert!(
                    proof
                        .load_context_implication(antecedent, consequent)?
                        .is_some()
                );
                assert!(
                    proof
                        .load_context_implication(consequent, antecedent)?
                        .is_none()
                );
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn implication_introduction_requires_exact_witnesses() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let p = connection.insert_bool_term(false).unwrap();
        let q = connection.insert_bool_term(true).unwrap();
        let consequent = connection.define_context([p]).unwrap();
        let antecedent = connection.define_context([p, q]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let p_at_antecedent = proof.prove_hypothesis(antecedent, p)?;
                let duplicate = proof.prove_hypothesis(antecedent, p)?;
                let q_at_antecedent = proof.prove_hypothesis(antecedent, q)?;
                let p_at_consequent = proof.prove_hypothesis(consequent, p)?;
                assert!(matches!(
                    proof.prove_context_implication(antecedent, consequent, &[]),
                    Err(ProofError::MissingImplicationWitness { term, .. }) if term == p
                ));
                assert!(matches!(
                    proof.prove_context_implication(
                        antecedent,
                        consequent,
                        &[p_at_antecedent, duplicate]
                    ),
                    Err(ProofError::DuplicateImplicationWitness(term)) if term == p
                ));
                let p_with_extra = proof.prove_hypothesis(antecedent, p)?;
                assert!(matches!(
                    proof.prove_context_implication(
                        antecedent,
                        consequent,
                        &[p_with_extra, q_at_antecedent]
                    ),
                    Err(ProofError::UnexpectedImplicationWitness { term, .. }) if term == q
                ));
                assert!(matches!(
                    proof.prove_context_implication(antecedent, consequent, &[p_at_consequent]),
                    Err(ProofError::WrongImplicationWitnessContext { .. })
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        assert!(
            !connection
                .proved_context_implication(antecedent, consequent)
                .unwrap()
        );
    }

    #[test]
    fn context_implication_metadata_is_physical_only() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(
                MetadataTable::ContextImplication,
                "source",
                MetadataType::Text,
            )
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::ContextImplication,
                "implication source",
                ["source"],
                false,
            )
            .unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(AllowAll, schema).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let implication =
                    proof.prove_context_implication(ContextId::empty(), ContextId::empty(), &[])?;
                proof.persist_context_implication(&implication)
            })
            .unwrap();
        let target = MetadataTarget::context_implication(ContextId::empty(), ContextId::empty());
        connection
            .set_metadata(
                target,
                &[("source", MetadataValue::Text("checked".to_owned()))],
            )
            .unwrap();
        assert_eq!(
            connection.metadata(target, &["source"]).unwrap(),
            [MetadataValue::Text("checked".to_owned())]
        );
    }

    #[test]
    fn implication_events_are_repeatable_and_policy_denial_is_atomic() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let first =
                    proof.prove_context_implication(ContextId::empty(), ContextId::empty(), &[])?;
                proof.persist_context_implication(&first)?;
                let second =
                    proof.prove_context_implication(ContextId::empty(), ContextId::empty(), &[])?;
                proof.persist_context_implication(&second)
            })
            .unwrap();
        let counts = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT
                     (SELECT count(*) FROM hol_context_implication),
                     (SELECT count(*) FROM hol_context_implication_event)",
                [],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .unwrap();
        assert_eq!(counts, (1, 2));

        let mut denied = Connection::open_hol_in_memory(RecordingPolicy::default()).unwrap();
        assert!(matches!(
            denied.with_proof_session(|mut proof| {
                proof
                    .prove_context_implication(ContextId::empty(), ContextId::empty(), &[])
                    .map(|_| ())
            }),
            Err(ProofError::Denied(Operation::ProveContextImplication))
        ));
        assert!(matches!(
            denied.proved_context_implication(ContextId::empty(), ContextId::empty()),
            Err(ProofError::Denied(Operation::ReadContextImplication))
        ));
        let (neutron, hol) = denied.parts_mut();
        assert_eq!(
            hol.policy.operations,
            [
                Operation::ProveContextImplication,
                Operation::ReadContextImplication
            ]
        );
        let rows = neutron
            .sqlite()
            .query_row("SELECT count(*) FROM hol_context_implication", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 0);
    }

    #[test]
    fn explicit_implication_paths_are_checked_edge_by_edge() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let p = connection.insert_bool_term(false).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let first = connection.define_context([p, truth]).unwrap();
        let second = connection.define_context([p]).unwrap();
        let third = connection.define_context([truth]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let first_to_second = proof.prove_hypothesis(first, p)?;
                let first_to_second =
                    proof.prove_context_implication(first, second, &[first_to_second])?;
                proof.persist_context_implication(&first_to_second)?;
                let second_to_third = proof.prove_truth(second)?;
                let second_to_third =
                    proof.prove_context_implication(second, third, &[second_to_third])?;
                proof.persist_context_implication(&second_to_third)?;
                let composed = proof.prove_context_implication_path(&[first, second, third])?;
                assert_eq!(composed.antecedent(), first);
                assert_eq!(composed.consequent(), third);
                let reflexive = proof.prove_context_implication_path(&[first])?;
                assert_eq!(reflexive.antecedent(), first);
                assert_eq!(reflexive.consequent(), first);
                assert!(matches!(
                    proof.prove_context_implication_path(&[]),
                    Err(ProofError::EmptyImplicationPath)
                ));
                assert!(matches!(
                    proof.prove_context_implication_path(&[third, second]),
                    Err(ProofError::MissingContextImplicationEdge {
                        antecedent,
                        consequent,
                    }) if antecedent == third && consequent == second
                ));
                proof.persist_context_implication(&composed)?;
                proof.persist_context_implication(&reflexive)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();

        assert!(connection.proved_context_implication(first, third).unwrap());
        assert_eq!(
            connection.context_implication_edges().unwrap(),
            [
                (first, first),
                (first, second),
                (first, third),
                (second, third)
            ]
        );
    }

    #[test]
    fn exact_context_unions_are_checked_ordered_and_reloaded() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let p = connection.insert_free_term(40, BOOL_TYPE_ID).unwrap();
        let q = connection.insert_free_term(41, BOOL_TYPE_ID).unwrap();
        let r = connection.insert_free_term(42, BOOL_TYPE_ID).unwrap();
        let left = connection.define_context([p, q]).unwrap();
        let right = connection.define_context([q, r]).unwrap();
        let result = connection.define_context([p, q, r]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let union = proof.prove_context_union(left, right, result)?;
                assert_eq!(union.left(), left);
                assert_eq!(union.right(), right);
                assert_eq!(union.result(), result);
                let loaded = proof.load_context_union(left, right)?.unwrap();
                assert_eq!(loaded.result(), result);
                assert!(proof.load_context_union(right, left)?.is_none());
                proof.prove_context_union(left, right, result).map(|_| ())
            })
            .unwrap();

        let counts = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT
                     (SELECT count(*) FROM hol_context_exact_union),
                     (SELECT count(*) FROM hol_context_exact_union_event),
                     (SELECT count(*) FROM hol_context_implication)",
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
        assert_eq!(counts, (1, 2, 0));
    }

    #[test]
    fn exact_context_union_rejects_wrong_members_and_supports_metadata() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::ContextUnion, "source", MetadataType::Text)
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::ContextUnion,
                "union source",
                ["source"],
                false,
            )
            .unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(AllowAll, schema).unwrap();
        let p = connection.insert_free_term(50, BOOL_TYPE_ID).unwrap();
        let q = connection.insert_free_term(51, BOOL_TYPE_ID).unwrap();
        let r = connection.insert_free_term(52, BOOL_TYPE_ID).unwrap();
        let left = connection.define_context([p]).unwrap();
        let right = connection.define_context([q]).unwrap();
        let missing = left;
        let exact = connection.define_context([p, q]).unwrap();
        let unexpected = connection.define_context([p, q, r]).unwrap();
        connection
            .with_proof_session(|mut proof| {
                assert!(matches!(
                    proof.prove_context_union(left, right, missing),
                    Err(ProofError::ContextUnionMissingMember { term, .. }) if term == q
                ));
                assert!(matches!(
                    proof.prove_context_union(left, right, unexpected),
                    Err(ProofError::ContextUnionUnexpectedMember { term, .. }) if term == r
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "INSERT INTO hol_context_exact_union(
                     left_ctx_id, right_ctx_id, result_ctx_id
                 ) VALUES (?1, ?2, ?3)",
                (left.get(), right.get(), missing.get()),
            )
            .unwrap();
        connection
            .with_proof_session(|mut proof| {
                assert!(matches!(
                    proof.load_context_union(left, right),
                    Err(ProofError::ContextUnionMissingMember { term, .. }) if term == q
                ));
                assert!(matches!(
                    proof.prove_context_union(left, right, exact),
                    Err(ProofError::ContextUnionConflict {
                        stored_result,
                        requested_result,
                        ..
                    }) if stored_result == missing && requested_result == exact
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "DELETE FROM hol_context_exact_union
                 WHERE left_ctx_id = ?1 AND right_ctx_id = ?2",
                (left.get(), right.get()),
            )
            .unwrap();
        connection
            .with_proof_session(|mut proof| {
                proof.prove_context_union(left, right, exact).map(|_| ())
            })
            .unwrap();
        let target = MetadataTarget::context_union(left, right);
        connection
            .set_metadata(
                target,
                &[("source", MetadataValue::Text("structural".to_owned()))],
            )
            .unwrap();
        assert_eq!(
            connection.metadata(target, &["source"]).unwrap(),
            [MetadataValue::Text("structural".to_owned())]
        );
    }

    #[test]
    fn exact_context_union_policy_denial_is_atomic() {
        let mut denied = Connection::open_hol_in_memory(RecordingPolicy::default()).unwrap();
        assert!(matches!(
            denied.with_proof_session(|mut proof| proof
                .prove_context_union(ContextId::empty(), ContextId::empty(), ContextId::empty())
                .map(|_| ())),
            Err(ProofError::Denied(Operation::ProveContextUnion))
        ));
        let (neutron, hol) = denied.parts_mut();
        assert_eq!(hol.policy.operations, [Operation::ProveContextUnion]);
        assert_eq!(
            neutron
                .sqlite()
                .query_row("SELECT count(*) FROM hol_context_exact_union", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            0
        );
    }

    #[test]
    fn context_equivalence_is_only_two_opposite_implications() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let p = connection.insert_free_term(60, BOOL_TYPE_ID).unwrap();
        let equality = connection.insert_equality(p, p).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let left = connection.define_context([equality]).unwrap();
        let right = connection.define_context([truth]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let truth_witness = proof.prove_truth(left)?;
                let forward = proof.prove_context_implication(left, right, &[truth_witness])?;
                let equality_witness = proof.prove_reflexivity(right, p)?;
                let backward = proof.prove_context_implication(right, left, &[equality_witness])?;
                assert!(matches!(
                    proof.prove_context_equivalence(&forward, &forward),
                    Err(ProofError::ContextEquivalenceMismatch { .. })
                ));
                let equivalence = proof.prove_context_equivalence(&forward, &backward)?;
                assert_eq!(equivalence.left(), left);
                assert_eq!(equivalence.right(), right);
                proof.persist_context_implication(&forward)?;
                proof.persist_context_implication(&backward)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();

        let rows = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_context_implication", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 2);
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
                let theorem = proof.prove_hypothesis(context, term)?;
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(theorem.conclusion())
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

    #[test]
    fn schematic_types_are_canonical_rank_zero_and_constants_remain_monomorphic() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(-10).unwrap();
        assert_eq!(connection.insert_free_type(-10).unwrap(), alpha);
        assert_eq!(
            connection.type_view(alpha).unwrap(),
            TypeView::Free { symbol: -10 }
        );
        assert_eq!(connection.type_kind(alpha).unwrap(), STAR_ID);
        assert!(connection.type_is_locally_closed(alpha).unwrap());

        let arrow = connection.insert_arrow_type(alpha, alpha).unwrap();
        assert_eq!(connection.type_free_variables(arrow).unwrap(), [alpha]);
        let variable = connection.insert_free_term(900, arrow).unwrap();
        assert_eq!(
            connection.term_free_type_variables(variable).unwrap(),
            [alpha]
        );

        let node_count = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert!(matches!(
            connection.insert_constant(901, arrow),
            Err(TermError::PolymorphicConstantType { symbol: 901, ty }) if ty == arrow
        ));
        assert_eq!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_node", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            node_count
        );
    }

    #[test]
    fn type_instantiation_is_simultaneous_and_rebuilds_the_exact_context() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(1000).unwrap();
        let beta = connection.insert_free_type(1001).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();

        let alpha_predicate_type = connection.insert_arrow_type(alpha, bool_type).unwrap();
        let predicate = connection
            .insert_free_term(1002, alpha_predicate_type)
            .unwrap();
        let epsilon = connection.insert_epsilon(predicate).unwrap();
        let selected = connection.insert_application(predicate, epsilon).unwrap();

        let alpha_bound = connection.insert_bound_term(0, alpha).unwrap();
        let alpha_identity = connection.insert_lambda(alpha, alpha_bound).unwrap();
        let identity_reflexivity = connection
            .insert_equality(alpha_identity, alpha_identity)
            .unwrap();
        let beta_variable = connection.insert_free_term(1003, beta).unwrap();
        let beta_reflexivity = connection
            .insert_equality(beta_variable, beta_variable)
            .unwrap();
        let source_context = connection
            .define_context([selected, identity_reflexivity, beta_reflexivity])
            .unwrap();

        let beta_predicate_type = connection.insert_arrow_type(beta, bool_type).unwrap();
        let expected_predicate = connection
            .insert_free_term(1002, beta_predicate_type)
            .unwrap();
        let expected_epsilon = connection.insert_epsilon(expected_predicate).unwrap();
        let expected_selected = connection
            .insert_application(expected_predicate, expected_epsilon)
            .unwrap();
        let beta_bound = connection.insert_bound_term(0, beta).unwrap();
        let beta_identity = connection.insert_lambda(beta, beta_bound).unwrap();
        let expected_identity = connection
            .insert_equality(beta_identity, beta_identity)
            .unwrap();
        let bool_variable = connection.insert_free_term(1003, bool_type).unwrap();
        let expected_bool_reflexivity = connection
            .insert_equality(bool_variable, bool_variable)
            .unwrap();
        let expected_context = connection
            .define_context([
                expected_selected,
                expected_identity,
                expected_bool_reflexivity,
            ])
            .unwrap();

        let (actual_context, actual_conclusion) = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(source_context, selected)?;
                let instantiated = proof.instantiate_types(
                    &theorem,
                    &[
                        TypeInstantiation {
                            variable: alpha,
                            replacement: beta,
                        },
                        TypeInstantiation {
                            variable: beta,
                            replacement: bool_type,
                        },
                    ],
                )?;
                proof.persist_theorem(&instantiated)?;
                Ok::<_, ProofError>((instantiated.context(), instantiated.conclusion()))
            })
            .unwrap();
        assert_eq!(actual_context, expected_context);
        assert_eq!(actual_conclusion, expected_selected);
        assert_eq!(
            connection
                .term_free_type_variables(actual_conclusion)
                .unwrap(),
            [beta]
        );
        let rule = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT rule FROM hol_proof_event WHERE ctx_id = ?1 AND term_id = ?2",
                [actual_context.get(), actual_conclusion.get()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(rule, "type_instantiation");
    }

    #[test]
    fn type_instantiation_rejects_invalid_maps_without_writes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(1100).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(1101, alpha).unwrap();
        let equality = connection.insert_equality(x, x).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(ContextId::empty(), x)?;
                assert!(matches!(
                    proof.instantiate_types(
                        &theorem,
                        &[TypeInstantiation { variable: bool_type, replacement: alpha }]
                    ),
                    Err(ProofError::TypeInstantiationKeyNotFree(ty)) if ty == bool_type
                ));
                assert!(matches!(
                    proof.instantiate_types(
                        &theorem,
                        &[
                            TypeInstantiation { variable: alpha, replacement: bool_type },
                            TypeInstantiation { variable: alpha, replacement: bool_type },
                        ]
                    ),
                    Err(ProofError::DuplicateTypeInstantiation(ty)) if ty == alpha
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
        assert_eq!(connection.term_type(equality).unwrap(), bool_type);
        assert_eq!(
            connection
                .parts_mut()
                .0
                .sqlite()
                .query_row("SELECT count(*) FROM hol_node", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            before
        );
    }

    #[test]
    fn type_instantiation_collapses_exact_free_terms_and_deduplicates_contexts() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(1200).unwrap();
        let beta = connection.insert_free_type(1201).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x_alpha = connection.insert_free_term(1202, alpha).unwrap();
        let x_beta = connection.insert_free_term(1202, beta).unwrap();
        let alpha_eq = connection.insert_equality(x_alpha, x_alpha).unwrap();
        let beta_eq = connection.insert_equality(x_beta, x_beta).unwrap();
        let context = connection.define_context([alpha_eq, beta_eq]).unwrap();
        let x_bool = connection.insert_free_term(1202, bool_type).unwrap();
        let expected = connection.insert_equality(x_bool, x_bool).unwrap();
        let expected_context = connection.define_context([expected]).unwrap();

        let (actual_context, conclusion) = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_hypothesis(context, alpha_eq)?;
                let instantiated = proof.instantiate_types(
                    &theorem,
                    &[
                        TypeInstantiation {
                            variable: alpha,
                            replacement: bool_type,
                        },
                        TypeInstantiation {
                            variable: beta,
                            replacement: bool_type,
                        },
                    ],
                )?;
                Ok::<_, ProofError>((instantiated.context(), instantiated.conclusion()))
            })
            .unwrap();
        assert_eq!(actual_context, expected_context);
        assert_eq!(conclusion, expected);
        assert_eq!(
            connection.context_members(actual_context).unwrap(),
            [expected]
        );
    }

    #[test]
    fn type_instantiation_checks_all_policy_gates_before_database_work() {
        for denied in [
            Operation::ProveTypeInstantiation,
            Operation::InsertType,
            Operation::InsertTerm,
            Operation::DefineContext,
        ] {
            let armed = Rc::new(Cell::new(false));
            let mut connection = Connection::open_hol_in_memory(ArmedDenial {
                operation: denied,
                armed: Rc::clone(&armed),
            })
            .unwrap();
            let alpha = connection.insert_free_type(1300).unwrap();
            let x = connection.insert_free_term(1301, alpha).unwrap();
            let context = connection.define_context([]).unwrap();
            let result = connection.with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(context, x)?;
                armed.set(true);
                proof
                    .instantiate_types(
                        &theorem,
                        &[TypeInstantiation {
                            variable: TypeId::from_i64(999_999),
                            replacement: TypeId::from_i64(999_998),
                        }],
                    )
                    .map(|_| ())
            });
            let expected = match denied {
                Operation::DefineContext => ProofError::Context(ContextError::Denied(denied)),
                _ => ProofError::Denied(denied),
            };
            assert_eq!(result.unwrap_err().to_string(), expected.to_string());
        }
    }

    #[test]
    fn type_instantiation_rolls_back_partial_syntax_when_context_interning_fails() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(1400).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x = connection.insert_free_term(1401, alpha).unwrap();
        let proposition = connection.insert_equality(x, x).unwrap();
        let context = connection.define_context([proposition]).unwrap();
        let before = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row("SELECT count(*) FROM hol_node", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch(
                "CREATE TEMP TRIGGER reject_type_instantiated_context
                 BEFORE INSERT ON hol_context
                 BEGIN
                   SELECT RAISE(ABORT, 'test type context rejection');
                 END",
            )
            .unwrap();

        let result = connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_hypothesis(context, proposition)?;
            proof
                .instantiate_types(
                    &theorem,
                    &[TypeInstantiation {
                        variable: alpha,
                        replacement: bool_type,
                    }],
                )
                .map(|_| ())
        });
        assert!(matches!(
            result,
            Err(ProofError::Context(ContextError::Sqlite(_)))
        ));
        let sqlite = connection.parts_mut().0.sqlite();
        assert_eq!(
            sqlite
                .query_row("SELECT count(*) FROM hol_node", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            before
        );
        assert!(
            sqlite
                .query_row(
                    "SELECT NOT EXISTS(
                         SELECT 1 FROM hol_node
                         WHERE tag = 'MFV' AND lhs = 1401 AND ty = ?1
                     )",
                    [bool_type.get()],
                    |row| row.get::<_, bool>(0),
                )
                .unwrap()
        );
    }

    #[test]
    fn rank_zero_polymorphic_identity_is_canonical_and_instantiates() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_bound_type(0).unwrap();
        let variable = connection.insert_bound_term(0, alpha).unwrap();
        let identity = connection.insert_lambda(alpha, variable).unwrap();
        let polymorphic = connection.insert_type_lambda(identity).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let instantiated = connection
            .insert_type_application(polymorphic, bool_type)
            .unwrap();
        let bool_identity = connection.insert_arrow_type(bool_type, bool_type).unwrap();

        assert_eq!(connection.term_type(instantiated).unwrap(), bool_identity);
        assert_eq!(
            connection.term(polymorphic).unwrap(),
            TermView::TypeLambda { body: identity }
        );
        assert!(connection.term_is_locally_closed(polymorphic).unwrap());
        assert!(
            connection
                .term_unbound_type_variables(polymorphic)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            instantiated,
            connection
                .insert_type_application(polymorphic, bool_type)
                .unwrap()
        );
    }

    #[test]
    fn bound_type_substitution_lifts_under_nested_forall() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let inner = connection.insert_bound_type(0).unwrap();
        let outer = connection.insert_bound_type(1).unwrap();
        let pair = connection.insert_arrow_type(outer, inner).unwrap();
        let nested = connection.insert_forall_type(pair).unwrap();
        let universal = connection.insert_forall_type(nested).unwrap();
        let constant = connection.insert_constant(9_001, universal).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let instantiated = connection
            .insert_type_application(constant, bool_type)
            .unwrap();
        let expected_body = connection.insert_arrow_type(bool_type, inner).unwrap();
        let expected = connection.insert_forall_type(expected_body).unwrap();

        assert_eq!(connection.term_type(instantiated).unwrap(), expected);
    }

    #[test]
    fn bound_type_shift_memo_distinguishes_different_amounts() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let replacement = connection.insert_bound_type(0).unwrap();
        let at_depth_one = connection.insert_bound_type(1).unwrap();
        let at_depth_two = connection.insert_bound_type(2).unwrap();
        let beneath_one = connection.insert_forall_type(at_depth_one).unwrap();
        let beneath_two_inner = connection.insert_forall_type(at_depth_two).unwrap();
        let beneath_two = connection.insert_forall_type(beneath_two_inner).unwrap();
        let body = connection
            .insert_arrow_type(beneath_one, beneath_two)
            .unwrap();
        let universal = connection.insert_forall_type(body).unwrap();
        let constant = connection.insert_constant(9_010, universal).unwrap();

        let instantiated = connection
            .insert_type_application(constant, replacement)
            .unwrap();

        assert_eq!(connection.term_type(instantiated).unwrap(), body);
        let TypeView::Arrow { domain, codomain } = connection.type_view(body).unwrap() else {
            panic!("expected substituted arrow type")
        };
        assert_eq!(domain, beneath_one);
        assert_eq!(codomain, beneath_two);
    }

    #[test]
    fn type_lambda_rejects_external_and_schematic_term_environments() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let external = connection.insert_bound_term(0, bool_type).unwrap();
        assert!(matches!(
            connection.insert_type_lambda(external),
            Err(TermError::TypeLambdaOpenTermBody(term)) if term == external
        ));

        let free = connection.insert_free_term(9_002, bool_type).unwrap();
        assert!(matches!(
            connection.insert_type_lambda(free),
            Err(TermError::TypeLambdaFreeTermBody(term)) if term == free
        ));
    }

    #[test]
    fn erased_type_annotations_keep_boolean_results_type_open() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_bound_type(0).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let function_type = connection.insert_arrow_type(alpha, bool_type).unwrap();
        let function = connection.insert_free_term(9_003, function_type).unwrap();
        let argument = connection.insert_free_term(9_004, alpha).unwrap();
        let proposition = connection.insert_application(function, argument).unwrap();

        assert_eq!(connection.term_type(proposition).unwrap(), bool_type);
        assert!(!connection.term_is_locally_closed(proposition).unwrap());
        assert_eq!(
            connection.term_unbound_type_variables(proposition).unwrap(),
            [UnboundTypeVariable {
                index: 0,
                kind: STAR_ID,
            }]
        );
        assert!(matches!(
            connection.define_context([proposition]),
            Err(ContextError::OpenMember(term)) if term == proposition
        ));
    }

    #[test]
    fn constants_accept_closed_universals_and_reject_open_types() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_bound_type(0).unwrap();
        let universal = connection.insert_forall_type(alpha).unwrap();
        assert!(connection.insert_constant(9_005, universal).is_ok());
        assert!(matches!(
            connection.insert_constant(9_006, alpha),
            Err(TermError::OpenConstantType { symbol: 9_006, ty }) if ty == alpha
        ));
        let schematic = connection.insert_free_type(9_007).unwrap();
        assert!(matches!(
            connection.insert_constant(9_008, schematic),
            Err(TermError::PolymorphicConstantType { symbol: 9_008, ty }) if ty == schematic
        ));
    }

    #[test]
    fn schematic_type_instantiation_traverses_type_lambdas_and_rejects_open_replacements() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(9_009).unwrap();
        let variable = connection.insert_bound_term(0, alpha).unwrap();
        let identity = connection.insert_lambda(alpha, variable).unwrap();
        let polymorphic = connection.insert_type_lambda(identity).unwrap();
        let context = ContextId::empty();
        let bool_type = connection.insert_bool_type().unwrap();

        let instantiated_conclusion = connection
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_reflexivity(context, polymorphic)?;
                let instantiated = proof.instantiate_types(
                    &theorem,
                    &[TypeInstantiation {
                        variable: alpha,
                        replacement: bool_type,
                    }],
                )?;
                Ok::<_, ProofError>(instantiated.conclusion())
            })
            .unwrap();
        let TermView::Equality { left, right } = connection.term(instantiated_conclusion).unwrap()
        else {
            panic!("expected instantiated reflexive equality")
        };
        assert_eq!(left, right);
        let TermView::TypeLambda { body } = connection.term(left).unwrap() else {
            panic!("expected instantiated type abstraction")
        };
        let TermView::Lambda { parameter_type, .. } = connection.term(body).unwrap() else {
            panic!("expected instantiated term abstraction")
        };
        assert_eq!(parameter_type, bool_type);

        let open = connection.insert_bound_type(0).unwrap();
        let result = connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_truth(context)?;
            proof
                .instantiate_types(
                    &theorem,
                    &[TypeInstantiation {
                        variable: alpha,
                        replacement: open,
                    }],
                )
                .map(|_| ())
        });
        assert!(matches!(
            result,
            Err(ProofError::OpenTypeInstantiationReplacement(ty)) if ty == open
        ));
    }
}
