//! Semi-trusted, exhaustive `SpecTec`-to-HOL compilation records.
//!
//! This crate owns correspondence bookkeeping, not theorem authority. A
//! lowering mutates a transactional [`Kernel`] only through its public checked
//! API, then binds every source declaration to one or more resident rows. The
//! finished DRISL record links exact input and kernel bytes and remains
//! independently discardable audit metadata.

use std::collections::{BTreeMap, BTreeSet};

mod add_slice;
mod closure;
mod document;
mod expression;
mod grammar;
mod grammar_definition;
mod parameterized;
mod premise;
mod program_logic;
mod relational;
mod schema;
mod selected;
mod theory;
mod type_definition;
mod types;

pub use add_slice::{
    ADD_SLICE_TYPE_NAME, AddSliceArtifact, AddSliceArtifactError, AddSliceError, AddSlicePlan,
    ClauseCoverage, Coverage, CoverageArtifact, CoverageDisposition, CoverageParts, CoveragePlan,
    DeclarationCoverage, Disposition, Rejection, RuleCoverage, SourceSpan, TranslationCase,
};
pub use closure::{
    HolRule, LeastFamilyBuilder, LeastPredicate, LeastPredicateError, begin_least_closed_family,
    begin_least_closed_family_avoiding, close_hol_rule, close_hol_rules, least_closed_family,
    least_closed_predicate,
};
pub use document::{RelationalDocumentDefinition, relational_document};
pub use expression::{ExpressionAlgebra, fold_expression};
pub use grammar::{GrammarAlgebra, GrammarArgument, GrammarChildren, fold_grammar};
pub use grammar_definition::{RelationalGrammarDefinition, relational_grammar_declaration};
pub use parameterized::{
    InterpretationKind, InterpretationSignature, InterpretationSymbol, ParameterizedDocument,
    ParameterizedError, parameterized_document, parameterized_document_with,
};
pub use premise::{PremiseAlgebra, PremiseChildren, fold_premise};
pub use program_logic::{AssertCombinator, CallsAssert, Established, Evidence, Proposition};
pub use relational::{
    RelationalCall, RelationalCaseError, RelationalClause, RelationalCondition,
    RelationalDefinition, RelationalDefinitionSchema, RelationalDefinitionSource,
    RelationalExpressionAlgebra, RelationalRelation, RelationalRelationDefinition,
    RelationalResolver, RelationalTerm, relational_definition, relational_definition_declaration,
    relational_definition_schema, relational_hol_case, relational_hol_rule,
    relational_relation_declaration, relational_relations, relational_relations_avoiding,
};
pub use schema::{
    HolDeclaration, HolEmbedding, HolSchema, HolSchemaError, IndexErasure, declare_hol_schema,
};
pub use selected::{SelectedCompileError, SelectedCompiler, SelectedKernel, SelectedRoot};
pub use theory::{
    HolCase, HolFamilyBranch, HolFamilyDefinition, HolFamilyError, HolTheory, HolTheoryError,
    close_family_definition, close_graph_equation, close_hol_theory, conjoin_constraints,
    existential_case, ordered_cases,
};
pub use type_definition::{RelationalTypeDefinition, relational_type_declaration};
pub use types::{TypeAlgebra, TypeArgument, TypeChildren, fold_type};

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash, Policy, Value};
use covalence_data_spectec::{
    DeclarationId, IlDeclaration, IlDocument, IlKind, Wasm3Bundle, wasm3_bundle,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Arena, Kernel, KernelError, Ref, Sort, wire};

/// Closed-record discriminator for a `SpecTec` compilation.
pub const TYPE_NAME: &str = "io.github.imbrem.nucleus.spectecCompilationV1";

/// Exact source identity and declaration inventory consumed by a compiler.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Source {
    bundle: Cid,
    ast: Cid,
    release: String,
    revision: String,
    il: IlDocument,
    declarations: Vec<SourceDeclaration>,
}

impl Source {
    /// Builds source metadata from a verified IL document.
    ///
    /// # Errors
    ///
    /// Returns an error unless the bundle is a SHA-256 DRISL CID, the AST is a
    /// SHA-256 raw CID, and declaration selectors are unique.
    pub fn new(
        bundle: Cid,
        ast: Cid,
        release: impl Into<String>,
        revision: impl Into<String>,
        il: &IlDocument,
    ) -> Result<Self, CompileError> {
        if bundle.codec() != CidCodec::Drisl || bundle.hash() != CidHash::Sha256 {
            return Err(CompileError::SourceLink {
                field: "bundle",
                expected: "SHA-256 DRISL CID",
            });
        }
        if ast.codec() != CidCodec::Raw || ast.hash() != CidHash::Sha256 {
            return Err(CompileError::SourceLink {
                field: "ast",
                expected: "SHA-256 raw CID",
            });
        }
        let declarations = il
            .declarations()
            .iter()
            .map(SourceDeclaration::from)
            .collect::<Vec<_>>();
        let unique = declarations
            .iter()
            .map(|declaration| declaration.id)
            .collect::<BTreeSet<_>>();
        if unique.len() != declarations.len() {
            return Err(CompileError::DuplicateSourceSelector);
        }
        Ok(Self {
            bundle,
            ast,
            release: release.into(),
            revision: revision.into(),
            il: il.clone(),
            declarations,
        })
    }

    /// Loads the repository's complete pinned WebAssembly 3.0 input.
    ///
    /// # Errors
    ///
    /// Returns an error if the offline bundle or its source identity fails any
    /// byte, schema, resource, inventory, or CID check.
    pub fn wasm3() -> Result<Self, CompileError> {
        let bundle = wasm3_bundle().map_err(|source| CompileError::Wasm3 { source })?;
        Self::from_wasm3(&bundle)
    }

    /// Constructs source metadata from an already verified WebAssembly bundle.
    ///
    /// # Errors
    ///
    /// Returns an error if the verified bundle carries a link outside the
    /// compilation-record profile or duplicate declaration selectors.
    pub fn from_wasm3(bundle: &Wasm3Bundle) -> Result<Self, CompileError> {
        Self::new(
            bundle.manifest_cid(),
            bundle.manifest().ast.artifact.cid,
            &bundle.manifest().release,
            &bundle.manifest().revision,
            bundle.il(),
        )
    }

    /// Returns the number of declarations that must be lowered.
    #[must_use]
    pub fn declaration_count(&self) -> usize {
        self.declarations.len()
    }

    /// Returns the canonical source-bundle link.
    #[must_use]
    pub const fn bundle(&self) -> Cid {
        self.bundle
    }

    /// Returns the exact elaborated-AST link.
    #[must_use]
    pub const fn ast(&self) -> Cid {
        self.ast
    }

    /// Returns the upstream release name.
    #[must_use]
    pub fn release(&self) -> &str {
        &self.release
    }

    /// Returns the exact upstream revision.
    #[must_use]
    pub fn revision(&self) -> &str {
        &self.revision
    }

    /// Returns the complete bounded elaborated IL document.
    #[must_use]
    pub const fn il(&self) -> &IlDocument {
        &self.il
    }

    /// Returns declarations in exact elaborated source order.
    #[must_use]
    pub fn declarations(&self) -> &[SourceDeclaration] {
        &self.declarations
    }
}

/// One declaration that an exhaustive lowering must account for.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceDeclaration {
    id: DeclarationId,
    kind: IlKind,
    name: String,
}

impl SourceDeclaration {
    /// Returns the stable structural selector.
    #[must_use]
    pub const fn id(&self) -> DeclarationId {
        self.id
    }

    /// Returns the declaration form.
    #[must_use]
    pub const fn kind(&self) -> IlKind {
        self.kind
    }

    /// Returns the exact elaborated name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl From<&IlDeclaration> for SourceDeclaration {
    fn from(declaration: &IlDeclaration) -> Self {
        Self {
            id: declaration.id(),
            kind: declaration.kind(),
            name: declaration.name().to_owned(),
        }
    }
}

/// One role-labelled kernel row returned by a declaration lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KernelRoot {
    role: String,
    reference: Ref,
}

impl KernelRoot {
    /// Names one checked row's role in a declaration lowering.
    #[must_use]
    pub fn new(role: impl Into<String>, reference: Ref) -> Self {
        Self {
            role: role.into(),
            reference,
        }
    }

    /// Returns the local arena reference.
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }

    /// Returns the source-local role name.
    #[must_use]
    pub fn role(&self) -> &str {
        &self.role
    }
}

/// Transactional compiler state with exact source-coverage bookkeeping.
#[derive(Debug)]
pub struct Compiler {
    source: Source,
    kernel: Kernel,
    bindings: BTreeMap<DeclarationId, Vec<BoundRoot>>,
}

impl Compiler {
    /// Starts an exhaustive compilation over an existing checked kernel.
    ///
    /// The initial kernel normally contains the generic HOL/init library needed
    /// by the lowering. Those rows are not attributed to a `SpecTec` declaration.
    #[must_use]
    pub fn new(source: Source, kernel: Kernel) -> Self {
        Self {
            source,
            kernel,
            bindings: BTreeMap::new(),
        }
    }

    /// Borrows the current checked state for resolving earlier outputs.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Borrows the exact source inventory being compiled.
    #[must_use]
    pub const fn source(&self) -> &Source {
        &self.source
    }

    /// Returns the number of declarations already accounted for.
    #[must_use]
    pub fn completed(&self) -> usize {
        self.bindings.len()
    }

    /// Returns the checked roots already recorded for a declaration.
    #[must_use]
    pub fn roots(&self, id: DeclarationId) -> Option<&[BoundRoot]> {
        self.bindings.get(&id).map(Vec::as_slice)
    }

    /// Resolves one previously recorded role to its checked row.
    #[must_use]
    pub fn resolve(&self, id: DeclarationId, role: &str) -> Option<Ref> {
        self.roots(id)?
            .iter()
            .find(|root| root.role == role)
            .map(|root| root.reference)
    }

    /// Lowers one declaration transactionally and records all of its roots.
    ///
    /// The callback receives a fork. Its mutations are committed only after it
    /// returns a nonempty set of uniquely named, resident checked rows. A
    /// declaration may bind an existing row when it is an alias.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or repeated selector, a checked kernel
    /// rejection, no roots, duplicate or empty roles, or a missing row.
    pub fn lower<F>(&mut self, id: DeclarationId, operation: F) -> Result<(), CompileError>
    where
        F: FnOnce(&mut Kernel) -> Result<Vec<KernelRoot>, KernelError>,
    {
        if !self
            .source
            .declarations
            .iter()
            .any(|source| source.id == id)
        {
            return Err(CompileError::UnknownDeclaration { id });
        }
        if self.bindings.contains_key(&id) {
            return Err(CompileError::DuplicateDeclaration { id });
        }
        let mut staged = self.kernel.fork();
        let roots = operation(&mut staged).map_err(|source| CompileError::Kernel { source })?;
        if roots.is_empty() {
            return Err(CompileError::NoRoots { id });
        }
        let mut roles = BTreeSet::new();
        let mut bound = Vec::with_capacity(roots.len());
        for root in roots {
            if root.role.is_empty() {
                return Err(CompileError::EmptyRole { id });
            }
            if !roles.insert(root.role.clone()) {
                return Err(CompileError::DuplicateRole {
                    id,
                    role: root.role,
                });
            }
            let sort = staged
                .category(root.reference)
                .map_err(|source| CompileError::Kernel { source })?;
            bound.push(BoundRoot {
                role: root.role,
                reference: root.reference,
                sort,
            });
        }
        self.kernel = staged;
        self.bindings.insert(id, bound);
        Ok(())
    }

    /// Freezes a complete compilation and its portable correspondence record.
    ///
    /// # Errors
    ///
    /// Returns the first source declaration that has not been lowered, or a
    /// kernel-CBOR/DRISL encoding failure.
    pub fn finish(self) -> Result<SpecTecKernel, CompileError> {
        for declaration in &self.source.declarations {
            if !self.bindings.contains_key(&declaration.id) {
                return Err(CompileError::MissingDeclaration { id: declaration.id });
            }
        }
        let mut kernel_cbor = Vec::new();
        wire::serialize(self.kernel.arena(), &mut kernel_cbor)
            .map_err(|source| CompileError::KernelEncode { source })?;
        let kernel = drisl::address(CidCodec::Raw, CidHash::Sha256, &kernel_cbor);
        let kernel_blake3 = self.kernel.arena().addr().into_bytes();
        let declarations = self
            .source
            .declarations
            .iter()
            .map(|source| DeclarationRecord {
                id: source.id,
                kind: source.kind,
                name: source.name.clone(),
                roots: self.bindings[&source.id].clone(),
            })
            .collect();
        let record = CompilationRecord {
            bundle: self.source.bundle,
            ast: self.source.ast,
            kernel,
            kernel_blake3,
            release: self.source.release,
            revision: self.source.revision,
            declarations,
        };
        let record_drisl = record.encode()?;
        Ok(SpecTecKernel {
            kernel: self.kernel,
            record,
            kernel_cbor,
            record_drisl,
        })
    }
}

/// One source declaration's checked kernel correspondence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationRecord {
    id: DeclarationId,
    kind: IlKind,
    name: String,
    roots: Vec<BoundRoot>,
}

impl DeclarationRecord {
    /// Returns the stable source selector.
    #[must_use]
    pub const fn id(&self) -> DeclarationId {
        self.id
    }

    /// Returns the elaborated declaration form.
    #[must_use]
    pub const fn kind(&self) -> IlKind {
        self.kind
    }

    /// Returns the exact elaborated declaration name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns all role-labelled checked rows.
    #[must_use]
    pub fn roots(&self) -> &[BoundRoot] {
        &self.roots
    }
}

/// A role-labelled checked row recorded in the portable correspondence map.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundRoot {
    role: String,
    reference: Ref,
    sort: Sort,
}

impl BoundRoot {
    /// Returns the correspondence role.
    #[must_use]
    pub fn role(&self) -> &str {
        &self.role
    }

    /// Returns the exact local kernel reference.
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }

    /// Returns the checked syntactic category.
    #[must_use]
    pub const fn sort(&self) -> Sort {
        self.sort
    }
}

/// Portable `ATProto` record linking source, kernel, and complete correspondence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilationRecord {
    bundle: Cid,
    ast: Cid,
    kernel: Cid,
    kernel_blake3: [u8; 32],
    release: String,
    revision: String,
    declarations: Vec<DeclarationRecord>,
}

impl CompilationRecord {
    /// Returns the canonical source-bundle link.
    #[must_use]
    pub const fn bundle(&self) -> Cid {
        self.bundle
    }

    /// Returns the exact elaborated-AST link.
    #[must_use]
    pub const fn ast(&self) -> Cid {
        self.ast
    }

    /// Returns the raw SHA-256 CID of the exact kernel CBOR bytes.
    #[must_use]
    pub const fn kernel(&self) -> Cid {
        self.kernel
    }

    /// Returns the current Ethane BLAKE3 address as compatibility metadata.
    #[must_use]
    pub const fn kernel_blake3(&self) -> [u8; 32] {
        self.kernel_blake3
    }

    /// Returns the upstream release name.
    #[must_use]
    pub fn release(&self) -> &str {
        &self.release
    }

    /// Returns the exact upstream revision.
    #[must_use]
    pub fn revision(&self) -> &str {
        &self.revision
    }

    /// Returns declaration mappings in source order.
    #[must_use]
    pub fn declarations(&self) -> &[DeclarationRecord] {
        &self.declarations
    }

    /// Checks that this record exhaustively describes one verified source.
    ///
    /// This compares exact links, release identity, declaration order,
    /// selectors, forms, and names. It does not inspect the linked kernel; use
    /// [`verify_kernel`](Self::verify_kernel) for that independent check.
    ///
    /// # Errors
    ///
    /// Returns an error at the first source-identity or inventory mismatch.
    pub fn verify_source(&self, source: &Source) -> Result<(), ArtifactError> {
        if self.bundle != source.bundle {
            return Err(ArtifactError::SourceMismatch {
                reason: "bundle CID differs",
            });
        }
        if self.ast != source.ast {
            return Err(ArtifactError::SourceMismatch {
                reason: "AST CID differs",
            });
        }
        if self.release != source.release {
            return Err(ArtifactError::SourceMismatch {
                reason: "release name differs",
            });
        }
        if self.revision != source.revision {
            return Err(ArtifactError::SourceMismatch {
                reason: "revision differs",
            });
        }
        if self.declarations.len() != source.declarations.len() {
            return Err(ArtifactError::SourceMismatch {
                reason: "declaration count differs",
            });
        }
        for (record, expected) in self.declarations.iter().zip(&source.declarations) {
            if record.id != expected.id {
                return Err(ArtifactError::SourceMismatch {
                    reason: "declaration selector differs",
                });
            }
            if record.kind != expected.kind {
                return Err(ArtifactError::SourceMismatch {
                    reason: "declaration kind differs",
                });
            }
            if record.name != expected.name {
                return Err(ArtifactError::SourceMismatch {
                    reason: "declaration name differs",
                });
            }
        }
        Ok(())
    }

    /// Encodes this closed record in canonical `ATProto` DRISL form.
    ///
    /// # Errors
    ///
    /// Returns an error if deterministic DRISL encoding rejects the value.
    pub fn encode(&self) -> Result<Vec<u8>, CompileError> {
        drisl::encode(Policy::ATPROTO, &self.to_value())
            .map_err(|source| CompileError::RecordEncode { source })
    }

    /// Decodes one exact canonical `ATProto` compilation record.
    ///
    /// This validates the closed schema, CID families, selectors, roles, and
    /// row-reference domains. It does not fetch or trust the linked kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for noncanonical DRISL, an unknown or missing field,
    /// a wrong scalar type, an invalid selector or reference, duplicate
    /// coverage, or a link outside the normal-form SHA-256 profile.
    pub fn decode(bytes: &[u8]) -> Result<Self, ArtifactError> {
        let value = drisl::decode(Policy::ATPROTO, bytes)
            .map_err(|source| ArtifactError::RecordDecode { source })?;
        record_from_value(&value)
    }

    /// Verifies and decodes the exact kernel bytes linked by this record.
    ///
    /// The result is a raw arena suitable for checked import. This operation
    /// establishes byte identity, canonical arena decoding, and correspondence
    /// reference categories; it does not create a [`Kernel`] or theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error for a CID mismatch, invalid arena CBOR, a BLAKE3
    /// compatibility-address mismatch, a missing row, or a category mismatch.
    pub fn verify_kernel(&self, bytes: &[u8]) -> Result<Arena, ArtifactError> {
        if !drisl::addresses(self.kernel, bytes) {
            return Err(ArtifactError::KernelAddress);
        }
        let arena =
            wire::deserialize(bytes).map_err(|source| ArtifactError::KernelDecode { source })?;
        if arena.addr().into_bytes() != self.kernel_blake3 {
            return Err(ArtifactError::KernelBlake3);
        }
        for declaration in &self.declarations {
            for root in &declaration.roots {
                let Some(tag) = arena.tag(root.reference) else {
                    return Err(ArtifactError::MissingReference {
                        id: declaration.id,
                        role: root.role.clone(),
                        reference: root.reference,
                    });
                };
                let actual = tag.sort();
                if actual != root.sort {
                    return Err(ArtifactError::SortMismatch {
                        id: declaration.id,
                        role: root.role.clone(),
                        expected: root.sort,
                        actual,
                    });
                }
            }
        }
        Ok(arena)
    }

    fn to_value(&self) -> Value {
        Value::Map(BTreeMap::from([
            field("$type", Value::Text(TYPE_NAME.to_owned())),
            field("bundle", Value::Link(self.bundle)),
            field("ast", Value::Link(self.ast)),
            field("kernel", Value::Link(self.kernel)),
            field("kernelBlake3", Value::Bytes(self.kernel_blake3.to_vec())),
            field("release", Value::Text(self.release.clone())),
            field("revision", Value::Text(self.revision.clone())),
            field(
                "declarations",
                Value::Array(self.declarations.iter().map(declaration_value).collect()),
            ),
        ]))
    }
}

/// A frozen checked kernel together with its exact portable representation.
#[derive(Debug)]
pub struct SpecTecKernel {
    kernel: Kernel,
    record: CompilationRecord,
    kernel_cbor: Vec<u8>,
    record_drisl: Vec<u8>,
}

impl SpecTecKernel {
    /// Borrows the exact checked kernel built by the lowering.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Forks the complete checked state for a secondary theorem kernel.
    #[must_use]
    pub fn fork(&self) -> Kernel {
        self.kernel.fork()
    }

    /// Borrows the portable source-to-kernel record.
    #[must_use]
    pub const fn record(&self) -> &CompilationRecord {
        &self.record
    }

    /// Borrows the exact canonical kernel CBOR bytes linked by the record.
    #[must_use]
    pub fn kernel_cbor(&self) -> &[u8] {
        &self.kernel_cbor
    }

    /// Borrows the exact canonical `ATProto` DRISL record bytes.
    #[must_use]
    pub fn record_drisl(&self) -> &[u8] {
        &self.record_drisl
    }

    /// Returns the SHA-256 DRISL CID of the compilation record.
    #[must_use]
    pub fn record_cid(&self) -> Cid {
        drisl::address(CidCodec::Drisl, CidHash::Sha256, &self.record_drisl)
    }
}

/// Why an exhaustive compilation could not be recorded.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CompileError {
    /// The pinned WebAssembly input failed offline validation.
    #[snafu(display("could not load pinned Wasm 3.0 input: {source}"))]
    Wasm3 {
        /// Underlying pinned-bundle error.
        source: covalence_data_spectec::Wasm3Error,
    },
    /// A source link used the wrong content kind or hash policy.
    #[snafu(display("SpecTec {field} link must be a {expected}"))]
    SourceLink {
        /// Record field.
        field: &'static str,
        /// Required CID family.
        expected: &'static str,
    },
    /// Two declarations had the same stable selector.
    #[snafu(display("SpecTec source contains a duplicate declaration selector"))]
    DuplicateSourceSelector,
    /// The requested selector is absent from the source inventory.
    #[snafu(display("SpecTec declaration {id:?} is not in the source inventory"))]
    UnknownDeclaration {
        /// Unknown selector.
        id: DeclarationId,
    },
    /// A declaration was lowered twice.
    #[snafu(display("SpecTec declaration {id:?} already has a kernel binding"))]
    DuplicateDeclaration {
        /// Repeated selector.
        id: DeclarationId,
    },
    /// A declaration lowering returned no correspondence roots.
    #[snafu(display("SpecTec declaration {id:?} produced no kernel roots"))]
    NoRoots {
        /// Unaccounted selector.
        id: DeclarationId,
    },
    /// A declaration root used an empty role.
    #[snafu(display("SpecTec declaration {id:?} produced an empty root role"))]
    EmptyRole {
        /// Declaration selector.
        id: DeclarationId,
    },
    /// A declaration repeated a role name.
    #[snafu(display("SpecTec declaration {id:?} repeated root role {role:?}"))]
    DuplicateRole {
        /// Declaration selector.
        id: DeclarationId,
        /// Repeated role.
        role: String,
    },
    /// A checked kernel operation rejected a lowering.
    #[snafu(display("checked SpecTec lowering failed: {source}"))]
    Kernel {
        /// Underlying kernel rejection.
        source: KernelError,
    },
    /// A source declaration remained unaccounted for at freeze time.
    #[snafu(display("SpecTec declaration {id:?} has not been lowered"))]
    MissingDeclaration {
        /// First missing selector in source order.
        id: DeclarationId,
    },
    /// Canonical Ethane CBOR encoding failed.
    #[snafu(display("could not encode SpecTec kernel CBOR: {source}"))]
    KernelEncode {
        /// Underlying arena encoder failure.
        source: wire::EncodeError,
    },
    /// Canonical `ATProto` DRISL encoding failed.
    #[snafu(display("could not encode SpecTec compilation record: {source}"))]
    RecordEncode {
        /// Underlying DRISL encoder failure.
        source: drisl::EncodeError,
    },
}

/// Why a portable compilation record or its linked kernel was rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ArtifactError {
    /// The record was not one exact canonical `ATProto` DRISL item.
    #[snafu(display("could not decode SpecTec compilation record: {source}"))]
    RecordDecode {
        /// Underlying deterministic-profile failure.
        source: drisl::DecodeError,
    },
    /// The closed record schema or a local invariant was violated.
    #[snafu(display("invalid SpecTec compilation record: {reason}"))]
    Schema {
        /// Exact rejected invariant.
        reason: &'static str,
    },
    /// The record did not describe the supplied verified source exactly.
    #[snafu(display("SpecTec compilation record does not match its source: {reason}"))]
    SourceMismatch {
        /// First failed source invariant.
        reason: &'static str,
    },
    /// The supplied kernel bytes did not match their SHA-256 CID.
    #[snafu(display("SpecTec kernel bytes do not match the record's kernel CID"))]
    KernelAddress,
    /// The linked bytes were not one canonical Ethane arena.
    #[snafu(display("could not decode linked SpecTec kernel: {source}"))]
    KernelDecode {
        /// Underlying arena-CBOR failure.
        source: wire::DecodeError,
    },
    /// The arena's current BLAKE3 address disagreed with the compatibility field.
    #[snafu(display("SpecTec kernel BLAKE3 address does not match the record"))]
    KernelBlake3,
    /// A correspondence root did not exist in the linked arena.
    #[snafu(display(
        "SpecTec declaration {id:?} root {role:?} references missing row {reference:?}"
    ))]
    MissingReference {
        /// Source declaration selector.
        id: DeclarationId,
        /// Correspondence role.
        role: String,
        /// Missing local row.
        reference: Ref,
    },
    /// A correspondence root's recorded category disagreed with the arena tag.
    #[snafu(display(
        "SpecTec declaration {id:?} root {role:?} records {expected:?}, found {actual:?}"
    ))]
    SortMismatch {
        /// Source declaration selector.
        id: DeclarationId,
        /// Correspondence role.
        role: String,
        /// Category recorded in DRISL.
        expected: Sort,
        /// Category declared by the arena row.
        actual: Sort,
    },
}

fn declaration_value(declaration: &DeclarationRecord) -> Value {
    Value::Map(BTreeMap::from([
        field(
            "root",
            Value::Integer(i64::from(declaration.id.root().get())),
        ),
        field(
            "member",
            Value::Integer(i64::from(declaration.id.member().unwrap_or(0))),
        ),
        field("kind", Value::Text(kind_name(declaration.kind).to_owned())),
        field("name", Value::Text(declaration.name.clone())),
        field(
            "roots",
            Value::Array(declaration.roots.iter().map(root_value).collect()),
        ),
    ]))
}

fn root_value(root: &BoundRoot) -> Value {
    Value::Map(BTreeMap::from([
        field("role", Value::Text(root.role.clone())),
        field("ref", Value::Integer(i64::from(root.reference.get()))),
        field("sort", Value::Text(sort_name(root.sort).to_owned())),
    ]))
}

const fn kind_name(kind: IlKind) -> &'static str {
    match kind {
        IlKind::Type => "typ",
        IlKind::Definition => "def",
        IlKind::Grammar => "gram",
        IlKind::Relation => "rel",
    }
}

const fn sort_name(sort: Sort) -> &'static str {
    match sort {
        Sort::Kind => "kind",
        Sort::Ty => "type",
        Sort::Tm => "term",
    }
}

fn field(name: &str, value: Value) -> (String, Value) {
    (name.to_owned(), value)
}

fn record_from_value(value: &Value) -> Result<CompilationRecord, ArtifactError> {
    let fields = exact_map(value, 8, "top-level item must have exactly eight fields")?;
    if text(required(fields, "$type")?)? != TYPE_NAME {
        return schema("$type must be the exact SpecTec compilation discriminator");
    }
    let bundle = link(required(fields, "bundle")?)?;
    if bundle.codec() != CidCodec::Drisl || bundle.hash() != CidHash::Sha256 {
        return schema("bundle must be a SHA-256 DRISL CID");
    }
    let ast = link(required(fields, "ast")?)?;
    if ast.codec() != CidCodec::Raw || ast.hash() != CidHash::Sha256 {
        return schema("ast must be a SHA-256 raw CID");
    }
    let kernel = link(required(fields, "kernel")?)?;
    if kernel.codec() != CidCodec::Raw || kernel.hash() != CidHash::Sha256 {
        return schema("kernel must be a SHA-256 raw CID");
    }
    let kernel_blake3 = bytes(required(fields, "kernelBlake3")?)?
        .try_into()
        .map_err(|_| ArtifactError::Schema {
            reason: "kernelBlake3 must contain exactly 32 bytes",
        })?;
    let release = text(required(fields, "release")?)?.to_owned();
    let revision = text(required(fields, "revision")?)?.to_owned();
    let Value::Array(values) = required(fields, "declarations")? else {
        return schema("declarations must be an array");
    };
    let declarations = values
        .iter()
        .map(declaration_from_value)
        .collect::<Result<Vec<_>, _>>()?;
    let unique = declarations
        .iter()
        .map(|declaration| declaration.id)
        .collect::<BTreeSet<_>>();
    if unique.len() != declarations.len() {
        return schema("declaration selectors must be unique");
    }
    Ok(CompilationRecord {
        bundle,
        ast,
        kernel,
        kernel_blake3,
        release,
        revision,
        declarations,
    })
}

fn declaration_from_value(value: &Value) -> Result<DeclarationRecord, ArtifactError> {
    let fields = exact_map(value, 5, "each declaration must have exactly five fields")?;
    let root = positive_u32(required(fields, "root")?)?;
    let member = nonnegative_u32(required(fields, "member")?)?;
    let id =
        DeclarationId::new(root, (member != 0).then_some(member)).ok_or(ArtifactError::Schema {
            reason: "declaration selector must use one-based positions",
        })?;
    let kind = match text(required(fields, "kind")?)? {
        "typ" => IlKind::Type,
        "def" => IlKind::Definition,
        "gram" => IlKind::Grammar,
        "rel" => IlKind::Relation,
        _ => return schema("declaration kind is not recognized"),
    };
    let name = text(required(fields, "name")?)?.to_owned();
    let Value::Array(values) = required(fields, "roots")? else {
        return schema("declaration roots must be an array");
    };
    if values.is_empty() {
        return schema("each declaration must have at least one root");
    }
    let roots = values
        .iter()
        .map(bound_root_from_value)
        .collect::<Result<Vec<_>, _>>()?;
    let unique = roots
        .iter()
        .map(|root| root.role.as_str())
        .collect::<BTreeSet<_>>();
    if unique.len() != roots.len() {
        return schema("root roles must be unique within a declaration");
    }
    Ok(DeclarationRecord {
        id,
        kind,
        name,
        roots,
    })
}

fn bound_root_from_value(value: &Value) -> Result<BoundRoot, ArtifactError> {
    let fields = exact_map(value, 3, "each root must have exactly three fields")?;
    let role = text(required(fields, "role")?)?.to_owned();
    if role.is_empty() {
        return schema("root role must not be empty");
    }
    let raw_reference = positive_i32(required(fields, "ref")?)?;
    let reference = Ref::new(raw_reference).ok_or(ArtifactError::Schema {
        reason: "root reference must be one-based",
    })?;
    let sort = match text(required(fields, "sort")?)? {
        "kind" => Sort::Kind,
        "type" => Sort::Ty,
        "term" => Sort::Tm,
        _ => return schema("root sort is not recognized"),
    };
    Ok(BoundRoot {
        role,
        reference,
        sort,
    })
}

fn exact_map<'a>(
    value: &'a Value,
    length: usize,
    reason: &'static str,
) -> Result<&'a BTreeMap<String, Value>, ArtifactError> {
    let Value::Map(fields) = value else {
        return schema(reason);
    };
    if fields.len() != length {
        return schema(reason);
    }
    Ok(fields)
}

fn required<'a>(
    fields: &'a BTreeMap<String, Value>,
    name: &'static str,
) -> Result<&'a Value, ArtifactError> {
    fields
        .get(name)
        .ok_or(ArtifactError::Schema { reason: name })
}

fn text(value: &Value) -> Result<&str, ArtifactError> {
    let Value::Text(value) = value else {
        return schema("field must be text");
    };
    Ok(value)
}

fn bytes(value: &Value) -> Result<&[u8], ArtifactError> {
    let Value::Bytes(value) = value else {
        return schema("field must be bytes");
    };
    Ok(value)
}

fn link(value: &Value) -> Result<Cid, ArtifactError> {
    let Value::Link(value) = value else {
        return schema("field must be a CID link");
    };
    Ok(*value)
}

fn positive_u32(value: &Value) -> Result<u32, ArtifactError> {
    let value = nonnegative_u32(value)?;
    if value == 0 {
        return schema("integer must be positive");
    }
    Ok(value)
}

fn nonnegative_u32(value: &Value) -> Result<u32, ArtifactError> {
    let Value::Integer(value) = value else {
        return schema("field must be an integer");
    };
    u32::try_from(*value).map_err(|_| ArtifactError::Schema {
        reason: "integer must fit the nonnegative u32 domain",
    })
}

fn positive_i32(value: &Value) -> Result<i32, ArtifactError> {
    let Value::Integer(value) = value else {
        return schema("field must be an integer");
    };
    let value = i32::try_from(*value).map_err(|_| ArtifactError::Schema {
        reason: "reference must fit the positive i32 domain",
    })?;
    if value <= 0 {
        return schema("reference must be positive");
    }
    Ok(value)
}

fn schema<T>(reason: &'static str) -> Result<T, ArtifactError> {
    Err(ArtifactError::Schema { reason })
}
