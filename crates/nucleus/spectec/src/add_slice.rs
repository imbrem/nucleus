//! Closed translation plan for the first parameter-only Wasm add slice.
//!
//! The plan is policy, not theorem authority. It classifies the complete
//! elaborated declaration/rule/clause inventory against exact structural
//! selectors. Selected cases carry raw-source audit locations; everything
//! else is represented by an explicit rejection.

use std::collections::{BTreeMap, BTreeSet};

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash, Policy, Value};
use covalence_data_spectec::{ClauseId, DeclarationId, IlError, IlKind, RuleId};
use covalence_lib_error::snafu::Snafu;

use crate::Source;

/// Closed-record discriminator for a parameter-only add slice.
pub const ADD_SLICE_TYPE_NAME: &str = "io.github.imbrem.nucleus.spectecAddSliceV1";

/// One exact translation case in the parameter-only add slice.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TranslationCase {
    /// The width-indexed integer carrier declaration.
    IntegerCarrier,
    /// The numeric type variant declaration.
    NumericType,
    /// Numeric bit-width definition.
    Size,
    /// Numeric bit-width specialization.
    SizeNn,
    /// Numeric binary-operation syntax.
    BinaryOperationSyntax,
    /// Runtime value syntax.
    Value,
    /// Runtime frame syntax.
    Frame,
    /// Core instruction syntax.
    Instruction,
    /// Modular integer addition.
    IntegerAdd,
    /// Numeric binary-operation evaluator.
    BinaryOperation,
    /// Local lookup.
    Local,
    /// Pure-step relation.
    StepPure,
    /// Read-step relation.
    StepRead,
    /// Eventful step relation.
    Step,
    /// Reflexive-transitive step relation.
    Steps,
    /// `I32` branch of `size`.
    SizeI32Clause,
    /// Sole `sizenn` clause.
    SizeNnClause,
    /// Sole modular-addition clause.
    IntegerAddClause,
    /// Integer `ADD` branch of `binop_`.
    BinaryOperationI32AddClause,
    /// Sole local-lookup clause.
    LocalClause,
    /// Pure numeric binary-operation rule.
    BinaryOperationValueRule,
    /// Explicit function-return rule.
    ReturnFrameRule,
    /// Local-read rule.
    LocalGetRule,
    /// Eventful wrapper for a pure step.
    StepPureRule,
    /// Pure-step premise inside the eventful wrapper.
    StepPurePremise,
    /// Eventful wrapper for a read step.
    StepReadRule,
    /// Read-step premise inside the eventful wrapper.
    StepReadPremise,
    /// Reflexive multi-step rule.
    StepsReflexiveRule,
    /// Transitive multi-step rule.
    StepsTransitiveRule,
    /// Single-step premise inside transitivity.
    StepsStepPremise,
    /// Recursive multi-step premise inside transitivity.
    StepsTailPremise,
}

/// Why an input form is deliberately outside the first slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rejection {
    /// The declaration is not needed for the parameter-only add theorem.
    DeclarationOutsideSlice,
    /// The enclosing declaration is selected, but this alternative is not.
    AlternativeOutsideSlice,
}

/// Inclusive one-based line range in one pinned raw source file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceSpan {
    /// Bundle-relative source path.
    pub path: &'static str,
    /// First included line.
    pub first_line: u32,
    /// Last included line.
    pub last_line: u32,
}

/// Generic classification shared by structurally selected source forms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CoverageDisposition<Case, Reject, Source> {
    /// This form has exactly one translation case and raw-source mapping.
    Translate {
        /// Closed translator dispatch case.
        case: Case,
        /// Independent raw-source audit location.
        source: Source,
    },
    /// This form must be rejected by the first slice.
    Reject(Reject),
}

/// Add-slice specialization of the generic coverage disposition.
pub type Disposition = CoverageDisposition<TranslationCase, Rejection, SourceSpan>;

/// One generic selector and its complete coverage disposition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Coverage<Selector, Classification> {
    /// Exact structural selector.
    pub id: Selector,
    /// Classification for the slice.
    pub disposition: Classification,
}

/// Coverage for one elaborated declaration.
pub type DeclarationCoverage = Coverage<DeclarationId, Disposition>;

/// Coverage for one elaborated definition clause.
pub type ClauseCoverage = Coverage<ClauseId, Disposition>;

/// Coverage for one elaborated relation rule.
pub type RuleCoverage = Coverage<RuleId, Disposition>;

/// Generic deterministic coverage schema for elaborated declarations and
/// their nested clauses and rules.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoveragePlan<Classification> {
    declarations: Vec<Coverage<DeclarationId, Classification>>,
    clauses: Vec<Coverage<ClauseId, Classification>>,
    rules: Vec<Coverage<RuleId, Classification>>,
}

/// Owned declaration, clause, and rule parts of a generic coverage plan.
pub type CoverageParts<Classification> = (
    Vec<Coverage<DeclarationId, Classification>>,
    Vec<Coverage<ClauseId, Classification>>,
    Vec<Coverage<RuleId, Classification>>,
);

/// Deterministic, exhaustive coverage plan for the first add slice.
pub type AddSlicePlan = CoveragePlan<Disposition>;

/// Canonical audit artifact linking exact inputs to one closed coverage plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AddSliceArtifact {
    bundle: Cid,
    ast: Cid,
    plan: AddSlicePlan,
}

impl AddSliceArtifact {
    /// Builds the canonical plan for one exact verified source.
    ///
    /// # Errors
    ///
    /// Returns any structural coverage error from [`AddSlicePlan::build`].
    pub fn build(source: &Source) -> Result<Self, AddSliceError> {
        Ok(Self {
            bundle: source.bundle(),
            ast: source.ast(),
            plan: AddSlicePlan::build(source)?,
        })
    }

    /// Returns the exact source-bundle CID.
    #[must_use]
    pub const fn bundle(&self) -> Cid {
        self.bundle
    }

    /// Returns the exact elaborated-AST CID.
    #[must_use]
    pub const fn ast(&self) -> Cid {
        self.ast
    }

    /// Returns the closed coverage plan.
    #[must_use]
    pub const fn plan(&self) -> &AddSlicePlan {
        &self.plan
    }

    /// Encodes the artifact as canonical ATProto-profile DRISL.
    ///
    /// # Errors
    ///
    /// Returns an error if canonical DRISL encoding rejects the closed value.
    pub fn encode(&self) -> Result<Vec<u8>, AddSliceError> {
        drisl::encode(Policy::ATPROTO, &self.to_value())
            .map_err(|source| AddSliceError::RecordEncode { source })
    }

    /// Returns the SHA-256 DRISL CID of the exact canonical artifact bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if canonical DRISL encoding rejects the closed value.
    pub fn cid(&self) -> Result<Cid, AddSliceError> {
        Ok(drisl::address(
            CidCodec::Drisl,
            CidHash::Sha256,
            &self.encode()?,
        ))
    }

    /// Decodes one exact canonical add-slice audit artifact.
    ///
    /// This checks the closed schema, CID profiles, selector domains,
    /// disposition invariants, unique coverage, and closed translator case
    /// vocabulary. It does not establish that the coverage matches an input;
    /// use [`verify_source`](Self::verify_source) for that comparison.
    ///
    /// # Errors
    ///
    /// Returns an error for noncanonical DRISL or any schema/local-invariant
    /// violation.
    pub fn decode(bytes: &[u8]) -> Result<Self, AddSliceArtifactError> {
        let value = drisl::decode(Policy::ATPROTO, bytes)
            .map_err(|source| AddSliceArtifactError::RecordDecode { source })?;
        artifact_from_value(&value)
    }

    /// Decodes an artifact and verifies it against one exact source.
    ///
    /// # Errors
    ///
    /// Returns any decoding, schema, input-identity, or coverage mismatch.
    pub fn decode_for_source(bytes: &[u8], source: &Source) -> Result<Self, AddSliceArtifactError> {
        let artifact = Self::decode(bytes)?;
        artifact.verify_source(source)?;
        Ok(artifact)
    }

    /// Verifies this artifact against one exact verified source.
    ///
    /// # Errors
    ///
    /// Returns an error if either input CID differs, deriving the expected
    /// closed plan fails, or any decoded coverage entry differs.
    pub fn verify_source(&self, source: &Source) -> Result<(), AddSliceArtifactError> {
        if self.bundle != source.bundle() {
            return Err(AddSliceArtifactError::SourceMismatch {
                reason: "bundle CID differs",
            });
        }
        if self.ast != source.ast() {
            return Err(AddSliceArtifactError::SourceMismatch {
                reason: "AST CID differs",
            });
        }
        let expected =
            AddSlicePlan::build(source).map_err(|source| AddSliceArtifactError::Plan { source })?;
        if self.plan != expected {
            return Err(AddSliceArtifactError::SourceMismatch {
                reason: "coverage plan differs",
            });
        }
        Ok(())
    }

    fn to_value(&self) -> Value {
        Value::Map(BTreeMap::from([
            value_field("$type", Value::Text(ADD_SLICE_TYPE_NAME.to_owned())),
            value_field("bundle", Value::Link(self.bundle)),
            value_field("ast", Value::Link(self.ast)),
            value_field(
                "declarations",
                Value::Array(
                    self.plan
                        .declarations
                        .iter()
                        .map(declaration_value)
                        .collect(),
                ),
            ),
            value_field(
                "clauses",
                Value::Array(self.plan.clauses.iter().map(clause_value).collect()),
            ),
            value_field(
                "rules",
                Value::Array(self.plan.rules.iter().map(rule_value).collect()),
            ),
        ]))
    }
}

impl CoveragePlan<Disposition> {
    /// Validates the exact selected forms and classifies the complete input.
    ///
    /// Selection is by structural IDs. Expected names and kinds are checked as
    /// audit assertions, never used to locate a form.
    ///
    /// # Errors
    ///
    /// Returns an error when the pinned shape differs, a rule is malformed, a
    /// selected selector is absent, or a translation case occurs more than once.
    pub fn build(source: &Source) -> Result<Self, AddSliceError> {
        let mut declarations = Vec::with_capacity(source.declaration_count());
        let mut clauses = Vec::new();
        let mut rules = Vec::new();
        let mut seen = BTreeSet::new();

        for declaration in source.declarations() {
            let selected = declaration_case(declaration.id());
            let disposition = match selected {
                Some(specification) => {
                    if declaration.kind() != specification.kind
                        || declaration.name() != specification.name
                    {
                        return Err(AddSliceError::DeclarationShape {
                            id: declaration.id(),
                        });
                    }
                    translated(specification.case, specification.source, &mut seen)?
                }
                None => Disposition::Reject(Rejection::DeclarationOutsideSlice),
            };
            declarations.push(Coverage {
                id: declaration.id(),
                disposition,
            });

            let declaration_clauses =
                source
                    .il()
                    .clauses(declaration.id())
                    .ok_or(AddSliceError::MissingDeclaration {
                        id: declaration.id(),
                    })?;
            for clause in declaration_clauses {
                let disposition = match clause_case(clause.id()) {
                    Some((case, span)) => translated(case, span, &mut seen)?,
                    None => Disposition::Reject(Rejection::AlternativeOutsideSlice),
                };
                clauses.push(Coverage {
                    id: clause.id().clone(),
                    disposition,
                });
            }
            let declaration_rules = source
                .il()
                .rules(declaration.id())
                .map_err(|source| AddSliceError::Il { source })?
                .ok_or(AddSliceError::MissingDeclaration {
                    id: declaration.id(),
                })?;
            for rule in declaration_rules {
                let disposition = match rule_case(rule.id()) {
                    Some(specification) => {
                        if rule.name() != specification.name {
                            return Err(AddSliceError::RuleShape {
                                id: rule.id().clone(),
                            });
                        }
                        translated(specification.case, specification.source, &mut seen)?
                    }
                    None => Disposition::Reject(Rejection::AlternativeOutsideSlice),
                };
                rules.push(Coverage {
                    id: rule.id().clone(),
                    disposition,
                });
            }
        }

        if seen.len() != TRANSLATION_CASE_COUNT {
            return Err(AddSliceError::MissingCases {
                expected: TRANSLATION_CASE_COUNT,
                actual: seen.len(),
            });
        }
        Ok(Self {
            declarations,
            clauses,
            rules,
        })
    }
}

impl<Classification> CoveragePlan<Classification> {
    /// Composes a generic plan from declaration, clause, and rule coverage.
    #[must_use]
    pub fn new(
        declarations: Vec<Coverage<DeclarationId, Classification>>,
        clauses: Vec<Coverage<ClauseId, Classification>>,
        rules: Vec<Coverage<RuleId, Classification>>,
    ) -> Self {
        Self {
            declarations,
            clauses,
            rules,
        }
    }

    /// Returns declaration coverage in elaborated source order.
    #[must_use]
    pub fn declarations(&self) -> &[Coverage<DeclarationId, Classification>] {
        &self.declarations
    }

    /// Returns clause coverage in deterministic tree order.
    #[must_use]
    pub fn clauses(&self) -> &[Coverage<ClauseId, Classification>] {
        &self.clauses
    }

    /// Returns rule coverage in deterministic tree order.
    #[must_use]
    pub fn rules(&self) -> &[Coverage<RuleId, Classification>] {
        &self.rules
    }

    /// Decomposes a plan without cloning its coverage entries.
    #[must_use]
    pub fn into_parts(self) -> CoverageParts<Classification> {
        (self.declarations, self.clauses, self.rules)
    }
}

/// Why the closed add-slice plan did not match an input.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AddSliceError {
    /// A selected declaration's checked metadata changed.
    #[snafu(display("SpecTec add declaration {id:?} has an unexpected form"))]
    DeclarationShape {
        /// Exact structural selector.
        id: DeclarationId,
    },
    /// An inventoried declaration no longer resolved to an expression.
    #[snafu(display("SpecTec add declaration {id:?} is missing from its document"))]
    MissingDeclaration {
        /// Missing structural selector.
        id: DeclarationId,
    },
    /// A selected rule's checked name changed.
    #[snafu(display("SpecTec add rule {id:?} has an unexpected form"))]
    RuleShape {
        /// Exact structural selector.
        id: RuleId,
    },
    /// Nested rule inventory rejected malformed IL.
    #[snafu(display("could not inventory SpecTec add rules: {source}"))]
    Il {
        /// Underlying typed IL error.
        source: IlError,
    },
    /// Two selectors were assigned the same closed translator case.
    #[snafu(display("SpecTec add translation case {case:?} occurs more than once"))]
    DuplicateCase {
        /// Duplicated dispatch case.
        case: TranslationCase,
    },
    /// One or more required cases were absent.
    #[snafu(display("SpecTec add plan expected {expected} cases, found {actual}"))]
    MissingCases {
        /// Closed case count.
        expected: usize,
        /// Cases observed in the supplied source.
        actual: usize,
    },
    /// Canonical coverage-record encoding failed.
    #[snafu(display("could not encode SpecTec add-slice record: {source}"))]
    RecordEncode {
        /// Underlying deterministic encoding error.
        source: drisl::EncodeError,
    },
}

/// Why stored add-slice audit bytes were rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AddSliceArtifactError {
    /// The bytes were not one canonical ATProto-profile DRISL item.
    #[snafu(display("could not decode SpecTec add-slice record: {source}"))]
    RecordDecode {
        /// Underlying deterministic decoder failure.
        source: drisl::DecodeError,
    },
    /// The closed schema or a local invariant was violated.
    #[snafu(display("invalid SpecTec add-slice record: {reason}"))]
    Schema {
        /// Exact rejected invariant.
        reason: &'static str,
    },
    /// Rebuilding the expected plan from the verified source failed.
    #[snafu(display("could not derive expected SpecTec add-slice plan: {source}"))]
    Plan {
        /// Underlying structural coverage failure.
        source: AddSliceError,
    },
    /// The artifact did not describe the supplied source exactly.
    #[snafu(display("SpecTec add-slice record does not match its source: {reason}"))]
    SourceMismatch {
        /// First failed identity or coverage invariant.
        reason: &'static str,
    },
}

#[derive(Clone, Copy)]
struct DeclarationSpec {
    kind: IlKind,
    name: &'static str,
    case: TranslationCase,
    source: SourceSpan,
}

#[derive(Clone, Copy)]
struct RuleSpec {
    name: &'static str,
    case: TranslationCase,
    source: SourceSpan,
}

const TRANSLATION_CASE_COUNT: usize = 31;
const TYPES: &str = "source/1.2-syntax.types.spectec";
const INSTRUCTIONS: &str = "source/1.3-syntax.instructions.spectec";
const NUMERICS: &str = "source/3.1-numerics.scalar.spectec";
const CONFIGURATIONS: &str = "source/4.0-execution.configurations.spectec";
const EXECUTION: &str = "source/4.3-execution.instructions.spectec";
const VALUES: &str = "source/1.1-syntax.values.spectec";

const fn span(path: &'static str, first_line: u32, last_line: u32) -> SourceSpan {
    SourceSpan {
        path,
        first_line,
        last_line,
    }
}

fn declaration_case(id: DeclarationId) -> Option<DeclarationSpec> {
    syntax_declaration_case(id)
        .or_else(|| numeric_declaration_case(id))
        .or_else(|| execution_declaration_case(id))
}

fn syntax_declaration_case(id: DeclarationId) -> Option<DeclarationSpec> {
    let direct = |root, kind, name, case, source| {
        (id == DeclarationId::new(root, None)?).then_some(DeclarationSpec {
            kind,
            name,
            case,
            source,
        })
    };
    direct(
        26,
        IlKind::Type,
        "iN",
        TranslationCase::IntegerCarrier,
        span(VALUES, 14, 15),
    )
    .or_else(|| {
        direct(
            88,
            IlKind::Type,
            "numtype",
            TranslationCase::NumericType,
            span(TYPES, 13, 18),
        )
    })
    .or_else(|| {
        direct(
            131,
            IlKind::Definition,
            "size",
            TranslationCase::Size,
            span(TYPES, 196, 208),
        )
    })
    .or_else(|| {
        direct(
            142,
            IlKind::Definition,
            "sizenn",
            TranslationCase::SizeNn,
            span(TYPES, 239, 242),
        )
    })
    .or_else(|| {
        direct(
            218,
            IlKind::Type,
            "binop_",
            TranslationCase::BinaryOperationSyntax,
            span(INSTRUCTIONS, 35, 40),
        )
    })
    .or_else(|| {
        direct(
            268,
            IlKind::Type,
            "val",
            TranslationCase::Value,
            span(CONFIGURATIONS, 48, 58),
        )
    })
    .or_else(|| {
        direct(
            269,
            IlKind::Type,
            "frame",
            TranslationCase::Frame,
            span(CONFIGURATIONS, 130, 133),
        )
    })
    .or_else(|| {
        recursive(
            id,
            270,
            1,
            IlKind::Type,
            "instr",
            TranslationCase::Instruction,
            span(INSTRUCTIONS, 214, 358),
        )
    })
}

fn numeric_declaration_case(id: DeclarationId) -> Option<DeclarationSpec> {
    let direct = |root, kind, name, case, source| {
        (id == DeclarationId::new(root, None)?).then_some(DeclarationSpec {
            kind,
            name,
            case,
            source,
        })
    };
    direct(
        425,
        IlKind::Definition,
        "iadd_",
        TranslationCase::IntegerAdd,
        span(NUMERICS, 107, 165),
    )
    .or_else(|| {
        direct(
            498,
            IlKind::Definition,
            "binop_",
            TranslationCase::BinaryOperation,
            span(NUMERICS, 366, 407),
        )
    })
}

fn execution_declaration_case(id: DeclarationId) -> Option<DeclarationSpec> {
    let direct = |root, kind, name, case, source| {
        (id == DeclarationId::new(root, None)?).then_some(DeclarationSpec {
            kind,
            name,
            case,
            source,
        })
    };
    direct(
        602,
        IlKind::Definition,
        "local",
        TranslationCase::Local,
        span(CONFIGURATIONS, 264, 274),
    )
    .or_else(|| {
        direct(
            628,
            IlKind::Relation,
            "Step_pure",
            TranslationCase::StepPure,
            span(EXECUTION, 6, 1096),
        )
    })
    .or_else(|| {
        direct(
            630,
            IlKind::Relation,
            "Step_read",
            TranslationCase::StepRead,
            span(EXECUTION, 7, 911),
        )
    })
    .or_else(|| {
        recursive(
            id,
            631,
            1,
            IlKind::Relation,
            "Step",
            TranslationCase::Step,
            span(EXECUTION, 5, 911),
        )
    })
    .or_else(|| {
        recursive(
            id,
            632,
            1,
            IlKind::Relation,
            "Steps",
            TranslationCase::Steps,
            span(EXECUTION, 8, 30),
        )
    })
}

fn recursive(
    id: DeclarationId,
    root: u32,
    member: u32,
    kind: IlKind,
    name: &'static str,
    case: TranslationCase,
    source: SourceSpan,
) -> Option<DeclarationSpec> {
    (id == DeclarationId::new(root, Some(member))?).then_some(DeclarationSpec {
        kind,
        name,
        case,
        source,
    })
}

fn clause_case(id: &ClauseId) -> Option<(TranslationCase, SourceSpan)> {
    clause(
        id,
        131,
        None,
        &[5],
        TranslationCase::SizeI32Clause,
        span(TYPES, 205, 205),
    )
    .or_else(|| {
        clause(
            id,
            142,
            None,
            &[5],
            TranslationCase::SizeNnClause,
            span(TYPES, 242, 242),
        )
    })
    .or_else(|| {
        clause(
            id,
            425,
            None,
            &[7],
            TranslationCase::IntegerAddClause,
            span(NUMERICS, 165, 165),
        )
    })
    .or_else(|| {
        clause(
            id,
            498,
            None,
            &[8],
            TranslationCase::BinaryOperationI32AddClause,
            span(NUMERICS, 388, 388),
        )
    })
    .or_else(|| {
        clause(
            id,
            602,
            None,
            &[6],
            TranslationCase::LocalClause,
            span(CONFIGURATIONS, 274, 274),
        )
    })
}

fn clause(
    actual: &ClauseId,
    root: u32,
    member: Option<u32>,
    path: &[u32],
    case: TranslationCase,
    source: SourceSpan,
) -> Option<(TranslationCase, SourceSpan)> {
    let expected = ClauseId::new(DeclarationId::new(root, member)?, path.iter().copied())?;
    (actual == &expected).then_some((case, source))
}

fn rule_case(id: &RuleId) -> Option<RuleSpec> {
    primitive_rule_case(id)
        .or_else(|| step_rule_case(id))
        .or_else(|| steps_rule_case(id))
}

fn primitive_rule_case(id: &RuleId) -> Option<RuleSpec> {
    rule(
        id,
        628,
        None,
        &[52],
        "binop-val",
        TranslationCase::BinaryOperationValueRule,
        span(EXECUTION, 948, 951),
    )
    .or_else(|| {
        rule(
            id,
            628,
            None,
            &[27],
            "return-frame",
            TranslationCase::ReturnFrameRule,
            span(EXECUTION, 215, 217),
        )
    })
    .or_else(|| {
        rule(
            id,
            630,
            None,
            &[30],
            "local.get",
            TranslationCase::LocalGetRule,
            span(EXECUTION, 298, 301),
        )
    })
}

fn step_rule_case(id: &RuleId) -> Option<RuleSpec> {
    rule(
        id,
        631,
        Some(1),
        &[5],
        "pure",
        TranslationCase::StepPureRule,
        span(EXECUTION, 13, 16),
    )
    .or_else(|| {
        rule(
            id,
            631,
            Some(1),
            &[5, 8],
            "Step_pure",
            TranslationCase::StepPurePremise,
            span(EXECUTION, 15, 15),
        )
    })
    .or_else(|| {
        rule(
            id,
            631,
            Some(1),
            &[6],
            "read",
            TranslationCase::StepReadRule,
            span(EXECUTION, 17, 20),
        )
    })
    .or_else(|| {
        rule(
            id,
            631,
            Some(1),
            &[6, 8],
            "Step_read",
            TranslationCase::StepReadPremise,
            span(EXECUTION, 19, 19),
        )
    })
}

fn steps_rule_case(id: &RuleId) -> Option<RuleSpec> {
    rule(
        id,
        632,
        Some(1),
        &[5],
        "refl",
        TranslationCase::StepsReflexiveRule,
        span(EXECUTION, 21, 23),
    )
    .or_else(|| {
        rule(
            id,
            632,
            Some(1),
            &[6],
            "trans",
            TranslationCase::StepsTransitiveRule,
            span(EXECUTION, 24, 30),
        )
    })
    .or_else(|| {
        rule(
            id,
            632,
            Some(1),
            &[6, 11],
            "Step",
            TranslationCase::StepsStepPremise,
            span(EXECUTION, 28, 28),
        )
    })
    .or_else(|| {
        rule(
            id,
            632,
            Some(1),
            &[6, 12],
            "Steps",
            TranslationCase::StepsTailPremise,
            span(EXECUTION, 29, 29),
        )
    })
}

fn rule(
    actual: &RuleId,
    root: u32,
    member: Option<u32>,
    path: &[u32],
    name: &'static str,
    case: TranslationCase,
    source: SourceSpan,
) -> Option<RuleSpec> {
    let expected = RuleId::new(DeclarationId::new(root, member)?, path.iter().copied())?;
    (actual == &expected).then_some(RuleSpec { name, case, source })
}

fn translated(
    case: TranslationCase,
    source: SourceSpan,
    seen: &mut BTreeSet<TranslationCase>,
) -> Result<Disposition, AddSliceError> {
    if !seen.insert(case) {
        return Err(AddSliceError::DuplicateCase { case });
    }
    Ok(Disposition::Translate { case, source })
}

fn declaration_value(coverage: &DeclarationCoverage) -> Value {
    let (root, member) = declaration_parts(coverage.id);
    Value::Map(BTreeMap::from([
        value_field("root", Value::Integer(i64::from(root))),
        value_field("member", Value::Integer(i64::from(member))),
        value_field("disposition", disposition_value(coverage.disposition)),
    ]))
}

fn clause_value(coverage: &ClauseCoverage) -> Value {
    let (root, member) = declaration_parts(coverage.id.declaration());
    Value::Map(BTreeMap::from([
        value_field("root", Value::Integer(i64::from(root))),
        value_field("member", Value::Integer(i64::from(member))),
        value_field(
            "path",
            Value::Array(
                coverage
                    .id
                    .path()
                    .map(|position| Value::Integer(i64::from(position)))
                    .collect(),
            ),
        ),
        value_field("disposition", disposition_value(coverage.disposition)),
    ]))
}

fn rule_value(coverage: &RuleCoverage) -> Value {
    let (root, member) = declaration_parts(coverage.id.declaration());
    Value::Map(BTreeMap::from([
        value_field("root", Value::Integer(i64::from(root))),
        value_field("member", Value::Integer(i64::from(member))),
        value_field(
            "path",
            Value::Array(
                coverage
                    .id
                    .path()
                    .map(|position| Value::Integer(i64::from(position)))
                    .collect(),
            ),
        ),
        value_field("disposition", disposition_value(coverage.disposition)),
    ]))
}

fn disposition_value(disposition: Disposition) -> Value {
    let (status, case, rejection, source_path, first_line, last_line) = match disposition {
        Disposition::Translate { case, source } => (
            "translate",
            case_name(case),
            "",
            source.path,
            source.first_line,
            source.last_line,
        ),
        Disposition::Reject(rejection) => ("reject", "", rejection_name(rejection), "", 0, 0),
    };
    Value::Map(BTreeMap::from([
        value_field("status", Value::Text(status.to_owned())),
        value_field("case", Value::Text(case.to_owned())),
        value_field("rejection", Value::Text(rejection.to_owned())),
        value_field("sourcePath", Value::Text(source_path.to_owned())),
        value_field("firstLine", Value::Integer(i64::from(first_line))),
        value_field("lastLine", Value::Integer(i64::from(last_line))),
    ]))
}

fn declaration_parts(id: DeclarationId) -> (u32, u32) {
    (id.root().get(), id.member().unwrap_or(0))
}

const fn rejection_name(rejection: Rejection) -> &'static str {
    match rejection {
        Rejection::DeclarationOutsideSlice => "declaration-outside-slice",
        Rejection::AlternativeOutsideSlice => "alternative-outside-slice",
    }
}

const fn case_name(case: TranslationCase) -> &'static str {
    match case {
        TranslationCase::IntegerCarrier => "integer-carrier",
        TranslationCase::NumericType => "numeric-type",
        TranslationCase::Size => "size",
        TranslationCase::SizeNn => "size-nn",
        TranslationCase::BinaryOperationSyntax => "binary-operation-syntax",
        TranslationCase::Value => "value",
        TranslationCase::Frame => "frame",
        TranslationCase::Instruction => "instruction",
        TranslationCase::IntegerAdd => "integer-add",
        TranslationCase::BinaryOperation => "binary-operation",
        TranslationCase::Local => "local",
        TranslationCase::StepPure => "step-pure",
        TranslationCase::StepRead => "step-read",
        TranslationCase::Step => "step",
        TranslationCase::Steps => "steps",
        TranslationCase::SizeI32Clause => "size-i32-clause",
        TranslationCase::SizeNnClause => "size-nn-clause",
        TranslationCase::IntegerAddClause => "integer-add-clause",
        TranslationCase::BinaryOperationI32AddClause => "binary-operation-i32-add-clause",
        TranslationCase::LocalClause => "local-clause",
        TranslationCase::BinaryOperationValueRule => "binary-operation-value-rule",
        TranslationCase::ReturnFrameRule => "return-frame-rule",
        TranslationCase::LocalGetRule => "local-get-rule",
        TranslationCase::StepPureRule => "step-pure-rule",
        TranslationCase::StepPurePremise => "step-pure-premise",
        TranslationCase::StepReadRule => "step-read-rule",
        TranslationCase::StepReadPremise => "step-read-premise",
        TranslationCase::StepsReflexiveRule => "steps-reflexive-rule",
        TranslationCase::StepsTransitiveRule => "steps-transitive-rule",
        TranslationCase::StepsStepPremise => "steps-step-premise",
        TranslationCase::StepsTailPremise => "steps-tail-premise",
    }
}

fn value_field(name: &str, value: Value) -> (String, Value) {
    (name.to_owned(), value)
}

fn artifact_from_value(value: &Value) -> Result<AddSliceArtifact, AddSliceArtifactError> {
    let fields = artifact_map(value, 6, "top-level item must have exactly six fields")?;
    if artifact_text(artifact_required(fields, "$type")?)? != ADD_SLICE_TYPE_NAME {
        return artifact_schema("$type must be the exact add-slice discriminator");
    }
    let bundle = artifact_link(artifact_required(fields, "bundle")?)?;
    if bundle.codec() != CidCodec::Drisl || bundle.hash() != CidHash::Sha256 {
        return artifact_schema("bundle must be a SHA-256 DRISL CID");
    }
    let ast = artifact_link(artifact_required(fields, "ast")?)?;
    if ast.codec() != CidCodec::Raw || ast.hash() != CidHash::Sha256 {
        return artifact_schema("ast must be a SHA-256 raw CID");
    }
    let declarations = declaration_array(artifact_required(fields, "declarations")?)?;
    let clauses = clause_array(artifact_required(fields, "clauses")?)?;
    let rules = rule_array(artifact_required(fields, "rules")?)?;
    require_unique(declarations.iter().map(|coverage| coverage.id))?;
    require_unique(clauses.iter().map(|coverage| coverage.id.clone()))?;
    require_unique(rules.iter().map(|coverage| coverage.id.clone()))?;
    let cases = declarations
        .iter()
        .map(|coverage| coverage.disposition)
        .chain(clauses.iter().map(|coverage| coverage.disposition))
        .chain(rules.iter().map(|coverage| coverage.disposition))
        .filter_map(|disposition| match disposition {
            Disposition::Translate { case, .. } => Some(case),
            Disposition::Reject(_) => None,
        })
        .collect::<Vec<_>>();
    if cases.len() != TRANSLATION_CASE_COUNT
        || cases.iter().copied().collect::<BTreeSet<_>>().len() != cases.len()
    {
        return artifact_schema("translation cases must occur exactly once");
    }
    Ok(AddSliceArtifact {
        bundle,
        ast,
        plan: CoveragePlan {
            declarations,
            clauses,
            rules,
        },
    })
}

fn declaration_array(value: &Value) -> Result<Vec<DeclarationCoverage>, AddSliceArtifactError> {
    let Value::Array(values) = value else {
        return artifact_schema("declarations must be an array");
    };
    values.iter().map(declaration_from_value).collect()
}

fn clause_array(value: &Value) -> Result<Vec<ClauseCoverage>, AddSliceArtifactError> {
    let Value::Array(values) = value else {
        return artifact_schema("clauses must be an array");
    };
    values.iter().map(clause_from_value).collect()
}

fn rule_array(value: &Value) -> Result<Vec<RuleCoverage>, AddSliceArtifactError> {
    let Value::Array(values) = value else {
        return artifact_schema("rules must be an array");
    };
    values.iter().map(rule_from_value).collect()
}

fn declaration_from_value(value: &Value) -> Result<DeclarationCoverage, AddSliceArtifactError> {
    let fields = artifact_map(value, 3, "declaration must have exactly three fields")?;
    Ok(Coverage {
        id: decoded_declaration(fields)?,
        disposition: disposition_from_value(artifact_required(fields, "disposition")?)?,
    })
}

fn clause_from_value(value: &Value) -> Result<ClauseCoverage, AddSliceArtifactError> {
    let fields = artifact_map(value, 4, "clause must have exactly four fields")?;
    let declaration = decoded_declaration(fields)?;
    let path = decoded_path(artifact_required(fields, "path")?)?;
    let id = ClauseId::new(declaration, path).ok_or(AddSliceArtifactError::Schema {
        reason: "clause path must be nonempty and one-based",
    })?;
    Ok(Coverage {
        id,
        disposition: disposition_from_value(artifact_required(fields, "disposition")?)?,
    })
}

fn rule_from_value(value: &Value) -> Result<RuleCoverage, AddSliceArtifactError> {
    let fields = artifact_map(value, 4, "rule must have exactly four fields")?;
    let declaration = decoded_declaration(fields)?;
    let path = decoded_path(artifact_required(fields, "path")?)?;
    let id = RuleId::new(declaration, path).ok_or(AddSliceArtifactError::Schema {
        reason: "rule path must be nonempty and one-based",
    })?;
    Ok(Coverage {
        id,
        disposition: disposition_from_value(artifact_required(fields, "disposition")?)?,
    })
}

fn decoded_declaration(
    fields: &BTreeMap<String, Value>,
) -> Result<DeclarationId, AddSliceArtifactError> {
    let root = artifact_positive_u32(artifact_required(fields, "root")?)?;
    let member = artifact_nonnegative_u32(artifact_required(fields, "member")?)?;
    DeclarationId::new(root, (member != 0).then_some(member)).ok_or(AddSliceArtifactError::Schema {
        reason: "declaration selector must be one-based",
    })
}

fn decoded_path(value: &Value) -> Result<Vec<u32>, AddSliceArtifactError> {
    let Value::Array(values) = value else {
        return artifact_schema("selector path must be an array");
    };
    if values.is_empty() {
        return artifact_schema("selector path must not be empty");
    }
    values.iter().map(artifact_positive_u32).collect()
}

fn disposition_from_value(value: &Value) -> Result<Disposition, AddSliceArtifactError> {
    let fields = artifact_map(value, 6, "disposition must have exactly six fields")?;
    let status = artifact_text(artifact_required(fields, "status")?)?;
    let case = artifact_text(artifact_required(fields, "case")?)?;
    let rejection = artifact_text(artifact_required(fields, "rejection")?)?;
    let source_path = artifact_text(artifact_required(fields, "sourcePath")?)?;
    let first_line = artifact_nonnegative_u32(artifact_required(fields, "firstLine")?)?;
    let last_line = artifact_nonnegative_u32(artifact_required(fields, "lastLine")?)?;
    match status {
        "translate" => {
            if !rejection.is_empty() || first_line == 0 || first_line > last_line {
                return artifact_schema("translated disposition fields are inconsistent");
            }
            Ok(Disposition::Translate {
                case: case_from_name(case)?,
                source: SourceSpan {
                    path: source_path_from_name(source_path)?,
                    first_line,
                    last_line,
                },
            })
        }
        "reject" => {
            if !case.is_empty() || !source_path.is_empty() || first_line != 0 || last_line != 0 {
                return artifact_schema("rejected disposition fields are inconsistent");
            }
            Ok(Disposition::Reject(rejection_from_name(rejection)?))
        }
        _ => artifact_schema("disposition status is not recognized"),
    }
}

fn case_from_name(name: &str) -> Result<TranslationCase, AddSliceArtifactError> {
    let case = match name {
        "integer-carrier" => TranslationCase::IntegerCarrier,
        "numeric-type" => TranslationCase::NumericType,
        "size" => TranslationCase::Size,
        "size-nn" => TranslationCase::SizeNn,
        "binary-operation-syntax" => TranslationCase::BinaryOperationSyntax,
        "value" => TranslationCase::Value,
        "frame" => TranslationCase::Frame,
        "instruction" => TranslationCase::Instruction,
        "integer-add" => TranslationCase::IntegerAdd,
        "binary-operation" => TranslationCase::BinaryOperation,
        "local" => TranslationCase::Local,
        "step-pure" => TranslationCase::StepPure,
        "step-read" => TranslationCase::StepRead,
        "step" => TranslationCase::Step,
        "steps" => TranslationCase::Steps,
        "size-i32-clause" => TranslationCase::SizeI32Clause,
        "size-nn-clause" => TranslationCase::SizeNnClause,
        "integer-add-clause" => TranslationCase::IntegerAddClause,
        "binary-operation-i32-add-clause" => TranslationCase::BinaryOperationI32AddClause,
        "local-clause" => TranslationCase::LocalClause,
        "binary-operation-value-rule" => TranslationCase::BinaryOperationValueRule,
        "return-frame-rule" => TranslationCase::ReturnFrameRule,
        "local-get-rule" => TranslationCase::LocalGetRule,
        "step-pure-rule" => TranslationCase::StepPureRule,
        "step-pure-premise" => TranslationCase::StepPurePremise,
        "step-read-rule" => TranslationCase::StepReadRule,
        "step-read-premise" => TranslationCase::StepReadPremise,
        "steps-reflexive-rule" => TranslationCase::StepsReflexiveRule,
        "steps-transitive-rule" => TranslationCase::StepsTransitiveRule,
        "steps-step-premise" => TranslationCase::StepsStepPremise,
        "steps-tail-premise" => TranslationCase::StepsTailPremise,
        _ => return artifact_schema("translation case is not recognized"),
    };
    Ok(case)
}

fn rejection_from_name(name: &str) -> Result<Rejection, AddSliceArtifactError> {
    match name {
        "declaration-outside-slice" => Ok(Rejection::DeclarationOutsideSlice),
        "alternative-outside-slice" => Ok(Rejection::AlternativeOutsideSlice),
        _ => artifact_schema("rejection reason is not recognized"),
    }
}

fn source_path_from_name(name: &str) -> Result<&'static str, AddSliceArtifactError> {
    match name {
        TYPES => Ok(TYPES),
        INSTRUCTIONS => Ok(INSTRUCTIONS),
        NUMERICS => Ok(NUMERICS),
        CONFIGURATIONS => Ok(CONFIGURATIONS),
        EXECUTION => Ok(EXECUTION),
        VALUES => Ok(VALUES),
        _ => artifact_schema("source path is not recognized"),
    }
}

fn require_unique<T: Ord>(
    values: impl IntoIterator<Item = T>,
) -> Result<(), AddSliceArtifactError> {
    let mut seen = BTreeSet::new();
    if values.into_iter().all(|value| seen.insert(value)) {
        Ok(())
    } else {
        artifact_schema("coverage selectors must be unique")
    }
}

fn artifact_map<'a>(
    value: &'a Value,
    length: usize,
    reason: &'static str,
) -> Result<&'a BTreeMap<String, Value>, AddSliceArtifactError> {
    let Value::Map(fields) = value else {
        return artifact_schema(reason);
    };
    if fields.len() != length {
        return artifact_schema(reason);
    }
    Ok(fields)
}

fn artifact_required<'a>(
    fields: &'a BTreeMap<String, Value>,
    name: &'static str,
) -> Result<&'a Value, AddSliceArtifactError> {
    fields
        .get(name)
        .ok_or(AddSliceArtifactError::Schema { reason: name })
}

fn artifact_text(value: &Value) -> Result<&str, AddSliceArtifactError> {
    let Value::Text(value) = value else {
        return artifact_schema("field must be text");
    };
    Ok(value)
}

fn artifact_link(value: &Value) -> Result<Cid, AddSliceArtifactError> {
    let Value::Link(value) = value else {
        return artifact_schema("field must be a CID link");
    };
    Ok(*value)
}

fn artifact_positive_u32(value: &Value) -> Result<u32, AddSliceArtifactError> {
    let value = artifact_nonnegative_u32(value)?;
    if value == 0 {
        return artifact_schema("integer must be positive");
    }
    Ok(value)
}

fn artifact_nonnegative_u32(value: &Value) -> Result<u32, AddSliceArtifactError> {
    let Value::Integer(value) = value else {
        return artifact_schema("field must be an integer");
    };
    u32::try_from(*value).map_err(|_| AddSliceArtifactError::Schema {
        reason: "integer must fit the nonnegative u32 domain",
    })
}

fn artifact_schema<T>(reason: &'static str) -> Result<T, AddSliceArtifactError> {
    Err(AddSliceArtifactError::Schema { reason })
}
