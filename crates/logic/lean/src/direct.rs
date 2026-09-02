//! An intentionally small direct lowering from non-dependent Lean to HOL.
//!
//! This backend is a first consumer of the generic import API, not the intended
//! full Lean embedding. It supports monomorphic simple types, constants,
//! applications, lambdas, and non-dependent `forallE` arrows. For propositions
//! it checks implication-introduction proofs made from lambdas, hypotheses, and
//! earlier checked theorems, and interprets Lean's primitive `Eq`/`Eq.refl` as
//! HOL equality/reflexivity. Definitions are eagerly delta-lowered to their
//! values. Conversion beyond equality already known to the kernel is delegated
//! to [`ConversionTactic`].

use std::collections::BTreeMap;
use std::error::Error as StdError;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, SynFactId, ThmId, builtin::Op2};

use crate::import::{Artifacts, Backend};
use crate::lean4export::Metadata;
use crate::syntax::{Declaration, Expr, ExprId, Level, Name, NameId, Record, Tables};

/// Checked evidence returned by a conversion tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Conversion {
    /// Left side requested by the lowering backend.
    pub left: Ref,
    /// Right side requested by the lowering backend.
    pub right: Ref,
    /// LCF syntactic facts used to establish conversion before quotienting.
    pub facts: Vec<SynFactId>,
}

/// Proof-producing conversion strategy used by a direct lowering backend.
///
/// Implementations may use normalization, an e-graph, or any other search
/// strategy. Search is outside the TCB: successful calls must establish the
/// conversion through checked kernel rules before returning.
pub trait ConversionTactic {
    /// Search or kernel failure.
    type Error: StdError + 'static;

    /// Establish that two already-typed HOL objects are convertible.
    ///
    /// # Errors
    ///
    /// Returns an error when conversion search fails or its proposed LCF steps
    /// are rejected by the kernel.
    fn prove(
        &mut self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<Conversion, Self::Error>;
}

/// Conversion tactic accepting only equality already present in the kernel.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoConversion;

/// Failure from [`NoConversion`].
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum NoConversionError {
    /// A kernel query failed.
    #[snafu(display("could not query HOL conversion: {source}"))]
    Query { source: KernelError },
    /// The conversion quotient did not already relate the objects.
    #[snafu(display("HOL objects {left:?} and {right:?} are not already convertible"))]
    NotConvertible { left: Ref, right: Ref },
}

impl ConversionTactic for NoConversion {
    type Error = NoConversionError;

    fn prove(
        &mut self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<Conversion, Self::Error> {
        let equivalent = kernel
            .equivalent_mut(left, right)
            .map_err(|source| NoConversionError::Query { source })?;
        if !equivalent {
            return Err(NoConversionError::NotConvertible { left, right });
        }
        Ok(Conversion {
            left,
            right,
            facts: Vec::new(),
        })
    }
}

/// Why the direct backend accepted one declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DirectDerivation {
    /// Kernel construction established that the lowered value has this type.
    HasType { term: Ref, ty: Ref },
    /// An exported Lean proof term was checked through HOL sequent rules.
    Proof {
        /// Source proof expression.
        proof: ExprId,
        /// Lowered HOL proposition proved by `theorem`.
        proposition: Ref,
        /// Checked LCF steps, in construction order.
        steps: Vec<DirectProofStep>,
    },
    /// A conversion tactic established equality of two classifiers.
    Conversion(Conversion),
}

/// One checked step used to lower a Lean proof term.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DirectProofStep {
    /// A bound proof variable selected a hypothesis through identity and
    /// weakening.
    Hypothesis {
        proof: ExprId,
        proposition: Ref,
        theorem: ThmId,
    },
    /// A Lean proof lambda discharged one implication premise.
    ImplicationIntroduction {
        proof: ExprId,
        implication: Ref,
        premise: ThmId,
        theorem: ThmId,
    },
    /// A prior checked theorem was copied into a fresh resident slot.
    KnownTheorem {
        proof: ExprId,
        proposition: Ref,
        source: ThmId,
        theorem: ThmId,
    },
    /// Lean's primitive `Eq.refl` was checked by HOL equality reflexivity.
    EqualityReflexivity {
        proof: ExprId,
        equality: Ref,
        theorem: ThmId,
    },
}

/// Failure to lower the deliberately small direct-HOL fragment.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DirectError<E: StdError + 'static> {
    /// Syntax lies outside the direct backend's current fragment.
    #[snafu(display("direct HOL lowering does not support {feature}"))]
    Unsupported { feature: String },
    /// A constant has not been introduced by an earlier declaration.
    #[snafu(display("Lean constant name index {name} has no direct HOL lowering"))]
    MissingConstant { name: usize },
    /// An expression was used in the wrong direct-HOL category.
    #[snafu(display("expected {expected}, found {actual}"))]
    Category {
        expected: &'static str,
        actual: &'static str,
    },
    /// A bound variable was outside the current lambda context.
    #[snafu(display("bound variable {index} is outside a context of depth {depth}"))]
    BoundVariable { index: usize, depth: usize },
    /// A proof term established a different proposition from the expected one.
    #[snafu(display("Lean proof expression {proof} does not establish its expected proposition"))]
    ProofMismatch { proof: usize },
    /// A checked HOL constructor rejected the proposed lowering.
    #[snafu(display("HOL construction failed: {source}"))]
    Construction { source: KernelError },
    /// The selected conversion tactic could not justify classifier equality.
    #[snafu(display("HOL conversion failed: {source}"))]
    Conversion { source: E },
}

#[derive(Clone, Copy, Debug)]
enum Lowered {
    Kind(Ref),
    Type(Ref),
    Term(Ref),
}

impl Lowered {
    const fn category(self) -> &'static str {
        match self {
            Self::Kind(_) => "kind",
            Self::Type(_) => "type",
            Self::Term(_) => "term",
        }
    }
}

#[derive(Clone, Debug)]
enum Proposition {
    Atom {
        expression: ExprId,
        reference: Ref,
    },
    Implication {
        expression: ExprId,
        reference: Ref,
        left: Box<Self>,
        right: Box<Self>,
    },
    Equality {
        expression: ExprId,
        reference: Ref,
        ty: Ref,
        left: Ref,
        right: Ref,
    },
}

impl Proposition {
    const fn expression(&self) -> ExprId {
        match self {
            Self::Atom { expression, .. }
            | Self::Implication { expression, .. }
            | Self::Equality { expression, .. } => *expression,
        }
    }

    const fn reference(&self) -> Ref {
        match self {
            Self::Atom { reference, .. }
            | Self::Implication { reference, .. }
            | Self::Equality { reference, .. } => *reference,
        }
    }
}

/// Direct, monomorphic, non-dependent Lean-to-HOL backend.
#[derive(Debug)]
pub struct DirectHol<C = NoConversion> {
    kernel: Kernel,
    conversion: C,
    star: Option<Ref>,
    bool_ty: Option<Ref>,
    constants: BTreeMap<NameId, Lowered>,
    propositions: BTreeMap<ExprId, Proposition>,
    theorems: BTreeMap<NameId, (Ref, ThmId)>,
    conversions: Vec<Conversion>,
    next_binder: u64,
}

impl DirectHol<NoConversion> {
    /// Start with an empty HOL kernel and no nontrivial conversion tactic.
    #[must_use]
    pub fn new() -> Self {
        Self::with_conversion(Kernel::new(), NoConversion)
    }
}

impl Default for DirectHol<NoConversion> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C> DirectHol<C> {
    /// Use an explicit kernel and proof-producing conversion tactic.
    #[must_use]
    pub fn with_conversion(kernel: Kernel, conversion: C) -> Self {
        Self {
            kernel,
            conversion,
            star: None,
            bool_ty: None,
            constants: BTreeMap::new(),
            propositions: BTreeMap::new(),
            theorems: BTreeMap::new(),
            conversions: Vec::new(),
            next_binder: u64::MAX,
        }
    }

    /// Borrow the checked HOL state accumulated so far.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Consume the backend and recover its checked HOL kernel.
    #[must_use]
    pub fn into_kernel(self) -> Kernel {
        self.kernel
    }

    /// Conversion evidence used during this import.
    #[must_use]
    pub fn conversions(&self) -> &[Conversion] {
        &self.conversions
    }
}

impl<C: ConversionTactic> Backend for DirectHol<C> {
    type Object = Ref;
    type Theorem = ThmId;
    type Derivation = DirectDerivation;
    type Error = DirectError<C::Error>;

    fn begin(
        &mut self,
        _metadata: &Metadata,
        _tables: &Tables,
    ) -> Result<Artifacts<Ref, ThmId, DirectDerivation>, Self::Error> {
        let star = self
            .kernel
            .star()
            .map_err(|source| DirectError::Construction { source })?;
        let bool_ty = self
            .kernel
            .bool_ty(star)
            .map_err(|source| DirectError::Construction { source })?;
        self.star = Some(star);
        self.bool_ty = Some(bool_ty);
        Ok(Artifacts::default())
    }

    fn lower(
        &mut self,
        record: &Record,
        tables: &Tables,
    ) -> Result<Artifacts<Ref, ThmId, DirectDerivation>, Self::Error> {
        let Record::Declaration(ordinal) = *record else {
            return Ok(Artifacts::default());
        };
        let declaration = &tables.declarations[ordinal];
        let syntax = record.syntax(tables);
        if let Declaration::Theorem {
            header,
            value,
            all: _,
        } = declaration
        {
            Self::require_monomorphic(&header.level_params)?;
            let proposition = self.lower_proposition(header.ty, tables)?;
            let mut steps = Vec::new();
            let theorem = self.prove(*value, &proposition, tables, &mut Vec::new(), &mut steps)?;
            self.theorems
                .insert(header.name, (proposition.reference(), theorem));
            return Ok(Artifacts {
                objects: vec![(proposition.reference(), syntax)],
                theorems: vec![(
                    theorem,
                    DirectDerivation::Proof {
                        proof: *value,
                        proposition: proposition.reference(),
                        steps,
                    },
                )],
            });
        }
        let (name, lowered, derivation) = match declaration {
            Declaration::Axiom { header, .. } => {
                Self::require_monomorphic(&header.level_params)?;
                let declared = self.lower_expr(header.ty, tables, &mut Vec::new())?;
                let name = u64::try_from(header.name.0).map_err(|_| DirectError::Unsupported {
                    feature: "name indices beyond u64".to_owned(),
                })?;
                let object = match declared {
                    Lowered::Kind(kind) => Lowered::Type(
                        self.kernel
                            .ty_fv(name, kind)
                            .map_err(|source| DirectError::Construction { source })?,
                    ),
                    Lowered::Type(ty) => Lowered::Term(
                        self.kernel
                            .tm_fv(name, ty)
                            .map_err(|source| DirectError::Construction { source })?,
                    ),
                    Lowered::Term(_) => {
                        return Err(DirectError::Category {
                            expected: "type or kind",
                            actual: "term",
                        });
                    }
                };
                (header.name, object, None)
            }
            Declaration::Definition { header, value, .. }
            | Declaration::Opaque { header, value, .. } => {
                Self::require_monomorphic(&header.level_params)?;
                let declared_value = self.lower_expr(header.ty, tables, &mut Vec::new())?;
                let declared = Self::expect_type(declared_value)?;
                let term_value = self.lower_expr(*value, tables, &mut Vec::new())?;
                let term = Self::expect_term(term_value)?;
                let actual = self
                    .kernel
                    .classifier(term)
                    .map_err(|source| DirectError::Construction { source })?;
                if actual != declared {
                    let evidence = self
                        .conversion
                        .prove(&mut self.kernel, actual, declared)
                        .map_err(|source| DirectError::Conversion { source })?;
                    self.conversions.push(evidence);
                }
                (
                    header.name,
                    Lowered::Term(term),
                    Some(DirectDerivation::HasType { term, ty: declared }),
                )
            }
            Declaration::Theorem { .. } => unreachable!("handled above"),
            Declaration::Quotient { .. } => return Self::unsupported("quotient declarations"),
            Declaration::Inductive { .. } => return Self::unsupported("inductive declarations"),
        };
        self.constants.insert(name, lowered);
        let object = match lowered {
            Lowered::Kind(value) | Lowered::Type(value) | Lowered::Term(value) => value,
        };
        let artifacts = Artifacts {
            objects: vec![(object, syntax)],
            theorems: Vec::new(),
        };
        // Direct construction validates typing but does not itself create a HOL
        // theorem. A deep-embedding backend will populate theorem artifacts.
        let _ = derivation;
        Ok(artifacts)
    }
}

impl<C: ConversionTactic> DirectHol<C> {
    fn lower_proposition(
        &mut self,
        id: ExprId,
        tables: &Tables,
    ) -> Result<Proposition, DirectError<C::Error>> {
        if let Some(proposition) = self.propositions.get(&id) {
            return Ok(proposition.clone());
        }
        let (head, arguments) = application_spine(id, tables);
        let proposition = if const_named(head, tables, &["Eq"]) && arguments.len() == 3 {
            let ty_value = self.lower_expr(arguments[0], tables, &mut Vec::new())?;
            let ty = Self::expect_type(ty_value)?;
            let left_value = self.lower_expr(arguments[1], tables, &mut Vec::new())?;
            let left = Self::expect_term(left_value)?;
            let right_value = self.lower_expr(arguments[2], tables, &mut Vec::new())?;
            let right = Self::expect_term(right_value)?;
            let reference = self
                .kernel
                .eq_at(self.bool_type()?, ty, left, right)
                .map_err(|source| DirectError::Construction { source })?;
            Proposition::Equality {
                expression: id,
                reference,
                ty,
                left,
                right,
            }
        } else {
            match &tables.expressions[id.0] {
                Expr::Forall { ty, body, .. } => {
                    if occurs_bound(*body, 0, tables, 0) {
                        return Self::unsupported("dependent propositions");
                    }
                    let left = self.lower_proposition(*ty, tables)?;
                    let right = self.lower_proposition(*body, tables)?;
                    let reference = self
                        .kernel
                        .op2(Op2::Imp, left.reference(), right.reference())
                        .map_err(|source| DirectError::Construction { source })?;
                    Proposition::Implication {
                        expression: id,
                        reference,
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
                Expr::MData { expression, .. } => self.lower_proposition(*expression, tables)?,
                _ => {
                    let lowered = self.lower_expr(id, tables, &mut Vec::new())?;
                    let reference = Self::expect_term(lowered)?;
                    let classifier = self
                        .kernel
                        .classifier(reference)
                        .map_err(|source| DirectError::Construction { source })?;
                    if classifier != self.bool_type()? {
                        return Err(DirectError::ProofMismatch { proof: id.0 });
                    }
                    Proposition::Atom {
                        expression: id,
                        reference,
                    }
                }
            }
        };
        self.propositions.insert(id, proposition.clone());
        Ok(proposition)
    }

    fn prove(
        &mut self,
        proof: ExprId,
        expected: &Proposition,
        tables: &Tables,
        context: &mut Vec<Ref>,
        steps: &mut Vec<DirectProofStep>,
    ) -> Result<ThmId, DirectError<C::Error>> {
        let (head, arguments) = application_spine(proof, tables);
        if const_named(head, tables, &["Eq", "refl"]) && arguments.len() == 2 {
            return self
                .prove_equality_reflexivity(proof, &arguments, expected, tables, context, steps);
        }
        match &tables.expressions[proof.0] {
            Expr::BVar(index) => {
                let position =
                    context
                        .len()
                        .checked_sub(index + 1)
                        .ok_or(DirectError::BoundVariable {
                            index: *index,
                            depth: context.len(),
                        })?;
                let proposition = context[position];
                if proposition != expected.reference() {
                    return Err(DirectError::ProofMismatch { proof: proof.0 });
                }
                let theorem = self
                    .kernel
                    .identity(Lit::positive(proposition.get()))
                    .map_err(|source| DirectError::Construction { source })?;
                for (hypothesis_position, hypothesis) in context.iter().enumerate() {
                    if hypothesis_position != position {
                        self.kernel
                            .weaken(theorem, &[Lit::positive(hypothesis.get())], &[])
                            .map_err(|source| DirectError::Construction { source })?;
                    }
                }
                steps.push(DirectProofStep::Hypothesis {
                    proof,
                    proposition,
                    theorem,
                });
                Ok(theorem)
            }
            Expr::Lam { ty, body, .. } => {
                let Proposition::Implication {
                    reference,
                    left,
                    right,
                    ..
                } = expected
                else {
                    return Err(DirectError::ProofMismatch { proof: proof.0 });
                };
                if *ty != left.expression() {
                    return Err(DirectError::ProofMismatch { proof: proof.0 });
                }
                context.push(left.reference());
                let premise_result = self.prove(*body, right, tables, context, steps);
                context.pop();
                let premise = premise_result?;
                let theorem = self
                    .kernel
                    .imp_right(premise, Lit::positive(reference.get()))
                    .map_err(|source| DirectError::Construction { source })?;
                steps.push(DirectProofStep::ImplicationIntroduction {
                    proof,
                    implication: *reference,
                    premise,
                    theorem,
                });
                Ok(theorem)
            }
            Expr::Const { name, universes } if universes.is_empty() => {
                let Some((proposition, source)) = self.theorems.get(name).copied() else {
                    return Self::unsupported("proof constants without an earlier checked theorem");
                };
                if proposition != expected.reference() {
                    return Err(DirectError::ProofMismatch { proof: proof.0 });
                }
                let theorem = self
                    .kernel
                    .copy_theorem(source)
                    .map_err(|source| DirectError::Construction { source })?;
                for hypothesis in context.iter() {
                    self.kernel
                        .weaken(theorem, &[Lit::positive(hypothesis.get())], &[])
                        .map_err(|source| DirectError::Construction { source })?;
                }
                steps.push(DirectProofStep::KnownTheorem {
                    proof,
                    proposition,
                    source,
                    theorem,
                });
                Ok(theorem)
            }
            Expr::MData { expression, .. } => {
                self.prove(*expression, expected, tables, context, steps)
            }
            _ => Self::unsupported("proof terms beyond implication introduction and hypotheses"),
        }
    }

    fn prove_equality_reflexivity(
        &mut self,
        proof: ExprId,
        arguments: &[ExprId],
        expected: &Proposition,
        tables: &Tables,
        context: &[Ref],
        steps: &mut Vec<DirectProofStep>,
    ) -> Result<ThmId, DirectError<C::Error>> {
        let Proposition::Equality {
            reference,
            ty,
            left,
            right,
            ..
        } = expected
        else {
            return Err(DirectError::ProofMismatch { proof: proof.0 });
        };
        let proof_ty_value = self.lower_expr(arguments[0], tables, &mut Vec::new())?;
        let proof_ty = Self::expect_type(proof_ty_value)?;
        let value_value = self.lower_expr(arguments[1], tables, &mut Vec::new())?;
        let value = Self::expect_term(value_value)?;
        if proof_ty != *ty || value != *left || left != right {
            return Err(DirectError::ProofMismatch { proof: proof.0 });
        }
        let theorem = self
            .kernel
            .refl_at(*reference)
            .map_err(|source| DirectError::Construction { source })?;
        for hypothesis in context {
            self.kernel
                .weaken(theorem, &[Lit::positive(hypothesis.get())], &[])
                .map_err(|source| DirectError::Construction { source })?;
        }
        steps.push(DirectProofStep::EqualityReflexivity {
            proof,
            equality: *reference,
            theorem,
        });
        Ok(theorem)
    }

    fn take_binder_name(&mut self) -> Result<u64, DirectError<C::Error>> {
        let name = self.next_binder;
        self.next_binder =
            self.next_binder
                .checked_sub(1)
                .ok_or_else(|| DirectError::Unsupported {
                    feature: "exhausted direct-HOL binder names".to_owned(),
                })?;
        Ok(name)
    }

    fn lower_expr(
        &mut self,
        id: ExprId,
        tables: &Tables,
        context: &mut Vec<Ref>,
    ) -> Result<Lowered, DirectError<C::Error>> {
        match &tables.expressions[id.0] {
            Expr::BVar(index) => {
                let position =
                    context
                        .len()
                        .checked_sub(index + 1)
                        .ok_or(DirectError::BoundVariable {
                            index: *index,
                            depth: context.len(),
                        })?;
                Ok(Lowered::Term(context[position]))
            }
            Expr::Sort(level) => match &tables.levels[level.0] {
                Level::Zero => Ok(Lowered::Type(self.bool_type()?)),
                Level::Succ(inner) if matches!(tables.levels[inner.0], Level::Zero) => {
                    Ok(Lowered::Kind(self.star()?))
                }
                _ => Self::unsupported("universe levels above Type or universe polymorphism"),
            },
            Expr::Const { name, universes } => {
                if !universes.is_empty() {
                    return Self::unsupported("universe-instantiated constants");
                }
                self.constants
                    .get(name)
                    .copied()
                    .ok_or(DirectError::MissingConstant { name: name.0 })
            }
            Expr::App { function, argument } => {
                let function_value = self.lower_expr(*function, tables, context)?;
                let function = Self::expect_term(function_value)?;
                let argument_value = self.lower_expr(*argument, tables, context)?;
                let argument = Self::expect_term(argument_value)?;
                self.kernel
                    .app(function, argument)
                    .map(Lowered::Term)
                    .map_err(|source| DirectError::Construction { source })
            }
            Expr::Lam { ty, body, .. } => {
                let ty_value = self.lower_expr(*ty, tables, context)?;
                let ty = Self::expect_type(ty_value)?;
                let name = self.take_binder_name()?;
                let binder = self
                    .kernel
                    .tm_fv(name, ty)
                    .map_err(|source| DirectError::Construction { source })?;
                context.push(binder);
                let body_result = self.lower_expr(*body, tables, context);
                context.pop();
                let body = Self::expect_term(body_result?)?;
                self.kernel
                    .lam(binder, body)
                    .map(Lowered::Term)
                    .map_err(|source| DirectError::Construction { source })
            }
            Expr::Forall { body, ty, .. } => {
                if occurs_bound(*body, 0, tables, 0) {
                    return Self::unsupported("dependent forallE");
                }
                let domain_value = self.lower_expr(*ty, tables, context)?;
                let domain = Self::expect_type(domain_value)?;
                let codomain_value = self.lower_expr(*body, tables, context)?;
                let codomain = Self::expect_type(codomain_value)?;
                self.kernel
                    .ty_arr(domain, codomain)
                    .map(Lowered::Type)
                    .map_err(|source| DirectError::Construction { source })
            }
            Expr::MData { expression, .. } => self.lower_expr(*expression, tables, context),
            Expr::Let { .. } => {
                Self::unsupported("let expressions before a zeta conversion tactic")
            }
            Expr::Proj { .. } => Self::unsupported("projections before an iota conversion tactic"),
            Expr::NatLit(_) => Self::unsupported("natural literals"),
            Expr::StrLit(_) => Self::unsupported("string literals"),
        }
    }

    fn expect_type(value: Lowered) -> Result<Ref, DirectError<C::Error>> {
        match value {
            Lowered::Type(value) => Ok(value),
            other => Err(DirectError::Category {
                expected: "type",
                actual: other.category(),
            }),
        }
    }

    fn expect_term(value: Lowered) -> Result<Ref, DirectError<C::Error>> {
        match value {
            Lowered::Term(value) => Ok(value),
            other => Err(DirectError::Category {
                expected: "term",
                actual: other.category(),
            }),
        }
    }

    fn star(&self) -> Result<Ref, DirectError<C::Error>> {
        self.star.ok_or_else(|| DirectError::Unsupported {
            feature: "backend use before metadata".to_owned(),
        })
    }

    fn bool_type(&self) -> Result<Ref, DirectError<C::Error>> {
        self.bool_ty.ok_or_else(|| DirectError::Unsupported {
            feature: "backend use before metadata".to_owned(),
        })
    }

    fn require_monomorphic(params: &[NameId]) -> Result<(), DirectError<C::Error>> {
        if params.is_empty() {
            Ok(())
        } else {
            Self::unsupported("universe-polymorphic declarations")
        }
    }

    fn unsupported<T>(feature: &str) -> Result<T, DirectError<C::Error>> {
        Err(DirectError::Unsupported {
            feature: feature.to_owned(),
        })
    }
}

fn occurs_bound(id: ExprId, target: usize, tables: &Tables, depth: usize) -> bool {
    match &tables.expressions[id.0] {
        Expr::BVar(index) => *index == target + depth,
        Expr::App { function, argument } => {
            occurs_bound(*function, target, tables, depth)
                || occurs_bound(*argument, target, tables, depth)
        }
        Expr::Lam { ty, body, .. } | Expr::Forall { ty, body, .. } => {
            occurs_bound(*ty, target, tables, depth)
                || occurs_bound(*body, target, tables, depth + 1)
        }
        Expr::Let {
            ty, value, body, ..
        } => {
            occurs_bound(*ty, target, tables, depth)
                || occurs_bound(*value, target, tables, depth)
                || occurs_bound(*body, target, tables, depth + 1)
        }
        Expr::Proj { structure, .. } => occurs_bound(*structure, target, tables, depth),
        Expr::MData { expression, .. } => occurs_bound(*expression, target, tables, depth),
        Expr::Sort(_) | Expr::Const { .. } | Expr::NatLit(_) | Expr::StrLit(_) => false,
    }
}

fn application_spine(id: ExprId, tables: &Tables) -> (ExprId, Vec<ExprId>) {
    let mut head = id;
    let mut arguments = Vec::new();
    while let Expr::App { function, argument } = tables.expressions[head.0] {
        arguments.push(argument);
        head = function;
    }
    arguments.reverse();
    (head, arguments)
}

fn const_named(id: ExprId, tables: &Tables, expected: &[&str]) -> bool {
    let Expr::Const { name, .. } = &tables.expressions[id.0] else {
        return false;
    };
    let mut components = Vec::new();
    let mut current = *name;
    loop {
        match &tables.names[current.0] {
            Name::Anonymous => break,
            Name::Str { prefix, value } => {
                components.push(value.as_str());
                current = *prefix;
            }
            Name::Num { .. } => return false,
        }
    }
    components.reverse();
    components == expected
}
