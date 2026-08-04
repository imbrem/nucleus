//! Bounded, transport-neutral recipes for one generative HOL proof session.
//!
//! Recipe references are append-only indexes. They are deliberately not
//! Nucleus proof capabilities: replay checks every step inside one fresh
//! generative session, and only inert database coordinates leave that scope.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::hol::{ContextEquivalence, ContextUnion};
use covalence_nucleus::{
    Connection, ContextId, ContextImplication, Conversion, Hol, Policy, ProofError, TermId,
    TermInstantiation, Theorem, TypeId, TypeInstantiation,
};

/// Maximum number of steps accepted in one untrusted proof recipe.
pub const MAX_LOCAL_HOL_PROOF_STEPS: usize = 4_096;

/// Maximum aggregate number of variable-length operands in one proof recipe.
pub const MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS: usize = 4_096;

/// A slot produced by a strictly earlier step in the same recipe.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LocalHolProofRef(u32);

impl LocalHolProofRef {
    /// Constructs a recipe-local reference from its zero-based step index.
    #[must_use]
    pub const fn from_u32(index: u32) -> Self {
        Self(index)
    }

    /// Returns the zero-based producing-step index.
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0
    }
}

/// One exact free-variable replacement carried by an untrusted proof recipe.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalHolTermInstantiation {
    /// Exact free-variable term to replace.
    pub variable: TermId,
    /// Locally closed, same-typed replacement term.
    pub replacement: TermId,
}

/// One exact free-type-variable replacement carried by an untrusted proof recipe.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalHolTypeInstantiation {
    /// Exact free-type-variable type to replace.
    pub variable: TypeId,
    /// Well-formed replacement type, copied without recursive substitution.
    pub replacement: TypeId,
}

/// One checked operation replayed in a fresh Nucleus proof session.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LocalHolProofStep {
    /// Reconstruct an exact persisted theorem capability.
    LoadTheorem {
        /// Assumption context.
        context: ContextId,
        /// Boolean conclusion.
        conclusion: TermId,
    },
    /// Apply the hypothesis rule.
    Hypothesis {
        /// Assumption context.
        context: ContextId,
        /// Context member to prove.
        term: TermId,
    },
    /// Apply primitive truth.
    Truth {
        /// Assumption context.
        context: ContextId,
    },
    /// Prove a closed term equal to itself.
    Reflexivity {
        /// Assumption context.
        context: ContextId,
        /// Closed term.
        term: TermId,
    },
    /// Apply the legacy closed beta theorem rule.
    Beta {
        /// Assumption context.
        context: ContextId,
        /// Closed lambda abstraction.
        abstraction: TermId,
        /// Closed argument.
        argument: TermId,
    },
    /// Persist an earlier theorem as an authoritative judgement.
    PersistTheorem {
        /// Earlier theorem slot.
        theorem: LocalHolProofRef,
    },
    /// Introduce reflexive conversion, including for an open term.
    ConversionReflexivity {
        /// Admitted term.
        term: TermId,
    },
    /// Reverse an earlier conversion.
    ConversionSymmetry {
        /// Earlier conversion slot.
        conversion: LocalHolProofRef,
    },
    /// Compose two conversions with an identical middle endpoint.
    ConversionTransitivity {
        /// First conversion slot.
        first: LocalHolProofRef,
        /// Second conversion slot.
        second: LocalHolProofRef,
    },
    /// Apply application congruence to function and argument conversions.
    ConversionApplication {
        /// Function conversion slot.
        function: LocalHolProofRef,
        /// Argument conversion slot.
        argument: LocalHolProofRef,
    },
    /// Close one common conversion boundary beneath a lambda.
    ConversionLambda {
        /// Captured binder type.
        parameter_type: TypeId,
        /// Body conversion slot.
        body: LocalHolProofRef,
    },
    /// Apply conversion congruence beneath Hilbert choice.
    ConversionEpsilon {
        /// Earlier Boolean-valued predicate conversion slot.
        predicate: LocalHolProofRef,
    },
    /// Produce one closed beta conversion.
    ConversionBeta {
        /// Closed lambda abstraction.
        abstraction: TermId,
        /// Closed argument.
        argument: TermId,
    },
    /// Produce the restricted closed eta conversion for a function.
    ConversionEta {
        /// Closed function term.
        function: TermId,
    },
    /// Turn a closed conversion into an equality theorem.
    ConversionEquality {
        /// Assumption context.
        context: ContextId,
        /// Closed conversion slot.
        conversion: LocalHolProofRef,
    },
    /// Transport a Boolean theorem along a closed conversion.
    ConvertTheorem {
        /// Earlier theorem slot.
        theorem: LocalHolProofRef,
        /// Boolean conversion slot.
        conversion: LocalHolProofRef,
    },
    /// Introduce an exact context implication from theorem witnesses.
    ContextImplication {
        /// Context shared by every witness.
        antecedent: ContextId,
        /// Context whose members are witnessed exactly.
        consequent: ContextId,
        /// Distinct earlier theorem slots.
        witnesses: Vec<LocalHolProofRef>,
    },
    /// Reconstruct an exact persisted implication capability.
    LoadContextImplication {
        /// Source context.
        antecedent: ContextId,
        /// Target context.
        consequent: ContextId,
    },
    /// Check and compose an explicit persisted implication path.
    ContextImplicationPath {
        /// Nonempty context path.
        path: Vec<ContextId>,
    },
    /// Persist an earlier implication as an authoritative edge.
    PersistContextImplication {
        /// Earlier implication slot.
        implication: LocalHolProofRef,
    },
    /// Weaken a theorem along an implication.
    Weaken {
        /// Earlier implication slot.
        implication: LocalHolProofRef,
        /// Earlier theorem under the implication target.
        theorem: LocalHolProofRef,
    },
    /// Apply equality modus ponens to two theorem capabilities.
    EqualityModusPonens {
        /// Earlier equality theorem slot.
        equality: LocalHolProofRef,
        /// Earlier left-premise theorem slot.
        premise: LocalHolProofRef,
    },
    /// Apply typed Leibniz substitution to two theorem capabilities.
    EqualitySubstitution {
        /// Earlier equality theorem slot.
        equality: LocalHolProofRef,
        /// Closed predicate term.
        predicate: TermId,
        /// Earlier theorem proving the predicate at the equality's left side.
        premise: LocalHolProofRef,
    },
    /// Apply deduction antisymmetry to two theorem capabilities.
    DeductionAntisymmetry {
        /// First earlier theorem slot.
        first: LocalHolProofRef,
        /// Second earlier theorem slot.
        second: LocalHolProofRef,
    },
    /// Apply Hilbert choice to an earlier theorem proving a predicate application.
    Choice {
        /// Earlier theorem slot used as the exact choice premise.
        premise: LocalHolProofRef,
    },
    /// Simultaneously instantiate exact free variables in an earlier theorem.
    InstantiateTerms {
        /// Earlier theorem slot.
        theorem: LocalHolProofRef,
        /// Bounded variable/replacement pairs.
        instantiations: Vec<LocalHolTermInstantiation>,
    },
    /// Simultaneously instantiate exact free type variables in an earlier theorem.
    InstantiateTypes {
        /// Earlier theorem slot.
        theorem: LocalHolProofRef,
        /// Bounded variable/replacement pairs.
        instantiations: Vec<LocalHolTypeInstantiation>,
    },
    /// Abstract one exact free-variable node in both sides of an equality theorem.
    Abstraction {
        /// Earlier equality theorem slot.
        theorem: LocalHolProofRef,
        /// Exact free-variable term to bind.
        variable: TermId,
    },
    /// Check and persist an exact structural context union.
    ContextUnion {
        /// Left input context.
        left: ContextId,
        /// Right input context.
        right: ContextId,
        /// Claimed exact union context.
        result: ContextId,
    },
    /// Reconstruct and recheck an exact persisted union capability.
    LoadContextUnion {
        /// Left input context.
        left: ContextId,
        /// Right input context.
        right: ContextId,
    },
    /// Package two opposite implication capabilities as an equivalence.
    ContextEquivalence {
        /// Forward implication slot.
        forward: LocalHolProofRef,
        /// Backward implication slot.
        backward: LocalHolProofRef,
    },
}

/// Inert observation of one checked step. Its position is the reference used
/// by later steps in the same recipe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LocalHolProofOutput {
    /// A checked theorem coordinate.
    Theorem {
        /// Assumption context.
        context: ContextId,
        /// Boolean conclusion.
        conclusion: TermId,
    },
    /// A checked conversion observation.
    Conversion {
        /// Left endpoint.
        left: TermId,
        /// Right endpoint.
        right: TermId,
        /// Common endpoint type.
        ty: TypeId,
        /// Whether the conversion has no external de Bruijn boundary.
        closed: bool,
    },
    /// A checked implication observation.
    ContextImplication {
        /// Source context.
        antecedent: ContextId,
        /// Target context.
        consequent: ContextId,
    },
    /// A checked exact-union observation.
    ContextUnion {
        /// Left input.
        left: ContextId,
        /// Right input.
        right: ContextId,
        /// Exact result.
        result: ContextId,
    },
    /// A checked context-equivalence observation.
    ContextEquivalence {
        /// Left context.
        left: ContextId,
        /// Right context.
        right: ContextId,
    },
    /// The requested exact persisted theorem did not exist.
    MissingTheorem,
    /// The requested exact persisted implication did not exist.
    MissingContextImplication,
    /// The requested exact persisted union did not exist.
    MissingContextUnion,
    /// A persistence-only step completed.
    Unit,
}

/// Static capability sort produced by a recipe step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalHolProofSort {
    /// Theorem capability.
    Theorem,
    /// Definitional-conversion capability.
    Conversion,
    /// Context-implication capability.
    ContextImplication,
    /// Exact context-union capability.
    ContextUnion,
    /// Context-equivalence capability.
    ContextEquivalence,
    /// A load produced no capability at replay time.
    Missing,
    /// A persistence-only result.
    Unit,
}

/// Rejection of an untrusted recipe or of one checked Nucleus rule.
#[derive(Debug)]
pub enum LocalHolProofScriptError {
    /// The recipe exceeds its total step bound.
    TooManySteps {
        /// Supplied step count.
        count: usize,
        /// Fixed maximum.
        maximum: usize,
    },
    /// One variable-length step exceeds its operand bound.
    TooManyOperands {
        /// Rejecting step index.
        step: u32,
        /// Supplied operand count.
        count: usize,
        /// Fixed maximum.
        maximum: usize,
    },
    /// The aggregate of all variable-length operands exceeds its fixed bound.
    TooManyTotalOperands {
        /// Aggregate operand count at rejection.
        count: usize,
        /// Fixed maximum.
        maximum: usize,
    },
    /// A reference is forward, cyclic, or outside the recipe.
    InvalidReference {
        /// Rejecting step index.
        step: u32,
        /// Invalid recipe-local reference.
        reference: LocalHolProofRef,
    },
    /// A reference names a capability of another sort.
    WrongSort {
        /// Rejecting step index.
        step: u32,
        /// Sort-confused recipe-local reference.
        reference: LocalHolProofRef,
        /// Required capability sort.
        expected: LocalHolProofSort,
        /// Observed static or replay-time sort.
        actual: LocalHolProofSort,
    },
    /// A witness list repeats one slot, which cannot exactly cover a set.
    RepeatedReference {
        /// Rejecting step index.
        step: u32,
        /// Repeated recipe-local reference.
        reference: LocalHolProofRef,
    },
    /// Nucleus rejected a checked operation.
    Proof(ProofError),
}

impl fmt::Display for LocalHolProofScriptError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManySteps { count, maximum } => {
                write!(
                    formatter,
                    "HOL proof recipe has {count} steps; maximum is {maximum}"
                )
            }
            Self::TooManyOperands {
                step,
                count,
                maximum,
            } => write!(
                formatter,
                "HOL proof recipe step {step} has {count} operands; maximum is {maximum}"
            ),
            Self::TooManyTotalOperands { count, maximum } => write!(
                formatter,
                "HOL proof recipe has {count} total variable-length operands; maximum is {maximum}"
            ),
            Self::InvalidReference { step, reference } => write!(
                formatter,
                "HOL proof recipe step {step} references non-earlier slot {}",
                reference.get()
            ),
            Self::WrongSort {
                step,
                reference,
                expected,
                actual,
            } => write!(
                formatter,
                "HOL proof recipe step {step} references {:?} slot {} as {:?}",
                actual,
                reference.get(),
                expected
            ),
            Self::RepeatedReference { step, reference } => write!(
                formatter,
                "HOL proof recipe step {step} repeats witness slot {}",
                reference.get()
            ),
            Self::Proof(error) => error.fmt(formatter),
        }
    }
}

impl StdError for LocalHolProofScriptError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Proof(error) => Some(error),
            _ => None,
        }
    }
}

impl From<ProofError> for LocalHolProofScriptError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

enum Capability<'brand> {
    Theorem(Theorem<'brand>),
    Conversion(Conversion<'brand>),
    ContextImplication(ContextImplication<'brand>),
    ContextUnion(ContextUnion<'brand>),
    ContextEquivalence(ContextEquivalence<'brand>),
    Missing,
    Unit,
}

impl Capability<'_> {
    fn sort(&self) -> LocalHolProofSort {
        match self {
            Self::Theorem(_) => LocalHolProofSort::Theorem,
            Self::Conversion(_) => LocalHolProofSort::Conversion,
            Self::ContextImplication(_) => LocalHolProofSort::ContextImplication,
            Self::ContextUnion(_) => LocalHolProofSort::ContextUnion,
            Self::ContextEquivalence(_) => LocalHolProofSort::ContextEquivalence,
            Self::Missing => LocalHolProofSort::Missing,
            Self::Unit => LocalHolProofSort::Unit,
        }
    }

    fn output(&self, missing: Option<LocalHolProofOutput>) -> LocalHolProofOutput {
        match self {
            Self::Theorem(value) => LocalHolProofOutput::Theorem {
                context: value.context(),
                conclusion: value.conclusion(),
            },
            Self::Conversion(value) => LocalHolProofOutput::Conversion {
                left: value.left(),
                right: value.right(),
                ty: value.ty(),
                closed: value.is_closed(),
            },
            Self::ContextImplication(value) => LocalHolProofOutput::ContextImplication {
                antecedent: value.antecedent(),
                consequent: value.consequent(),
            },
            Self::ContextUnion(value) => LocalHolProofOutput::ContextUnion {
                left: value.left(),
                right: value.right(),
                result: value.result(),
            },
            Self::ContextEquivalence(value) => LocalHolProofOutput::ContextEquivalence {
                left: value.left(),
                right: value.right(),
            },
            Self::Missing => missing.expect("load steps label missing capabilities"),
            Self::Unit => LocalHolProofOutput::Unit,
        }
    }
}

fn slot<'a, 'brand>(
    slots: &'a [Option<Capability<'brand>>],
    step: usize,
    reference: LocalHolProofRef,
) -> Result<&'a Capability<'brand>, LocalHolProofScriptError> {
    let index = usize::try_from(reference.get()).unwrap_or(usize::MAX);
    if index >= step {
        return Err(LocalHolProofScriptError::InvalidReference {
            step: u32::try_from(step).unwrap_or(u32::MAX),
            reference,
        });
    }
    Ok(slots[index]
        .as_ref()
        .expect("recipe capabilities are restored before the next step"))
}

macro_rules! typed_slot {
    ($name:ident, $variant:ident, $ty:ty, $sort:ident) => {
        fn $name<'a, 'brand>(
            slots: &'a [Option<Capability<'brand>>],
            step: usize,
            reference: LocalHolProofRef,
        ) -> Result<&'a $ty, LocalHolProofScriptError> {
            let value = slot(slots, step, reference)?;
            if let Capability::$variant(value) = value {
                Ok(value)
            } else {
                Err(LocalHolProofScriptError::WrongSort {
                    step: u32::try_from(step).unwrap_or(u32::MAX),
                    reference,
                    expected: LocalHolProofSort::$sort,
                    actual: value.sort(),
                })
            }
        }
    };
}

typed_slot!(theorem, Theorem, Theorem<'brand>, Theorem);
typed_slot!(conversion, Conversion, Conversion<'brand>, Conversion);
typed_slot!(
    implication,
    ContextImplication,
    ContextImplication<'brand>,
    ContextImplication
);

fn declared_sort(step: &LocalHolProofStep) -> LocalHolProofSort {
    match step {
        LocalHolProofStep::LoadTheorem { .. }
        | LocalHolProofStep::Hypothesis { .. }
        | LocalHolProofStep::Truth { .. }
        | LocalHolProofStep::Reflexivity { .. }
        | LocalHolProofStep::Beta { .. }
        | LocalHolProofStep::ConversionEquality { .. }
        | LocalHolProofStep::ConvertTheorem { .. }
        | LocalHolProofStep::Weaken { .. }
        | LocalHolProofStep::EqualityModusPonens { .. }
        | LocalHolProofStep::EqualitySubstitution { .. }
        | LocalHolProofStep::DeductionAntisymmetry { .. }
        | LocalHolProofStep::Choice { .. }
        | LocalHolProofStep::InstantiateTerms { .. }
        | LocalHolProofStep::InstantiateTypes { .. }
        | LocalHolProofStep::Abstraction { .. } => LocalHolProofSort::Theorem,
        LocalHolProofStep::ConversionReflexivity { .. }
        | LocalHolProofStep::ConversionSymmetry { .. }
        | LocalHolProofStep::ConversionTransitivity { .. }
        | LocalHolProofStep::ConversionApplication { .. }
        | LocalHolProofStep::ConversionLambda { .. }
        | LocalHolProofStep::ConversionEpsilon { .. }
        | LocalHolProofStep::ConversionBeta { .. }
        | LocalHolProofStep::ConversionEta { .. } => LocalHolProofSort::Conversion,
        LocalHolProofStep::ContextImplication { .. }
        | LocalHolProofStep::LoadContextImplication { .. }
        | LocalHolProofStep::ContextImplicationPath { .. } => LocalHolProofSort::ContextImplication,
        LocalHolProofStep::ContextUnion { .. } | LocalHolProofStep::LoadContextUnion { .. } => {
            LocalHolProofSort::ContextUnion
        }
        LocalHolProofStep::ContextEquivalence { .. } => LocalHolProofSort::ContextEquivalence,
        LocalHolProofStep::PersistTheorem { .. }
        | LocalHolProofStep::PersistContextImplication { .. } => LocalHolProofSort::Unit,
    }
}

fn preflight_reference(
    sorts: &[LocalHolProofSort],
    step: usize,
    reference: LocalHolProofRef,
    expected: LocalHolProofSort,
) -> Result<(), LocalHolProofScriptError> {
    let index = usize::try_from(reference.get()).unwrap_or(usize::MAX);
    let Some(actual) = sorts.get(index).copied().filter(|_| index < step) else {
        return Err(LocalHolProofScriptError::InvalidReference {
            step: u32::try_from(step).unwrap_or(u32::MAX),
            reference,
        });
    };
    if actual != expected {
        return Err(LocalHolProofScriptError::WrongSort {
            step: u32::try_from(step).unwrap_or(u32::MAX),
            reference,
            expected,
            actual,
        });
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn preflight(steps: &[LocalHolProofStep]) -> Result<(), LocalHolProofScriptError> {
    if steps.len() > MAX_LOCAL_HOL_PROOF_STEPS {
        return Err(LocalHolProofScriptError::TooManySteps {
            count: steps.len(),
            maximum: MAX_LOCAL_HOL_PROOF_STEPS,
        });
    }
    let sorts = steps.iter().map(declared_sort).collect::<Vec<_>>();
    let mut total_operands = 0_usize;
    for (index, step) in steps.iter().enumerate() {
        let check = |reference, expected| preflight_reference(&sorts, index, reference, expected);
        match step {
            LocalHolProofStep::PersistTheorem { theorem: source } => {
                check(*source, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::ConversionSymmetry { conversion: source }
            | LocalHolProofStep::ConversionLambda { body: source, .. }
            | LocalHolProofStep::ConversionEpsilon { predicate: source }
            | LocalHolProofStep::ConversionEquality {
                conversion: source, ..
            } => check(*source, LocalHolProofSort::Conversion)?,
            LocalHolProofStep::ConversionTransitivity { first, second }
            | LocalHolProofStep::ConversionApplication {
                function: first,
                argument: second,
            } => {
                check(*first, LocalHolProofSort::Conversion)?;
                check(*second, LocalHolProofSort::Conversion)?;
            }
            LocalHolProofStep::ConvertTheorem {
                theorem: theorem_ref,
                conversion: conversion_ref,
            } => {
                check(*theorem_ref, LocalHolProofSort::Theorem)?;
                check(*conversion_ref, LocalHolProofSort::Conversion)?;
            }
            LocalHolProofStep::ContextImplication { witnesses, .. } => {
                if witnesses.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                    return Err(LocalHolProofScriptError::TooManyOperands {
                        step: u32::try_from(index).unwrap_or(u32::MAX),
                        count: witnesses.len(),
                        maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                    });
                }
                total_operands = total_operands
                    .checked_add(witnesses.len())
                    .filter(|count| *count <= MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS)
                    .ok_or(LocalHolProofScriptError::TooManyTotalOperands {
                        count: total_operands.saturating_add(witnesses.len()),
                        maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
                    })?;
                let mut seen = HashSet::with_capacity(witnesses.len());
                for reference in witnesses {
                    if !seen.insert(*reference) {
                        return Err(LocalHolProofScriptError::RepeatedReference {
                            step: u32::try_from(index).unwrap_or(u32::MAX),
                            reference: *reference,
                        });
                    }
                    check(*reference, LocalHolProofSort::Theorem)?;
                }
            }
            LocalHolProofStep::ContextImplicationPath { path } => {
                if path.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                    return Err(LocalHolProofScriptError::TooManyOperands {
                        step: u32::try_from(index).unwrap_or(u32::MAX),
                        count: path.len(),
                        maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                    });
                }
                total_operands = total_operands
                    .checked_add(path.len())
                    .filter(|count| *count <= MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS)
                    .ok_or(LocalHolProofScriptError::TooManyTotalOperands {
                        count: total_operands.saturating_add(path.len()),
                        maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
                    })?;
            }
            LocalHolProofStep::PersistContextImplication {
                implication: source,
            } => check(*source, LocalHolProofSort::ContextImplication)?,
            LocalHolProofStep::Weaken {
                implication: implication_ref,
                theorem: theorem_ref,
            } => {
                check(*implication_ref, LocalHolProofSort::ContextImplication)?;
                check(*theorem_ref, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::EqualityModusPonens { equality, premise }
            | LocalHolProofStep::EqualitySubstitution {
                equality, premise, ..
            } => {
                check(*equality, LocalHolProofSort::Theorem)?;
                check(*premise, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::DeductionAntisymmetry { first, second } => {
                check(*first, LocalHolProofSort::Theorem)?;
                check(*second, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::Choice { premise } => {
                check(*premise, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::InstantiateTerms {
                theorem,
                instantiations,
            } => {
                check(*theorem, LocalHolProofSort::Theorem)?;
                if instantiations.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                    return Err(LocalHolProofScriptError::TooManyOperands {
                        step: u32::try_from(index).unwrap_or(u32::MAX),
                        count: instantiations.len(),
                        maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                    });
                }
                total_operands = total_operands
                    .checked_add(instantiations.len())
                    .filter(|count| *count <= MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS)
                    .ok_or(LocalHolProofScriptError::TooManyTotalOperands {
                        count: total_operands.saturating_add(instantiations.len()),
                        maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
                    })?;
            }
            LocalHolProofStep::InstantiateTypes {
                theorem,
                instantiations,
            } => {
                check(*theorem, LocalHolProofSort::Theorem)?;
                if instantiations.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                    return Err(LocalHolProofScriptError::TooManyOperands {
                        step: u32::try_from(index).unwrap_or(u32::MAX),
                        count: instantiations.len(),
                        maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                    });
                }
                total_operands = total_operands
                    .checked_add(instantiations.len())
                    .filter(|count| *count <= MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS)
                    .ok_or(LocalHolProofScriptError::TooManyTotalOperands {
                        count: total_operands.saturating_add(instantiations.len()),
                        maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
                    })?;
            }
            LocalHolProofStep::Abstraction { theorem, .. } => {
                check(*theorem, LocalHolProofSort::Theorem)?;
            }
            LocalHolProofStep::ContextEquivalence { forward, backward } => {
                check(*forward, LocalHolProofSort::ContextImplication)?;
                check(*backward, LocalHolProofSort::ContextImplication)?;
            }
            LocalHolProofStep::LoadTheorem { .. }
            | LocalHolProofStep::Hypothesis { .. }
            | LocalHolProofStep::Truth { .. }
            | LocalHolProofStep::Reflexivity { .. }
            | LocalHolProofStep::Beta { .. }
            | LocalHolProofStep::ConversionReflexivity { .. }
            | LocalHolProofStep::ConversionBeta { .. }
            | LocalHolProofStep::ConversionEta { .. }
            | LocalHolProofStep::LoadContextImplication { .. }
            | LocalHolProofStep::ContextUnion { .. }
            | LocalHolProofStep::LoadContextUnion { .. } => {}
        }
    }
    Ok(())
}

/// Replays an append-only recipe in exactly one fresh generative proof scope.
///
/// No output is a proof capability and no reference is meaningful in another
/// call. A semantic failure may follow earlier canonical syntax insertion,
/// implicit persistence by [`LocalHolProofStep::ContextUnion`], or explicit
/// persistence steps. Callers needing all-or-nothing database mutation should
/// use a fresh connection or a future transaction wrapper.
///
/// # Errors
///
/// Returns an error if structural preflight rejects the bounded append-only
/// recipe, a runtime load is used as the wrong capability sort, or Nucleus
/// rejects any checked rule, read, or persistence operation.
#[allow(clippy::too_many_lines)]
pub fn run_local_hol_proof_script<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    steps: &[LocalHolProofStep],
) -> Result<Vec<LocalHolProofOutput>, LocalHolProofScriptError> {
    preflight(steps)?;
    connection.with_proof_session(|mut proof| {
        let mut slots = Vec::with_capacity(steps.len());
        let mut outputs = Vec::with_capacity(steps.len());
        for (index, step) in steps.iter().enumerate() {
            let mut missing = None;
            let value = match step {
                LocalHolProofStep::LoadTheorem {
                    context,
                    conclusion,
                } => {
                    if let Some(value) = proof.load_theorem(*context, *conclusion)? {
                        Capability::Theorem(value)
                    } else {
                        missing = Some(LocalHolProofOutput::MissingTheorem);
                        Capability::Missing
                    }
                }
                LocalHolProofStep::Hypothesis { context, term } => {
                    Capability::Theorem(proof.prove_hypothesis(*context, *term)?)
                }
                LocalHolProofStep::Truth { context } => {
                    Capability::Theorem(proof.prove_truth(*context)?)
                }
                LocalHolProofStep::Reflexivity { context, term } => {
                    Capability::Theorem(proof.prove_reflexivity(*context, *term)?)
                }
                LocalHolProofStep::Beta {
                    context,
                    abstraction,
                    argument,
                } => Capability::Theorem(proof.prove_beta(*context, *abstraction, *argument)?),
                LocalHolProofStep::PersistTheorem { theorem: source } => {
                    proof.persist_theorem(theorem(&slots, index, *source)?)?;
                    Capability::Unit
                }
                LocalHolProofStep::ConversionReflexivity { term } => {
                    Capability::Conversion(proof.conversion_reflexivity(*term)?)
                }
                LocalHolProofStep::ConversionSymmetry { conversion: source } => {
                    Capability::Conversion(
                        proof.conversion_symmetry(conversion(&slots, index, *source)?)?,
                    )
                }
                LocalHolProofStep::ConversionTransitivity { first, second } => {
                    Capability::Conversion(proof.conversion_transitivity(
                        conversion(&slots, index, *first)?,
                        conversion(&slots, index, *second)?,
                    )?)
                }
                LocalHolProofStep::ConversionApplication { function, argument } => {
                    Capability::Conversion(proof.conversion_application(
                        conversion(&slots, index, *function)?,
                        conversion(&slots, index, *argument)?,
                    )?)
                }
                LocalHolProofStep::ConversionLambda {
                    parameter_type,
                    body,
                } => Capability::Conversion(
                    proof.conversion_lambda(*parameter_type, conversion(&slots, index, *body)?)?,
                ),
                LocalHolProofStep::ConversionEpsilon { predicate } => Capability::Conversion(
                    proof.conversion_epsilon(conversion(&slots, index, *predicate)?)?,
                ),
                LocalHolProofStep::ConversionBeta {
                    abstraction,
                    argument,
                } => Capability::Conversion(proof.conversion_beta(*abstraction, *argument)?),
                LocalHolProofStep::ConversionEta { function } => {
                    Capability::Conversion(proof.conversion_eta(*function)?)
                }
                LocalHolProofStep::ConversionEquality {
                    context,
                    conversion: source,
                } => Capability::Theorem(
                    proof
                        .prove_conversion_equality(*context, conversion(&slots, index, *source)?)?,
                ),
                LocalHolProofStep::ConvertTheorem {
                    theorem: theorem_ref,
                    conversion: conversion_ref,
                } => Capability::Theorem(proof.convert_theorem(
                    theorem(&slots, index, *theorem_ref)?,
                    conversion(&slots, index, *conversion_ref)?,
                )?),
                LocalHolProofStep::ContextImplication {
                    antecedent,
                    consequent,
                    witnesses,
                } => {
                    if witnesses.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                        return Err(LocalHolProofScriptError::TooManyOperands {
                            step: u32::try_from(index).unwrap_or(u32::MAX),
                            count: witnesses.len(),
                            maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                        });
                    }
                    let mut seen = HashSet::with_capacity(witnesses.len());
                    let mut witness_indexes = Vec::with_capacity(witnesses.len());
                    for reference in witnesses {
                        if !seen.insert(*reference) {
                            return Err(LocalHolProofScriptError::RepeatedReference {
                                step: u32::try_from(index).unwrap_or(u32::MAX),
                                reference: *reference,
                            });
                        }
                        theorem(&slots, index, *reference)?;
                        witness_indexes
                            .push(usize::try_from(reference.get()).unwrap_or(usize::MAX));
                    }
                    let mut witness_values = Vec::with_capacity(witness_indexes.len());
                    for witness_index in &witness_indexes {
                        let Some(Capability::Theorem(value)) = slots[*witness_index].take() else {
                            unreachable!("witness slots were checked as distinct theorems")
                        };
                        witness_values.push(value);
                    }
                    let result =
                        proof.prove_context_implication(*antecedent, *consequent, &witness_values);
                    for (witness_index, value) in witness_indexes.into_iter().zip(witness_values) {
                        slots[witness_index] = Some(Capability::Theorem(value));
                    }
                    Capability::ContextImplication(result?)
                }
                LocalHolProofStep::LoadContextImplication {
                    antecedent,
                    consequent,
                } => {
                    if let Some(value) = proof.load_context_implication(*antecedent, *consequent)? {
                        Capability::ContextImplication(value)
                    } else {
                        missing = Some(LocalHolProofOutput::MissingContextImplication);
                        Capability::Missing
                    }
                }
                LocalHolProofStep::ContextImplicationPath { path } => {
                    if path.len() > MAX_LOCAL_HOL_PROOF_STEPS {
                        return Err(LocalHolProofScriptError::TooManyOperands {
                            step: u32::try_from(index).unwrap_or(u32::MAX),
                            count: path.len(),
                            maximum: MAX_LOCAL_HOL_PROOF_STEPS,
                        });
                    }
                    Capability::ContextImplication(proof.prove_context_implication_path(path)?)
                }
                LocalHolProofStep::PersistContextImplication {
                    implication: source,
                } => {
                    proof.persist_context_implication(implication(&slots, index, *source)?)?;
                    Capability::Unit
                }
                LocalHolProofStep::Weaken {
                    implication: implication_ref,
                    theorem: theorem_ref,
                } => Capability::Theorem(proof.weaken(
                    implication(&slots, index, *implication_ref)?,
                    theorem(&slots, index, *theorem_ref)?,
                )?),
                LocalHolProofStep::EqualityModusPonens { equality, premise } => {
                    Capability::Theorem(proof.equality_modus_ponens(
                        theorem(&slots, index, *equality)?,
                        theorem(&slots, index, *premise)?,
                    )?)
                }
                LocalHolProofStep::EqualitySubstitution {
                    equality,
                    predicate,
                    premise,
                } => Capability::Theorem(proof.equality_substitution(
                    theorem(&slots, index, *equality)?,
                    *predicate,
                    theorem(&slots, index, *premise)?,
                )?),
                LocalHolProofStep::DeductionAntisymmetry { first, second } => {
                    Capability::Theorem(proof.deduction_antisymmetry(
                        theorem(&slots, index, *first)?,
                        theorem(&slots, index, *second)?,
                    )?)
                }
                LocalHolProofStep::Choice { premise } => {
                    Capability::Theorem(proof.choice(theorem(&slots, index, *premise)?)?)
                }
                LocalHolProofStep::InstantiateTerms {
                    theorem: theorem_ref,
                    instantiations,
                } => {
                    let instantiations = instantiations
                        .iter()
                        .map(|instantiation| TermInstantiation {
                            variable: instantiation.variable,
                            replacement: instantiation.replacement,
                        })
                        .collect::<Vec<_>>();
                    Capability::Theorem(proof.instantiate_terms(
                        theorem(&slots, index, *theorem_ref)?,
                        &instantiations,
                    )?)
                }
                LocalHolProofStep::InstantiateTypes {
                    theorem: theorem_ref,
                    instantiations,
                } => {
                    let instantiations = instantiations
                        .iter()
                        .map(|instantiation| TypeInstantiation {
                            variable: instantiation.variable,
                            replacement: instantiation.replacement,
                        })
                        .collect::<Vec<_>>();
                    Capability::Theorem(proof.instantiate_types(
                        theorem(&slots, index, *theorem_ref)?,
                        &instantiations,
                    )?)
                }
                LocalHolProofStep::Abstraction {
                    theorem: theorem_ref,
                    variable,
                } => Capability::Theorem(
                    proof.abstraction(theorem(&slots, index, *theorem_ref)?, *variable)?,
                ),
                LocalHolProofStep::ContextUnion {
                    left,
                    right,
                    result,
                } => Capability::ContextUnion(proof.prove_context_union(*left, *right, *result)?),
                LocalHolProofStep::LoadContextUnion { left, right } => {
                    if let Some(value) = proof.load_context_union(*left, *right)? {
                        Capability::ContextUnion(value)
                    } else {
                        missing = Some(LocalHolProofOutput::MissingContextUnion);
                        Capability::Missing
                    }
                }
                LocalHolProofStep::ContextEquivalence { forward, backward } => {
                    Capability::ContextEquivalence(proof.prove_context_equivalence(
                        implication(&slots, index, *forward)?,
                        implication(&slots, index, *backward)?,
                    )?)
                }
            };
            outputs.push(value.output(missing));
            slots.push(Some(value));
        }
        Ok(outputs)
    })
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use covalence_nucleus::{AllowAll, Operation};

    use super::*;

    fn reference(index: u32) -> LocalHolProofRef {
        LocalHolProofRef::from_u32(index)
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn one_recipe_exercises_every_branded_rule_family() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let free = connection.insert_free_term(17, bool_type).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let identity_truth = connection.insert_application(identity, truth).unwrap();
        let empty = ContextId::empty();
        let truth_context = connection.define_context([truth]).unwrap();
        let identity_truth_context = connection.define_context([identity_truth]).unwrap();
        let free_context = connection.define_context([free]).unwrap();

        let steps = vec![
            LocalHolProofStep::Truth { context: empty }, // 0 theorem
            LocalHolProofStep::PersistTheorem {
                theorem: reference(0),
            }, // 1
            LocalHolProofStep::LoadTheorem {
                context: empty,
                conclusion: truth,
            }, // 2 theorem
            LocalHolProofStep::Hypothesis {
                context: truth_context,
                term: truth,
            }, // 3 theorem
            LocalHolProofStep::Reflexivity {
                context: empty,
                term: truth,
            }, // 4 theorem true = true
            LocalHolProofStep::EqualityModusPonens {
                equality: reference(4),
                premise: reference(0),
            }, // 5 theorem true
            LocalHolProofStep::ConversionBeta {
                abstraction: identity,
                argument: truth,
            }, // 6 conversion
            LocalHolProofStep::ConversionSymmetry {
                conversion: reference(6),
            }, // 7 conversion
            LocalHolProofStep::ConversionTransitivity {
                first: reference(6),
                second: reference(7),
            }, // 8 conversion
            LocalHolProofStep::ConversionEquality {
                context: empty,
                conversion: reference(6),
            }, // 9 theorem
            LocalHolProofStep::PersistTheorem {
                theorem: reference(9),
            }, // 10
            LocalHolProofStep::ConversionReflexivity { term: identity }, // 11 conversion
            LocalHolProofStep::ConversionReflexivity { term: truth }, // 12 conversion
            LocalHolProofStep::ConversionApplication {
                function: reference(11),
                argument: reference(12),
            }, // 13 conversion
            LocalHolProofStep::ConversionReflexivity { term: bound }, // 14 open conversion
            LocalHolProofStep::ConversionLambda {
                parameter_type: bool_type,
                body: reference(14),
            }, // 15 closed conversion
            LocalHolProofStep::ConversionEta { function: identity }, // 16 conversion
            LocalHolProofStep::ConvertTheorem {
                theorem: reference(0),
                conversion: reference(12),
            }, // 17 theorem
            LocalHolProofStep::Beta {
                context: empty,
                abstraction: identity,
                argument: truth,
            }, // 18 theorem
            LocalHolProofStep::ContextImplication {
                antecedent: empty,
                consequent: truth_context,
                witnesses: vec![reference(0)],
            }, // 19 implication; transient theorem witness is enough
            LocalHolProofStep::PersistContextImplication {
                implication: reference(19),
            }, // 20
            LocalHolProofStep::LoadContextImplication {
                antecedent: empty,
                consequent: truth_context,
            }, // 21 implication
            LocalHolProofStep::Weaken {
                implication: reference(21),
                theorem: reference(3),
            }, // 22 theorem under empty
            LocalHolProofStep::ContextImplicationPath {
                path: vec![empty, truth_context],
            }, // 23 implication
            LocalHolProofStep::ContextImplicationPath { path: vec![empty] }, // 24 reflexive
            LocalHolProofStep::PersistContextImplication {
                implication: reference(24),
            }, // 25
            LocalHolProofStep::ContextEquivalence {
                forward: reference(24),
                backward: reference(24),
            }, // 26 equivalence
            LocalHolProofStep::ContextUnion {
                left: empty,
                right: truth_context,
                result: truth_context,
            }, // 27 union
            LocalHolProofStep::LoadContextUnion {
                left: empty,
                right: truth_context,
            }, // 28 union
            LocalHolProofStep::Reflexivity {
                context: identity_truth_context,
                term: truth,
            }, // 29 theorem true = true
            LocalHolProofStep::Hypothesis {
                context: identity_truth_context,
                term: identity_truth,
            }, // 30 theorem (lambda x. x) true
            LocalHolProofStep::EqualitySubstitution {
                equality: reference(29),
                predicate: identity,
                premise: reference(30),
            }, // 31 theorem (lambda x. x) true
            LocalHolProofStep::DeductionAntisymmetry {
                first: reference(0),
                second: reference(0),
            }, // 32 theorem true = true under empty
            LocalHolProofStep::Hypothesis {
                context: free_context,
                term: free,
            }, // 33 theorem free under {free}
            LocalHolProofStep::InstantiateTerms {
                theorem: reference(33),
                instantiations: vec![LocalHolTermInstantiation {
                    variable: free,
                    replacement: truth,
                }],
            }, // 34 theorem true under {true}
            LocalHolProofStep::Beta {
                context: empty,
                abstraction: identity,
                argument: free,
            }, // 35 theorem (lambda x. x) free = free
            LocalHolProofStep::Abstraction {
                theorem: reference(35),
                variable: free,
            }, // 36 theorem abstracting the exact free node
        ];

        let outputs = run_local_hol_proof_script(&mut connection, &steps).unwrap();
        assert_eq!(outputs.len(), steps.len());
        assert!(matches!(
            outputs[6],
            LocalHolProofOutput::Conversion { closed: true, .. }
        ));
        assert_eq!(
            outputs[22],
            LocalHolProofOutput::Theorem {
                context: empty,
                conclusion: truth,
            }
        );
        assert_eq!(
            outputs[26],
            LocalHolProofOutput::ContextEquivalence {
                left: empty,
                right: empty,
            }
        );
        assert_eq!(
            outputs[28],
            LocalHolProofOutput::ContextUnion {
                left: empty,
                right: truth_context,
                result: truth_context,
            }
        );
        assert_eq!(
            outputs[31],
            LocalHolProofOutput::Theorem {
                context: identity_truth_context,
                conclusion: identity_truth,
            }
        );
        assert!(matches!(
            outputs[32],
            LocalHolProofOutput::Theorem { context, .. } if context == empty
        ));
        assert_eq!(
            outputs[34],
            LocalHolProofOutput::Theorem {
                context: truth_context,
                conclusion: truth,
            }
        );
        assert!(matches!(
            outputs[36],
            LocalHolProofOutput::Theorem { context, .. } if context == empty
        ));
    }

    #[test]
    fn type_instantiation_replays_to_an_inert_theorem_output() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let alpha = connection.insert_free_type(700).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let x_alpha = connection.insert_free_term(701, alpha).unwrap();
        let x_bool = connection.insert_free_term(701, bool_type).unwrap();
        let expected = connection.insert_equality(x_bool, x_bool).unwrap();

        let outputs = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Reflexivity {
                    context: ContextId::empty(),
                    term: x_alpha,
                },
                LocalHolProofStep::InstantiateTypes {
                    theorem: reference(0),
                    instantiations: vec![LocalHolTypeInstantiation {
                        variable: alpha,
                        replacement: bool_type,
                    }],
                },
            ],
        )
        .unwrap();

        assert_eq!(
            outputs[1],
            LocalHolProofOutput::Theorem {
                context: ContextId::empty(),
                conclusion: expected,
            }
        );
    }

    #[test]
    fn choice_and_epsilon_conversion_replay_to_inert_outputs() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let predicate = connection.insert_lambda(bool_type, bound).unwrap();
        let witness = connection.insert_bool_term(true).unwrap();
        let premise = connection.insert_application(predicate, witness).unwrap();
        let context = connection.define_context([premise]).unwrap();
        let epsilon = connection.insert_epsilon(predicate).unwrap();
        let expected_choice = connection.insert_application(predicate, epsilon).unwrap();

        let outputs = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Hypothesis {
                    context,
                    term: premise,
                },
                LocalHolProofStep::Choice {
                    premise: reference(0),
                },
                LocalHolProofStep::ConversionReflexivity { term: predicate },
                LocalHolProofStep::ConversionEpsilon {
                    predicate: reference(2),
                },
            ],
        )
        .unwrap();

        assert_eq!(
            outputs[1],
            LocalHolProofOutput::Theorem {
                context,
                conclusion: expected_choice,
            }
        );
        assert_eq!(
            outputs[3],
            LocalHolProofOutput::Conversion {
                left: epsilon,
                right: epsilon,
                ty: bool_type,
                closed: true,
            }
        );
    }

    #[test]
    fn choice_and_epsilon_conversion_references_are_preflighted_by_sort() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();

        let choice_error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::Choice {
                    premise: reference(0),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            choice_error,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
                ..
            }
        ));

        let epsilon_error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
                LocalHolProofStep::ConversionEpsilon {
                    predicate: reference(0),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            epsilon_error,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                expected: LocalHolProofSort::Conversion,
                actual: LocalHolProofSort::Theorem,
                ..
            }
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn type_instantiation_reference_and_operands_are_preflighted() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let bad_pair = LocalHolTypeInstantiation {
            variable: TypeId::from_i64(i64::MAX),
            replacement: TypeId::from_i64(i64::MAX),
        };
        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::InstantiateTypes {
                    theorem: reference(0),
                    instantiations: vec![bad_pair; MAX_LOCAL_HOL_PROOF_STEPS + 1],
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
                ..
            }
        ));
        assert!(operations.borrow().is_empty());

        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
                LocalHolProofStep::InstantiateTypes {
                    theorem: reference(0),
                    instantiations: vec![bad_pair; MAX_LOCAL_HOL_PROOF_STEPS + 1],
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::TooManyOperands {
                step: 1,
                count,
                maximum: MAX_LOCAL_HOL_PROOF_STEPS,
            } if count == MAX_LOCAL_HOL_PROOF_STEPS + 1
        ));
        assert!(operations.borrow().is_empty());

        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
                LocalHolProofStep::InstantiateTypes {
                    theorem: reference(0),
                    instantiations: vec![bad_pair; MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS],
                },
                LocalHolProofStep::ContextImplicationPath {
                    path: vec![ContextId::empty()],
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::TooManyTotalOperands {
                count,
                maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
            } if count == MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS + 1
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn term_instantiation_reference_is_preflighted_as_an_earlier_theorem() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();

        let forward = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::InstantiateTerms {
                    theorem: reference(1),
                    instantiations: Vec::new(),
                },
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            forward,
            LocalHolProofScriptError::InvalidReference {
                step: 0,
                reference: bad_reference,
            } if bad_reference == reference(1)
        ));

        let wrong_sort = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::InstantiateTerms {
                    theorem: reference(0),
                    instantiations: Vec::new(),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            wrong_sort,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                reference: bad_reference,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
            } if bad_reference == reference(0)
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn abstraction_reference_is_preflighted_as_an_earlier_theorem() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();

        let forward = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Abstraction {
                    theorem: reference(1),
                    variable: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            forward,
            LocalHolProofScriptError::InvalidReference {
                step: 0,
                reference: bad_reference,
            } if bad_reference == reference(1)
        ));

        let wrong_sort = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::Abstraction {
                    theorem: reference(0),
                    variable: TermId::from_i64(i64::MAX),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            wrong_sort,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                reference: bad_reference,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
            } if bad_reference == reference(0)
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn term_instantiation_pairs_count_toward_aggregate_operand_bound() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let pair = LocalHolTermInstantiation {
            variable: TermId::from_i64(i64::MAX),
            replacement: TermId::from_i64(i64::MAX),
        };
        let steps = [
            LocalHolProofStep::Truth {
                context: ContextId::empty(),
            },
            LocalHolProofStep::InstantiateTerms {
                theorem: reference(0),
                instantiations: vec![pair; MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS],
            },
            LocalHolProofStep::ContextImplicationPath {
                path: vec![ContextId::empty()],
            },
        ];

        let error = run_local_hol_proof_script(&mut connection, &steps).unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::TooManyTotalOperands {
                count,
                maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
            } if count == MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS + 1
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn new_binary_theorem_rules_are_preflighted_by_sort() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
                LocalHolProofStep::DeductionAntisymmetry {
                    first: reference(0),
                    second: reference(1),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::WrongSort {
                step: 2,
                reference: bad_reference,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
            } if bad_reference == reference(0)
        ));
        assert!(operations.borrow().is_empty());
    }

    #[derive(Clone)]
    struct RecordingPolicy {
        operations: Rc<RefCell<Vec<Operation>>>,
        denied: Option<Operation>,
    }

    impl Policy for RecordingPolicy {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.borrow_mut().push(operation);
            self.denied != Some(operation)
        }
    }

    #[test]
    fn structural_preflight_rejects_forward_reference_before_any_rule() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::Truth {
                    context: ContextId::empty(),
                },
                LocalHolProofStep::PersistTheorem {
                    theorem: reference(2),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::InvalidReference { step: 1, .. }
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn structural_preflight_rejects_sort_confusion_before_any_rule() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let error = run_local_hol_proof_script(
            &mut connection,
            &[
                LocalHolProofStep::ConversionReflexivity {
                    term: TermId::from_i64(i64::MAX),
                },
                LocalHolProofStep::PersistTheorem {
                    theorem: reference(0),
                },
            ],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::WrongSort {
                step: 1,
                expected: LocalHolProofSort::Theorem,
                actual: LocalHolProofSort::Conversion,
                ..
            }
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn structural_preflight_bounds_aggregate_operands_before_any_rule() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: None,
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let mut steps = vec![LocalHolProofStep::Truth {
            context: ContextId::empty(),
        }];
        steps.extend((0..(MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS / 2)).map(|_| {
            LocalHolProofStep::ContextImplicationPath {
                path: vec![ContextId::empty(), ContextId::empty()],
            }
        }));
        steps.push(LocalHolProofStep::ContextImplicationPath {
            path: vec![ContextId::empty()],
        });

        let error = run_local_hol_proof_script(&mut connection, &steps).unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::TooManyTotalOperands {
                count,
                maximum: MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS,
            } if count == MAX_TOTAL_LOCAL_HOL_PROOF_OPERANDS + 1
        ));
        assert!(operations.borrow().is_empty());
    }

    #[test]
    fn checked_rule_policy_denial_is_not_hidden_by_recipe_layer() {
        let operations = Rc::new(RefCell::new(Vec::new()));
        let policy = RecordingPolicy {
            operations: Rc::clone(&operations),
            denied: Some(Operation::ProveConversionReflexivity),
        };
        let mut connection = Connection::open_hol_in_memory(policy).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        operations.borrow_mut().clear();

        let error = run_local_hol_proof_script(
            &mut connection,
            &[LocalHolProofStep::ConversionReflexivity { term: truth }],
        )
        .unwrap_err();
        assert!(matches!(
            error,
            LocalHolProofScriptError::Proof(ProofError::Denied(
                Operation::ProveConversionReflexivity
            ))
        ));
        assert_eq!(
            *operations.borrow(),
            [Operation::ProveConversionReflexivity]
        );
    }
}
