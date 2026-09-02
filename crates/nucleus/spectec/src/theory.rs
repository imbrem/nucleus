//! Exact HOL model constraints for ordered and potentially non-monotone definitions.

use std::collections::{BTreeMap, BTreeSet};

use covalence_data_spectec::DeclarationId;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Ref,
    builtin::{Op1, Op2},
};

use crate::Source;

/// A complete source-ordered set of declaration constraints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HolTheory {
    constraints: Vec<(DeclarationId, Ref)>,
    proposition: Ref,
}

impl HolTheory {
    /// Returns declaration constraints in exact elaborated source order.
    #[must_use]
    pub fn constraints(&self) -> &[(DeclarationId, Ref)] {
        &self.constraints
    }

    /// Returns their checked conjunction.
    #[must_use]
    pub const fn proposition(&self) -> Ref {
        self.proposition
    }
}

/// Why declaration constraints could not form one complete HOL theory.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolTheoryError {
    /// A source declaration has no semantic constraint.
    #[snafu(display("SpecTec declaration {id:?} has no HOL semantic constraint"))]
    Missing {
        /// Uncovered structural selector.
        id: DeclarationId,
    },
    /// A constraint names no declaration in the exact source.
    #[snafu(display("HOL semantic constraint names foreign SpecTec declaration {id:?}"))]
    Foreign {
        /// Selector outside the source inventory.
        id: DeclarationId,
    },
    /// The checked conjunction could not be constructed.
    #[snafu(display("could not construct complete SpecTec HOL theory: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Applicability and result proposition for one source-ordered clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolCase {
    /// Existential proposition that this clause matches and its premises hold,
    /// independent of the graph result currently being tested.
    pub applicable: Ref,
    /// Proposition that this clause produces the graph result being tested.
    pub produces: Ref,
    /// Whether this clause carries the `SpecTec` `otherwise` premise.
    pub otherwise: bool,
}

/// Builds an exact ordered-clause body for fixed graph inputs and result.
///
/// An `otherwise` case is guarded by the negation of the disjunction of every
/// earlier clause's applicability. Ordinary cases retain their source formula.
/// Empty case lists denote false.
///
/// # Errors
///
/// Returns an error unless every applicability and production term is Boolean
/// and all checked Boolean constructors succeed.
pub fn ordered_cases(
    kernel: &mut Kernel,
    bool_ty: Ref,
    cases: &[HolCase],
) -> Result<Ref, KernelError> {
    let mut prior = kernel.bool(bool_ty, false)?;
    let mut body = kernel.bool(bool_ty, false)?;
    for case in cases {
        let produces = if case.otherwise {
            let no_prior = kernel.op1(Op1::Not, prior)?;
            kernel.op2(Op2::And, no_prior, case.produces)?
        } else {
            case.produces
        };
        body = kernel.op2(Op2::Or, body, produces)?;
        prior = kernel.op2(Op2::Or, prior, case.applicable)?;
    }
    Ok(body)
}

/// Existentially closes a conjunction over clause-local variables.
///
/// Empty propositions denote true. Local variables are closed in source order.
///
/// # Errors
///
/// Returns an error unless propositions are Boolean, locals are free term
/// variables, and checked conjunction or existential construction fails.
pub fn existential_case(
    kernel: &mut Kernel,
    bool_ty: Ref,
    locals: &[Ref],
    propositions: &[Ref],
) -> Result<Ref, KernelError> {
    let mut body = conjoin(kernel, bool_ty, propositions)?;
    for &local in locals.iter().rev() {
        body = kernel.exists_tm(local, body)?;
    }
    Ok(body)
}

/// Closes one exact graph equation as a universally quantified proposition.
///
/// Constructs `∀ variables. predicate arguments... = body`. This only creates
/// checked syntax; it does not assume the equation or mint a theorem fact.
///
/// # Errors
///
/// Returns an error for ill-typed predicate application, a non-Boolean body,
/// invalid universal variables, or rejected equality construction.
pub fn close_graph_equation(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate: Ref,
    variables: &[Ref],
    arguments: &[Ref],
    body: Ref,
) -> Result<Ref, KernelError> {
    let applied = arguments
        .iter()
        .try_fold(predicate, |function, &argument| {
            kernel.app(function, argument)
        })?;
    let mut equation = kernel.eq(bool_ty, applied, body)?;
    for &variable in variables.iter().rev() {
        equation = kernel.forall_tm(bool_ty, variable, equation)?;
    }
    Ok(equation)
}

/// Conjoins exact declaration constraints into one model proposition.
///
/// Empty theories denote true.
///
/// # Errors
///
/// Returns an error unless every constraint is Boolean.
pub fn conjoin_constraints(
    kernel: &mut Kernel,
    bool_ty: Ref,
    constraints: &[Ref],
) -> Result<Ref, KernelError> {
    conjoin(kernel, bool_ty, constraints)
}

/// Transactionally closes exactly one constraint per source declaration into
/// one source-ordered HOL model proposition.
///
/// Structural selectors, not names, establish coverage. The result is checked
/// syntax only and does not assume the proposition or mint a theorem fact.
///
/// # Errors
///
/// Returns the first missing declaration in source order, the first foreign
/// selector in map order, or a checked Boolean-conjunction failure. `kernel`
/// is unchanged on failure.
pub fn close_hol_theory(
    source: &Source,
    kernel: &mut Kernel,
    bool_ty: Ref,
    constraints: &BTreeMap<DeclarationId, Ref>,
) -> Result<HolTheory, HolTheoryError> {
    let source_ids = source
        .declarations()
        .iter()
        .map(crate::SourceDeclaration::id)
        .collect::<BTreeSet<_>>();
    if let Some(&id) = constraints.keys().find(|id| !source_ids.contains(id)) {
        return Err(HolTheoryError::Foreign { id });
    }
    let ordered = source
        .declarations()
        .iter()
        .map(|declaration| {
            constraints
                .get(&declaration.id())
                .copied()
                .map(|constraint| (declaration.id(), constraint))
                .ok_or(HolTheoryError::Missing {
                    id: declaration.id(),
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut staged = kernel.fork();
    let propositions = ordered
        .iter()
        .map(|(_, constraint)| *constraint)
        .collect::<Vec<_>>();
    let proposition = conjoin_constraints(&mut staged, bool_ty, &propositions)
        .map_err(|source| HolTheoryError::Kernel { source })?;
    *kernel = staged;
    Ok(HolTheory {
        constraints: ordered,
        proposition,
    })
}

fn conjoin(kernel: &mut Kernel, bool_ty: Ref, propositions: &[Ref]) -> Result<Ref, KernelError> {
    let truth = kernel.bool(bool_ty, true)?;
    propositions
        .iter()
        .try_fold(truth, |left, &right| kernel.op2(Op2::And, left, right))
}
