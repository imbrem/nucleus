//! Exact HOL model constraints for ordered and potentially non-monotone definitions.

use covalence_logic_hol::{
    Kernel, KernelError, Ref,
    builtin::{Op1, Op2},
};

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

fn conjoin(kernel: &mut Kernel, bool_ty: Ref, propositions: &[Ref]) -> Result<Ref, KernelError> {
    let Some((&first, rest)) = propositions.split_first() else {
        return kernel.bool(bool_ty, true);
    };
    rest.iter()
        .try_fold(first, |left, &right| kernel.op2(Op2::And, left, right))
}
