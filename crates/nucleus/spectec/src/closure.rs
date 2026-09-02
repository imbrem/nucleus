//! Impredicative least-closure construction for relational semantics.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, Tag, TyTag, builtin::Op2};

/// Lowered ingredients of one relational rule.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct HolRule {
    /// Free variables universally closed around the rule.
    pub binders: Vec<Ref>,
    /// Boolean premises conjoined in source order.
    pub premises: Vec<Ref>,
    /// Curried arguments applied to the candidate predicate.
    pub conclusion: Vec<Ref>,
}

impl HolRule {
    /// Constructs one compositional rule description.
    #[must_use]
    pub const fn new(binders: Vec<Ref>, premises: Vec<Ref>, conclusion: Vec<Ref>) -> Self {
        Self {
            binders,
            premises,
            conclusion,
        }
    }
}

/// Checked terms defining the least predicate closed under a rule schema.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LeastPredicate {
    /// Exact predicate classifier supplied by the caller.
    pub predicate_ty: Ref,
    /// Candidate predicate bound by the impredicative definition.
    pub candidate: Ref,
    /// Proposition stating that the candidate is closed under every rule.
    pub closure: Ref,
    /// `∀ candidate. closure candidate → candidate arguments` before argument
    /// abstraction.
    pub characterization: Ref,
    /// Curried least closed predicate with classifier [`predicate_ty`](Self::predicate_ty).
    pub predicate: Ref,
}

/// Why a least-closure definition could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum LeastPredicateError {
    /// A checked HOL constructor rejected the definition.
    #[snafu(display("could not construct least closed HOL predicate: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The supplied classifier was not a curried predicate ending in Boolean.
    #[snafu(display("least-closure classifier is not a function ending in bool"))]
    NotPredicate,
}

/// Defines the least predicate satisfying a caller-built closure proposition.
///
/// For predicate classifier `A₁ → ... → Aₙ → bool`, this constructs
/// `λa₁ ... aₙ. ∀P. closed(P) → P a₁ ... aₙ`. The closure callback receives
/// the checked candidate `P` and must return a Boolean proposition. No theorem
/// fact or axiom is introduced.
///
/// The operation is transactional.
///
/// # Errors
///
/// Returns an error unless `bool_ty` is the checked Boolean type,
/// `predicate_ty` is a curried predicate with at least one domain, the callback
/// returns a Boolean proposition, and every checked constructor succeeds. The
/// supplied kernel is unchanged on failure.
pub fn least_closed_predicate<F>(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate_ty: Ref,
    build_closure: F,
) -> Result<LeastPredicate, LeastPredicateError>
where
    F: FnOnce(&mut Kernel, Ref) -> Result<Ref, KernelError>,
{
    let mut staged = kernel.fork();
    let arrows = predicate_arrows(&staged, predicate_ty, bool_ty)?;
    if arrows.is_empty() {
        return Err(LeastPredicateError::NotPredicate);
    }
    let roots = [bool_ty, predicate_ty];
    let base = staged
        .fresh_name(&roots)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let candidate = staged
        .tm_fv(base, predicate_ty)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let closure = build_closure(&mut staged, candidate)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let mut arguments = Vec::with_capacity(arrows.len());
    let mut applied = candidate;
    for (offset, &(_, domain)) in arrows.iter().enumerate() {
        let name = base
            .checked_add(u64::try_from(offset).map_err(|_| LeastPredicateError::NotPredicate)? + 1)
            .ok_or(LeastPredicateError::NotPredicate)?;
        let argument = staged
            .tm_fv(name, domain)
            .map_err(|source| LeastPredicateError::Kernel { source })?;
        applied = staged
            .app(applied, argument)
            .map_err(|source| LeastPredicateError::Kernel { source })?;
        arguments.push(argument);
    }
    let bool_tail = staged
        .ty_arr(bool_ty, bool_ty)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let bool_binary = staged
        .ty_arr(bool_ty, bool_tail)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let logic_name = base
        .checked_add(
            u64::try_from(arguments.len()).map_err(|_| LeastPredicateError::NotPredicate)? + 1,
        )
        .ok_or(LeastPredicateError::NotPredicate)?;
    let logic = staged
        .tm_fv(logic_name, bool_binary)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let implication = staged
        .imp_tm(bool_ty, logic, closure, applied)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let characterization = staged
        .forall_tm(bool_ty, candidate, implication)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let mut predicate = characterization;
    for ((arrow, _), argument) in arrows.iter().zip(&arguments).rev() {
        predicate = staged
            .lam_at(*arrow, *argument, predicate)
            .map_err(|source| LeastPredicateError::Kernel { source })?;
    }
    *kernel = staged;
    Ok(LeastPredicate {
        predicate_ty,
        candidate,
        closure,
        characterization,
        predicate,
    })
}

/// Constructs the universally closed proposition for one candidate rule.
///
/// The result is `∀ binders. (premise₁ ∧ ... ∧ premiseₙ) →
/// candidate conclusion...`. Empty premises denote truth.
///
/// # Errors
///
/// Returns an error unless the candidate accepts every conclusion argument,
/// every premise is Boolean, every binder is a free term variable, and all
/// involved propositions use `bool_ty`.
pub fn close_hol_rule(
    kernel: &mut Kernel,
    bool_ty: Ref,
    candidate: Ref,
    rule: &HolRule,
) -> Result<Ref, KernelError> {
    let conclusion = rule
        .conclusion
        .iter()
        .try_fold(candidate, |function, &argument| {
            kernel.app(function, argument)
        })?;
    let premises = conjoin(kernel, bool_ty, &rule.premises)?;
    let bool_tail = kernel.ty_arr(bool_ty, bool_ty)?;
    let bool_binary = kernel.ty_arr(bool_ty, bool_tail)?;
    let roots = rule
        .binders
        .iter()
        .chain(rule.premises.iter())
        .copied()
        .chain([candidate, conclusion, bool_ty, bool_binary])
        .collect::<Vec<_>>();
    let name = kernel.fresh_name(&roots)?;
    let logic = kernel.tm_fv(name, bool_binary)?;
    let mut proposition = kernel.imp_tm(bool_ty, logic, premises, conclusion)?;
    for &binder in rule.binders.iter().rev() {
        proposition = kernel.forall_tm(bool_ty, binder, proposition)?;
    }
    Ok(proposition)
}

/// Conjoins the closure propositions for all rules.
///
/// Empty rule sets denote truth, which makes the resulting least predicate
/// empty rather than accidentally unconstrained.
///
/// # Errors
///
/// Returns an error unless every rule proposition is Boolean and uses
/// `bool_ty`.
pub fn close_hol_rules(
    kernel: &mut Kernel,
    bool_ty: Ref,
    rules: &[Ref],
) -> Result<Ref, KernelError> {
    conjoin(kernel, bool_ty, rules)
}

fn conjoin(kernel: &mut Kernel, bool_ty: Ref, propositions: &[Ref]) -> Result<Ref, KernelError> {
    let Some((&first, tail)) = propositions.split_first() else {
        return kernel.bool(bool_ty, true);
    };
    tail.iter()
        .try_fold(first, |left, &right| kernel.op2(Op2::And, left, right))
}

fn predicate_arrows(
    kernel: &Kernel,
    predicate_ty: Ref,
    bool_ty: Ref,
) -> Result<Vec<(Ref, Ref)>, LeastPredicateError> {
    let mut arrows = Vec::new();
    let mut current = predicate_ty;
    while kernel.arena().tag(current) == Some(Tag::Ty(TyTag::Arr)) {
        let children = kernel
            .arena()
            .children(current)
            .ok_or(LeastPredicateError::NotPredicate)?
            .collect::<Vec<_>>();
        let [domain, codomain] = children.as_slice() else {
            return Err(LeastPredicateError::NotPredicate);
        };
        arrows.push((current, *domain));
        current = *codomain;
    }
    if !kernel
        .equivalent(current, bool_ty)
        .map_err(|source| LeastPredicateError::Kernel { source })?
    {
        return Err(LeastPredicateError::NotPredicate);
    }
    Ok(arrows)
}
