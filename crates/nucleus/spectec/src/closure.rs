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
    let mut family =
        least_closed_family(kernel, bool_ty, &[predicate_ty], |kernel, candidates| {
            build_closure(kernel, candidates[0])
        })?;
    family.pop().ok_or(LeastPredicateError::NotPredicate)
}

/// Simultaneously defines the least family satisfying a shared closure.
///
/// Every resulting predicate quantifies over the entire candidate family, so
/// rules may refer mutually to any candidate supplied to `build_closure`.
/// Predicate order is preserved in both the callback and result.
///
/// # Errors
///
/// Returns an error for an empty family, a classifier that is not a curried
/// predicate with at least one domain, a non-Boolean shared closure, name-space
/// exhaustion, or any rejected checked constructor. `kernel` is unchanged on
/// failure.
pub fn least_closed_family<F>(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate_tys: &[Ref],
    build_closure: F,
) -> Result<Vec<LeastPredicate>, LeastPredicateError>
where
    F: FnOnce(&mut Kernel, &[Ref]) -> Result<Ref, KernelError>,
{
    if predicate_tys.is_empty() {
        return Err(LeastPredicateError::NotPredicate);
    }
    let mut staged = kernel.fork();
    let arrows = predicate_tys
        .iter()
        .map(|&predicate_ty| predicate_arrows(&staged, predicate_ty, bool_ty))
        .collect::<Result<Vec<_>, _>>()?;
    if arrows.iter().any(Vec::is_empty) {
        return Err(LeastPredicateError::NotPredicate);
    }
    let roots = std::iter::once(bool_ty)
        .chain(predicate_tys.iter().copied())
        .collect::<Vec<_>>();
    let base = staged
        .fresh_name(&roots)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let mut offset = 0_u64;
    let mut candidates = Vec::with_capacity(predicate_tys.len());
    for &predicate_ty in predicate_tys {
        let name = next_name(base, &mut offset)?;
        candidates.push(
            staged
                .tm_fv(name, predicate_ty)
                .map_err(|source| LeastPredicateError::Kernel { source })?,
        );
    }
    let closure = build_closure(&mut staged, &candidates)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let bool_tail = staged
        .ty_arr(bool_ty, bool_ty)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let bool_binary = staged
        .ty_arr(bool_ty, bool_tail)
        .map_err(|source| LeastPredicateError::Kernel { source })?;
    let mut predicates = Vec::with_capacity(predicate_tys.len());
    for ((&predicate_ty, &candidate), predicate_arrows) in
        predicate_tys.iter().zip(&candidates).zip(&arrows)
    {
        let mut arguments = Vec::with_capacity(predicate_arrows.len());
        let mut applied = candidate;
        for &(_, domain) in predicate_arrows {
            let name = next_name(base, &mut offset)?;
            let argument = staged
                .tm_fv(name, domain)
                .map_err(|source| LeastPredicateError::Kernel { source })?;
            applied = staged
                .app(applied, argument)
                .map_err(|source| LeastPredicateError::Kernel { source })?;
            arguments.push(argument);
        }
        let logic_name = next_name(base, &mut offset)?;
        let logic = staged
            .tm_fv(logic_name, bool_binary)
            .map_err(|source| LeastPredicateError::Kernel { source })?;
        let implication = staged
            .imp_tm(bool_ty, logic, closure, applied)
            .map_err(|source| LeastPredicateError::Kernel { source })?;
        let mut characterization = implication;
        for &family_candidate in candidates.iter().rev() {
            characterization = staged
                .forall_tm(bool_ty, family_candidate, characterization)
                .map_err(|source| LeastPredicateError::Kernel { source })?;
        }
        let mut predicate = characterization;
        for ((arrow, _), argument) in predicate_arrows.iter().zip(&arguments).rev() {
            predicate = staged
                .lam_at(*arrow, *argument, predicate)
                .map_err(|source| LeastPredicateError::Kernel { source })?;
        }
        predicates.push(LeastPredicate {
            predicate_ty,
            candidate,
            closure,
            characterization,
            predicate,
        });
    }
    *kernel = staged;
    Ok(predicates)
}

fn next_name(base: u64, offset: &mut u64) -> Result<u64, LeastPredicateError> {
    let name = base
        .checked_add(*offset)
        .ok_or(LeastPredicateError::NotPredicate)?;
    *offset = offset
        .checked_add(1)
        .ok_or(LeastPredicateError::NotPredicate)?;
    Ok(name)
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
