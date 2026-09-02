//! Impredicative least-closure construction for relational semantics.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, Tag, TyTag};

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
