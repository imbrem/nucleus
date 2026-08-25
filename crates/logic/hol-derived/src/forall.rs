//! Derived elimination for equality-encoded term universals.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, SynRel, Tag, ThmId, TmTag};

use crate::{ModelError, substitute};

/// A premise-free theorem concluding one checked proposition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProvedTerm {
    /// The proposition concluded by [`theorem`](Self::theorem).
    pub proposition: Ref,
    /// Exact theorem `⊢ proposition`.
    pub theorem: ThmId,
}

/// Failure while eliminating an equality-encoded universal.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ForallError {
    /// A checked kernel operation rejected the derivation.
    #[snafu(display("universal elimination was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Userspace beta substitution could not be certified.
    #[snafu(display("universal beta substitution failed: {source}"))]
    Substitution {
        /// Underlying userspace traversal failure.
        source: ModelError,
    },
    /// The source theorem does not conclude the supported universal shape.
    #[snafu(display("theorem does not conclude an equality-encoded universal"))]
    WrongForm,
}

impl From<KernelError> for ForallError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<ModelError> for ForallError {
    fn from(source: ModelError) -> Self {
        Self::Substitution { source }
    }
}

/// Specializes an exact theorem of an equality-encoded universal.
///
/// This is ordinary userspace orchestration over `AP_THM`, checked beta
/// conversion, theorem transport, and `EQT_ELIM`. It introduces no new trusted
/// rule beyond those kernel operations.
///
/// # Errors
///
/// Returns an error unless `theorem` is exactly `⊢ ∀x. body`, `argument` has
/// the quantified type, and every checked substitution/conversion step is
/// accepted.
pub fn forall_elim(
    kernel: &mut Kernel,
    theorem: ThmId,
    argument: Ref,
) -> Result<ProvedTerm, ForallError> {
    let universal = sole_positive_assertion(kernel, theorem)?;
    let mut equality_children = children(kernel, universal)?;
    if kernel.arena().tag(universal) != Some(Tag::Tm(TmTag::Eq)) || equality_children.len() != 3 {
        return Err(ForallError::WrongForm);
    }
    let left_function = equality_children[1];
    let right_function = equality_children[2];
    require_lambda(kernel, left_function)?;
    let right_children = require_lambda(kernel, right_function)?;
    if kernel.arena().bool_value(right_children[1]) != Some(true) {
        return Err(ForallError::WrongForm);
    }

    let applied = kernel.ap_thm(theorem, argument)?;
    let (left, left_beta) = beta_reduce(kernel, applied.left)?;
    let (right, right_beta) = beta_reduce(kernel, applied.right)?;
    let bool_ty = kernel.classifier(left)?;
    let target = kernel.eq(bool_ty, left, right)?;

    equality_children = children(kernel, applied.equality)?;
    let target_children = children(kernel, target)?;
    if equality_children.len() != 3 || target_children.len() != 3 {
        return Err(ForallError::WrongForm);
    }
    let type_fact = kernel.syn_refl(None, SynRel::Syn, equality_children[0])?;
    let congruence = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        applied.equality,
        target,
        &[type_fact, left_beta, right_beta],
    )?;
    kernel.union_syn_fact(congruence)?;
    kernel.convert_theorem(applied.theorem, applied.equality, target)?;
    let theorem = kernel.eqt_elim(applied.theorem)?;
    Ok(ProvedTerm {
        proposition: left,
        theorem,
    })
}

fn beta_reduce(kernel: &mut Kernel, application: Ref) -> Result<(Ref, SynFactId), ForallError> {
    let app_children = children(kernel, application)?;
    if app_children.len() != 2 {
        return Err(ForallError::WrongForm);
    }
    let lambda_children = require_lambda(kernel, app_children[0])?;
    let substitution = substitute(
        kernel,
        lambda_children[0],
        app_children[1],
        lambda_children[1],
    )?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    Ok((substitution.output, beta))
}

fn require_lambda(kernel: &Kernel, reference: Ref) -> Result<Vec<Ref>, ForallError> {
    if kernel.arena().tag(reference) != Some(Tag::Tm(TmTag::Lam)) {
        return Err(ForallError::WrongForm);
    }
    let children = children(kernel, reference)?;
    if children.len() == 2 {
        Ok(children)
    } else {
        Err(ForallError::WrongForm)
    }
}

fn children(kernel: &Kernel, reference: Ref) -> Result<Vec<Ref>, ForallError> {
    kernel
        .arena()
        .children(reference)
        .map(Iterator::collect)
        .ok_or(ForallError::WrongForm)
}

fn sole_positive_assertion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, ForallError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    if theorem.lhs.rows().next().is_some() {
        return Err(ForallError::WrongForm);
    }
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(ForallError::WrongForm)?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(ForallError::WrongForm);
    }
    Ref::new(i32::try_from(row[0].magnitude()).map_err(|_| ForallError::WrongForm)?)
        .ok_or(ForallError::WrongForm)
}
