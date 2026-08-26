//! Standard equality rules derived from the small checked HOL surface.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynRel, Tag, ThmId, TmTag};

use crate::{ForallError, ModelError, SyntaxError, forall_elim, join_same_syntax, substitute};

/// A proved object-language equality and its endpoints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProvedEquality {
    /// Left operand.
    pub left: Ref,
    /// Right operand.
    pub right: Ref,
    /// Boolean equality row `left = right`.
    pub equality: Ref,
    /// The theorem concluding exactly [`equality`](Self::equality).
    pub theorem: ThmId,
}

/// Failure in a userspace-derived equality rule.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum EqualityError {
    /// A checked kernel operation rejected the derivation.
    #[snafu(display("derived equality rule was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Capture-avoiding beta substitution failed.
    #[snafu(display("derived equality substitution failed: {source}"))]
    Substitution {
        /// Underlying userspace substitution failure.
        source: ModelError,
    },
    /// Structural syntax certification failed.
    #[snafu(display("derived equality syntax certification failed: {source}"))]
    Syntax {
        /// Underlying userspace certification failure.
        source: SyntaxError,
    },
    /// Universal specialization failed.
    #[snafu(display("derived function extensionality specialization failed: {source}"))]
    Forall {
        /// Underlying userspace universal-elimination failure.
        source: ForallError,
    },
    /// A theorem does not have the equality shape required by the rule.
    #[snafu(display("theorem {theorem:?} does not conclude one positive equality"))]
    WrongTheorem {
        /// Rejected theorem slot.
        theorem: ThmId,
    },
}

impl From<KernelError> for EqualityError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<ModelError> for EqualityError {
    fn from(source: ModelError) -> Self {
        Self::Substitution { source }
    }
}

impl From<SyntaxError> for EqualityError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

impl From<ForallError> for EqualityError {
    fn from(source: ForallError) -> Self {
        Self::Forall { source }
    }
}

/// Derives function extensionality from universal pointwise equality.
///
/// Given a theorem of `∀x. f x = g x` and a fresh checked variable `binder`,
/// this specializes at `binder`, applies the kernel's standard abstraction
/// congruence rule, and eta-converts both sides to derive `f = g`.
///
/// # Errors
///
/// Returns an error unless the theorem has the displayed checked shape,
/// `binder` has the quantified domain and is fresh for every premise, and all
/// abstraction and eta certificates are accepted. Rejection is transactional.
pub fn function_extensionality(
    kernel: &mut Kernel,
    bool_ty: Ref,
    theorem: ThmId,
    binder: Ref,
) -> Result<ProvedEquality, EqualityError> {
    let mut staged = kernel.fork();
    let specialized = forall_elim(&mut staged, theorem, binder)?;
    let (_pointwise, _codomain, left_application, right_application) =
        equality_conclusion(&staged, specialized.theorem)?;
    let [left, left_argument] = application_children(&staged, left_application, theorem)?;
    let [right, right_argument] = application_children(&staged, right_application, theorem)?;
    join_same_syntax(&mut staged, left_argument, binder)?;
    join_same_syntax(&mut staged, right_argument, binder)?;
    let abstracted = staged.abs_thm(specialized.theorem, binder)?;
    let (_source, function_ty, _left_lambda, _right_lambda) =
        equality_conclusion(&staged, abstracted.theorem)?;
    let left_function_ty = staged.classifier(left)?;
    let right_function_ty = staged.classifier(right)?;
    join_same_syntax(&mut staged, function_ty, left_function_ty)?;
    join_same_syntax(&mut staged, function_ty, right_function_ty)?;
    let left_eta = staged.tm_eta_fact(None, abstracted.left)?;
    let right_eta = staged.tm_eta_fact(None, abstracted.right)?;
    let equality = staged.eq(bool_ty, left, right)?;
    let [target_function_ty, _target_left, _target_right] =
        equality_children(&staged, equality, theorem)?;
    let type_conversion = join_same_syntax(&mut staged, function_ty, target_function_ty)?;
    let type_conversion = staged.syn_refine(None, type_conversion, SynRel::Conv)?;
    let conversion = staged.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        abstracted.equality,
        equality,
        &[type_conversion, left_eta, right_eta],
    )?;
    staged.union_syn_fact(conversion)?;
    staged.convert_conclusions(abstracted.theorem, abstracted.equality, equality)?;
    *kernel = staged;
    Ok(ProvedEquality {
        left,
        right,
        equality,
        theorem: abstracted.theorem,
    })
}

/// Derives equality symmetry using only `REFL`, `AP_TERM`, and `EQ_MP`.
///
/// # Errors
///
/// Returns an error unless `theorem` concludes one positive checked equality
/// and every userspace beta/congruence certificate is accepted.
pub fn equality_symmetry(
    kernel: &mut Kernel,
    bool_ty: Ref,
    theorem: ThmId,
) -> Result<ProvedEquality, EqualityError> {
    let (source, domain, left, right) = equality_conclusion(kernel, theorem)?;
    let binder = kernel.tm_fv(kernel.fresh_name(&[source])?, domain)?;
    let body = kernel.eq(bool_ty, binder, left)?;
    let predicate = kernel.lam(binder, body)?;
    let lifted = kernel.ap_term(theorem, predicate)?;

    let left_beta = beta_application(kernel, predicate, left)?;
    join_same_syntax(kernel, left_beta.0, lifted.left)?;
    let reflexive = kernel.refl(bool_ty, left)?;
    join_same_syntax(kernel, reflexive.equality, left_beta.1)?;
    kernel.convert_conclusions(reflexive.theorem, reflexive.equality, lifted.left)?;

    let result = kernel.eq_mp(lifted.theorem, reflexive.theorem)?;
    let right_beta = beta_application(kernel, predicate, right)?;
    join_same_syntax(kernel, right_beta.0, lifted.right)?;
    kernel.convert_conclusions(result, lifted.right, right_beta.1)?;
    Ok(ProvedEquality {
        left: right,
        right: left,
        equality: right_beta.1,
        theorem: result,
    })
}

/// Derives equality transitivity using only `AP_TERM` and `EQ_MP`.
///
/// # Errors
///
/// Returns an error unless `left_theorem` concludes `x = y`, `right_theorem`
/// concludes `y = z` with the exact same middle row, and every checked
/// beta/congruence certificate is accepted. Independently allocated but
/// syntactically identical domain and middle rows are transported first.
pub fn equality_transitivity(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left_theorem: ThmId,
    right_theorem: ThmId,
) -> Result<ProvedEquality, EqualityError> {
    let mut staged = kernel.fork();
    let result = equality_transitivity_inner(&mut staged, bool_ty, left_theorem, right_theorem)?;
    *kernel = staged;
    Ok(result)
}

fn equality_transitivity_inner(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left_theorem: ThmId,
    right_theorem: ThmId,
) -> Result<ProvedEquality, EqualityError> {
    let (left_equality, domain, left, middle) = equality_conclusion(kernel, left_theorem)?;
    let (right_equality, right_domain, right_middle, right) =
        equality_conclusion(kernel, right_theorem)?;
    let right_theorem = if domain == right_domain && middle == right_middle {
        right_theorem
    } else {
        let target = kernel.eq_at(bool_ty, domain, middle, right)?;
        let domain_fact = join_same_syntax(kernel, right_domain, domain)?;
        let middle_fact = join_same_syntax(kernel, right_middle, middle)?;
        let right_fact = kernel.syn_refl(None, covalence_logic_hol::SynRel::Syn, right)?;
        let fact = kernel.syn_congr(
            None,
            covalence_logic_hol::SynRel::Conv,
            None,
            None,
            right_equality,
            target,
            &[domain_fact, middle_fact, right_fact],
        )?;
        kernel.union_syn_fact(fact)?;
        let theorem = kernel.copy_theorem(right_theorem)?;
        kernel.convert_conclusions(theorem, right_equality, target)?;
        theorem
    };
    let binder = kernel.tm_fv(kernel.fresh_name(&[left_equality])?, domain)?;
    let body = kernel.eq(bool_ty, left, binder)?;
    let predicate = kernel.lam(binder, body)?;
    let lifted = kernel.ap_term(right_theorem, predicate)?;

    let middle_beta = beta_application(kernel, predicate, middle)?;
    join_same_syntax(kernel, middle_beta.0, lifted.left)?;
    join_same_syntax(kernel, middle_beta.1, left_equality)?;
    let premise = kernel.copy_theorem(left_theorem)?;
    kernel.convert_conclusions(premise, left_equality, lifted.left)?;

    let result = kernel.eq_mp(lifted.theorem, premise)?;
    let right_beta = beta_application(kernel, predicate, right)?;
    join_same_syntax(kernel, right_beta.0, lifted.right)?;
    kernel.convert_conclusions(result, lifted.right, right_beta.1)?;
    Ok(ProvedEquality {
        left,
        right,
        equality: right_beta.1,
        theorem: result,
    })
}

fn equality_conclusion(
    kernel: &Kernel,
    theorem: ThmId,
) -> Result<(Ref, Ref, Ref, Ref), EqualityError> {
    let theorem_row = kernel
        .thm()
        .get(theorem)
        .ok_or(EqualityError::WrongTheorem { theorem })?;
    let mut conclusions = theorem_row.rhs.rows();
    let Some(row) = conclusions.next() else {
        return Err(EqualityError::WrongTheorem { theorem });
    };
    if conclusions.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(EqualityError::WrongTheorem { theorem });
    }
    let equality = Ref::new(
        i32::try_from(row[0].magnitude()).map_err(|_| EqualityError::WrongTheorem { theorem })?,
    )
    .ok_or(EqualityError::WrongTheorem { theorem })?;
    let [domain, left, right] = equality_children(kernel, equality, theorem)?;
    Ok((equality, domain, left, right))
}

fn equality_children(
    kernel: &Kernel,
    equality: Ref,
    theorem: ThmId,
) -> Result<[Ref; 3], EqualityError> {
    if kernel.arena().tag(equality) != Some(Tag::Tm(TmTag::Eq)) {
        return Err(EqualityError::WrongTheorem { theorem });
    }
    kernel
        .arena()
        .children(equality)
        .ok_or(EqualityError::WrongTheorem { theorem })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| EqualityError::WrongTheorem { theorem })
}

fn application_children(
    kernel: &Kernel,
    application: Ref,
    theorem: ThmId,
) -> Result<[Ref; 2], EqualityError> {
    if kernel.arena().tag(application) != Some(Tag::Tm(TmTag::App)) {
        return Err(EqualityError::WrongTheorem { theorem });
    }
    kernel
        .arena()
        .children(application)
        .ok_or(EqualityError::WrongTheorem { theorem })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| EqualityError::WrongTheorem { theorem })
}

fn beta_application(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<(Ref, Ref), EqualityError> {
    let application = kernel.app(function, argument)?;
    let children = kernel
        .arena()
        .children(function)
        .ok_or(KernelError::MissingDefinition {
            reference: function,
        })?
        .collect::<Vec<_>>();
    let [binder, body] = children.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "derived equality beta function",
        }
        .into());
    };
    let substitution = substitute(kernel, *binder, argument, *body)?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    Ok((application, substitution.output))
}
