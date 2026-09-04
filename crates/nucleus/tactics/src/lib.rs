//! Untrusted high-level tactics composed from checked Nucleus operations.

mod metamath;

pub use metamath::{
    GroundArtifact, GroundArtifactRecord, GroundCorpus, GroundImport, GroundReplayError,
    GroundSession,
};

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, ThmId};
use covalence_logic_hol_derived::{EqualityError, equality_symmetry};

/// Direction in which a proved equality rewrites a proposition.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RewriteDirection {
    /// Rewrite the equality's left proposition to its right proposition.
    #[default]
    Forward,
    /// Rewrite the equality's right proposition to its left proposition.
    Backward,
}

/// A checked theorem produced by proposition rewriting.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RewriteResult {
    source: Ref,
    target: Ref,
    theorem: ThmId,
}

impl RewriteResult {
    /// Returns the proposition consumed by the rewrite.
    #[must_use]
    pub const fn source(self) -> Ref {
        self.source
    }

    /// Returns the proposition concluded after rewriting.
    #[must_use]
    pub const fn target(self) -> Ref {
        self.target
    }

    /// Returns the checked theorem concluding [`target`](Self::target).
    #[must_use]
    pub const fn theorem(self) -> ThmId {
        self.theorem
    }
}

/// Failure of a high-level Nucleus tactic.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TacticError {
    /// A checked primitive rejected the proposed proof step.
    #[snafu(display("checked tactic step was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Derived equality symmetry rejected the equality theorem.
    #[snafu(display("could not orient rewrite equality: {source}"))]
    Equality {
        /// Underlying userspace-derived equality failure.
        source: EqualityError,
    },
    /// A theorem does not have one positive proposition as its conclusion.
    #[snafu(display("theorem {theorem:?} does not have one positive conclusion"))]
    NonUnitConclusion {
        /// Rejected theorem slot.
        theorem: ThmId,
    },
}

/// Iterates one checked endomap from a checked base value.
///
/// This is deliberately generic: raw references do not certify that `zero`
/// and `successor` are the canonical natural-number constructors. A future
/// descriptor-level `nat_numeral` should accept a replayed `Naturals` package,
/// rather than attach canonical meaning to an untrusted name lookup.
///
/// The complete operation is staged. Failure leaves `kernel` byte-for-byte
/// unchanged, including when the function cannot accept the base value.
///
/// # Errors
///
/// Returns an error unless `successor` is a checked endomap on the type of
/// `zero`, or if checked application rejects any iteration.
pub fn iterate_unary(
    kernel: &mut Kernel,
    zero: Ref,
    successor: Ref,
    count: u64,
) -> Result<Ref, TacticError> {
    // Validate the endomap even for count zero without retaining the probe row.
    let mut probe = kernel.fork();
    let applied = probe.app(successor, zero)?;
    let base_ty = probe.classifier(zero)?;
    let result_ty = probe.classifier(applied)?;
    if !probe.equivalent(base_ty, result_ty)? {
        return Err(KernelError::ClassifierMismatch {
            expected: base_ty,
            actual: result_ty,
        }
        .into());
    }

    let mut staged = kernel.fork();
    let mut value = zero;
    for _ in 0..count {
        value = staged.app(successor, value)?;
    }
    *kernel = staged;
    Ok(value)
}

impl From<KernelError> for TacticError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<EqualityError> for TacticError {
    fn from(source: EqualityError) -> Self {
        Self::Equality { source }
    }
}

/// Rewrites a proved proposition using a proved Boolean equality.
///
/// The complete tactic runs on a fork and replaces `kernel` only after every
/// checked step succeeds. Failure therefore leaves the caller unchanged.
///
/// # Errors
///
/// Returns an error unless `equality` proves a Boolean equality whose selected
/// source is the sole positive conclusion of `premise`, or if any checked
/// equality step rejects the derivation.
pub fn rewrite_proposition(
    kernel: &mut Kernel,
    bool_ty: Ref,
    equality: ThmId,
    premise: ThmId,
    direction: RewriteDirection,
) -> Result<RewriteResult, TacticError> {
    let mut staged = kernel.fork();
    let equality = match direction {
        RewriteDirection::Forward => equality,
        RewriteDirection::Backward => equality_symmetry(&mut staged, bool_ty, equality)?.theorem,
    };
    let source = unit_conclusion(&staged, premise)?;
    let theorem = staged.eq_mp(equality, premise)?;
    let target = unit_conclusion(&staged, theorem)?;
    *kernel = staged;
    Ok(RewriteResult {
        source,
        target,
        theorem,
    })
}

fn unit_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, TacticError> {
    let row = kernel
        .thm()
        .get(theorem)
        .ok_or(TacticError::NonUnitConclusion { theorem })?;
    let mut conclusions = row.rhs.rows();
    let Some(literals) = conclusions.next() else {
        return Err(TacticError::NonUnitConclusion { theorem });
    };
    if conclusions.next().is_some() || literals.len() != 1 || !literals[0].is_positive() {
        return Err(TacticError::NonUnitConclusion { theorem });
    }
    Ref::new(
        i32::try_from(literals[0].magnitude())
            .map_err(|_| TacticError::NonUnitConclusion { theorem })?,
    )
    .ok_or(TacticError::NonUnitConclusion { theorem })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Kernel, Ref, ThmId, ThmId) {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let bool_ty = kernel.bool_ty(star).expect("bool");
        let truth = kernel.bool(bool_ty, true).expect("truth");
        let proposition = kernel.refl(bool_ty, truth).expect("truth equality");
        let equality = kernel
            .refl(bool_ty, proposition.equality)
            .expect("proposition equality");
        (kernel, bool_ty, equality.theorem, proposition.theorem)
    }

    #[test]
    fn forward_and_backward_rewrite_are_checked() {
        for direction in [RewriteDirection::Forward, RewriteDirection::Backward] {
            let (mut kernel, bool_ty, equality, premise) = fixture();
            let result = rewrite_proposition(&mut kernel, bool_ty, equality, premise, direction)
                .expect("rewrite");
            assert_eq!(result.source(), result.target());
            assert!(kernel.thm().get(result.theorem()).is_some());
        }
    }

    #[test]
    fn failed_rewrite_is_atomic() {
        let (mut kernel, bool_ty, equality, _premise) = fixture();
        let before = kernel.arena().clone();
        let missing = ThmId::new(i32::MAX).expect("theorem ID");
        assert!(
            rewrite_proposition(
                &mut kernel,
                bool_ty,
                equality,
                missing,
                RewriteDirection::Forward,
            )
            .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }

    #[test]
    fn unary_iteration_builds_exact_applications() {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let ty = kernel.bool_ty(star).expect("type");
        let zero = kernel.bool(ty, false).expect("zero");
        let binder = kernel.tm_fv(0, ty).expect("binder");
        let successor = kernel.lam(binder, binder).expect("successor");

        assert_eq!(
            iterate_unary(&mut kernel, zero, successor, 0).unwrap(),
            zero
        );
        let one = iterate_unary(&mut kernel, zero, successor, 1).unwrap();
        assert_eq!(kernel.classifier(one).unwrap(), ty);
        let three = iterate_unary(&mut kernel, zero, successor, 3).unwrap();
        assert_eq!(kernel.classifier(three).unwrap(), ty);
        assert_ne!(one, three);
    }

    #[test]
    fn malformed_iteration_is_atomic_even_at_zero() {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let ty = kernel.bool_ty(star).expect("type");
        let zero = kernel.bool(ty, false).expect("zero");
        let not_a_function = kernel.bool(ty, true).expect("nonfunction");
        let before = kernel.arena().clone();

        assert!(iterate_unary(&mut kernel, zero, not_a_function, 0).is_err());
        assert_eq!(kernel.arena(), &before);
    }
}
