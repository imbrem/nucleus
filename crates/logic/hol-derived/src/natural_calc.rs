//! Shared equational plumbing for the natural-number layers.
//!
//! The semiring, subtraction, and normalizer modules all build proofs the same
//! way: instantiate a law, rewrite under an operation, and chain the results.
//! [`Calc`] holds the syntax those steps need and wraps the checked kernel
//! rules they use. It proves nothing on its own.

use covalence_logic_hol::{Kernel, Ref, ThmId};

use crate::{
    NaturalError, NaturalNameSupply, Naturals,
    equality::equality_transitivity_in_place,
    equality_symmetry,
    natural_arithmetic::{forall_elim_normalized, prove_by_induction},
};

/// A proved law: its statement and its exact theorem.
pub(crate) type Law = (Ref, ThmId);

/// Equational reasoning over one natural-number package.
pub(crate) struct Calc<'a> {
    /// The naturals this reasoning is about.
    pub(crate) naturals: &'a Naturals,
    /// The Boolean type carrying every equality.
    pub(crate) bool_ty: Ref,
    /// Heads whose applications must not be unfolded when normalizing.
    pub(crate) opaque: Vec<Ref>,
}

impl Calc<'_> {
    // Term construction.

    /// Builds `succ value`.
    pub(crate) fn next(&self, kernel: &mut Kernel, value: Ref) -> Result<Ref, NaturalError> {
        Ok(kernel.app(self.naturals.succ, value)?)
    }

    /// Builds the proposition `left = right`.
    pub(crate) fn equation(
        &self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, NaturalError> {
        Ok(kernel.eq(self.bool_ty, left, right)?)
    }

    /// Allocates a fresh natural-number variable.
    pub(crate) fn variable(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
    ) -> Result<Ref, NaturalError> {
        names.variable(kernel, self.naturals.ty)
    }

    // Equality rules.

    /// Chains `x = y` and `y = z` into `x = z`.
    ///
    /// This does not stage the kernel: a rejection can leave rows behind. Every
    /// public entry point that reaches it forks first.
    pub(crate) fn trans(
        &self,
        kernel: &mut Kernel,
        first: ThmId,
        second: ThmId,
    ) -> Result<ThmId, NaturalError> {
        Ok(equality_transitivity_in_place(kernel, self.bool_ty, first, second)?.theorem)
    }

    /// Turns `x = y` into `y = x`.
    pub(crate) fn symm(&self, kernel: &mut Kernel, theorem: ThmId) -> Result<ThmId, NaturalError> {
        Ok(equality_symmetry(kernel, self.bool_ty, theorem)?.theorem)
    }

    /// Chains a non-empty run of equalities end to end.
    ///
    /// Each intermediate this builds is dropped once the next step consumes
    /// it. Every kernel rule stages a copy of the theorem table, so leaving
    /// spent theorems in it makes the whole chain quadratic. Only theorems
    /// created here are dropped; the caller's steps are left alone.
    pub(crate) fn chain(
        &self,
        kernel: &mut Kernel,
        steps: &[ThmId],
    ) -> Result<ThmId, NaturalError> {
        let (first, rest) = steps.split_first().ok_or(NaturalError::WrongForm {
            expected: "at least one rewrite step",
        })?;
        let mut theorem = *first;
        let mut spent = None;
        for step in rest {
            let next = self.trans(kernel, theorem, *step)?;
            if let Some(previous) = spent.replace(next) {
                let _ = kernel.remove_theorem(previous);
            }
            theorem = next;
        }
        Ok(theorem)
    }

    /// Turns `x = y` into `succ x = succ y`.
    pub(crate) fn under_succ(
        &self,
        kernel: &mut Kernel,
        theorem: ThmId,
    ) -> Result<ThmId, NaturalError> {
        under(kernel, self.naturals.succ, theorem)
    }

    // Quantifier rules.

    /// Instantiates a law's leading universals, left to right.
    pub(crate) fn at(
        &self,
        kernel: &mut Kernel,
        law: ThmId,
        arguments: &[Ref],
    ) -> Result<ThmId, NaturalError> {
        let mut theorem = law;
        for argument in arguments {
            let (_, next) = forall_elim_normalized(kernel, theorem, *argument, &self.opaque)?;
            theorem = next;
        }
        Ok(theorem)
    }

    /// Re-orders a law's universals: instantiate in its order, generalize in
    /// the caller's.
    pub(crate) fn restate(
        &self,
        kernel: &mut Kernel,
        law: ThmId,
        arguments: &[Ref],
        binders: &[Ref],
    ) -> Result<Law, NaturalError> {
        let instance = self.at(kernel, law, arguments)?;
        quantify(kernel, instance, binders)
    }

    /// Proves `body` by induction on `binder`, then quantifies over `binders`.
    ///
    /// Induction yields `∀x. predicate x` with the other variables still free.
    /// To bring them under the quantifier the statement is instantiated and
    /// generalized again. The instance uses a fresh variable: `binder` is bound
    /// by `predicate`, so substituting it would capture. `binders` therefore
    /// names the desired order using `binder`, and the fresh variable takes its
    /// place.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn by_induction(
        &self,
        kernel: &mut Kernel,
        names: &mut NaturalNameSupply,
        binder: Ref,
        body: Ref,
        binders: &[Ref],
        base: impl FnOnce(&mut Kernel) -> Result<ThmId, NaturalError>,
        step: impl FnOnce(&mut Kernel, ThmId) -> Result<ThmId, NaturalError>,
    ) -> Result<Law, NaturalError> {
        let induction = prove_by_induction(kernel, self.naturals, binder, body, base, step)?;
        let renamed = self.variable(kernel, names)?;
        let instance = self.at(kernel, induction.theorem, &[renamed])?;
        let order = binders
            .iter()
            .map(|entry| if *entry == binder { renamed } else { *entry })
            .collect::<Vec<_>>();
        quantify(kernel, instance, &order)
    }
}

/// Turns `x = y` into `function x = function y`.
pub(crate) fn under(
    kernel: &mut Kernel,
    function: Ref,
    theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    Ok(kernel.ap_term(theorem, function)?.theorem)
}

/// Turns `x = y` into `operation x right = operation y right`.
pub(crate) fn on_left(
    kernel: &mut Kernel,
    operation: Ref,
    theorem: ThmId,
    right: Ref,
) -> Result<ThmId, NaturalError> {
    let lifted = kernel.ap_term(theorem, operation)?;
    Ok(kernel.ap_thm(lifted.theorem, right)?.theorem)
}

/// Turns `x = y` into `operation left x = operation left y`.
pub(crate) fn on_right(
    kernel: &mut Kernel,
    operation: Ref,
    left: Ref,
    theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let partial = kernel.app(operation, left)?;
    under(kernel, partial, theorem)
}

/// Generalizes a theorem over `binders`, leftmost binder outermost.
pub(crate) fn quantify(
    kernel: &mut Kernel,
    theorem: ThmId,
    binders: &[Ref],
) -> Result<Law, NaturalError> {
    let mut universal = None;
    let mut theorem = theorem;
    for binder in binders.iter().rev() {
        let generalized = kernel.forall_intro(theorem, *binder)?;
        universal = Some(generalized.universal);
        theorem = generalized.theorem;
    }
    let universal = universal.ok_or(NaturalError::WrongForm {
        expected: "at least one binder",
    })?;
    Ok((universal, theorem))
}
