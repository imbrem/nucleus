//! Out-of-TCB propositional logic over the HOL kernel.
//!
//! This crate adds zero trusted code. Every theorem it produces is
//! minted by `proof_step` behind the kernel's sealed primitive rules;
//! the derivations here are the classic HOL Light ones (beta conversion,
//! the equality layer, abstraction, and deduction antisymmetry) driven
//! from outside the kernel. A bug in this crate can make a derivation
//! *fail* - it cannot make the kernel accept a false proposition,
//! because the kernel revalidates every premise and side condition
//! in-store on each step.
//!
//! The connectives are the interned closed terms exported by the
//! propositional init database (`covalence-hol-init`): a conjunction is
//! literally the application term `and p q`, and each derived rule
//! converts between that application form and its beta-reduced body as
//! needed, so callers only ever see connective applications.

use covalence_lib_error::snafu::Snafu;
use covalence_neutron::Bytes;
pub use covalence_nucleus::Connection;
use covalence_nucleus::hol::rules::{
    Abs, Assume, Beta, DeductAntisym, EqMp, MkComb, Refl, Sym, Trans, Truth, WeakenVar,
};
use covalence_nucleus::hol::syntax::TheoremId;
use covalence_nucleus::hol::typing::lift_tm_in_tm;
use covalence_nucleus::hol::{
    Hol, HolError, HolImageError, HolView, KindsId, Policy, TermId, Tm, Ty, TypeId, VarsId,
};

pub use covalence_hol_init::InitTerms;

/// Failure of a derived-rule application.
///
/// Everything here is an ordinary failure report: the kernel refused a
/// step, or a premise did not have the shape the rule needs. No variant
/// has soundness weight.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum LogicError {
    /// The kernel refused an operation or a primitive step.
    #[snafu(display("kernel refused the step"), context(false))]
    Kernel {
        /// Underlying kernel failure.
        source: HolError,
    },
    /// A premise conclusion is not an application of `init/and`.
    #[snafu(display("conclusion is not a conjunction"))]
    NotAConjunction,
    /// A premise conclusion is not an application of `init/imp`.
    #[snafu(display("conclusion is not an implication"))]
    NotAnImplication,
    /// The implication's antecedent differs from the premise conclusion.
    #[snafu(display("antecedent does not match the premise"))]
    PremiseMismatch,
    /// The premises live in different contexts.
    #[snafu(display("premise contexts disagree"))]
    ContextMismatch,
    /// An internal derivation invariant failed to line up.
    ///
    /// This indicates a bug in this crate's derivations, never an
    /// unsoundness: the kernel simply produced a different (still valid)
    /// theorem than the one the derivation expected to continue from.
    #[snafu(display("derivation invariant failed: {what}"))]
    Derivation {
        /// Which invariant failed.
        what: &'static str,
    },
}

/// Opens a serialized init image as a writable kernel-state connection.
///
/// This is a thin convenience over the kernel's image admission; see
/// there for the trust caveats (the schema is checked, the rows are
/// trusted as far as the image's provenance).
///
/// # Errors
///
/// Returns an error if the image cannot be opened or does not carry the
/// current kernel-state schema.
pub fn open_image<P: Policy>(
    bytes: &Bytes,
    policy: P,
) -> Result<Connection<Hol<P>>, HolImageError> {
    Connection::open_hol_image(bytes, policy)
}

/// The propositional API over one kernel view.
///
/// Construction resolves the init database's exported connectives and
/// checks their types; the check reports a malformed database early and
/// carries no soundness weight.
pub struct Logic<'l, 'v, P: Policy> {
    hol: &'l HolView<'v, P>,
    terms: InitTerms<'v>,
    bool_ty: TypeId<'v>,
}

impl<'l, 'v, P: Policy> Logic<'l, 'v, P> {
    /// Resolves the init exports of the view's database.
    ///
    /// # Errors
    ///
    /// Fails if the `init` namespace or one of its exports is missing,
    /// or a connective does not have its expected type.
    pub fn new(hol: &'l HolView<'v, P>) -> Result<Self, LogicError> {
        let terms = covalence_hol_init::resolve(hol)?;
        let bool_ty = hol.ty(Ty::Bool)?;
        let bool_bool = hol.ty(Ty::Arr(bool_ty, bool_ty))?;
        let binary = hol.ty(Ty::Arr(bool_ty, bool_bool))?;
        let empty = (hol.empty_kinds(), hol.empty_vars());
        for (connective, expected) in [
            (terms.and, binary),
            (terms.or, binary),
            (terms.imp, binary),
            (terms.not, bool_bool),
        ] {
            if hol.type_of(empty.0, empty.1, connective)? != expected {
                return DerivationSnafu {
                    what: "init connective has an unexpected type",
                }
                .fail();
            }
        }
        Ok(Self {
            hol,
            terms,
            bool_ty,
        })
    }

    /// Returns the resolved init constants.
    #[must_use]
    pub const fn constants(&self) -> InitTerms<'v> {
        self.terms
    }

    // ------------------------------------------------------------------
    // Term builders.
    // ------------------------------------------------------------------

    /// Builds the conjunction `and p q` as an application term.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn and_term(&self, p: TermId<'v>, q: TermId<'v>) -> Result<TermId<'v>, LogicError> {
        self.apply2(self.terms.and, p, q)
    }

    /// Builds the disjunction `or p q` as an application term.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn or_term(&self, p: TermId<'v>, q: TermId<'v>) -> Result<TermId<'v>, LogicError> {
        self.apply2(self.terms.or, p, q)
    }

    /// Builds the implication `imp p q` as an application term.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn imp_term(&self, p: TermId<'v>, q: TermId<'v>) -> Result<TermId<'v>, LogicError> {
        self.apply2(self.terms.imp, p, q)
    }

    /// Builds the negation `not p` as an application term.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn not_term(&self, p: TermId<'v>) -> Result<TermId<'v>, LogicError> {
        Ok(self.hol.tm(Tm::App(self.terms.not, p))?)
    }

    fn apply2(
        &self,
        connective: TermId<'v>,
        p: TermId<'v>,
        q: TermId<'v>,
    ) -> Result<TermId<'v>, LogicError> {
        let partial = self.hol.tm(Tm::App(connective, p))?;
        Ok(self.hol.tm(Tm::App(partial, q))?)
    }

    // ------------------------------------------------------------------
    // Derived rules.
    // ------------------------------------------------------------------

    /// `TRUTH`: `|- true` in the given context.
    ///
    /// # Errors
    ///
    /// Fails if the kernel refuses the step.
    pub fn truth(&self, kinds: KindsId<'v>, vars: VarsId<'v>) -> Result<TheoremId<'v>, LogicError> {
        Ok(self.hol.proof_step(Truth { kinds, vars })?)
    }

    /// `ASSUME`: `{p} |- p` in the given context.
    ///
    /// # Errors
    ///
    /// Fails if `p` is not Boolean or the kernel refuses the step.
    pub fn assume(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        prop: TermId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        Ok(self.hol.proof_step(Assume { kinds, vars, prop })?)
    }

    /// `EQT_INTRO`: from `A |- p`, `A |- p = true`.
    ///
    /// As in HOL Light, a literal `true` hypothesis is absorbed by the
    /// underlying deduction antisymmetry.
    ///
    /// # Errors
    ///
    /// Fails if the kernel refuses a step.
    pub fn eqt_intro(&self, theorem: TheoremId<'v>) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, ..) = self.hol.theorem(theorem)?;
        let truth = self.truth(kinds, vars)?;
        Ok(self.hol.proof_step(DeductAntisym {
            left: theorem,
            right: truth,
        })?)
    }

    /// `EQT_ELIM`: from `A |- p = true`, `A |- p`.
    ///
    /// # Errors
    ///
    /// Fails if the conclusion is not an equality with `true` or the
    /// kernel refuses a step.
    pub fn eqt_elim(&self, theorem: TheoremId<'v>) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, ..) = self.hol.theorem(theorem)?;
        let flipped = self.hol.proof_step(Sym { premise: theorem })?;
        let truth = self.truth(kinds, vars)?;
        Ok(self.hol.proof_step(EqMp {
            equality: flipped,
            premise: truth,
        })?)
    }

    /// `CONJ`: from `A |- p` and `B |- q`, `A u B |- and p q`.
    ///
    /// # Errors
    ///
    /// Fails if the premises live in different contexts or the kernel
    /// refuses a step.
    pub fn conj(
        &self,
        left: TheoremId<'v>,
        right: TheoremId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, _, p) = self.hol.theorem(left)?;
        let (right_kinds, right_vars, _, q) = self.hol.theorem(right)?;
        if kinds != right_kinds || vars != right_vars {
            return ContextMismatchSnafu.fail();
        }
        let selector_ty = self.selector_ty()?;

        // A |- p = true and B |- q = true, pushed under the selector
        // variable f.
        let p_true = self.eqt_intro(left)?;
        let q_true = self.eqt_intro(right)?;
        let p_lifted = self.hol.proof_step(WeakenVar {
            thm: p_true,
            ty: selector_ty,
        })?;
        let q_lifted = self.hol.proof_step(WeakenVar {
            thm: q_true,
            ty: selector_ty,
        })?;
        let (inner_kinds, inner_vars, ..) = self.hol.theorem(p_lifted)?;

        // f p' q' = f true true by congruence, then abstraction over f
        // yields the beta-reduced conjunction body.
        let selector = self.hol.tm(Tm::Bv(0))?;
        let selector_refl = self.hol.proof_step(Refl {
            kinds: inner_kinds,
            vars: inner_vars,
            term: selector,
        })?;
        let once = self.hol.proof_step(MkComb {
            function: selector_refl,
            argument: p_lifted,
        })?;
        let twice = self.hol.proof_step(MkComb {
            function: once,
            argument: q_lifted,
        })?;
        let body = self.hol.proof_step(Abs { premise: twice })?;

        // Transport backwards across `and p q = body`.
        let unfolded = self.unfold_binary(kinds, vars, self.terms.and, p, q)?;
        let (.., body_concl) = self.hol.theorem(body)?;
        if self.equality_rhs(unfolded)? != body_concl {
            return DerivationSnafu {
                what: "conjunction body disagrees with the unfolded definition",
            }
            .fail();
        }
        let folded = self.hol.proof_step(Sym { premise: unfolded })?;
        Ok(self.hol.proof_step(EqMp {
            equality: folded,
            premise: body,
        })?)
    }

    /// `CONJUNCT1`: from `A |- and p q`, `A |- p`.
    ///
    /// # Errors
    ///
    /// Fails if the conclusion is not a conjunction or the kernel
    /// refuses a step.
    pub fn conjunct1(&self, theorem: TheoremId<'v>) -> Result<TheoremId<'v>, LogicError> {
        self.conjunct(theorem, true)
    }

    /// `CONJUNCT2`: from `A |- and p q`, `A |- q`.
    ///
    /// # Errors
    ///
    /// Fails if the conclusion is not a conjunction or the kernel
    /// refuses a step.
    pub fn conjunct2(&self, theorem: TheoremId<'v>) -> Result<TheoremId<'v>, LogicError> {
        self.conjunct(theorem, false)
    }

    /// `MP`: from `A |- imp p q` and `B |- p`, `A u B |- q`.
    ///
    /// # Errors
    ///
    /// Fails if the first conclusion is not an implication, the
    /// antecedent differs from the second conclusion, or the kernel
    /// refuses a step.
    pub fn mp(
        &self,
        implication: TheoremId<'v>,
        premise: TheoremId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, _, concl) = self.hol.theorem(implication)?;
        let (antecedent, consequent) = self
            .binary_operands(concl, self.terms.imp)?
            .ok_or(LogicError::NotAnImplication)?;
        let (.., premise_concl) = self.hol.theorem(premise)?;
        if premise_concl != antecedent {
            return PremiseMismatchSnafu.fail();
        }

        // imp p q unfolds to (and p q) = p; transport |- p across the
        // flipped equality and project the second conjunct.
        let unfolded = self.unfold_binary(kinds, vars, self.terms.imp, antecedent, consequent)?;
        let equation = self.hol.proof_step(EqMp {
            equality: unfolded,
            premise: implication,
        })?;
        let flipped = self.hol.proof_step(Sym { premise: equation })?;
        let conjunction = self.hol.proof_step(EqMp {
            equality: flipped,
            premise,
        })?;
        self.conjunct2(conjunction)
    }

    /// `DISCH`: from `A |- q`, `A \ {p} |- imp p q`.
    ///
    /// # Errors
    ///
    /// Fails if `p` is not Boolean or the kernel refuses a step.
    pub fn disch(
        &self,
        prop: TermId<'v>,
        theorem: TheoremId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, _, concl) = self.hol.theorem(theorem)?;
        let assumed = self.assume(kinds, vars, prop)?;
        let conjunction = self.conj(assumed, theorem)?;
        let (.., conjunction_term) = self.hol.theorem(conjunction)?;
        let assumed_conjunction = self.assume(kinds, vars, conjunction_term)?;
        let projected = self.conjunct1(assumed_conjunction)?;
        let equation = self.hol.proof_step(DeductAntisym {
            left: conjunction,
            right: projected,
        })?;
        let unfolded = self.unfold_binary(kinds, vars, self.terms.imp, prop, concl)?;
        let folded = self.hol.proof_step(Sym { premise: unfolded })?;
        Ok(self.hol.proof_step(EqMp {
            equality: folded,
            premise: equation,
        })?)
    }

    /// `DISJ1`: from `A |- p`, `A |- or p q`.
    ///
    /// # Errors
    ///
    /// Fails if `q` is not Boolean or the kernel refuses a step.
    pub fn disj1(
        &self,
        theorem: TheoremId<'v>,
        q: TermId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        self.disj(theorem, q, true)
    }

    /// `DISJ2`: from `A |- q`, `A |- or p q`.
    ///
    /// # Errors
    ///
    /// Fails if `p` is not Boolean or the kernel refuses a step.
    pub fn disj2(
        &self,
        p: TermId<'v>,
        theorem: TheoremId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        self.disj(theorem, p, false)
    }

    // ------------------------------------------------------------------
    // Derivation internals.
    // ------------------------------------------------------------------

    fn selector_ty(&self) -> Result<TypeId<'v>, LogicError> {
        let bool_bool = self.hol.ty(Ty::Arr(self.bool_ty, self.bool_ty))?;
        Ok(self.hol.ty(Ty::Arr(self.bool_ty, bool_bool))?)
    }

    /// Splits `App(App(connective, p), q)` into `(p, q)`.
    fn binary_operands(
        &self,
        term: TermId<'v>,
        connective: TermId<'v>,
    ) -> Result<Option<(TermId<'v>, TermId<'v>)>, LogicError> {
        let Tm::App(partial, q) = self.hol.tm_node(term)? else {
            return Ok(None);
        };
        let Tm::App(head, p) = self.hol.tm_node(partial)? else {
            return Ok(None);
        };
        Ok((head == connective).then_some((p, q)))
    }

    /// Returns the right-hand side of an equality conclusion.
    fn equality_rhs(&self, theorem: TheoremId<'v>) -> Result<TermId<'v>, LogicError> {
        let (.., concl) = self.hol.theorem(theorem)?;
        match self.hol.tm_node(concl)? {
            Tm::Eq(_, rhs) => Ok(rhs),
            _ => DerivationSnafu {
                what: "expected an equality conclusion",
            }
            .fail(),
        }
    }

    /// Head-beta conversion for a binary connective:
    /// `|- connective a b = body[a, b]`.
    fn unfold_binary(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        connective: TermId<'v>,
        a: TermId<'v>,
        b: TermId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        let first = self.hol.proof_step(Beta {
            kinds,
            vars,
            lam: connective,
            arg: a,
        })?;
        let partial = self.equality_rhs(first)?;
        let argument = self.hol.proof_step(Refl {
            kinds,
            vars,
            term: b,
        })?;
        let applied = self.hol.proof_step(MkComb {
            function: first,
            argument,
        })?;
        let second = self.hol.proof_step(Beta {
            kinds,
            vars,
            lam: partial,
            arg: b,
        })?;
        Ok(self.hol.proof_step(Trans {
            left: applied,
            right: second,
        })?)
    }

    /// Projects one side of a conjunction with a selector combinator.
    fn conjunct(&self, theorem: TheoremId<'v>, first: bool) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, _, concl) = self.hol.theorem(theorem)?;
        let (p, q) = self
            .binary_operands(concl, self.terms.and)?
            .ok_or(LogicError::NotAConjunction)?;

        // A |- (\f. f p q) = (\f. f true true).
        let unfolded = self.unfold_binary(kinds, vars, self.terms.and, p, q)?;
        let body = self.hol.proof_step(EqMp {
            equality: unfolded,
            premise: theorem,
        })?;
        let (.., body_concl) = self.hol.theorem(body)?;
        let Tm::Eq(pair, pair_true) = self.hol.tm_node(body_concl)? else {
            return DerivationSnafu {
                what: "unfolded conjunction is not an equality",
            }
            .fail();
        };

        // Apply both sides to \a. \b. a (or \a. \b. b) and beta-reduce.
        let inner = self.hol.tm(Tm::Bv(u32::from(first)))?;
        let choose = self.hol.tm(Tm::Lam(self.bool_ty, inner))?;
        let selector = self.hol.tm(Tm::Lam(self.bool_ty, choose))?;
        let selector_refl = self.hol.proof_step(Refl {
            kinds,
            vars,
            term: selector,
        })?;
        let applied = self.hol.proof_step(MkComb {
            function: body,
            argument: selector_refl,
        })?;
        let left = self.reduce_selected(kinds, vars, pair, selector)?;
        let right = self.reduce_selected(kinds, vars, pair_true, selector)?;

        // p = (\f. f p q) sel = (\f. f true true) sel = true.
        let start = self.hol.proof_step(Sym { premise: left })?;
        let across = self.hol.proof_step(Trans {
            left: start,
            right: applied,
        })?;
        let equation = self.hol.proof_step(Trans {
            left: across,
            right,
        })?;
        self.eqt_elim(equation)
    }

    /// `|- (\f. f x y) sel = sel x y = picked` for a pairing lambda.
    fn reduce_selected(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        pair: TermId<'v>,
        selector: TermId<'v>,
    ) -> Result<TheoremId<'v>, LogicError> {
        let opened = self.hol.proof_step(Beta {
            kinds,
            vars,
            lam: pair,
            arg: selector,
        })?;
        let spread = self.equality_rhs(opened)?;
        let Some((x, y)) = self.binary_operands(spread, selector)? else {
            return DerivationSnafu {
                what: "pairing lambda did not open to a selector application",
            }
            .fail();
        };
        let picked = self.unfold_binary(kinds, vars, selector, x, y)?;
        Ok(self.hol.proof_step(Trans {
            left: opened,
            right: picked,
        })?)
    }

    /// Shared derivation for both disjunction introductions.
    fn disj(
        &self,
        theorem: TheoremId<'v>,
        other: TermId<'v>,
        left_side: bool,
    ) -> Result<TheoremId<'v>, LogicError> {
        let (kinds, vars, _, concl) = self.hol.theorem(theorem)?;
        let (p, q) = if left_side {
            (concl, other)
        } else {
            (other, concl)
        };

        // Work under the quantified variable r: lift the premise and
        // assume the branch hypothesis that applies to it.
        let lifted = self.hol.proof_step(WeakenVar {
            thm: theorem,
            ty: self.bool_ty,
        })?;
        let (inner_kinds, inner_vars, _, lifted_concl) = self.hol.theorem(lifted)?;
        let r = self.hol.tm(Tm::Bv(0))?;
        let p_lifted = if left_side {
            lifted_concl
        } else {
            self.lift_term(p)?
        };
        let q_lifted = if left_side {
            self.lift_term(q)?
        } else {
            lifted_concl
        };
        let p_implies_r = self.apply2(self.terms.imp, p_lifted, r)?;
        let q_implies_r = self.apply2(self.terms.imp, q_lifted, r)?;
        let branch = if left_side { p_implies_r } else { q_implies_r };
        let assumed = self.assume(inner_kinds, inner_vars, branch)?;
        let reached = self.mp(assumed, lifted)?;

        // Discharge q -> r then p -> r, close over r, and fold back to
        // the or application.
        let inner_implication = self.disch(q_implies_r, reached)?;
        let chain = self.disch(p_implies_r, inner_implication)?;
        let body_true = self.eqt_intro(chain)?;
        let closed = self.hol.proof_step(Abs { premise: body_true })?;

        let unfolded = self.unfold_binary(kinds, vars, self.terms.or, p, q)?;
        let (.., closed_concl) = self.hol.theorem(closed)?;
        if self.equality_rhs(unfolded)? != closed_concl {
            return DerivationSnafu {
                what: "disjunction body disagrees with the unfolded definition",
            }
            .fail();
        }
        let folded = self.hol.proof_step(Sym { premise: unfolded })?;
        Ok(self.hol.proof_step(EqMp {
            equality: folded,
            premise: closed,
        })?)
    }

    /// Lifts a term across one new innermost variable.
    fn lift_term(&self, term: TermId<'v>) -> Result<TermId<'v>, LogicError> {
        let tree = self.hol.load_tm(term)?;
        Ok(self.hol.intern_tm(&lift_tm_in_tm(&tree, 1, 0))?)
    }
}

#[cfg(test)]
mod tests {
    use covalence_nucleus::hol::{AllowAll, Hol, HypsId, syntax::TheoremId};

    use super::*;

    fn open_seeded() -> Connection<Hol<AllowAll>> {
        let bytes = covalence_hol_init::init_image().expect("generate init image");
        open_image(&bytes, AllowAll).expect("open init image")
    }

    /// Runs `check` with a logic API over two Boolean variables
    /// `p = Bv 0` and `q = Bv 1`.
    fn with_two_props(
        check: impl for<'l, 'v> FnOnce(
            &Logic<'l, 'v, AllowAll>,
            VarsId<'v>,
            TermId<'v>,
            TermId<'v>,
        ) -> Result<(), LogicError>,
    ) {
        let connection = open_seeded();
        let hol = connection.view();
        let logic = Logic::new(&hol).expect("resolve init exports");
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let vars = hol.vars(&[bool_ty, bool_ty]).expect("vars");
        let p = hol.tm(Tm::Bv(0)).expect("p");
        let q = hol.tm(Tm::Bv(1)).expect("q");
        check(&logic, vars, p, q).expect("derivation");
    }

    fn parts<'v>(
        logic: &Logic<'_, 'v, AllowAll>,
        theorem: TheoremId<'v>,
    ) -> (HypsId<'v>, TermId<'v>) {
        let (_, _, hyps, concl) = logic.hol.theorem(theorem).expect("theorem parts");
        (hyps, concl)
    }

    fn hyp_terms<'v>(logic: &Logic<'_, 'v, AllowAll>, hyps: HypsId<'v>) -> Vec<TermId<'v>> {
        logic.hol.hyps_entries(hyps).expect("hypotheses")
    }

    #[test]
    fn truth_is_provable_in_the_empty_context() {
        let connection = open_seeded();
        let hol = connection.view();
        let logic = Logic::new(&hol).expect("resolve init exports");
        let theorem = logic
            .truth(hol.empty_kinds(), hol.empty_vars())
            .expect("truth");
        let (_, _, hyps, concl) = hol.theorem(theorem).expect("parts");
        assert_eq!(hyps, hol.empty_hyps());
        assert_eq!(concl, logic.constants().truth);
    }

    #[test]
    fn conjunction_introduces_from_hypotheses() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            let assume_q = logic.assume(hol.empty_kinds(), vars, q)?;
            let both = logic.conj(assume_p, assume_q)?;
            let (hyps, concl) = parts(logic, both);
            assert_eq!(hyp_terms(logic, hyps), vec![p, q]);
            assert_eq!(concl, logic.and_term(p, q)?);
            Ok(())
        });
    }

    #[test]
    fn conjunction_commutes() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let conjunction = logic.and_term(p, q)?;
            let assumed = logic.assume(hol.empty_kinds(), vars, conjunction)?;
            let left = logic.conjunct1(assumed)?;
            let right = logic.conjunct2(assumed)?;
            assert_eq!(parts(logic, left).1, p);
            assert_eq!(parts(logic, right).1, q);
            let swapped = logic.conj(right, left)?;
            let (hyps, concl) = parts(logic, swapped);
            assert_eq!(hyp_terms(logic, hyps), vec![conjunction]);
            assert_eq!(concl, logic.and_term(q, p)?);
            Ok(())
        });
    }

    #[test]
    fn disjunction_introduces_on_both_sides() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            let left = logic.disj1(assume_p, q)?;
            let (hyps, concl) = parts(logic, left);
            assert_eq!(hyp_terms(logic, hyps), vec![p]);
            assert_eq!(concl, logic.or_term(p, q)?);

            let assume_q = logic.assume(hol.empty_kinds(), vars, q)?;
            let right = logic.disj2(p, assume_q)?;
            let (hyps, concl) = parts(logic, right);
            assert_eq!(hyp_terms(logic, hyps), vec![q]);
            assert_eq!(concl, logic.or_term(p, q)?);
            Ok(())
        });
    }

    #[test]
    fn modus_ponens_eliminates_implications() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let implication = logic.imp_term(p, q)?;
            let assume_imp = logic.assume(hol.empty_kinds(), vars, implication)?;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            let consequence = logic.mp(assume_imp, assume_p)?;
            let (hyps, concl) = parts(logic, consequence);
            assert_eq!(hyp_terms(logic, hyps), vec![p, implication]);
            assert_eq!(concl, q);
            Ok(())
        });
    }

    #[test]
    fn discharge_proves_the_identity_implication() {
        with_two_props(|logic, vars, p, _| {
            let hol = logic.hol;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            let identity = logic.disch(p, assume_p)?;
            let (hyps, concl) = parts(logic, identity);
            assert_eq!(hyps, hol.empty_hyps());
            assert_eq!(concl, logic.imp_term(p, p)?);
            Ok(())
        });
    }

    #[test]
    fn discharge_then_modus_ponens_round_trips() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            let assume_q = logic.assume(hol.empty_kinds(), vars, q)?;
            let both = logic.conj(assume_p, assume_q)?;
            // {p, q} |- and p q becomes {q} |- imp p (and p q), and modus
            // ponens with a fresh |- p recovers the conjunction.
            let discharged = logic.disch(p, both)?;
            let (hyps, concl) = parts(logic, discharged);
            assert_eq!(hyp_terms(logic, hyps), vec![q]);
            assert_eq!(concl, logic.imp_term(p, logic.and_term(p, q)?)?);
            let recovered = logic.mp(discharged, assume_p)?;
            let (hyps, concl) = parts(logic, recovered);
            assert_eq!(hyp_terms(logic, hyps), vec![p, q]);
            assert_eq!(concl, logic.and_term(p, q)?);
            Ok(())
        });
    }

    #[test]
    fn shape_errors_are_reported_cleanly() {
        with_two_props(|logic, vars, p, q| {
            let hol = logic.hol;
            let assume_p = logic.assume(hol.empty_kinds(), vars, p)?;
            assert!(matches!(
                logic.conjunct1(assume_p),
                Err(LogicError::NotAConjunction)
            ));
            assert!(matches!(
                logic.mp(assume_p, assume_p),
                Err(LogicError::NotAnImplication)
            ));
            let implication = logic.imp_term(p, q)?;
            let assume_imp = logic.assume(hol.empty_kinds(), vars, implication)?;
            let assume_q = logic.assume(hol.empty_kinds(), vars, q)?;
            assert!(matches!(
                logic.mp(assume_imp, assume_q),
                Err(LogicError::PremiseMismatch)
            ));

            // Premises from different variable contexts are refused.
            let bool_ty = hol.ty(Ty::Bool)?;
            let narrow = hol.vars(&[bool_ty])?;
            let elsewhere = logic.assume(hol.empty_kinds(), narrow, p)?;
            assert!(matches!(
                logic.conj(assume_p, elsewhere),
                Err(LogicError::ContextMismatch)
            ));
            Ok(())
        });
    }

    #[test]
    fn logic_requires_a_seeded_database() {
        let connection =
            Connection::<Hol<AllowAll>>::open_hol_in_memory(AllowAll).expect("open unseeded");
        let hol = connection.view();
        assert!(matches!(
            Logic::new(&hol),
            Err(LogicError::Kernel {
                source: HolError::UnknownExport { .. }
            })
        ));
    }
}
