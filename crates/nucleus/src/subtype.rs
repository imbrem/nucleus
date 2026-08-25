//! Guarded subtypes, as an untrusted layer over the subtype axiom.
//!
//! [`Kernel::sub_exists`] concludes one sentence: *some* type stands in the
//! guarded bijection with the carrier. That is the whole of what the kernel
//! will say, and it is not yet a subtype anybody can use — there is no `rep`,
//! no `abs`, and no law to appeal to. This module builds those.
//!
//! ```text
//!   { x : A // P x  ∨  ¬∃y. P y }
//! ```
//!
//! is the type carved out. The guard is what makes the construction total: HOL's
//! `typedef` needs a proof that `P` holds somewhere, because a type must be
//! inhabited, and here the fallback clause supplies all of `A` when `P` holds
//! nowhere. So [`SubtypeExt::guarded_subtype`] never asks the caller for a
//! nonemptiness proof. The price is that `rep` inverts `abs` only on guarded
//! values, which is what [`Subtype::rep_abs`] says.
//!
//! ## Why this is outside the kernel
//!
//! Nothing here carries authority. Every term is built through public checked
//! constructors, so the worst a bug in this module can do is produce a
//! well-formed term that is not the one intended — a useless statement, not a
//! provable falsehood. The one operation that *does* carry authority, minting
//! the sentence as a theorem, stays in the kernel and is called once, from
//! [`SubtypeExt::guarded_subtype`].
//!
//! That means this module deliberately **rebuilds** the package laws that
//! `Kernel::sub_exists` builds privately, rather than reaching into the
//! kernel for them. The duplication is the point: an untrusted layer that
//! borrowed the kernel's construction would not be replaceable. Its risk is
//! drift — if the two stopped agreeing, the laws here would quietly cease to
//! be about the sentence the axiom concluded — so `same_shape` in the tests
//! walks both terms and fails if they ever diverge.
//!
//! ## Type rows are not interchangeable
//!
//! Ethane's type equality is the row union-find, not structural: two
//! separately appended `sub → carrier` rows are *different types*. [`Subtype`]
//! therefore hands back the rows it built ([`rep_ty`](Subtype::rep_ty),
//! [`abs_ty`](Subtype::abs_ty), [`sub`](Subtype::sub)) instead of leaving a
//! caller to reconstruct them, and every construction below threads one row
//! rather than rebuilding it.

use covalence_logic_hol::{Binder, Kernel, KernelError, Ref, SubtypeAxiom, ThmId};

/// A usable guarded subtype.
///
/// The three law fields are *statements*. They are true exactly when
/// [`theorem`](Self::theorem) is present, which is what the `ax.sub`
/// capability buys; on their own they are just Boolean terms.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Subtype {
    /// The carrier type the subtype was carved out of.
    pub carrier: Ref,
    /// The defining predicate, of type `carrier → bool`.
    pub predicate: Ref,
    /// The subtype itself: `model B. package`.
    pub sub: Ref,
    /// `rep : sub → carrier`.
    pub rep: Ref,
    /// `abs : carrier → sub`.
    pub abs: Ref,
    /// The `sub → carrier` row classifying [`rep`](Self::rep).
    pub rep_ty: Ref,
    /// The `carrier → sub` row classifying [`abs`](Self::abs).
    pub abs_ty: Ref,
    /// `∀ b : sub. abs (rep b) = b`.
    pub abs_rep: Ref,
    /// `∀ a : carrier. guard a → rep (abs a) = a`.
    pub rep_abs: Ref,
    /// `∀ b : sub. guard (rep b)`.
    pub rep_guarded: Ref,
    /// The package sentence, and the theorem concluding it, when this subtype
    /// was built through the axiom rather than merely constructed.
    pub axiom: Option<SubtypeAxiom>,
    /// The first name reserved for the package's own binders.
    pub base_name: u64,
}

impl Subtype {
    /// The name given to `binder`.
    #[must_use]
    pub const fn name_of(&self, binder: Binder) -> u64 {
        self.base_name + binder as u64
    }

    /// The sequent concluding the package sentence, if this subtype came from
    /// the axiom.
    #[must_use]
    pub fn theorem(&self) -> Option<ThmId> {
        self.axiom.map(|axiom| axiom.theorem)
    }
}

/// Guarded subtypes over any checked Ethane kernel.
pub trait SubtypeExt {
    /// Builds the guarded subtype of `carrier` cut out by `predicate`, and
    /// concludes its package sentence.
    ///
    /// Consumes the `ax.sub` capability, so the arena records that it rests on
    /// the subtype axiom. Total: every predicate has a package, and no
    /// nonemptiness proof is required.
    ///
    /// # Errors
    ///
    /// Returns an error if the arena does not carry the [`AX_SUB`] capability,
    /// or unless `bool_ty` is Boolean, `carrier` is a type of kind `star`, and
    /// `predicate` is a term of type `carrier → bool`.
    fn guarded_subtype(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<Subtype, KernelError>;

    /// Builds the same terms without invoking the axiom.
    ///
    /// The laws are then unsupported statements. Useful for constructing a
    /// subtype's syntax in an arena that has not taken on `ax.sub` — to hash
    /// it, to compare it, or to hand it somewhere the axiom is available.
    ///
    /// # Errors
    ///
    /// As [`guarded_subtype`](Self::guarded_subtype), less the capability.
    fn subtype_terms(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<Subtype, KernelError>;
}

impl SubtypeExt for Kernel {
    fn guarded_subtype(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<Subtype, KernelError> {
        // The axiom first: it fixes the base name and the package body, and
        // everything below has to be about *that* subtype.
        let axiom = self.sub_exists(bool_ty, carrier, predicate)?;
        let sub = self.model(axiom.model_name, axiom.package)?;
        let mut built = Builder {
            kernel: self,
            bool_ty,
            carrier,
            predicate,
            base: axiom.base_name,
        }
        .over(sub)?;
        built.axiom = Some(axiom);
        Ok(built)
    }

    fn subtype_terms(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<Subtype, KernelError> {
        let base = self.fresh_name(&[carrier, predicate])?;
        let mut builder = Builder {
            kernel: self,
            bool_ty,
            carrier,
            predicate,
            base,
        };
        let package = builder.package_body()?;
        let model_name = builder.name(Binder::ModelType);
        let sub = builder.kernel.model(model_name, package)?;
        builder.over(sub)
    }
}

/// One package under construction.
///
/// `bool_ty`, the carrier, the predicate and the base name are fixed for the
/// whole build, so they are held once rather than threaded through every
/// signature.
struct Builder<'kernel> {
    kernel: &'kernel mut Kernel,
    bool_ty: Ref,
    carrier: Ref,
    predicate: Ref,
    base: u64,
}

impl Builder<'_> {
    const fn name(&self, binder: Binder) -> u64 {
        self.base + binder as u64
    }

    /// Choose `rep` and `abs` out of the package at a concrete subtype, then
    /// state the three laws about that choice.
    fn over(&mut self, sub: Ref) -> Result<Subtype, KernelError> {
        let rep_ty = self.kernel.ty_arr(sub, self.carrier)?;
        let abs_ty = self.kernel.ty_arr(self.carrier, sub)?;
        let representation = self
            .kernel
            .tm_fv(self.name(Binder::Representation), rep_ty)?;
        let abstraction = self.kernel.tm_fv(self.name(Binder::Abstraction), abs_ty)?;

        // `rep` is the representation for which *some* compatible abstraction
        // exists; `abs` is then an abstraction compatible with that `rep`.
        // Choosing in this order is what makes the pair cohere.
        let rep_laws = self.laws(sub, representation, abstraction)?;
        let rep_has_abstraction = self.kernel.exists_tm(abstraction, rep_laws)?;
        let rep_chooser = self.kernel.lam(representation, rep_has_abstraction)?;
        let rep = self.kernel.eps(rep_ty, rep_chooser)?;

        let abs_laws = self.laws(sub, rep, abstraction)?;
        let abs_chooser = self.kernel.lam(abstraction, abs_laws)?;
        let abs = self.kernel.eps(abs_ty, abs_chooser)?;

        let (abs_rep, rep_abs, rep_guarded) = self.law_parts(sub, rep, abs)?;

        Ok(Subtype {
            carrier: self.carrier,
            predicate: self.predicate,
            sub,
            rep,
            abs,
            rep_ty,
            abs_ty,
            abs_rep,
            rep_abs,
            rep_guarded,
            axiom: None,
            base_name: self.base,
        })
    }

    /// `∃rep. ∃abs. laws` over a bound model type — the body the sentence
    /// quantifies, rebuilt so a subtype can be constructed without the axiom.
    fn package_body(&mut self) -> Result<Ref, KernelError> {
        let star = self.kernel.star()?;
        let model_ty = self.kernel.ty_fv(self.name(Binder::ModelType), star)?;
        let rep_ty = self.kernel.ty_arr(model_ty, self.carrier)?;
        let abs_ty = self.kernel.ty_arr(self.carrier, model_ty)?;
        let representation = self
            .kernel
            .tm_fv(self.name(Binder::Representation), rep_ty)?;
        let abstraction = self.kernel.tm_fv(self.name(Binder::Abstraction), abs_ty)?;
        let laws = self.laws(model_ty, representation, abstraction)?;
        let has_abstraction = self.kernel.exists_tm(abstraction, laws)?;
        self.kernel.exists_tm(representation, has_abstraction)
    }

    /// `P value ∨ ¬∃w. P w` — membership in the guarded predicate.
    fn guard(&mut self, value: Ref) -> Result<Ref, KernelError> {
        let witness = self
            .kernel
            .tm_fv(self.name(Binder::Witness), self.carrier)?;
        let holds_witness = self.kernel.app(self.predicate, witness)?;
        let inhabited = self.kernel.exists_tm(witness, holds_witness)?;
        let empty = self.kernel.not_tm(self.bool_ty, inhabited)?;
        let holds_value = self.kernel.app(self.predicate, value)?;
        let conjunction = self.conjunction_binder()?;
        self.kernel
            .or_tm(self.bool_ty, conjunction, holds_value, empty)
    }

    /// The three package laws for one candidate model type.
    fn law_parts(
        &mut self,
        model_ty: Ref,
        representation: Ref,
        abstraction: Ref,
    ) -> Result<(Ref, Ref, Ref), KernelError> {
        let carrier_value = self
            .kernel
            .tm_fv(self.name(Binder::CarrierValue), self.carrier)?;
        let subtype_value = self
            .kernel
            .tm_fv(self.name(Binder::SubtypeValue), model_ty)?;

        let rep_b = self.kernel.app(representation, subtype_value)?;
        let abs_a = self.kernel.app(abstraction, carrier_value)?;

        let abs_rep = {
            let applied = self.kernel.app(abstraction, rep_b)?;
            let equality = self.kernel.eq(self.bool_ty, applied, subtype_value)?;
            self.kernel
                .forall_tm(self.bool_ty, subtype_value, equality)?
        };

        let rep_abs = {
            let guard = self.guard(carrier_value)?;
            let applied = self.kernel.app(representation, abs_a)?;
            let equality = self.kernel.eq(self.bool_ty, applied, carrier_value)?;
            let conjunction = self.conjunction_binder()?;
            let implication = self
                .kernel
                .imp_tm(self.bool_ty, conjunction, guard, equality)?;
            self.kernel
                .forall_tm(self.bool_ty, carrier_value, implication)?
        };

        let rep_guarded = {
            let guard = self.guard(rep_b)?;
            self.kernel.forall_tm(self.bool_ty, subtype_value, guard)?
        };

        Ok((abs_rep, rep_abs, rep_guarded))
    }

    /// The three laws conjoined, right-nested.
    fn laws(
        &mut self,
        model_ty: Ref,
        representation: Ref,
        abstraction: Ref,
    ) -> Result<Ref, KernelError> {
        let (abs_rep, rep_abs, rep_guarded) =
            self.law_parts(model_ty, representation, abstraction)?;
        let conjunction = self.conjunction_binder()?;
        let tail = self
            .kernel
            .and_tm(self.bool_ty, conjunction, rep_abs, rep_guarded)?;
        self.kernel.and_tm(self.bool_ty, conjunction, abs_rep, tail)
    }

    /// The bound function variable of the equality-only conjunction encoding.
    fn conjunction_binder(&mut self) -> Result<Ref, KernelError> {
        let unary = self.kernel.ty_arr(self.bool_ty, self.bool_ty)?;
        let binary = self.kernel.ty_arr(self.bool_ty, unary)?;
        self.kernel.tm_fv(self.name(Binder::Conjunction), binary)
    }
}
