//! Guarded subtypes, as a library definition over `ty.model`.
//!
//! Ethane has type choice (`ty.model`) but no primitive subtype, abstraction,
//! or representation constructor. A subtype is instead the model selected by a
//! predicate saying "this type is in bijection with the part of `A` that `P`
//! picks out" — no new syntax, and one axiom.
//!
//! ## The guard, and why there is no nonemptiness premise
//!
//! HOL's `typedef` requires a proof that `P` holds somewhere, because a type
//! must be inhabited. Ethane sidesteps that by carving out
//!
//! ```text
//!   { x : A // P x  ∨  ¬∃y. P y }
//! ```
//!
//! instead of `{ x : A // P x }`. When `P` holds somewhere the guard is
//! equivalent to `P`; when `P` holds nowhere the guard is *everywhere* true
//! and the subtype is all of `A`, which is inhabited because `A` is. So
//! [`Kernel::subtype`] is **total**: every predicate has a package, and the
//! caller owes nothing. The price is that the `rep`-inverts-`abs` law holds
//! only on guarded values, which is what [`Subtype::rep_abs`] states.
//!
//! ## What the axiom is, and what it is not
//!
//! [`Kernel::subtype`] only *builds terms* — it appends no assumption and
//! needs no capability, because `ty.model` is a primitive and choosing a model
//! is always well-formed. What the axiom supplies is that the chosen model is
//! a *genuine* one: that the package sentence
//! [`Subtype::exists_type`] is true, so the laws may be used. That is
//! [`Kernel::sub_exists`], and it consumes the `ax.sub` capability.
//!
//! ## What is established about the sentence, and what is not
//!
//! Lean carries **two** constructions of this package, and they are not the
//! same object:
//!
//! * `Nucleus.Hol.Ethane.Subtype` builds it in *named* Ethane syntax. That is
//!   the one this module mirrors, and after the `freshBase` alignment it
//!   builds the same term — see the hygiene section.
//! * `Nucleus.HolE.Empty.SubtypePackage` rebuilds it through the
//!   intrinsically checked de Bruijn API, and that is the one carrying the
//!   soundness theorem:
//!
//! ```text
//!   theorem Eval.existsType_true (A) (P : Term Ctx.empty (A.arr FamK.boolTy)) (env) :
//!     Eval (existsType A P) env emptyCBoundEnv cBool true
//! ```
//!
//! — the sentence is true for **every** checked predicate, in the classical
//! pointed-set semantics, with no `sorry` and no side condition, witnessed by
//! the concrete guarded carrier (`Subtype.guardedPackage`), off the
//! nonemptiness-free `semanticPackage_exists`.
//!
//! **No lemma links the two.** They are visibly the same construction written
//! twice, and each is checked, but "the sentence this module builds is true"
//! is not currently a theorem — it is a theorem about a parallel term plus a
//! reading of two definitions side by side. Closing that needs the named
//! construction lowered to the intrinsic one and the lowering shown to
//! preserve evaluation.
//!
//! So `ax.sub` is an axiom of the *object* logic — the kernel cannot derive
//! it, and an arena that uses it says so — and its truth is argued rather than
//! transported. That is a weaker claim than it would be worth making, and it
//! is the reason the capability is explicit.
//!
//! ## Type rows are not interchangeable
//!
//! Ethane's type equality is the row union-find, not structural: two
//! separately appended `sub → carrier` rows are different types. So
//! [`Subtype`] hands back the rows it built ([`Subtype::rep_ty`],
//! [`Subtype::abs_ty`], [`Subtype::sub`]) rather than leaving the caller to
//! reconstruct them, and every derived construction here threads one row
//! instead of rebuilding it.
//!
//! ## Hygiene
//!
//! The package binds seven variables of its own ([`Binder`]), and the caller's
//! `carrier` and `predicate` are dropped inside all of them. Capture would be
//! unsound, so the private names are allocated **above every name the caller's
//! terms use**: [`Kernel::subtype`] walks the sub-DAG reachable from the two
//! arguments and starts its binders one past the largest name it finds,
//! counting "no names at all" as zero.
//!
//! That makes the construction a function of `(carrier, predicate)` alone and
//! not of the surrounding arena, so the same pair yields the same sentence in
//! any arena — which content addressing depends on.
//!
//! `Nucleus.Hol.Ethane.Subtype` computes the same base the same way
//! (`freshBase = (callerNames A P).sup id + 1`, over `nameIndices`, which
//! counts bound names as well as free ones because materialization renames
//! binders too) and assigns the same names from it (`assign base`, leaving the
//! caller's names alone). `fresh_freshBase` discharges the freshness side
//! condition and `binder_notMem_of_fresh` is the hygiene guarantee it buys.
//! The two therefore build the same term, not merely equivalent ones.
//!
//! It did not start that way. Lean originally materialized through a parity
//! encoding — private binders even, caller names odd — which is equally
//! hygienic but renames the caller's terms, so a kernel building the package
//! in place could never match it. Aligning the two immediately turned up an
//! off-by-one in the empty case, where `Finset.sup ∅ + 1` is one and this was
//! zero.

use std::collections::BTreeSet;
use std::convert::Infallible;

use super::{Kernel, KernelError, ThmId};
use crate::{Ref, row::Expr as Node};

/// The name of the axiom capability [`Kernel::sub_exists`] consumes.
pub const AX_SUB: &str = "ax.sub";

/// The variables the guarded subtype package binds.
///
/// The discriminants match `Nucleus.Hol.Ethane.Subtype.Binder.code`, so a
/// reader can line the two constructions up.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u64)]
pub enum Binder {
    /// The type variable bound by `ty.exists` and `ty.model`.
    ModelType = 0,
    /// `rep`, of type `B → A`.
    Representation = 1,
    /// `abs`, of type `A → B`.
    Abstraction = 2,
    /// A value of the carrier `A`.
    CarrierValue = 3,
    /// A value of the subtype `B`.
    SubtypeValue = 4,
    /// The witness bound by the guard's inner existential.
    Witness = 5,
    /// The function variable of the equality-only conjunction encoding.
    Conjunction = 6,
}

/// How many names the package reserves above [`Subtype::base_name`].
pub const BINDER_COUNT: u64 = 7;

/// A built guarded subtype package.
///
/// Every field is a reference into the kernel that produced it. The three law
/// fields are *statements*, not theorems: they hold exactly when
/// [`Kernel::sub_exists`] has been used, which is what the axiom buys.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Subtype {
    /// The carrier type the subtype was carved out of.
    pub carrier: Ref,
    /// The defining predicate, of type `carrier → bool`.
    pub predicate: Ref,
    /// `∃type B. package` — the sentence `ax.sub` concludes.
    pub exists_type: Ref,
    /// The subtype itself: `model B. package`.
    pub sub: Ref,
    /// `rep : sub → carrier`.
    pub rep: Ref,
    /// `abs : carrier → sub`.
    pub abs: Ref,
    /// The `sub → carrier` row classifying [`rep`](Self::rep).
    ///
    /// Exposed because Ethane's type equality is the row union-find: an arrow
    /// the caller rebuilds is *not* equal to this one, so anything typed
    /// against `rep` must reuse this row.
    pub rep_ty: Ref,
    /// The `carrier → sub` row classifying [`abs`](Self::abs).
    pub abs_ty: Ref,
    /// `∀ b : sub. abs (rep b) = b`.
    pub abs_rep: Ref,
    /// `∀ a : carrier. guard a → rep (abs a) = a`.
    pub rep_abs: Ref,
    /// `∀ b : sub. guard (rep b)`.
    pub rep_guarded: Ref,
    /// The first name reserved for the package's own binders; the caller's
    /// terms use no name at or above it.
    pub base_name: u64,
}

impl Subtype {
    /// The name given to `binder`.
    #[must_use]
    pub const fn name_of(&self, binder: Binder) -> u64 {
        self.base_name + binder as u64
    }
}

impl Kernel {
    /// Builds the guarded subtype of `carrier` cut out by `predicate`.
    ///
    /// Appends terms only: no assumption is recorded and no capability is
    /// consumed. Using the resulting laws requires
    /// [`sub_exists`](Self::sub_exists).
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean, `carrier` is a type of
    /// kind `star`, and `predicate` is a term of type `carrier → bool`. Also
    /// propagates a name-space exhaustion if the caller's terms use names
    /// within [`BINDER_COUNT`] of `u64::MAX`.
    pub fn subtype(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<Subtype, KernelError> {
        self.require_bool_type::<Infallible>(bool_ty)?;
        self.require_star_type::<Infallible>(carrier)?;
        let predicate_ty = self.classifier(predicate)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(predicate_ty)?;
        if !self.equivalent(domain, carrier)? {
            return Err(KernelError::ClassifierMismatch {
                expected: carrier,
                actual: domain,
            });
        }
        self.require_bool_type::<Infallible>(codomain)?;

        let base_name = self.fresh_name_base(&[carrier, predicate])?;
        let name = |binder: Binder| base_name + binder as u64;

        // Kinds and the two function types the package quantifies over. The
        // model type is a *variable* here: everything below is built under the
        // `ty.exists` / `ty.model` binder that closes over it.
        let star = self.star()?;
        let model_ty = self.ty_fv(name(Binder::ModelType), star)?;
        let rep_ty = self.ty_arr(model_ty, carrier)?;
        let abs_ty = self.ty_arr(carrier, model_ty)?;
        let representation = self.tm_fv(name(Binder::Representation), rep_ty)?;
        let abstraction = self.tm_fv(name(Binder::Abstraction), abs_ty)?;

        let laws = self.package_laws(
            bool_ty,
            base_name,
            carrier,
            model_ty,
            predicate,
            representation,
            abstraction,
        )?;
        let has_abstraction = self.exists_tm(abstraction, laws)?;
        let package = self.exists_tm(representation, has_abstraction)?;

        let exists_type = self.ty_exists(name(Binder::ModelType), package)?;
        let sub = self.model(name(Binder::ModelType), package)?;

        // Outside the binder the model type is the concrete subtype, so the
        // two function types are rebuilt against `sub`.
        let concrete_rep_ty = self.ty_arr(sub, carrier)?;
        let concrete_abs_ty = self.ty_arr(carrier, sub)?;
        let concrete_representation = self.tm_fv(name(Binder::Representation), concrete_rep_ty)?;
        let concrete_abstraction = self.tm_fv(name(Binder::Abstraction), concrete_abs_ty)?;

        let rep_laws = self.package_laws(
            bool_ty,
            base_name,
            carrier,
            sub,
            predicate,
            concrete_representation,
            concrete_abstraction,
        )?;
        let rep_has_abstraction = self.exists_tm(concrete_abstraction, rep_laws)?;
        let rep_chooser = self.lam(concrete_representation, rep_has_abstraction)?;
        let rep = self.eps(concrete_rep_ty, rep_chooser)?;

        let abs_laws = self.package_laws(
            bool_ty,
            base_name,
            carrier,
            sub,
            predicate,
            rep,
            concrete_abstraction,
        )?;
        let abs_chooser = self.lam(concrete_abstraction, abs_laws)?;
        let abs = self.eps(concrete_abs_ty, abs_chooser)?;

        // The laws as usable statements about the chosen `rep` and `abs`.
        let (abs_rep, rep_abs, rep_guarded) =
            self.package_law_parts(bool_ty, base_name, carrier, sub, predicate, rep, abs)?;

        Ok(Subtype {
            carrier,
            predicate,
            exists_type,
            sub,
            rep,
            abs,
            rep_ty: concrete_rep_ty,
            abs_ty: concrete_abs_ty,
            abs_rep,
            rep_abs,
            rep_guarded,
            base_name,
        })
    }

    /// Concludes the guarded subtype-package sentence for `carrier` and
    /// `predicate`, consuming the `ax.sub` capability.
    ///
    /// The sentence is *rebuilt* here rather than taken from the caller, so
    /// the kernel asserts exactly the statement it constructed. The returned
    /// sequent is premise-free.
    ///
    /// # Errors
    ///
    /// Returns an error if the arena does not carry the [`AX_SUB`] capability,
    /// or for any reason [`subtype`](Self::subtype) would.
    pub fn sub_exists(
        &mut self,
        bool_ty: Ref,
        carrier: Ref,
        predicate: Ref,
    ) -> Result<(Subtype, ThmId), KernelError> {
        if !self.arena.axioms().any(|name| name == AX_SUB) {
            return Err(KernelError::MissingAxiom { name: AX_SUB });
        }
        let package = self.subtype(bool_ty, carrier, predicate)?;
        let theorem = self.push_axiom(package.exists_type)?;
        Ok((package, theorem))
    }

    /// `P value ∨ ¬∃w. P w` — membership in the guarded predicate.
    fn guard_body(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
        carrier: Ref,
        predicate: Ref,
        value: Ref,
    ) -> Result<Ref, KernelError> {
        let witness = self.tm_fv(base_name + Binder::Witness as u64, carrier)?;
        let holds_witness = self.app(predicate, witness)?;
        let inhabited = self.exists_tm(witness, holds_witness)?;
        let empty = self.not_tm(bool_ty, inhabited)?;
        let holds_value = self.app(predicate, value)?;
        let conjunction = self.conjunction_binder(bool_ty, base_name)?;
        self.or_tm(bool_ty, conjunction, holds_value, empty)
    }

    /// The three package laws for one candidate model type.
    #[allow(clippy::too_many_arguments)]
    fn package_law_parts(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
        carrier: Ref,
        model_ty: Ref,
        predicate: Ref,
        representation: Ref,
        abstraction: Ref,
    ) -> Result<(Ref, Ref, Ref), KernelError> {
        let carrier_value = self.tm_fv(base_name + Binder::CarrierValue as u64, carrier)?;
        let subtype_value = self.tm_fv(base_name + Binder::SubtypeValue as u64, model_ty)?;

        let rep_b = self.app(representation, subtype_value)?;
        let abs_a = self.app(abstraction, carrier_value)?;

        let abs_rep_body = {
            let applied = self.app(abstraction, rep_b)?;
            let equality = self.eq(bool_ty, applied, subtype_value)?;
            self.forall_tm(bool_ty, subtype_value, equality)?
        };

        let rep_abs_body = {
            let guard = self.guard_body(bool_ty, base_name, carrier, predicate, carrier_value)?;
            let applied = self.app(representation, abs_a)?;
            let equality = self.eq(bool_ty, applied, carrier_value)?;
            let conjunction = self.conjunction_binder(bool_ty, base_name)?;
            let implication = self.imp_tm(bool_ty, conjunction, guard, equality)?;
            self.forall_tm(bool_ty, carrier_value, implication)?
        };

        let rep_guarded_body = {
            let guard = self.guard_body(bool_ty, base_name, carrier, predicate, rep_b)?;
            self.forall_tm(bool_ty, subtype_value, guard)?
        };

        Ok((abs_rep_body, rep_abs_body, rep_guarded_body))
    }

    /// The three laws conjoined, right-nested as in Lean's `laws`.
    #[allow(clippy::too_many_arguments)]
    fn package_laws(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
        carrier: Ref,
        model_ty: Ref,
        predicate: Ref,
        representation: Ref,
        abstraction: Ref,
    ) -> Result<Ref, KernelError> {
        let (abs_rep, rep_abs, rep_guarded) = self.package_law_parts(
            bool_ty,
            base_name,
            carrier,
            model_ty,
            predicate,
            representation,
            abstraction,
        )?;
        let conjunction = self.conjunction_binder(bool_ty, base_name)?;
        let tail = self.and_tm(bool_ty, conjunction, rep_abs, rep_guarded)?;
        self.and_tm(bool_ty, conjunction, abs_rep, tail)
    }

    /// The bound function variable of the equality-only conjunction encoding.
    fn conjunction_binder(&mut self, bool_ty: Ref, base_name: u64) -> Result<Ref, KernelError> {
        let unary = self.ty_arr(bool_ty, bool_ty)?;
        let binary = self.ty_arr(bool_ty, unary)?;
        self.tm_fv(base_name + Binder::Conjunction as u64, binary)
    }

    /// One past the largest free name occurring in the sub-DAG reachable from
    /// `roots`, so a binder allocated there cannot capture.
    fn fresh_name_base(&self, roots: &[Ref]) -> Result<u64, KernelError> {
        let mut seen: BTreeSet<Ref> = BTreeSet::new();
        let mut stack: Vec<Ref> = roots.to_vec();
        let mut highest: Option<u64> = None;
        while let Some(reference) = stack.pop() {
            if !seen.insert(reference) {
                continue;
            }
            let row = self.row::<Infallible>(reference)?;
            let node = *row.expr();
            if let Node::TyFv { name, .. }
            | Node::TmFv { name, .. }
            | Node::TyExists { name, .. }
            | Node::Model { name, .. } = node
            {
                highest = Some(highest.map_or(name, |seen| seen.max(name)));
            }
            stack.extend(node.children());
        }
        // One past the largest name, counting "no names at all" as zero — the
        // uniform rule, so this agrees with `Nucleus.Hol.Ethane.Subtype.freshBase`
        // (`Finset.sup` of the empty set is zero) in every case rather than all
        // but one. Spending name zero is worth an exact correspondence.
        let base = highest
            .unwrap_or(0)
            .checked_add(1)
            .ok_or(KernelError::TooManyNames)?;
        if u64::MAX - base < BINDER_COUNT {
            return Err(KernelError::TooManyNames);
        }
        Ok(base)
    }
}
