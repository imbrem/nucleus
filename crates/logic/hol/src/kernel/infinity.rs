//! The axiom of infinity.
//!
//! Ethane's only base type is `bool`, so nothing in the core is infinite and
//! nothing built from the core can be. Every inductive type — the naturals
//! first among them — has to be carved out of a carrier that already has room,
//! and this is where that room comes from.
//!
//! ## What the sentence says
//!
//! ```text
//!   ∃type A. ∃ f : A → A. ∃ z : A.
//!     (∀x. ∀y. (f x = f y) = (x = y)) ∧ (∀x. ¬(f x = z))
//! ```
//!
//! — some type carries an endomap that reflects equality and misses a point,
//! i.e. is Dedekind-infinite. Equality *reflection* rather than injectivity
//! because the two coincide and reflection is what equality-only HOL states
//! naturally: the implication direction is free.
//!
//! Mirrors `Nucleus.HolE.Infinity.infinityAxiom` term for term, in the same
//! way and for the same reason as the subtype package — see
//! [`subtype`](super::subtype) for the hygiene discipline, which is shared.
//!
//! ## What is trusted, and what it does not yet reach
//!
//! Only [`Kernel::inf_exists`], which builds the sentence and concludes it.
//!
//! Concluding it is not the same as *using* it. Getting from
//! `⊢ ∃type A. …` to a concrete carrier needs elimination for `ty.exists`,
//! which the kernel does not offer, so a caller cannot yet name the `A` whose
//! existence this asserts. The classical half of the bootstrap is complete —
//! `Nucleus.HolE.Infinity.CInfinityStructure` to
//! `Nucleus.HolE.Infinity.CNatModel.natModel` carves the naturals out of any
//! Dedekind-infinite carrier and proves them categorical — and the
//! object-language half stops here until that rule exists.

use std::convert::Infallible;

use super::{Kernel, KernelError, ThmId};
use crate::Ref;

/// The name of the axiom capability [`Kernel::inf_exists`] consumes.
pub const AX_INF: &str = "ax.inf";

/// The variables the infinity sentence binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u64)]
pub enum InfinityBinder {
    /// The type variable bound by `ty.exists`.
    Carrier = 0,
    /// The endomap `f : A → A`.
    Map = 1,
    /// The point `z : A` the map misses.
    Missed = 2,
    /// The outer value bound by each universal.
    Left = 3,
    /// The inner value bound by equality reflection.
    Right = 4,
    /// The function variable of the equality-only conjunction encoding.
    Conjunction = 5,
}

/// How many names the sentence reserves above [`InfinityAxiom::base_name`].
pub const INFINITY_BINDER_COUNT: u64 = 6;

/// The infinity sentence and the handles an outside layer needs to talk about
/// the same carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinityAxiom {
    /// `∃type A. body` — the sentence [`theorem`](Self::theorem) concludes.
    pub exists_type: Ref,
    /// The body `exists_type` quantifies, with the carrier type variable free.
    pub body: Ref,
    /// The name of the carrier type variable bound in `body`.
    pub carrier_name: u64,
    /// The first name reserved for the sentence's own binders.
    pub base_name: u64,
    /// The premise-free sequent concluding `exists_type`.
    pub theorem: ThmId,
}

impl InfinityAxiom {
    /// The name given to `binder`.
    #[must_use]
    pub const fn name_of(&self, binder: InfinityBinder) -> u64 {
        self.base_name + binder as u64
    }
}

impl Kernel {
    /// Concludes the axiom of infinity, consuming the `ax.inf` capability.
    ///
    /// The sentence is closed, so unlike [`sub_exists`](Self::sub_exists) it
    /// takes no arguments beyond the Boolean type to build it at. It is still
    /// constructed here rather than accepted, for the same reason.
    ///
    /// # Errors
    ///
    /// Returns an error if the arena does not carry the [`AX_INF`] capability,
    /// if `bool_ty` is not Boolean, or if no names remain.
    pub fn inf_exists(&mut self, bool_ty: Ref) -> Result<InfinityAxiom, KernelError> {
        if !self.arena.axioms().any(|name| name == AX_INF) {
            return Err(KernelError::MissingAxiom { name: AX_INF });
        }
        self.require_bool_type::<Infallible>(bool_ty)?;

        let base_name = self.fresh_name(&[bool_ty])?;
        let name = |binder: InfinityBinder| base_name + binder as u64;

        let star = self.star()?;
        let carrier_name = name(InfinityBinder::Carrier);
        let carrier = self.ty_fv(carrier_name, star)?;
        let endomap_ty = self.ty_arr(carrier, carrier)?;
        let map = self.tm_fv(name(InfinityBinder::Map), endomap_ty)?;
        let missed = self.tm_fv(name(InfinityBinder::Missed), carrier)?;
        let left = self.tm_fv(name(InfinityBinder::Left), carrier)?;
        let right = self.tm_fv(name(InfinityBinder::Right), carrier)?;

        // ∀x. ∀y. (f x = f y) = (x = y)
        let reflects = {
            let applied_left = self.app(map, left)?;
            let applied_right = self.app(map, right)?;
            let images = self.eq(bool_ty, applied_left, applied_right)?;
            let arguments = self.eq(bool_ty, left, right)?;
            let body = self.eq(bool_ty, images, arguments)?;
            let inner = self.forall_tm(bool_ty, right, body)?;
            self.forall_tm(bool_ty, left, inner)?
        };

        // ∀x. ¬(f x = z)
        let avoids_point = {
            let applied = self.app(map, left)?;
            let hit = self.eq(bool_ty, applied, missed)?;
            let body = self.not_tm(bool_ty, hit)?;
            self.forall_tm(bool_ty, left, body)?
        };

        let conjunction = self.infinity_conjunction_binder(bool_ty, base_name)?;
        let infinite = self.and_tm(bool_ty, conjunction, reflects, avoids_point)?;
        let choose_missed = self.exists_tm(missed, infinite)?;
        let body = self.exists_tm(map, choose_missed)?;
        let exists_type = self.ty_exists(carrier_name, body)?;
        let theorem = self.push_axiom(exists_type)?;

        Ok(InfinityAxiom {
            exists_type,
            body,
            carrier_name,
            base_name,
            theorem,
        })
    }

    /// The bound function variable of the equality-only conjunction encoding.
    fn infinity_conjunction_binder(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
    ) -> Result<Ref, KernelError> {
        let unary = self.ty_arr(bool_ty, bool_ty)?;
        let binary = self.ty_arr(bool_ty, unary)?;
        self.tm_fv(base_name + InfinityBinder::Conjunction as u64, binary)
    }
}
