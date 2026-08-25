//! A proof component that builds the naturals arena.
//!
//! Two axioms, in the order the construction needs them.
//!
//! **Infinity** supplies a carrier with room in it. Ethane's only base type is
//! `bool`, so nothing built from the core is infinite; `inf-exists` concludes
//! that some type carries an equality-reflecting endomap missing a point.
//!
//! **The guarded subtype** carves the naturals out of that carrier. A
//! Dedekind-infinite type is strictly weaker than the naturals — it may hold
//! elements the map never reaches from the missed point — so the naturals are
//! the *reachable* part: the intersection of every subset containing the point
//! and closed under the map. That intersection is a predicate, and `sub-exists`
//! turns a predicate into a type.
//!
//! `Nucleus.HolE.Infinity.CInfinityStructure.natModel` is the same construction
//! in the classical semantics, where it is proved to satisfy Peano — induction
//! included, which is exactly what reachability buys — and to be categorical.
//!
//! ## Where this stops, and why
//!
//! The carrier cannot yet be *named*. `inf-exists` concludes
//! `∃type A. …`, and getting from there to a concrete `A` needs elimination for
//! `ty.exists`, which the kernel does not offer. So this component builds the
//! construction over a carrier it introduces as a free type variable, and
//! records both axioms in the arena it returns. What it demonstrates is that
//! the syntax composes and the capabilities are tracked; what it does not do is
//! discharge the existential, and no amount of arranging the calls would.

// `cargo component` generates the canonical-ABI glue. It intentionally uses
// low-level casts and naming patterns that are outside this crate's style.
#[allow(
    unsafe_code,
    warnings,
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::restriction
)]
#[cfg(target_os = "wasi")]
mod bindings;

#[cfg(target_os = "wasi")]
use bindings::{exports::nucleus::proof::standard::Guest, nucleus::proof::host::Kernel};

#[cfg(target_os = "wasi")]
struct Component;

#[cfg(target_os = "wasi")]
impl Guest for Component {
    fn prove() -> Result<Kernel, String> {
        let kernel = Kernel::new();
        let star = kernel.kind_star()?;
        let bool_ty = kernel.bool_type(star)?;

        // --- infinity ------------------------------------------------------
        kernel.add_axiom("ax.inf")?;
        let infinity = kernel.inf_exists(bool_ty)?;
        if infinity.carrier_name < infinity.base_name {
            return Err("the carrier binder should sit at the sentence's base".to_owned());
        }

        // --- a carrier to work over ----------------------------------------
        // Standing in for the type the sentence asserts, until `ty.exists`
        // elimination exists to produce it. Named above everything so far, so
        // it cannot collide with the sentence's own binders.
        let names = kernel.fresh_name(&[bool_ty, infinity.exists_type])?;
        let carrier = kernel.ty_fv(names, star)?;
        let endomap_ty = kernel.ty_arr(carrier, carrier)?;
        let map = kernel.tm_fv(names + 1, endomap_ty)?;
        let missed = kernel.tm_fv(names + 2, carrier)?;

        // --- reachability --------------------------------------------------
        // `reachable a` is `∀S. S missed → (∀x. S x → S (map x)) → S a`, the
        // intersection of every subset containing the point and closed under
        // the map. Impredicative, and that is the point: quantifying over all
        // subsets is what makes the induction principle hold for all of them.
        let predicate_ty = kernel.ty_arr(carrier, bool_ty)?;
        let subset = kernel.tm_fv(names + 3, predicate_ty)?;
        let element = kernel.tm_fv(names + 4, carrier)?;
        let point = kernel.tm_fv(names + 5, carrier)?;
        let conjunction_unary = kernel.ty_arr(bool_ty, bool_ty)?;
        let conjunction_ty = kernel.ty_arr(bool_ty, conjunction_unary)?;
        let conjunction = kernel.tm_fv(names + 6, conjunction_ty)?;

        let holds_missed = kernel.app(subset, missed)?;
        let closed = {
            let holds_element = kernel.app(subset, element)?;
            let image = kernel.app(map, element)?;
            let holds_image = kernel.app(subset, image)?;
            let step = kernel.imp_tm(bool_ty, conjunction, holds_element, holds_image)?;
            kernel.forall_tm(bool_ty, element, step)?
        };
        let reachable_body = {
            let holds_point = kernel.app(subset, point)?;
            let tail = kernel.imp_tm(bool_ty, conjunction, closed, holds_point)?;
            let guarded = kernel.imp_tm(bool_ty, conjunction, holds_missed, tail)?;
            kernel.forall_tm(bool_ty, subset, guarded)?
        };
        let reachable = kernel.lam(point, reachable_body)?;

        // --- the naturals --------------------------------------------------
        kernel.add_axiom("ax.sub")?;
        let naturals = kernel.sub_exists(bool_ty, carrier, reachable)?;
        let nat = kernel.model(naturals.model_name, naturals.package_body)?;

        // Zero and successor live on that subtype. `rep`/`abs` come from the
        // untrusted package layer, so what is checkable here is that the type
        // is well formed and that terms over it typecheck.
        let zero_like = kernel.tm_fv(naturals.base_name + 100, nat)?;
        let reflexive = kernel.tm_eq(bool_ty, zero_like, zero_like)?;
        let closed_law = kernel.forall_tm(bool_ty, zero_like, reflexive)?;
        if kernel.classifier(closed_law)? != bool_ty {
            return Err("a law over the naturals should be Boolean".to_owned());
        }

        Ok(kernel)
    }
}

#[cfg(target_os = "wasi")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
