//! Proof-component sketch of the natural-number construction.
//!
//! This is deliberately smaller than the standard init library. It exercises
//! the current async standard-proof ABI by concluding infinity, defining the
//! impredicative reachability predicate over an explicitly introduced carrier,
//! and carving a guarded subtype. It does not yet eliminate the type
//! existential, construct the subtype package's zero and successor, or prove
//! the Peano laws.
//!
//! The corresponding complete native derivation lives in
//! `covalence-logic-hol-derived`; moving that derivation behind a kernel-API
//! abstraction is the remaining step toward a Wasm generator for the current
//! init segment.

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
#[cfg(target_arch = "wasm32")]
mod bindings;

#[cfg(target_arch = "wasm32")]
use bindings::{exports::nucleus::proof::standard::Guest, nucleus::proof::host::Kernel};

#[cfg(target_arch = "wasm32")]
struct Component;

#[cfg(target_arch = "wasm32")]
impl Guest for Component {
    async fn prove(target: Vec<u8>) -> Result<Kernel, String> {
        if target.len() != 32 {
            return Err(format!(
                "proof targets contain 32 bytes, got {}",
                target.len()
            ));
        }
        if target.iter().any(|byte| *byte != 0) {
            return Err("the natural proof sketch only supports its default target".to_owned());
        }

        let kernel = Kernel::new();
        let star = kernel.kind_star()?;
        let bool_ty = kernel.bool_type(star)?;

        kernel.add_axiom("ax.inf")?;
        let infinity = kernel.inf_exists(bool_ty)?;
        if infinity.carrier_name < infinity.base_name {
            return Err("the infinity carrier binder precedes its reserved names".to_owned());
        }

        // `reachable a` is the intersection of every subset containing the
        // missed point and closed under the endomap. The complete native init
        // derivation eliminates `infinity.exists_type` and extracts the map
        // and missed point. This ABI sketch uses explicitly typed terms while
        // exercising the same impredicative predicate and subtype boundary.
        let names = kernel.fresh_name(&[bool_ty, infinity.exists_type])?;
        let carrier = kernel.ty_fv(names, star)?;
        let endomap_ty = kernel.ty_arr(carrier, carrier)?;
        let map = kernel.tm_fv(names + 1, endomap_ty)?;
        let missed = kernel.tm_fv(names + 2, carrier)?;
        let predicate_ty = kernel.ty_arr(carrier, bool_ty)?;
        let subset = kernel.tm_fv(names + 3, predicate_ty)?;
        let element = kernel.tm_fv(names + 4, carrier)?;
        let point = kernel.tm_fv(names + 5, carrier)?;
        let conjunction_unary = kernel.ty_arr(bool_ty, bool_ty)?;
        let conjunction_ty = kernel.ty_arr(bool_ty, conjunction_unary)?;
        let conjunction = kernel.tm_fv(names + 6, conjunction_ty)?;

        let holds_missed = kernel.app(subset, missed)?;
        let holds_element = kernel.app(subset, element)?;
        let image = kernel.app(map, element)?;
        let holds_image = kernel.app(subset, image)?;
        let step = kernel.imp_tm(bool_ty, conjunction, holds_element, holds_image)?;
        let closed = kernel.forall_tm(bool_ty, element, step)?;
        let holds_point = kernel.app(subset, point)?;
        let tail = kernel.imp_tm(bool_ty, conjunction, closed, holds_point)?;
        let guarded = kernel.imp_tm(bool_ty, conjunction, holds_missed, tail)?;
        let reachable_body = kernel.forall_tm(bool_ty, subset, guarded)?;
        let reachable = kernel.lam(point, reachable_body)?;

        kernel.add_axiom("ax.sub")?;
        let naturals = kernel.sub_exists(bool_ty, carrier, reachable)?;
        let natural_type = kernel.model(naturals.model_name, naturals.package_body)?;
        if kernel.classifier(natural_type)? != star {
            return Err("the carved natural carrier is not a type".to_owned());
        }

        Ok(kernel)
    }
}

#[cfg(target_arch = "wasm32")]
#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
