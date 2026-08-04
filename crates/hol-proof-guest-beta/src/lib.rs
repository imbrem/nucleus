//! Untrusted component which requests the closed-beta demo proof.
//!
//! Every value held here is an opaque host recipe handle. The host remains responsible for
//! replaying the recipe through Nucleus and independently deciding whether to serialize or sign
//! the resulting database.

mod bindings {
    wit_bindgen::generate!({
        path: "../nucleus/protocol/hol-proof-guest.wit",
        world: "hol-proof-guest",
    });
}

use bindings::covalence::hol_proof_guest::host::ProofPlan;
use bindings::exports::covalence::hol_proof_guest::guest::{Guest, GuestError};

struct ClosedBetaGuest;

impl Guest for ClosedBetaGuest {
    fn build(plan: &ProofPlan) -> Result<(), GuestError> {
        let bool_type = plan.bool_type().map_err(|_| GuestError::Aborted)?;
        let bound = plan
            .bound_term(0, &bool_type)
            .map_err(|_| GuestError::Aborted)?;
        let identity = plan
            .lambda(&bool_type, &bound)
            .map_err(|_| GuestError::Aborted)?;
        let truth = plan.bool_term(true).map_err(|_| GuestError::Aborted)?;
        let context = plan.empty_context().map_err(|_| GuestError::Aborted)?;
        let theorem = plan
            .prove_beta(&context, &identity, &truth)
            .map_err(|_| GuestError::Aborted)?;

        plan.persist_theorem(&theorem)
            .map_err(|_| GuestError::Aborted)?;
        let namespace = plan
            .root_child_namespace(Some("demo"))
            .map_err(|_| GuestError::Aborted)?;
        plan.export_theorem_conclusion(&namespace, 0, &theorem, Some("identity_true_beta"))
            .map_err(|_| GuestError::Aborted)?;
        plan.export_context(&namespace, 1, &context, Some("empty_context"))
            .map_err(|_| GuestError::Aborted)?;
        Ok(())
    }
}

#[allow(unsafe_code)]
mod component_export {
    use super::{ClosedBetaGuest, bindings};

    bindings::export!(ClosedBetaGuest with_types_in bindings);
}
