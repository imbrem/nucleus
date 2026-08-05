//! Untrusted component which requests a composed first-class conversion proof.
//!
//! Every value held here is an opaque host recipe handle. The host remains responsible for
//! replaying the recipe through Nucleus and independently deciding whether to serialize or sign
//! the resulting database.

#[cfg(target_arch = "wasm32")]
mod component {
    mod bindings {
        wit_bindgen::generate!({
            path: "../nucleus/protocol/hol-proof-guest.wit",
            world: "hol-proof-guest",
        });
    }

    use bindings::covalence::hol_proof_guest::host::ProofPlan;
    use bindings::exports::covalence::hol_proof_guest::guest::{Guest, GuestError};

    struct ConversionGuest;

    impl Guest for ConversionGuest {
        fn build(
            plan: &ProofPlan,
        ) -> Result<bindings::covalence::hol_proof_guest::host::NamespaceNode, GuestError> {
            let bool_type = plan.bool_type().map_err(|_| GuestError::Aborted)?;
            let bound = plan
                .bound_term(0, &bool_type)
                .map_err(|_| GuestError::Aborted)?;
            let identity = plan
                .lambda(&bool_type, &bound)
                .map_err(|_| GuestError::Aborted)?;
            let truth = plan.bool_term(true).map_err(|_| GuestError::Aborted)?;
            let context = plan.empty_context().map_err(|_| GuestError::Aborted)?;

            let identity_reflexivity = plan
                .conversion_reflexivity(&identity)
                .map_err(|_| GuestError::Aborted)?;
            let inner_beta = plan
                .conversion_beta(&identity, &truth)
                .map_err(|_| GuestError::Aborted)?;
            let outer_congruence = plan
                .conversion_application(&identity_reflexivity, &inner_beta)
                .map_err(|_| GuestError::Aborted)?;
            let nested_beta = plan
                .conversion_transitivity(&outer_congruence, &inner_beta)
                .map_err(|_| GuestError::Aborted)?;
            let theorem = plan
                .prove_conversion_equality(&context, &nested_beta)
                .map_err(|_| GuestError::Aborted)?;

            plan.persist_theorem(&theorem)
                .map_err(|_| GuestError::Aborted)?;
            let namespace = plan
                .root_child_namespace(Some("conversion-demo"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_context(&namespace, 0, &context, Some("empty_context"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_theorem_conclusion(&namespace, 1, &theorem, Some("nested_identity_beta"))
                .map_err(|_| GuestError::Aborted)?;
            Ok(namespace)
        }
    }

    #[allow(unsafe_code)]
    mod component_export {
        use super::{ConversionGuest, bindings};

        bindings::export!(ConversionGuest with_types_in bindings);
    }
}
