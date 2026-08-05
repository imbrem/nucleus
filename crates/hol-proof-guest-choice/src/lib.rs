//! Untrusted component requesting `|- id (epsilon id)` through Hilbert choice.

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

    struct ChoiceGuest;

    impl Guest for ChoiceGuest {
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
            let truth_term = plan.bool_term(true).map_err(|_| GuestError::Aborted)?;
            let empty = plan.empty_context().map_err(|_| GuestError::Aborted)?;
            let truth = plan.prove_truth(&empty).map_err(|_| GuestError::Aborted)?;
            let beta = plan
                .conversion_beta(&identity, &truth_term)
                .map_err(|_| GuestError::Aborted)?;
            let inverse_beta = plan
                .conversion_symmetry(&beta)
                .map_err(|_| GuestError::Aborted)?;
            let identity_truth = plan
                .convert_theorem(&truth, &inverse_beta)
                .map_err(|_| GuestError::Aborted)?;
            let choice = plan
                .prove_choice(&identity_truth)
                .map_err(|_| GuestError::Aborted)?;

            plan.persist_theorem(&choice)
                .map_err(|_| GuestError::Aborted)?;
            let namespace = plan
                .root_child_namespace(Some("choice-demo"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_context(&namespace, 0, &empty, Some("empty_context"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_theorem_conclusion(&namespace, 1, &choice, Some("identity_epsilon"))
                .map_err(|_| GuestError::Aborted)?;
            Ok(namespace)
        }
    }

    #[allow(unsafe_code)]
    mod component_export {
        use super::{ChoiceGuest, bindings};

        bindings::export!(ChoiceGuest with_types_in bindings);
    }
}
