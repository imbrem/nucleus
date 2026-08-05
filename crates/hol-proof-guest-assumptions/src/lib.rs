//! Untrusted component requesting `{p} |- true` through assumptions and equality composition.

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

    struct AssumptionsGuest;

    impl Guest for AssumptionsGuest {
        fn build(
            plan: &ProofPlan,
        ) -> Result<bindings::covalence::hol_proof_guest::host::NamespaceNode, GuestError> {
            let bool_type = plan.bool_type().map_err(|_| GuestError::Aborted)?;
            let p = plan
                .free_term(0, &bool_type)
                .map_err(|_| GuestError::Aborted)?;
            let empty = plan.empty_context().map_err(|_| GuestError::Aborted)?;
            let p_context = plan
                .extend_context(&empty, &p)
                .map_err(|_| GuestError::Aborted)?;
            let p_hypothesis = plan
                .prove_hypothesis(&p_context, &p)
                .map_err(|_| GuestError::Aborted)?;
            let truth = plan.prove_truth(&empty).map_err(|_| GuestError::Aborted)?;
            let p_equals_truth = plan
                .prove_deduction_antisymmetry(&p_hypothesis, &truth)
                .map_err(|_| GuestError::Aborted)?;
            let truth_from_p = plan
                .prove_equality_modus_ponens(&p_equals_truth, &p_hypothesis)
                .map_err(|_| GuestError::Aborted)?;

            plan.persist_theorem(&truth_from_p)
                .map_err(|_| GuestError::Aborted)?;
            let namespace = plan
                .root_child_namespace(Some("assumptions-demo"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_context(&namespace, 0, &p_context, Some("p_context"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_theorem_conclusion(&namespace, 1, &truth_from_p, Some("truth_from_p"))
                .map_err(|_| GuestError::Aborted)?;
            Ok(namespace)
        }
    }

    #[allow(unsafe_code)]
    mod component_export {
        use super::{AssumptionsGuest, bindings};

        bindings::export!(AssumptionsGuest with_types_in bindings);
    }
}
