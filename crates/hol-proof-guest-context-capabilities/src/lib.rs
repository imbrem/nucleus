//! Untrusted component exercising bounded HOL context capabilities.

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

    struct ContextCapabilitiesGuest;

    impl Guest for ContextCapabilitiesGuest {
        fn build(
            plan: &ProofPlan,
        ) -> Result<bindings::covalence::hol_proof_guest::host::NamespaceNode, GuestError> {
            let bool_type = plan.bool_type().map_err(|_| GuestError::Aborted)?;
            let p = plan
                .free_term(0, &bool_type)
                .map_err(|_| GuestError::Aborted)?;
            let truth_term = plan.bool_term(true).map_err(|_| GuestError::Aborted)?;
            let empty = plan.empty_context().map_err(|_| GuestError::Aborted)?;
            let a = plan
                .extend_context(&empty, &p)
                .map_err(|_| GuestError::Aborted)?;
            let b = plan
                .extend_context(&empty, &truth_term)
                .map_err(|_| GuestError::Aborted)?;
            let c = plan
                .extend_context(&a, &truth_term)
                .map_err(|_| GuestError::Aborted)?;

            let p_at_a = plan
                .prove_hypothesis(&a, &p)
                .map_err(|_| GuestError::Aborted)?;
            let truth_at_a = plan.prove_truth(&a).map_err(|_| GuestError::Aborted)?;
            let no_witnesses = plan
                .empty_theorem_witness_list()
                .map_err(|_| GuestError::Aborted)?;
            let p_witness = plan
                .extend_theorem_witness_list(&no_witnesses, &p_at_a)
                .map_err(|_| GuestError::Aborted)?;
            let a_to_c_witnesses = plan
                .extend_theorem_witness_list(&p_witness, &truth_at_a)
                .map_err(|_| GuestError::Aborted)?;
            let a_to_c = plan
                .prove_context_implication(&a, &c, &a_to_c_witnesses)
                .map_err(|_| GuestError::Aborted)?;
            plan.persist_context_implication(&a_to_c)
                .map_err(|_| GuestError::Aborted)?;

            let p_at_c = plan
                .prove_hypothesis(&c, &p)
                .map_err(|_| GuestError::Aborted)?;
            let no_witnesses = plan
                .empty_theorem_witness_list()
                .map_err(|_| GuestError::Aborted)?;
            let c_to_a_witnesses = plan
                .extend_theorem_witness_list(&no_witnesses, &p_at_c)
                .map_err(|_| GuestError::Aborted)?;
            let c_to_a = plan
                .prove_context_implication(&c, &a, &c_to_a_witnesses)
                .map_err(|_| GuestError::Aborted)?;
            plan.persist_context_implication(&c_to_a)
                .map_err(|_| GuestError::Aborted)?;
            let _equivalence = plan
                .prove_context_equivalence(&a_to_c, &c_to_a)
                .map_err(|_| GuestError::Aborted)?;
            let _union = plan
                .prove_context_union(&a, &b, &c)
                .map_err(|_| GuestError::Aborted)?;

            let no_witnesses = plan
                .empty_theorem_witness_list()
                .map_err(|_| GuestError::Aborted)?;
            let a_to_b_witnesses = plan
                .extend_theorem_witness_list(&no_witnesses, &truth_at_a)
                .map_err(|_| GuestError::Aborted)?;
            let a_to_b = plan
                .prove_context_implication(&a, &b, &a_to_b_witnesses)
                .map_err(|_| GuestError::Aborted)?;
            plan.persist_context_implication(&a_to_b)
                .map_err(|_| GuestError::Aborted)?;

            let c_path = plan
                .singleton_context_path(&c)
                .map_err(|_| GuestError::Aborted)?;
            let c_a_path = plan
                .extend_context_path(&c_path, &a)
                .map_err(|_| GuestError::Aborted)?;
            let c_a_b_path = plan
                .extend_context_path(&c_a_path, &b)
                .map_err(|_| GuestError::Aborted)?;
            let c_to_b = plan
                .prove_context_implication_path(&c_a_b_path)
                .map_err(|_| GuestError::Aborted)?;
            plan.persist_context_implication(&c_to_b)
                .map_err(|_| GuestError::Aborted)?;

            let truth_at_b = plan.prove_truth(&b).map_err(|_| GuestError::Aborted)?;
            let truth_at_c = plan
                .prove_weakening(&c_to_b, &truth_at_b)
                .map_err(|_| GuestError::Aborted)?;
            plan.persist_theorem(&truth_at_c)
                .map_err(|_| GuestError::Aborted)?;
            let namespace = plan
                .root_child_namespace(Some("context-capabilities-demo"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_context(&namespace, 0, &c, Some("combined_context"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_theorem_conclusion(&namespace, 1, &truth_at_c, Some("weakened_truth"))
                .map_err(|_| GuestError::Aborted)?;
            Ok(namespace)
        }
    }

    #[allow(unsafe_code)]
    mod component_export {
        use super::{ContextCapabilitiesGuest, bindings};

        bindings::export!(ContextCapabilitiesGuest with_types_in bindings);
    }
}
