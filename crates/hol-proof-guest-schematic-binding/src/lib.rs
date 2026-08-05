//! Untrusted component which requests the schematic-binding demo proof.
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

    struct SchematicBindingGuest;

    impl Guest for SchematicBindingGuest {
        fn build(
            plan: &ProofPlan,
        ) -> Result<bindings::covalence::hol_proof_guest::host::NamespaceNode, GuestError> {
            let alpha = plan.free_type(0).map_err(|_| GuestError::Aborted)?;
            let bound = plan
                .bound_term(0, &alpha)
                .map_err(|_| GuestError::Aborted)?;
            let identity = plan
                .lambda(&alpha, &bound)
                .map_err(|_| GuestError::Aborted)?;
            let x = plan.free_term(0, &alpha).map_err(|_| GuestError::Aborted)?;
            let y = plan.free_term(1, &alpha).map_err(|_| GuestError::Aborted)?;
            let context = plan.empty_context().map_err(|_| GuestError::Aborted)?;
            let schematic = plan
                .prove_beta(&context, &identity, &x)
                .map_err(|_| GuestError::Aborted)?;

            let empty_terms = plan
                .empty_term_instantiation_map()
                .map_err(|_| GuestError::Aborted)?;
            let term_map = plan
                .extend_term_instantiation_map(&empty_terms, &x, &y)
                .map_err(|_| GuestError::Aborted)?;
            let instantiated_term = plan
                .prove_term_instantiation(&schematic, &term_map)
                .map_err(|_| GuestError::Aborted)?;
            let abstracted = plan
                .prove_abstraction(&instantiated_term, &y)
                .map_err(|_| GuestError::Aborted)?;

            let bool_type = plan.bool_type().map_err(|_| GuestError::Aborted)?;
            let empty_types = plan
                .empty_type_instantiation_map()
                .map_err(|_| GuestError::Aborted)?;
            let type_map = plan
                .extend_type_instantiation_map(&empty_types, &alpha, &bool_type)
                .map_err(|_| GuestError::Aborted)?;
            let theorem = plan
                .prove_type_instantiation(&abstracted, &type_map)
                .map_err(|_| GuestError::Aborted)?;

            plan.persist_theorem(&theorem)
                .map_err(|_| GuestError::Aborted)?;
            let namespace = plan
                .root_child_namespace(Some("schematic-binding-demo"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_context(&namespace, 0, &context, Some("empty_context"))
                .map_err(|_| GuestError::Aborted)?;
            plan.export_theorem_conclusion(
                &namespace,
                1,
                &theorem,
                Some("schematic_identity_binding"),
            )
            .map_err(|_| GuestError::Aborted)?;
            Ok(namespace)
        }
    }

    #[allow(unsafe_code)]
    mod component_export {
        use super::{SchematicBindingGuest, bindings};

        bindings::export!(SchematicBindingGuest with_types_in bindings);
    }
}
