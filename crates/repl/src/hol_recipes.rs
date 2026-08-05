//! Untrusted HOL proof recipes shared by terminal and browser consumers.
//!
//! These functions can only compose branded capabilities returned by
//! Nucleus. Bugs here can fail to find a proof or choose an unintended valid
//! theorem, but cannot forge a theorem or access the enclosed `SQLite` state.

use covalence_nucleus::{ContextId, Policy, ProofError, ProofSession, TermId, Theorem};

/// Derives `context |- term = term` from conversion reflexivity.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn reflexivity<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    context: ContextId,
    term: TermId,
) -> Result<Theorem<'brand>, ProofError> {
    let conversion = proof.conversion_reflexivity(term)?;
    proof.prove_conversion_equality(context, &conversion)
}

/// Derives closed beta equality by composing checked beta conversion with
/// conversion-to-equality.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn beta<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    context: ContextId,
    abstraction: TermId,
    argument: TermId,
) -> Result<Theorem<'brand>, ProofError> {
    let conversion = proof.conversion_beta(abstraction, argument)?;
    proof.prove_conversion_equality(context, &conversion)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_nucleus::{AllowAll, Connection, TermView};

    #[test]
    fn beta_recipe_produces_a_persistable_kernel_theorem() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let theorem = beta(&mut proof, ContextId::empty(), identity, truth)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .unwrap();

        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("beta recipe did not produce equality")
        };
        assert!(matches!(
            connection.term(left).unwrap(),
            TermView::Application {
                function,
                argument
            } if function == identity && argument == truth
        ));
        assert_eq!(right, truth);
        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
    }
}
