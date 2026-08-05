//! Untrusted HOL proof recipes shared by terminal and browser consumers.
//!
//! These functions can only compose branded capabilities returned by
//! Nucleus. Bugs here can fail to find a proof or choose an unintended valid
//! theorem, but cannot forge a theorem or access the enclosed `SQLite` state.

use covalence_nucleus::{
    ContextId, ContextImplication, Conversion, Policy, ProofError, ProofSession, TermId, Theorem,
};

/// An ordinary upper-layer view of two opposite implication witnesses.
///
/// This is not a new kernel capability and has no authoritative table.
pub struct ContextEquivalence<'witness, 'brand> {
    forward: &'witness ContextImplication<'brand>,
    backward: &'witness ContextImplication<'brand>,
}

impl<'brand> ContextEquivalence<'_, 'brand> {
    /// Returns the left-to-right witness.
    #[must_use]
    pub const fn forward(&self) -> &ContextImplication<'brand> {
        self.forward
    }

    /// Returns the right-to-left witness.
    #[must_use]
    pub const fn backward(&self) -> &ContextImplication<'brand> {
        self.backward
    }

    /// Returns the left endpoint.
    #[must_use]
    pub const fn left(&self) -> ContextId {
        self.forward.antecedent()
    }

    /// Returns the right endpoint.
    #[must_use]
    pub const fn right(&self) -> ContextId {
        self.forward.consequent()
    }
}

/// Two implication witnesses are not exact opposites.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContextEquivalenceMismatch {
    /// Forward antecedent.
    pub forward_antecedent: ContextId,
    /// Forward consequent.
    pub forward_consequent: ContextId,
    /// Backward antecedent.
    pub backward_antecedent: ContextId,
    /// Backward consequent.
    pub backward_consequent: ContextId,
}

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

/// Derives closed eta equality by composing checked eta conversion with
/// conversion-to-equality.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn eta<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    context: ContextId,
    function: TermId,
) -> Result<Theorem<'brand>, ProofError> {
    let conversion = proof.conversion_eta(function)?;
    proof.prove_conversion_equality(context, &conversion)
}

/// Transports a Boolean theorem along a checked conversion.
///
/// This is exactly conversion-to-equality followed by equality modus ponens;
/// it introduces no additional trusted rule.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn convert_theorem<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    theorem: &Theorem<'brand>,
    conversion: &Conversion<'brand>,
) -> Result<Theorem<'brand>, ProofError> {
    let equality = proof.prove_conversion_equality(theorem.context(), conversion)?;
    proof.equality_modus_ponens(&equality, theorem)
}

/// Checks that two implication witnesses have exactly opposite endpoints.
///
/// # Errors
///
/// Returns the four observed endpoints when the witnesses are not opposites.
pub fn context_equivalence<'witness, 'brand>(
    forward: &'witness ContextImplication<'brand>,
    backward: &'witness ContextImplication<'brand>,
) -> Result<ContextEquivalence<'witness, 'brand>, ContextEquivalenceMismatch> {
    if forward.antecedent() != backward.consequent()
        || forward.consequent() != backward.antecedent()
    {
        return Err(ContextEquivalenceMismatch {
            forward_antecedent: forward.antecedent(),
            forward_consequent: forward.consequent(),
            backward_antecedent: backward.antecedent(),
            backward_consequent: backward.consequent(),
        });
    }
    Ok(ContextEquivalence { forward, backward })
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

    #[test]
    fn eta_recipe_produces_a_persistable_kernel_theorem() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let theorem = eta(&mut proof, ContextId::empty(), identity)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .unwrap();

        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("eta recipe did not produce equality")
        };
        let TermView::Lambda {
            parameter_type,
            body,
        } = connection.term(left).unwrap()
        else {
            panic!("eta left endpoint is not a lambda")
        };
        assert_eq!(parameter_type, bool_type);
        assert!(matches!(
            connection.term(body).unwrap(),
            TermView::Application { function, .. } if function == identity
        ));
        assert_eq!(right, identity);
        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
    }

    #[test]
    fn theorem_conversion_and_context_equivalence_are_ordinary_compositions() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let p = connection.insert_free_term(7, bool_type).unwrap();
        let equality = connection.insert_equality(p, p).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let application = connection.insert_application(identity, truth).unwrap();
        let application_context = connection.define_context([application]).unwrap();
        let left = connection.define_context([equality]).unwrap();
        let right = connection.define_context([truth]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let truth_witness = proof.prove_truth(left)?;
                let forward = proof.prove_context_implication(left, right, &[truth_witness])?;
                let equality_witness = reflexivity(&mut proof, right, p)?;
                let backward = proof.prove_context_implication(right, left, &[equality_witness])?;

                assert!(context_equivalence(&forward, &forward).is_err());
                let equivalence = context_equivalence(&forward, &backward).unwrap();
                assert_eq!(equivalence.left(), left);
                assert_eq!(equivalence.right(), right);
                assert_eq!(equivalence.forward().antecedent(), left);
                assert_eq!(equivalence.backward().antecedent(), right);

                let premise = proof.prove_hypothesis(application_context, application)?;
                let conversion = proof.conversion_beta(identity, truth)?;
                let converted = convert_theorem(&mut proof, &premise, &conversion)?;
                assert_eq!(converted.conclusion(), truth);
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }
}
