//! Small positive HOL derived rules assembled above the LCF kernel.
//!
//! Preparation interns only checked syntax needed by an implementation. Applying
//! a plan consumes branded premises from one [`ProofSession`] and returns a
//! theorem carrying that same generative brand. No derived result is persisted.

use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextId, Hol, Policy, ProofError, ProofSession, TermError, TermId, Theorem,
};

/// A rejected derived-rule syntax plan.
#[derive(Debug)]
pub enum DerivedRulePreparationError {
    /// One advertised closed input has an external de Bruijn boundary.
    OpenInput(TermId),
    /// A checked term constructor rejected the plan.
    Term(TermError),
}

impl fmt::Display for DerivedRulePreparationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpenInput(term) => write!(
                formatter,
                "derived rule input term {} is not locally closed",
                term.get()
            ),
            Self::Term(error) => error.fmt(formatter),
        }
    }
}

impl StdError for DerivedRulePreparationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Term(error) => Some(error),
            Self::OpenInput(_) => None,
        }
    }
}

impl From<TermError> for DerivedRulePreparationError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

/// A rejected derived-rule application.
#[derive(Debug)]
pub enum DerivedRuleError {
    /// A premise is not the exact theorem shape used to prepare this rule.
    PremiseConclusion {
        /// Expected conclusion.
        expected: TermId,
        /// Actual conclusion.
        actual: TermId,
    },
    /// The composed rules returned a conclusion outside the advertised specification.
    UnexpectedConclusion {
        /// Advertised conclusion.
        expected: TermId,
        /// Actual conclusion.
        actual: TermId,
    },
    /// The composed rules returned a context outside the advertised specification.
    UnexpectedContext {
        /// Advertised context.
        expected: ContextId,
        /// Actual context.
        actual: ContextId,
    },
    /// An existing branded kernel operation rejected the derivation.
    Proof(ProofError),
}

impl fmt::Display for DerivedRuleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PremiseConclusion { expected, actual } => write!(
                formatter,
                "derived rule expected premise conclusion {}, got {}",
                expected.get(),
                actual.get()
            ),
            Self::UnexpectedConclusion { expected, actual } => write!(
                formatter,
                "derived rule advertised conclusion {}, got {}",
                expected.get(),
                actual.get()
            ),
            Self::UnexpectedContext { expected, actual } => write!(
                formatter,
                "derived rule advertised context {}, got {}",
                expected.get(),
                actual.get()
            ),
            Self::Proof(error) => error.fmt(formatter),
        }
    }
}

impl StdError for DerivedRuleError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Proof(error) => Some(error),
            Self::PremiseConclusion { .. }
            | Self::UnexpectedConclusion { .. }
            | Self::UnexpectedContext { .. } => None,
        }
    }
}

impl From<ProofError> for DerivedRuleError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

fn require_conclusion(theorem: &Theorem<'_>, expected: TermId) -> Result<(), DerivedRuleError> {
    if theorem.conclusion() != expected {
        return Err(DerivedRuleError::PremiseConclusion {
            expected,
            actual: theorem.conclusion(),
        });
    }
    Ok(())
}

fn require_closed<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    term: TermId,
) -> Result<(), DerivedRulePreparationError> {
    if !connection.term_is_locally_closed(term)? {
        return Err(DerivedRulePreparationError::OpenInput(term));
    }
    Ok(())
}

fn require_result(
    theorem: &Theorem<'_>,
    context: ContextId,
    conclusion: TermId,
) -> Result<(), DerivedRuleError> {
    if theorem.context() != context {
        return Err(DerivedRuleError::UnexpectedContext {
            expected: context,
            actual: theorem.context(),
        });
    }
    if theorem.conclusion() != conclusion {
        return Err(DerivedRuleError::UnexpectedConclusion {
            expected: conclusion,
            actual: theorem.conclusion(),
        });
    }
    Ok(())
}

fn equality_predicate<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    parameter_type: covalence_nucleus::TypeId,
    fixed: TermId,
    fixed_on_left: bool,
) -> Result<TermId, TermError> {
    let variable = connection.insert_bound_term(0, parameter_type)?;
    let body = if fixed_on_left {
        connection.insert_equality(fixed, variable)?
    } else {
        connection.insert_equality(variable, fixed)?
    };
    connection.insert_lambda(parameter_type, body)
}

/// Prepared `EQ_SYM`: from `Γ ⊢ l = r`, derive `Γ ⊢ r = l`.
pub struct EqSym {
    premise: TermId,
    left: TermId,
    right: TermId,
    predicate: TermId,
    result: TermId,
}

impl EqSym {
    /// Prepares the exact checked syntax for endpoints `left` and `right`.
    ///
    /// # Errors
    ///
    /// Returns if the endpoints are invalid, open, or differently typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let premise = connection.insert_equality(left, right)?;
        let result = connection.insert_equality(right, left)?;
        let ty = connection.term_type(left)?;
        let predicate = equality_predicate(connection, ty, left, false)?;
        Ok(Self {
            premise,
            left,
            right,
            predicate,
            result,
        })
    }

    /// Applies `EQ_SYM` to its exact branded premise.
    ///
    /// # Errors
    ///
    /// Returns if the premise shape differs or an underlying HOL rule rejects.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality, self.premise)?;
        let reflexive = proof.prove_reflexivity(equality.context(), self.left)?;
        let beta = proof.conversion_beta(self.predicate, self.left)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let predicate_left = proof.convert_theorem(&reflexive, &reverse)?;
        let predicate_right =
            proof.equality_substitution(equality, self.predicate, &predicate_left)?;
        let beta = proof.conversion_beta(self.predicate, self.right)?;
        let result = proof.convert_theorem(&predicate_right, &beta)?;
        require_result(&result, equality.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `EQ_TRANS`: from `Γ ⊢ l = m` and `Γ ⊢ m = r`, derive `Γ ⊢ l = r`.
pub struct EqTrans {
    first: TermId,
    second: TermId,
    middle: TermId,
    right: TermId,
    predicate: TermId,
    result: TermId,
}

impl EqTrans {
    /// Prepares `EQ_TRANS` for the exact three endpoints.
    ///
    /// # Errors
    ///
    /// Returns if any endpoint is invalid, open, or differently typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        middle: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, middle)?;
        require_closed(connection, right)?;
        let first = connection.insert_equality(left, middle)?;
        let second = connection.insert_equality(middle, right)?;
        let result = connection.insert_equality(left, right)?;
        let ty = connection.term_type(left)?;
        let predicate = equality_predicate(connection, ty, left, true)?;
        Ok(Self {
            first,
            second,
            middle,
            right,
            predicate,
            result,
        })
    }

    /// Applies `EQ_TRANS` to two exact branded premises.
    ///
    /// # Errors
    ///
    /// Returns for wrong premise shapes, differing contexts, or a rejected HOL rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        first: &Theorem<'brand>,
        second: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(first, self.first)?;
        require_conclusion(second, self.second)?;
        let beta = proof.conversion_beta(self.predicate, self.middle)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let predicate_middle = proof.convert_theorem(first, &reverse)?;
        let predicate_right =
            proof.equality_substitution(second, self.predicate, &predicate_middle)?;
        let beta = proof.conversion_beta(self.predicate, self.right)?;
        let result = proof.convert_theorem(&predicate_right, &beta)?;
        require_result(&result, first.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `AP_TERM`: from `Γ ⊢ l = r`, derive `Γ ⊢ f l = f r`.
pub struct ApTerm {
    premise: TermId,
    left: TermId,
    right: TermId,
    applied_left: TermId,
    predicate: TermId,
    result: TermId,
}

impl ApTerm {
    /// Prepares `AP_TERM` for an exact function and equality endpoints.
    ///
    /// # Errors
    ///
    /// Returns if application or equality is not well typed and closed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        function: TermId,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, function)?;
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let premise = connection.insert_equality(left, right)?;
        let applied_left = connection.insert_application(function, left)?;
        let ty = connection.term_type(left)?;
        let variable = connection.insert_bound_term(0, ty)?;
        let applied_variable = connection.insert_application(function, variable)?;
        let applied_right = connection.insert_application(function, right)?;
        let result = connection.insert_equality(applied_left, applied_right)?;
        let body = connection.insert_equality(applied_left, applied_variable)?;
        let predicate = connection.insert_lambda(ty, body)?;
        Ok(Self {
            premise,
            left,
            right,
            applied_left,
            predicate,
            result,
        })
    }

    /// Applies `AP_TERM` to its exact branded equality premise.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise shape or rejected underlying HOL rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality, self.premise)?;
        let reflexive = proof.prove_reflexivity(equality.context(), self.applied_left)?;
        let beta = proof.conversion_beta(self.predicate, self.left)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let predicate_left = proof.convert_theorem(&reflexive, &reverse)?;
        let predicate_right =
            proof.equality_substitution(equality, self.predicate, &predicate_left)?;
        let beta = proof.conversion_beta(self.predicate, self.right)?;
        let result = proof.convert_theorem(&predicate_right, &beta)?;
        require_result(&result, equality.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `AP_THM`: from `Γ ⊢ f = g`, derive `Γ ⊢ f x = g x`.
pub struct ApThm {
    premise: TermId,
    left: TermId,
    right: TermId,
    applied_left: TermId,
    predicate: TermId,
    result: TermId,
}

impl ApThm {
    /// Prepares `AP_THM` for exact function endpoints and one argument.
    ///
    /// # Errors
    ///
    /// Returns if equality or either application is not well typed and closed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
        argument: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        require_closed(connection, argument)?;
        let premise = connection.insert_equality(left, right)?;
        let applied_left = connection.insert_application(left, argument)?;
        let function_type = connection.term_type(left)?;
        let variable = connection.insert_bound_term(0, function_type)?;
        let applied_variable = connection.insert_application(variable, argument)?;
        let applied_right = connection.insert_application(right, argument)?;
        let result = connection.insert_equality(applied_left, applied_right)?;
        let body = connection.insert_equality(applied_left, applied_variable)?;
        let predicate = connection.insert_lambda(function_type, body)?;
        Ok(Self {
            premise,
            left,
            right,
            applied_left,
            predicate,
            result,
        })
    }

    /// Applies `AP_THM` to its exact branded function equality.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise shape or rejected underlying HOL rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality, self.premise)?;
        let reflexive = proof.prove_reflexivity(equality.context(), self.applied_left)?;
        let beta = proof.conversion_beta(self.predicate, self.left)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let predicate_left = proof.convert_theorem(&reflexive, &reverse)?;
        let predicate_right =
            proof.equality_substitution(equality, self.predicate, &predicate_left)?;
        let beta = proof.conversion_beta(self.predicate, self.right)?;
        let result = proof.convert_theorem(&predicate_right, &beta)?;
        require_result(&result, equality.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `EQT_INTRO`: from `Γ ⊢ p`, derive `Γ ⊢ p = true`.
pub struct EqtIntro {
    proposition: TermId,
    truth: TermId,
    result: TermId,
}

impl EqtIntro {
    /// Prepares the exact closed Boolean proposition and equality to truth.
    ///
    /// # Errors
    ///
    /// Returns if the proposition is invalid, open, or non-Boolean.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        let truth = connection.insert_bool_term(true)?;
        let result = connection.insert_equality(proposition, truth)?;
        Ok(Self {
            proposition,
            truth,
            result,
        })
    }

    /// Applies `EQT_INTRO` to its exact branded proposition theorem.
    ///
    /// # Errors
    ///
    /// Returns for a wrong context/conclusion or rejected underlying HOL rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        theorem: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(theorem, self.proposition)?;
        let result = if self.proposition == self.truth {
            proof.prove_reflexivity(theorem.context(), self.proposition)?
        } else {
            let truth = proof.prove_truth(theorem.context())?;
            proof.deduction_antisymmetry(theorem, &truth)?
        };
        require_result(&result, theorem.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `EQT_ELIM`: from `Γ ⊢ p = true`, derive `Γ ⊢ p`.
pub struct EqtElim {
    premise: TermId,
    symmetry: EqSym,
    proposition: TermId,
}

impl EqtElim {
    /// Prepares `EQT_ELIM` for one exact Boolean proposition.
    ///
    /// # Errors
    ///
    /// Returns if the proposition is invalid, open, or non-Boolean.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        let truth = connection.insert_bool_term(true)?;
        let premise = connection.insert_equality(proposition, truth)?;
        let symmetry = EqSym::prepare(connection, proposition, truth)?;
        Ok(Self {
            premise,
            symmetry,
            proposition,
        })
    }

    /// Applies `EQT_ELIM` to its exact branded equality-to-truth premise.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise shape or rejected underlying HOL rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality_to_truth: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality_to_truth, self.premise)?;
        let truth_to_proposition = self.symmetry.apply(proof, equality_to_truth)?;
        let truth = proof.prove_truth(equality_to_truth.context())?;
        let result = proof.equality_modus_ponens(&truth_to_proposition, &truth)?;
        require_result(&result, equality_to_truth.context(), self.proposition)?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_nucleus::{AllowAll, Kernel, Operation, TermView};

    struct DenyOperation(Operation);

    impl Policy for DenyOperation {
        fn allows(&mut self, operation: Operation) -> bool {
            operation != self.0
        }
    }

    #[test]
    fn positive_rules_preserve_exact_contexts_and_term_shapes() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let truth_equality = connection.insert_equality(truth, truth).unwrap();
        let gamma = connection.define_context([truth, truth_equality]).unwrap();

        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let identity_application = connection.insert_application(identity, variable).unwrap();
        let expanded_identity = connection
            .insert_lambda(bool_type, identity_application)
            .unwrap();
        let p = connection.insert_application(identity, truth).unwrap();
        let q = connection
            .insert_application(expanded_identity, truth)
            .unwrap();

        let eq_sym = EqSym::prepare(&mut connection, p, q).unwrap();
        let eq_trans = EqTrans::prepare(&mut connection, p, q, truth).unwrap();
        let ap_term = ApTerm::prepare(&mut connection, identity, p, q).unwrap();
        let ap_thm = ApThm::prepare(&mut connection, expanded_identity, identity, truth).unwrap();
        let eqt_intro = EqtIntro::prepare(&mut connection, p).unwrap();
        let truth_intro = EqtIntro::prepare(&mut connection, truth).unwrap();
        let eqt_elim = EqtElim::prepare(&mut connection, p).unwrap();

        let q_equals_p = connection.insert_equality(q, p).unwrap();
        let p_equals_truth = connection.insert_equality(p, truth).unwrap();
        let identity_p = connection.insert_application(identity, p).unwrap();
        let identity_q = connection.insert_application(identity, q).unwrap();
        let applications_equal = connection.insert_equality(identity_p, identity_q).unwrap();
        let q_equals_p_again = connection.insert_equality(q, p).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let p_to_truth = proof.conversion_beta(identity, truth)?;
                let q_to_p = proof.conversion_beta(expanded_identity, truth)?;
                let q_to_truth = proof.conversion_transitivity(&q_to_p, &p_to_truth)?;
                let truth_to_q = proof.conversion_symmetry(&q_to_truth)?;
                let p_to_q = proof.conversion_transitivity(&p_to_truth, &truth_to_q)?;
                let p_equals_q = proof.prove_conversion_equality(gamma, &p_to_q)?;
                let q_equals_truth = proof.prove_conversion_equality(gamma, &q_to_truth)?;

                let symmetric = eq_sym.apply(&mut proof, &p_equals_q).unwrap();
                assert_eq!(symmetric.context(), gamma);
                assert_eq!(symmetric.conclusion(), q_equals_p);

                let transitive = eq_trans
                    .apply(&mut proof, &p_equals_q, &q_equals_truth)
                    .unwrap();
                assert_eq!(transitive.context(), gamma);
                assert_eq!(transitive.conclusion(), p_equals_truth);

                let applied_term = ap_term.apply(&mut proof, &p_equals_q).unwrap();
                assert_eq!(applied_term.context(), gamma);
                assert_eq!(applied_term.conclusion(), applications_equal);

                let eta = proof.conversion_eta(identity)?;
                assert_eq!(eta.left(), expanded_identity);
                let functions_equal = proof.prove_conversion_equality(gamma, &eta)?;
                let applied_theorem = ap_thm.apply(&mut proof, &functions_equal).unwrap();
                assert_eq!(applied_theorem.context(), gamma);
                assert_eq!(applied_theorem.conclusion(), q_equals_p_again);

                let truth_theorem = proof.prove_truth(gamma)?;
                let truth_to_p = proof.conversion_symmetry(&p_to_truth)?;
                let p_theorem = proof.convert_theorem(&truth_theorem, &truth_to_p)?;
                let p_equals_true = eqt_intro.apply(&mut proof, &p_theorem).unwrap();
                assert_eq!(p_equals_true.context(), gamma);
                assert_eq!(p_equals_true.conclusion(), p_equals_truth);
                let recovered_p = eqt_elim.apply(&mut proof, &p_equals_true).unwrap();
                assert_eq!(recovered_p.context(), gamma);
                assert_eq!(recovered_p.conclusion(), p);
                let truth_equals_true = truth_intro.apply(&mut proof, &truth_theorem).unwrap();
                assert_eq!(truth_equals_true.context(), gamma);
                assert_eq!(truth_equals_true.conclusion(), truth_equality);
                assert!(proof.load_theorem(gamma, p)?.is_none());
                proof.persist_theorem(&recovered_p)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();

        assert_eq!(
            connection.context_members(gamma).unwrap(),
            [truth, truth_equality]
        );
        assert!(matches!(
            connection.term(p_equals_truth).unwrap(),
            TermView::Equality { left, right } if left == p && right == truth
        ));
        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 1);
        assert!(connection.proved_judgement(gamma, p).unwrap());
    }

    #[test]
    fn plans_reject_wrong_shapes_contexts_and_mistyped_applications() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let truth_equality = connection.insert_equality(truth, truth).unwrap();
        let gamma = connection.define_context([truth]).unwrap();
        let delta = connection.define_context([truth_equality]).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let p = connection.insert_application(identity, truth).unwrap();

        let symmetry = EqSym::prepare(&mut connection, p, truth).unwrap();
        let transitivity = EqTrans::prepare(&mut connection, p, truth, p).unwrap();
        let eqt_elim = EqtElim::prepare(&mut connection, p).unwrap();
        let open_bool = connection.insert_bound_term(0, bool_type).unwrap();
        assert!(ApTerm::prepare(&mut connection, truth, p, truth).is_err());
        assert!(ApThm::prepare(&mut connection, identity, identity, identity).is_err());
        assert!(matches!(
            ApTerm::prepare(&mut connection, identity, open_bool, open_bool),
            Err(DerivedRulePreparationError::OpenInput(term)) if term == open_bool
        ));
        assert!(matches!(
            ApThm::prepare(&mut connection, identity, identity, open_bool),
            Err(DerivedRulePreparationError::OpenInput(term)) if term == open_bool
        ));
        assert!(matches!(
            EqtIntro::prepare(&mut connection, open_bool),
            Err(DerivedRulePreparationError::OpenInput(term)) if term == open_bool
        ));

        connection
            .with_proof_session(|mut proof| {
                let p_to_truth = proof.conversion_beta(identity, truth)?;
                let truth_to_p = proof.conversion_symmetry(&p_to_truth)?;
                let expected_equality = proof.prove_conversion_equality(gamma, &p_to_truth)?;
                let wrong_equality = proof.prove_conversion_equality(gamma, &truth_to_p)?;
                assert!(matches!(
                    symmetry.apply(&mut proof, &wrong_equality),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));

                let second_wrong_context = proof.prove_conversion_equality(delta, &truth_to_p)?;
                assert!(matches!(
                    transitivity.apply(&mut proof, &expected_equality, &second_wrong_context),
                    Err(DerivedRuleError::Proof(
                        ProofError::EqualitySubstitutionContextMismatch { .. }
                    ))
                ));
                assert!(matches!(
                    transitivity.apply(&mut proof, &expected_equality, &expected_equality),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));

                let truth_delta = proof.prove_truth(delta)?;
                let p_delta = proof.convert_theorem(&truth_delta, &truth_to_p)?;
                assert!(matches!(
                    eqt_elim.apply(&mut proof, &wrong_equality),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));
                assert!(matches!(
                    eqt_elim.apply(&mut proof, &p_delta),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn eqt_intro_preserves_every_context_membership_case() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let proposition = connection.insert_application(identity, truth).unwrap();
        let expected = connection.insert_equality(proposition, truth).unwrap();
        let truth_equality = connection.insert_equality(truth, truth).unwrap();
        let contexts = [
            connection.define_context([]).unwrap(),
            connection.define_context([proposition]).unwrap(),
            connection.define_context([truth]).unwrap(),
            connection.define_context([proposition, truth]).unwrap(),
        ];
        let proposition_intro = EqtIntro::prepare(&mut connection, proposition).unwrap();
        let truth_intro = EqtIntro::prepare(&mut connection, truth).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(identity, truth)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                for context in contexts {
                    let truth_theorem = proof.prove_truth(context)?;
                    let proposition_theorem = proof.convert_theorem(&truth_theorem, &reverse)?;
                    let introduced = proposition_intro
                        .apply(&mut proof, &proposition_theorem)
                        .unwrap();
                    assert_eq!(introduced.context(), context);
                    assert_eq!(introduced.conclusion(), expected);
                    let reflexive = truth_intro.apply(&mut proof, &truth_theorem).unwrap();
                    assert_eq!(reflexive.context(), context);
                    assert_eq!(reflexive.conclusion(), truth_equality);
                }
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    fn denied_eq_sym(operation: Operation) -> DerivedRuleError {
        let mut connection = Connection::open_hol_in_memory(DenyOperation(operation)).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let plan = EqSym::prepare(&mut connection, truth, truth).unwrap();
        connection.with_proof_session(|mut proof| {
            let premise = proof.prove_reflexivity(ContextId::empty(), truth).unwrap();
            match plan.apply(&mut proof, &premise) {
                Err(error) => error,
                Ok(_) => panic!("denied EQ_SYM unexpectedly succeeded"),
            }
        })
    }

    fn denied_nontrivial_eqt_intro(operation: Operation) -> DerivedRuleError {
        let mut connection = Connection::open_hol_in_memory(DenyOperation(operation)).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let proposition = connection.insert_application(identity, truth).unwrap();
        let plan = EqtIntro::prepare(&mut connection, proposition).unwrap();
        connection.with_proof_session(|mut proof| {
            let truth_theorem = proof.prove_truth(ContextId::empty()).unwrap();
            let beta = proof.conversion_beta(identity, truth).unwrap();
            let reverse = proof.conversion_symmetry(&beta).unwrap();
            let premise = proof.convert_theorem(&truth_theorem, &reverse).unwrap();
            match plan.apply(&mut proof, &premise) {
                Err(error) => error,
                Ok(_) => panic!("denied EQT_INTRO unexpectedly succeeded"),
            }
        })
    }

    fn denied_reflexive_eqt_intro() -> DerivedRuleError {
        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveReflexivity)).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let plan = EqtIntro::prepare(&mut connection, truth).unwrap();
        connection.with_proof_session(|mut proof| {
            let premise = proof.prove_truth(ContextId::empty()).unwrap();
            match plan.apply(&mut proof, &premise) {
                Err(error) => error,
                Ok(_) => panic!("denied reflexive EQT_INTRO unexpectedly succeeded"),
            }
        })
    }

    #[test]
    fn constituent_policy_denials_are_observed() {
        for operation in [
            Operation::ProveEqualitySubstitution,
            Operation::ProveConversionBeta,
        ] {
            assert!(matches!(
                denied_eq_sym(operation),
                DerivedRuleError::Proof(ProofError::Denied(actual)) if actual == operation
            ));
        }
        assert!(matches!(
            denied_nontrivial_eqt_intro(Operation::ProveDeductionAntisymmetry),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveDeductionAntisymmetry))
        ));
        assert!(matches!(
            denied_reflexive_eqt_intro(),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveReflexivity))
        ));
    }
}
