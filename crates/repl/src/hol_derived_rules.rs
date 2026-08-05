//! Small positive HOL derived rules assembled above the LCF kernel.
//!
//! Preparation interns only checked syntax needed by an implementation. Applying
//! a plan consumes branded premises from one [`ProofSession`] and returns a
//! theorem carrying that same generative brand. No derived result is persisted.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextError, ContextId, Hol, Policy, ProofError, ProofSession, TermError, TermId,
    TermView, Theorem, TypeId,
};

/// A rejected derived-rule syntax plan.
#[derive(Debug)]
pub enum DerivedRulePreparationError {
    /// One advertised closed input has an external de Bruijn boundary.
    OpenInput(TermId),
    /// A generalization variable is not an exact free-variable node.
    ExpectedFreeVariable(TermId),
    /// A generalization variable occurs in a supposedly fixed predicate or function.
    VariableOccursInFixedTerm {
        /// Exact free variable.
        variable: TermId,
        /// Fixed term containing it.
        term: TermId,
    },
    /// A checked term constructor rejected the plan.
    Term(TermError),
    /// A checked context constructor rejected the plan.
    Context(ContextError),
}

impl fmt::Display for DerivedRulePreparationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OpenInput(term) => write!(
                formatter,
                "derived rule input term {} is not locally closed",
                term.get()
            ),
            Self::ExpectedFreeVariable(term) => {
                write!(
                    formatter,
                    "term {} is not an exact free variable",
                    term.get()
                )
            }
            Self::VariableOccursInFixedTerm { variable, term } => write!(
                formatter,
                "free variable {} occurs in fixed term {}",
                variable.get(),
                term.get()
            ),
            Self::Term(error) => error.fmt(formatter),
            Self::Context(error) => error.fmt(formatter),
        }
    }
}

impl StdError for DerivedRulePreparationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Term(error) => Some(error),
            Self::Context(error) => Some(error),
            Self::OpenInput(_)
            | Self::ExpectedFreeVariable(_)
            | Self::VariableOccursInFixedTerm { .. } => None,
        }
    }
}

impl From<TermError> for DerivedRulePreparationError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ContextError> for DerivedRulePreparationError {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
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

fn contains_exact<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    root: TermId,
    needle: TermId,
    visited: &mut HashSet<TermId>,
) -> Result<bool, TermError> {
    if root == needle {
        return Ok(true);
    }
    if !visited.insert(root) {
        return Ok(false);
    }
    match connection.term(root)? {
        TermView::Application { function, argument } => {
            Ok(contains_exact(connection, function, needle, visited)?
                || contains_exact(connection, argument, needle, visited)?)
        }
        TermView::Lambda { body, .. } | TermView::TypeLambda { body } => {
            contains_exact(connection, body, needle, visited)
        }
        TermView::TypeApplication { function, .. } => {
            contains_exact(connection, function, needle, visited)
        }
        TermView::Equality { left, right } => {
            Ok(contains_exact(connection, left, needle, visited)?
                || contains_exact(connection, right, needle, visited)?)
        }
        TermView::Epsilon { predicate } => contains_exact(connection, predicate, needle, visited),
        TermView::Bool(_)
        | TermView::Free { .. }
        | TermView::Bound { .. }
        | TermView::Constant { .. } => Ok(false),
    }
}

fn require_fresh_variable<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    variable: TermId,
    fixed_terms: &[TermId],
) -> Result<TypeId, DerivedRulePreparationError> {
    if !matches!(connection.term(variable)?, TermView::Free { .. }) {
        return Err(DerivedRulePreparationError::ExpectedFreeVariable(variable));
    }
    for term in fixed_terms {
        if contains_exact(connection, *term, variable, &mut HashSet::new())? {
            return Err(DerivedRulePreparationError::VariableOccursInFixedTerm {
                variable,
                term: *term,
            });
        }
    }
    Ok(connection.term_type(variable)?)
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

/// Prepared `FUN_EXT`: from `Γ ⊢ f x = g x`, derive `Γ ⊢ f = g`.
pub struct FunExt {
    premise: TermId,
    variable: TermId,
    abstracted_result: TermId,
    left: TermId,
    right: TermId,
    left_eta_symmetry: EqSym,
    first_transitivity: EqTrans,
    second_transitivity: EqTrans,
    result: TermId,
}

impl FunExt {
    /// Prepares function extensionality for exact closed functions and a fresh `MFV`.
    ///
    /// # Errors
    ///
    /// Returns if either function is open/non-functional, the variable is not an
    /// exact fresh free variable, or the pointwise equality is ill typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
        variable: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let variable_type = require_fresh_variable(connection, variable, &[left, right])?;
        let applied_left = connection.insert_application(left, variable)?;
        let applied_right = connection.insert_application(right, variable)?;
        let premise = connection.insert_equality(applied_left, applied_right)?;
        let bound = connection.insert_bound_term(0, variable_type)?;
        let bound_left = connection.insert_application(left, bound)?;
        let bound_right = connection.insert_application(right, bound)?;
        let lambda_left = connection.insert_lambda(variable_type, bound_left)?;
        let lambda_right = connection.insert_lambda(variable_type, bound_right)?;
        let abstracted_result = connection.insert_equality(lambda_left, lambda_right)?;
        let result = connection.insert_equality(left, right)?;
        let left_eta_symmetry = EqSym::prepare(connection, lambda_left, left)?;
        let first_transitivity = EqTrans::prepare(connection, left, lambda_left, lambda_right)?;
        let second_transitivity = EqTrans::prepare(connection, left, lambda_right, right)?;
        Ok(Self {
            premise,
            variable,
            abstracted_result,
            left,
            right,
            left_eta_symmetry,
            first_transitivity,
            second_transitivity,
            result,
        })
    }

    /// Applies `FUN_EXT`; primitive abstraction enforces freshness in `Γ`.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise, failed freshness check, or rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        pointwise: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(pointwise, self.premise)?;
        let abstracted = proof.abstraction(pointwise, self.variable)?;
        require_result(&abstracted, pointwise.context(), self.abstracted_result)?;
        let left_eta = proof.conversion_eta(self.left)?;
        let right_eta = proof.conversion_eta(self.right)?;
        let left_eta = proof.prove_conversion_equality(pointwise.context(), &left_eta)?;
        let right_eta = proof.prove_conversion_equality(pointwise.context(), &right_eta)?;
        let left_to_lambda = self.left_eta_symmetry.apply(proof, &left_eta)?;
        let left_to_right_lambda =
            self.first_transitivity
                .apply(proof, &left_to_lambda, &abstracted)?;
        let result = self
            .second_transitivity
            .apply(proof, &left_to_right_lambda, &right_eta)?;
        require_result(&result, pointwise.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared `ALL_ELIM`: from `Γ ⊢ P = (λ_. true)`, derive `Γ ⊢ P t`.
pub struct AllElim {
    premise: TermId,
    application: TermId,
    application_rule: ApThm,
    constant_truth: TermId,
    argument: TermId,
    beta_transitivity: EqTrans,
    truth_elimination: EqtElim,
}

impl AllElim {
    /// Prepares universal elimination for an exact predicate and closed argument.
    ///
    /// # Errors
    ///
    /// Returns if the predicate/argument is open or the application is ill typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        predicate: TermId,
        argument: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, predicate)?;
        require_closed(connection, argument)?;
        let argument_type = connection.term_type(argument)?;
        let truth = connection.insert_bool_term(true)?;
        let constant_truth = connection.insert_lambda(argument_type, truth)?;
        let premise = connection.insert_equality(predicate, constant_truth)?;
        let application = connection.insert_application(predicate, argument)?;
        let applied_truth = connection.insert_application(constant_truth, argument)?;
        let application_rule = ApThm::prepare(connection, predicate, constant_truth, argument)?;
        let beta_transitivity = EqTrans::prepare(connection, application, applied_truth, truth)?;
        let truth_elimination = EqtElim::prepare(connection, application)?;
        Ok(Self {
            premise,
            application,
            application_rule,
            constant_truth,
            argument,
            beta_transitivity,
            truth_elimination,
        })
    }

    /// Applies `ALL_ELIM` to its exact branded universal premise.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise or rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        universal: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(universal, self.premise)?;
        let application_equals_applied_truth = self.application_rule.apply(proof, universal)?;
        let beta = proof.conversion_beta(self.constant_truth, self.argument)?;
        let applied_truth_equals_truth =
            proof.prove_conversion_equality(universal.context(), &beta)?;
        let application_equals_truth = self.beta_transitivity.apply(
            proof,
            &application_equals_applied_truth,
            &applied_truth_equals_truth,
        )?;
        let result = self
            .truth_elimination
            .apply(proof, &application_equals_truth)?;
        require_result(&result, universal.context(), self.application)?;
        Ok(result)
    }
}

/// Prepared applied-form `ALL_INTRO`: from `Γ ⊢ P x`, derive `Γ ⊢ P = (λ_. true)`.
pub struct AllIntroApplied {
    premise: TermId,
    variable: TermId,
    abstracted_result: TermId,
    predicate: TermId,
    truth_introduction: EqtIntro,
    eta_symmetry: EqSym,
    transitivity: EqTrans,
    result: TermId,
}

impl AllIntroApplied {
    /// Prepares applied-form universal introduction for a closed predicate and fresh exact `MFV`.
    ///
    /// # Errors
    ///
    /// Returns if the predicate is open/non-functional, the variable is not
    /// exact and fresh, or the application is ill typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        predicate: TermId,
        variable: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, predicate)?;
        let variable_type = require_fresh_variable(connection, variable, &[predicate])?;
        let premise = connection.insert_application(predicate, variable)?;
        let truth = connection.insert_bool_term(true)?;
        let constant_truth = connection.insert_lambda(variable_type, truth)?;
        let bound = connection.insert_bound_term(0, variable_type)?;
        let bound_application = connection.insert_application(predicate, bound)?;
        let lambda_application = connection.insert_lambda(variable_type, bound_application)?;
        let abstracted_result = connection.insert_equality(lambda_application, constant_truth)?;
        let result = connection.insert_equality(predicate, constant_truth)?;
        let truth_introduction = EqtIntro::prepare(connection, premise)?;
        let eta_symmetry = EqSym::prepare(connection, lambda_application, predicate)?;
        let transitivity =
            EqTrans::prepare(connection, predicate, lambda_application, constant_truth)?;
        Ok(Self {
            premise,
            variable,
            abstracted_result,
            predicate,
            truth_introduction,
            eta_symmetry,
            transitivity,
            result,
        })
    }

    /// Applies the applied-form `ALL_INTRO`; abstraction enforces freshness in `Γ`.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise, failed freshness check, or rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        instance: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(instance, self.premise)?;
        let instance_equals_truth = self.truth_introduction.apply(proof, instance)?;
        let abstracted = proof.abstraction(&instance_equals_truth, self.variable)?;
        require_result(&abstracted, instance.context(), self.abstracted_result)?;
        let eta = proof.conversion_eta(self.predicate)?;
        let eta = proof.prove_conversion_equality(instance.context(), &eta)?;
        let predicate_to_lambda = self.eta_symmetry.apply(proof, &eta)?;
        let result = self
            .transitivity
            .apply(proof, &predicate_to_lambda, &abstracted)?;
        require_result(&result, instance.context(), self.result)?;
        Ok(result)
    }
}

fn apply2<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    function: TermId,
    first: TermId,
    second: TermId,
) -> Result<TermId, TermError> {
    let partial = connection.insert_application(function, first)?;
    connection.insert_application(partial, second)
}

fn canonical_and<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    left: TermId,
    right: TermId,
) -> Result<(TermId, TermId, TermId, TermId), TermError> {
    let bool_type = connection.insert_bool_type()?;
    let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type)?;
    let binary = connection.insert_arrow_type(bool_type, bool_to_bool)?;
    let truth = connection.insert_bool_term(true)?;
    let choice = connection.insert_bound_term(0, binary)?;
    let first = connection.insert_bound_term(2, bool_type)?;
    let second = connection.insert_bound_term(1, bool_type)?;
    let selected = apply2(connection, choice, first, second)?;
    let selected_truth = apply2(connection, choice, truth, truth)?;
    let selected = connection.insert_lambda(binary, selected)?;
    let selected_truth = connection.insert_lambda(binary, selected_truth)?;
    let body = connection.insert_equality(selected, selected_truth)?;
    let body = connection.insert_lambda(bool_type, body)?;
    let conjunction = connection.insert_lambda(bool_type, body)?;

    let choice = connection.insert_bound_term(0, binary)?;
    let selected_left = apply2(connection, choice, left, right)?;
    let selected_right = apply2(connection, choice, truth, truth)?;
    let selected_left = connection.insert_lambda(binary, selected_left)?;
    let selected_right = connection.insert_lambda(binary, selected_right)?;
    let applied = apply2(connection, conjunction, left, right)?;
    Ok((conjunction, applied, selected_left, selected_right))
}

fn selector<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    choose_right: bool,
) -> Result<TermId, TermError> {
    let bool_type = connection.insert_bool_type()?;
    let index = u32::from(!choose_right);
    let selected = connection.insert_bound_term(index, bool_type)?;
    let selected = connection.insert_lambda(bool_type, selected)?;
    connection.insert_lambda(bool_type, selected)
}

fn normalize_selector<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    function: TermId,
    selector: TermId,
    first: TermId,
    second: TermId,
) -> Result<covalence_nucleus::Conversion<'brand>, ProofError> {
    let applied = proof.conversion_beta(function, selector)?;
    let first_beta = proof.conversion_beta(selector, first)?;
    let second_reflexive = proof.conversion_reflexivity(second)?;
    let first_applied = proof.conversion_application(&first_beta, &second_reflexive)?;
    let second_beta = proof.conversion_beta(first_beta.right(), second)?;
    let selected = proof.conversion_transitivity(&first_applied, &second_beta)?;
    proof.conversion_transitivity(&applied, &selected)
}

fn normalize_and<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    conjunction: TermId,
    left: TermId,
    right: TermId,
) -> Result<covalence_nucleus::Conversion<'brand>, ProofError> {
    let first = proof.conversion_beta(conjunction, left)?;
    let right_reflexive = proof.conversion_reflexivity(right)?;
    let applied = proof.conversion_application(&first, &right_reflexive)?;
    let second = proof.conversion_beta(first.right(), right)?;
    proof.conversion_transitivity(&applied, &second)
}

struct LeibnizTransport {
    equality: TermId,
    premise: TermId,
    predicate: TermId,
    left: TermId,
    right: TermId,
    result: TermId,
}

impl LeibnizTransport {
    fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
        predicate: TermId,
        premise: TermId,
        result: TermId,
    ) -> Result<Self, TermError> {
        let equality = connection.insert_equality(left, right)?;
        Ok(Self {
            equality,
            premise,
            predicate,
            left,
            right,
            result,
        })
    }

    fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality: &Theorem<'brand>,
        premise: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality, self.equality)?;
        require_conclusion(premise, self.premise)?;
        let beta = proof.conversion_beta(self.predicate, self.left)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let lifted = proof.convert_theorem(premise, &reverse)?;
        let transported = proof.equality_substitution(equality, self.predicate, &lifted)?;
        let beta = proof.conversion_beta(self.predicate, self.right)?;
        let result = proof.convert_theorem(&transported, &beta)?;
        require_result(&result, equality.context(), self.result)?;
        Ok(result)
    }
}

/// Prepared canonical `AND_ELIM_L` or `AND_ELIM_R`.
pub struct AndElim {
    conjunction: TermId,
    premise: TermId,
    selected: TermId,
    selected_left: TermId,
    selected_right: TermId,
    selector: TermId,
    left: TermId,
    right: TermId,
    application: ApThm,
    symmetry: EqSym,
    first_transitivity: EqTrans,
    second_transitivity: EqTrans,
    truth_elimination: EqtElim,
}

impl AndElim {
    fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
        choose_right: bool,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let (conjunction, premise, selected_left, selected_right) =
            canonical_and(connection, left, right)?;
        let selector = selector(connection, choose_right)?;
        let selected = if choose_right { right } else { left };
        let truth = connection.insert_bool_term(true)?;
        let applied_left = connection.insert_application(selected_left, selector)?;
        let applied_right = connection.insert_application(selected_right, selector)?;
        let application = ApThm::prepare(connection, selected_left, selected_right, selector)?;
        let symmetry = EqSym::prepare(connection, applied_left, selected)?;
        let first_transitivity =
            EqTrans::prepare(connection, selected, applied_left, applied_right)?;
        let second_transitivity = EqTrans::prepare(connection, selected, applied_right, truth)?;
        let truth_elimination = EqtElim::prepare(connection, selected)?;
        Ok(Self {
            conjunction,
            premise,
            selected,
            selected_left,
            selected_right,
            selector,
            left,
            right,
            application,
            symmetry,
            first_transitivity,
            second_transitivity,
            truth_elimination,
        })
    }

    /// Prepares canonical left-conjunct elimination.
    ///
    /// # Errors
    ///
    /// Returns if either proposition is invalid, open, or non-Boolean.
    pub fn left<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        Self::prepare(connection, left, right, false)
    }

    /// Prepares canonical right-conjunct elimination.
    ///
    /// # Errors
    ///
    /// Returns if either proposition is invalid, open, or non-Boolean.
    pub fn right<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        Self::prepare(connection, left, right, true)
    }

    /// Eliminates the selected conjunct from an exact canonical `AND` theorem.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise or rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        conjunction: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(conjunction, self.premise)?;
        let normalized = normalize_and(proof, self.conjunction, self.left, self.right)?;
        let normalized = proof.convert_theorem(conjunction, &normalized)?;
        let applied = self.application.apply(proof, &normalized)?;
        let left_normal = normalize_selector(
            proof,
            self.selected_left,
            self.selector,
            self.left,
            self.right,
        )?;
        let left_normal = proof.prove_conversion_equality(conjunction.context(), &left_normal)?;
        let selected_to_applied = self.symmetry.apply(proof, &left_normal)?;
        let selected_to_right =
            self.first_transitivity
                .apply(proof, &selected_to_applied, &applied)?;
        let truth = proof.prove_truth(conjunction.context())?;
        let right_normal = normalize_selector(
            proof,
            self.selected_right,
            self.selector,
            truth.conclusion(),
            truth.conclusion(),
        )?;
        let right_normal = proof.prove_conversion_equality(conjunction.context(), &right_normal)?;
        let selected_to_truth =
            self.second_transitivity
                .apply(proof, &selected_to_right, &right_normal)?;
        let result = self.truth_elimination.apply(proof, &selected_to_truth)?;
        require_result(&result, conjunction.context(), self.selected)?;
        Ok(result)
    }
}

/// Prepared canonical `AND_INTRO`.
pub struct AndIntro {
    left: TermId,
    right: TermId,
    result: TermId,
    conjunction: TermId,
    baseline: TermId,
    left_truth: EqtIntro,
    right_truth: EqtIntro,
    left_symmetry: EqSym,
    right_symmetry: EqSym,
    left_transport: LeibnizTransport,
    right_transport: LeibnizTransport,
}

impl AndIntro {
    /// Prepares canonical conjunction introduction for two closed Booleans.
    ///
    /// # Errors
    ///
    /// Returns if either proposition is invalid, open, or non-Boolean.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let (and, result, _, _) = canonical_and(connection, left, right)?;
        let truth = connection.insert_bool_term(true)?;
        let (_, baseline, baseline_left, baseline_right) = canonical_and(connection, truth, truth)?;
        if baseline_left != baseline_right {
            return Err(TermError::CorruptTerm(baseline).into());
        }
        let baseline_applied = apply2(connection, and, truth, truth)?;
        let left_result = apply2(connection, and, left, truth)?;
        let applied_result = apply2(connection, and, left, right)?;
        let bool_type = connection.insert_bool_type().map_err(TermError::from)?;
        let variable = connection.insert_bound_term(0, bool_type)?;
        let left_body = apply2(connection, and, variable, truth)?;
        let left_predicate = connection.insert_lambda(bool_type, left_body)?;
        let right_body = apply2(connection, and, left, variable)?;
        let right_predicate = connection.insert_lambda(bool_type, right_body)?;
        let left_transport = LeibnizTransport::prepare(
            connection,
            truth,
            left,
            left_predicate,
            baseline_applied,
            left_result,
        )?;
        let right_transport = LeibnizTransport::prepare(
            connection,
            truth,
            right,
            right_predicate,
            left_result,
            applied_result,
        )?;
        Ok(Self {
            left,
            right,
            result,
            conjunction: and,
            baseline: baseline_left,
            left_truth: EqtIntro::prepare(connection, left)?,
            right_truth: EqtIntro::prepare(connection, right)?,
            left_symmetry: EqSym::prepare(connection, left, truth)?,
            right_symmetry: EqSym::prepare(connection, right, truth)?,
            left_transport,
            right_transport,
        })
    }

    /// Introduces exact canonical `AND p q` from same-context `Γ ⊢ p` and `Γ ⊢ q`.
    ///
    /// # Errors
    ///
    /// Returns for wrong premises, differing contexts, or a rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        left: &Theorem<'brand>,
        right: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(left, self.left)?;
        require_conclusion(right, self.right)?;
        let left_true = self.left_truth.apply(proof, left)?;
        let right_true = self.right_truth.apply(proof, right)?;
        let true_left = self.left_symmetry.apply(proof, &left_true)?;
        let true_right = self.right_symmetry.apply(proof, &right_true)?;
        let baseline = proof.prove_reflexivity(left.context(), self.baseline)?;
        let truth = proof.prove_truth(left.context())?;
        let baseline_normal = normalize_and(
            proof,
            self.conjunction,
            truth.conclusion(),
            truth.conclusion(),
        )?;
        let baseline_reverse = proof.conversion_symmetry(&baseline_normal)?;
        let baseline = proof.convert_theorem(&baseline, &baseline_reverse)?;
        let left_conjunction = self.left_transport.apply(proof, &true_left, &baseline)?;
        let result = self
            .right_transport
            .apply(proof, &true_right, &left_conjunction)?;
        require_result(&result, left.context(), self.result)?;
        Ok(result)
    }
}

fn canonical_imp<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    antecedent: TermId,
    consequent: TermId,
) -> Result<(TermId, TermId), TermError> {
    let (_, conjunction, _, _) = canonical_and(connection, antecedent, consequent)?;
    let implication = connection.insert_equality(conjunction, antecedent)?;
    Ok((conjunction, implication))
}

/// Prepared canonical `IMP_ELIM`.
pub struct ImpElim {
    implication: TermId,
    antecedent: TermId,
    symmetry: EqSym,
    right_elimination: AndElim,
}

impl ImpElim {
    /// Prepares canonical implication elimination.
    ///
    /// # Errors
    ///
    /// Returns if either proposition is invalid, open, or non-Boolean.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        antecedent: TermId,
        consequent: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        let (conjunction, implication) = canonical_imp(connection, antecedent, consequent)?;
        Ok(Self {
            implication,
            antecedent,
            symmetry: EqSym::prepare(connection, conjunction, antecedent)?,
            right_elimination: AndElim::right(connection, antecedent, consequent)?,
        })
    }

    /// Applies modus ponens to exact same-context implication and antecedent theorems.
    ///
    /// # Errors
    ///
    /// Returns for wrong premises, differing contexts, or a rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        implication: &Theorem<'brand>,
        antecedent: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(implication, self.implication)?;
        require_conclusion(antecedent, self.antecedent)?;
        let antecedent_to_conjunction = self.symmetry.apply(proof, implication)?;
        let conjunction = proof.equality_modus_ponens(&antecedent_to_conjunction, antecedent)?;
        self.right_elimination.apply(proof, &conjunction)
    }
}

/// Prepared canonical `IMP_INTRO` with explicit base and discharge contexts.
pub struct ImpIntro {
    base: ContextId,
    consequent_context: ContextId,
    conjunction_context: ContextId,
    consequent: TermId,
    antecedent: TermId,
    conjunction: TermId,
    result: TermId,
    conjunction_intro: AndIntro,
    left_elimination: AndElim,
}

impl ImpIntro {
    /// Prepares `Γ ∪ {p}` and `Γ ∪ {AND p q}` for exact implication introduction.
    ///
    /// # Errors
    ///
    /// Returns if `Γ` or either proposition is invalid, open, or ill typed.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        antecedent: TermId,
        consequent: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        let mut consequent_members = connection.context_members(base)?;
        consequent_members.push(antecedent);
        let consequent_context = connection.define_context(consequent_members)?;
        let (conjunction, result) = canonical_imp(connection, antecedent, consequent)?;
        let mut conjunction_members = connection.context_members(base)?;
        conjunction_members.push(conjunction);
        let conjunction_context = connection.define_context(conjunction_members)?;
        Ok(Self {
            base,
            consequent_context,
            conjunction_context,
            consequent,
            antecedent,
            conjunction,
            result,
            conjunction_intro: AndIntro::prepare(connection, antecedent, consequent)?,
            left_elimination: AndElim::left(connection, antecedent, consequent)?,
        })
    }

    /// Returns the exact context under which the consequent premise is required.
    #[must_use]
    pub const fn premise_context(&self) -> ContextId {
        self.consequent_context
    }

    /// Introduces `Γ ⊢ IMP p q` from exact `Γ ∪ {p} ⊢ q`.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise context/conclusion or rejected constituent rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        consequent: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        if consequent.context() != self.consequent_context {
            return Err(DerivedRuleError::UnexpectedContext {
                expected: self.consequent_context,
                actual: consequent.context(),
            });
        }
        require_conclusion(consequent, self.consequent)?;
        let antecedent = proof.prove_hypothesis(self.consequent_context, self.antecedent)?;
        let conjunction = self
            .conjunction_intro
            .apply(proof, &antecedent, consequent)?;
        let conjunction_hypothesis =
            proof.prove_hypothesis(self.conjunction_context, self.conjunction)?;
        let antecedent_from_conjunction = self
            .left_elimination
            .apply(proof, &conjunction_hypothesis)?;
        let result = proof.deduction_antisymmetry(&conjunction, &antecedent_from_conjunction)?;
        require_result(&result, self.base, self.result)?;
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

    #[test]
    fn quantifier_rules_have_exact_shapes_freshness_and_no_implicit_persistence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let falsehood = connection.insert_bool_term(false).unwrap();
        let variable = connection.insert_free_term(100, bool_type).unwrap();
        let other = connection.insert_free_term(101, bool_type).unwrap();
        let marker = connection.insert_equality(other, other).unwrap();
        let context = connection.define_context([marker]).unwrap();

        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let identity_bound = connection.insert_application(identity, bound).unwrap();
        let expanded_identity = connection.insert_lambda(bool_type, identity_bound).unwrap();
        let pointwise_left = connection.insert_application(identity, variable).unwrap();
        let pointwise_right = connection
            .insert_application(expanded_identity, variable)
            .unwrap();
        let pointwise = connection
            .insert_equality(pointwise_left, pointwise_right)
            .unwrap();
        let functions_equal = connection
            .insert_equality(identity, expanded_identity)
            .unwrap();
        let fun_ext =
            FunExt::prepare(&mut connection, identity, expanded_identity, variable).unwrap();

        let p = connection.insert_application(identity, truth).unwrap();
        let predicate = connection.insert_lambda(bool_type, p).unwrap();
        let predicate_variable = connection.insert_application(predicate, variable).unwrap();
        let constant_truth = connection.insert_lambda(bool_type, truth).unwrap();
        let universal = connection
            .insert_equality(predicate, constant_truth)
            .unwrap();
        let predicate_false = connection.insert_application(predicate, falsehood).unwrap();
        let all_intro = AllIntroApplied::prepare(&mut connection, predicate, variable).unwrap();
        let all_elim = AllElim::prepare(&mut connection, predicate, falsehood).unwrap();

        let other_equality = connection.insert_equality(other, other).unwrap();
        let predicate_with_other = connection.insert_lambda(bool_type, other_equality).unwrap();
        assert!(AllIntroApplied::prepare(&mut connection, predicate_with_other, variable).is_ok());

        connection
            .with_proof_session(|mut proof| {
                let pointwise_beta = proof.conversion_beta(expanded_identity, variable)?;
                let pointwise_conversion = proof.conversion_symmetry(&pointwise_beta)?;
                assert_eq!(pointwise_conversion.left(), pointwise_left);
                assert_eq!(pointwise_conversion.right(), pointwise_right);
                let pointwise_theorem =
                    proof.prove_conversion_equality(context, &pointwise_conversion)?;
                assert_eq!(pointwise_theorem.conclusion(), pointwise);
                let extensional = fun_ext.apply(&mut proof, &pointwise_theorem).unwrap();
                assert_eq!(extensional.context(), context);
                assert_eq!(extensional.conclusion(), functions_equal);

                let predicate_beta = proof.conversion_beta(predicate, variable)?;
                let p_beta = proof.conversion_beta(identity, truth)?;
                let predicate_to_truth = proof.conversion_transitivity(&predicate_beta, &p_beta)?;
                let truth_to_predicate = proof.conversion_symmetry(&predicate_to_truth)?;
                let truth_theorem = proof.prove_truth(context)?;
                let predicate_instance =
                    proof.convert_theorem(&truth_theorem, &truth_to_predicate)?;
                assert_eq!(predicate_instance.conclusion(), predicate_variable);
                let introduced = all_intro.apply(&mut proof, &predicate_instance).unwrap();
                assert_eq!(introduced.context(), context);
                assert_eq!(introduced.conclusion(), universal);
                let eliminated = all_elim.apply(&mut proof, &introduced).unwrap();
                assert_eq!(eliminated.context(), context);
                assert_eq!(eliminated.conclusion(), predicate_false);
                assert!(proof.load_theorem(context, predicate_false)?.is_none());
                proof.persist_theorem(&eliminated)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();

        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 1);
        assert!(
            connection
                .proved_judgement(context, predicate_false)
                .unwrap()
        );
    }

    #[test]
    fn quantifier_plans_reject_bad_variables_and_abstraction_checks_context() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_free_term(200, bool_type).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let constant = connection.insert_constant(201, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        assert!(matches!(
            FunExt::prepare(&mut connection, identity, identity, bound),
            Err(DerivedRulePreparationError::ExpectedFreeVariable(term)) if term == bound
        ));
        assert!(matches!(
            AllIntroApplied::prepare(&mut connection, identity, constant),
            Err(DerivedRulePreparationError::ExpectedFreeVariable(term)) if term == constant
        ));

        let function_with_variable = connection.insert_lambda(bool_type, variable).unwrap();
        assert!(matches!(
            FunExt::prepare(
                &mut connection,
                function_with_variable,
                function_with_variable,
                variable,
            ),
            Err(DerivedRulePreparationError::VariableOccursInFixedTerm { variable: found, .. })
                if found == variable
        ));
        let variable_equality = connection.insert_equality(variable, variable).unwrap();
        let predicate_with_variable = connection
            .insert_lambda(bool_type, variable_equality)
            .unwrap();
        assert!(matches!(
            AllIntroApplied::prepare(&mut connection, predicate_with_variable, variable),
            Err(DerivedRulePreparationError::VariableOccursInFixedTerm { variable: found, .. })
                if found == variable
        ));

        let predicate = connection.insert_lambda(bool_type, truth).unwrap();
        let instance = connection.insert_application(predicate, variable).unwrap();
        let context = connection.define_context([variable_equality]).unwrap();
        let plan = AllIntroApplied::prepare(&mut connection, predicate, variable).unwrap();
        let pointwise = connection.insert_application(identity, variable).unwrap();
        let pointwise_equality = connection.insert_equality(pointwise, pointwise).unwrap();
        let fun_ext = FunExt::prepare(&mut connection, identity, identity, variable).unwrap();
        let all_elim = AllElim::prepare(&mut connection, predicate, truth).unwrap();
        connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(predicate, variable)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                let truth_theorem = proof.prove_truth(context)?;
                let instance_theorem = proof.convert_theorem(&truth_theorem, &reverse)?;
                assert_eq!(instance_theorem.conclusion(), instance);
                assert!(matches!(
                    plan.apply(&mut proof, &instance_theorem),
                    Err(DerivedRuleError::Proof(
                        ProofError::AbstractionVariableFreeInAssumption { variable: found, .. }
                    )) if found == variable
                ));
                let pointwise_theorem = proof.prove_reflexivity(context, pointwise)?;
                assert_eq!(pointwise_theorem.conclusion(), pointwise_equality);
                assert!(matches!(
                    fun_ext.apply(&mut proof, &pointwise_theorem),
                    Err(DerivedRuleError::Proof(
                        ProofError::AbstractionVariableFreeInAssumption { variable: found, .. }
                    )) if found == variable
                ));
                assert!(matches!(
                    all_elim.apply(&mut proof, &truth_theorem),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    fn denied_all_intro(operation: Operation) -> DerivedRuleError {
        let mut connection = Connection::open_hol_in_memory(DenyOperation(operation)).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_free_term(300, bool_type).unwrap();
        let predicate = connection.insert_lambda(bool_type, truth).unwrap();
        let plan = AllIntroApplied::prepare(&mut connection, predicate, variable).unwrap();
        connection.with_proof_session(|mut proof| {
            let beta = proof.conversion_beta(predicate, variable).unwrap();
            let reverse = proof.conversion_symmetry(&beta).unwrap();
            let truth_theorem = proof.prove_truth(ContextId::empty()).unwrap();
            let premise = proof.convert_theorem(&truth_theorem, &reverse).unwrap();
            match plan.apply(&mut proof, &premise) {
                Err(error) => error,
                Ok(_) => panic!("denied ALL_INTRO unexpectedly succeeded"),
            }
        })
    }

    #[test]
    fn quantifier_constituent_policy_denials_are_visible() {
        for operation in [Operation::ProveAbstraction, Operation::ProveConversionEta] {
            assert!(matches!(
                denied_all_intro(operation),
                DerivedRuleError::Proof(ProofError::Denied(actual)) if actual == operation
            ));
        }

        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveConversionBeta)).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let predicate = connection.insert_lambda(bool_type, truth).unwrap();
        let plan = AllElim::prepare(&mut connection, predicate, truth).unwrap();
        let error = connection.with_proof_session(|mut proof| {
            let universal = proof
                .prove_reflexivity(ContextId::empty(), predicate)
                .unwrap();
            match plan.apply(&mut proof, &universal) {
                Err(error) => error,
                Ok(_) => panic!("denied ALL_ELIM unexpectedly succeeded"),
            }
        });
        assert!(matches!(
            error,
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveConversionBeta))
        ));
    }

    #[test]
    fn connective_rules_have_exact_shapes_contexts_and_no_implicit_persistence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let marker = connection.insert_equality(truth, truth).unwrap();
        let context = connection.define_context([marker]).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let identity_bound = connection.insert_application(identity, bound).unwrap();
        let expanded_identity = connection.insert_lambda(bool_type, identity_bound).unwrap();
        let p = connection.insert_application(identity, truth).unwrap();
        let q = connection
            .insert_application(expanded_identity, truth)
            .unwrap();
        let (_, conjunction, _, _) = canonical_and(&mut connection, p, q).unwrap();
        let (_, implication) = canonical_imp(&mut connection, p, q).unwrap();
        assert_ne!(p, conjunction);

        let and_intro = AndIntro::prepare(&mut connection, p, q).unwrap();
        let and_left = AndElim::left(&mut connection, p, q).unwrap();
        let and_right = AndElim::right(&mut connection, p, q).unwrap();
        let imp_elim = ImpElim::prepare(&mut connection, p, q).unwrap();
        let imp_intro = ImpIntro::prepare(&mut connection, context, p, q).unwrap();
        let premise_context = imp_intro.premise_context();

        connection
            .with_proof_session(|mut proof| {
                let p_to_truth = proof.conversion_beta(identity, truth)?;
                let q_to_p = proof.conversion_beta(expanded_identity, truth)?;
                let q_to_truth = proof.conversion_transitivity(&q_to_p, &p_to_truth)?;
                let truth_theorem = proof.prove_truth(context)?;
                let truth_to_p = proof.conversion_symmetry(&p_to_truth)?;
                let truth_to_q = proof.conversion_symmetry(&q_to_truth)?;
                let p_theorem = proof.convert_theorem(&truth_theorem, &truth_to_p)?;
                let q_theorem = proof.convert_theorem(&truth_theorem, &truth_to_q)?;
                let conjunction_theorem =
                    and_intro.apply(&mut proof, &p_theorem, &q_theorem).unwrap();
                assert_eq!(conjunction_theorem.context(), context);
                assert_eq!(conjunction_theorem.conclusion(), conjunction);
                let recovered_p = and_left.apply(&mut proof, &conjunction_theorem).unwrap();
                let recovered_q = and_right.apply(&mut proof, &conjunction_theorem).unwrap();
                assert_eq!(
                    (recovered_p.context(), recovered_p.conclusion()),
                    (context, p)
                );
                assert_eq!(
                    (recovered_q.context(), recovered_q.conclusion()),
                    (context, q)
                );

                let premise_truth = proof.prove_truth(premise_context)?;
                let truth_to_q = proof.conversion_symmetry(&q_to_truth)?;
                let q_premise = proof.convert_theorem(&premise_truth, &truth_to_q)?;
                let implication_theorem = imp_intro.apply(&mut proof, &q_premise).unwrap();
                assert_eq!(implication_theorem.context(), context);
                assert_eq!(implication_theorem.conclusion(), implication);
                let modus_ponens = imp_elim
                    .apply(&mut proof, &implication_theorem, &p_theorem)
                    .unwrap();
                assert_eq!(
                    (modus_ponens.context(), modus_ponens.conclusion()),
                    (context, q)
                );
                assert!(proof.load_theorem(context, q)?.is_none());
                proof.persist_theorem(&modus_ponens)?;
                Ok::<_, ProofError>(())
            })
            .unwrap();

        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 1);
        assert!(connection.proved_judgement(context, q).unwrap());
    }

    #[test]
    fn connective_public_nodes_match_the_literal_canonical_graph() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type).unwrap();
        let binary = connection
            .insert_arrow_type(bool_type, bool_to_bool)
            .unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let p = connection.insert_equality(truth, truth).unwrap();
        let identity_body = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, identity_body).unwrap();
        let q = connection.insert_application(identity, truth).unwrap();

        // Build the fixture graph literally, independently of `canonical_and`.
        let choice = connection.insert_bound_term(0, binary).unwrap();
        let first = connection.insert_bound_term(2, bool_type).unwrap();
        let second = connection.insert_bound_term(1, bool_type).unwrap();
        let choice_first = connection.insert_application(choice, first).unwrap();
        let selected = connection.insert_application(choice_first, second).unwrap();
        let choice_truth = connection.insert_application(choice, truth).unwrap();
        let selected_truth = connection.insert_application(choice_truth, truth).unwrap();
        let selected = connection.insert_lambda(binary, selected).unwrap();
        let selected_truth = connection.insert_lambda(binary, selected_truth).unwrap();
        let body = connection
            .insert_equality(selected, selected_truth)
            .unwrap();
        let body = connection.insert_lambda(bool_type, body).unwrap();
        let and_operator = connection.insert_lambda(bool_type, body).unwrap();
        let and_p = connection.insert_application(and_operator, p).unwrap();
        let applied = connection.insert_application(and_p, q).unwrap();

        let choice = connection.insert_bound_term(0, binary).unwrap();
        let choice_p = connection.insert_application(choice, p).unwrap();
        let selected_pq = connection.insert_application(choice_p, q).unwrap();
        let choice_truth = connection.insert_application(choice, truth).unwrap();
        let selected_tt = connection.insert_application(choice_truth, truth).unwrap();
        let selected_pq = connection.insert_lambda(binary, selected_pq).unwrap();
        let selected_tt = connection.insert_lambda(binary, selected_tt).unwrap();
        let normalized = connection
            .insert_equality(selected_pq, selected_tt)
            .unwrap();
        let implication = connection.insert_equality(applied, p).unwrap();

        let (actual_operator, actual_applied, actual_left, actual_right) =
            canonical_and(&mut connection, p, q).unwrap();
        assert_eq!(actual_operator, and_operator);
        assert_eq!(actual_applied, applied);
        assert_eq!((actual_left, actual_right), (selected_pq, selected_tt));
        assert_eq!(
            connection.term(normalized).unwrap(),
            TermView::Equality {
                left: selected_pq,
                right: selected_tt
            }
        );
        assert_eq!(
            connection.term(applied).unwrap(),
            TermView::Application {
                function: and_p,
                argument: q
            }
        );
        assert_eq!(
            canonical_imp(&mut connection, p, q).unwrap(),
            (applied, implication)
        );

        let intro = AndIntro::prepare(&mut connection, p, q).unwrap();
        let elim = AndElim::left(&mut connection, p, q).unwrap();
        let imp_intro = ImpIntro::prepare(&mut connection, ContextId::empty(), p, q).unwrap();
        let imp_elim = ImpElim::prepare(&mut connection, p, q).unwrap();
        assert_eq!(intro.result, applied);
        assert_eq!(elim.premise, applied);
        assert_eq!(imp_intro.conjunction, applied);
        assert_eq!(imp_intro.result, implication);
        assert_eq!(imp_elim.implication, implication);
    }

    #[test]
    fn imp_intro_preserves_base_context_membership_matrix() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let antecedent = connection.insert_application(identity, truth).unwrap();
        let consequent = truth;
        let (conjunction, implication) =
            canonical_imp(&mut connection, antecedent, consequent).unwrap();
        assert_ne!(antecedent, conjunction);
        let bases = [
            connection.define_context([]).unwrap(),
            connection.define_context([antecedent]).unwrap(),
            connection.define_context([conjunction]).unwrap(),
            connection
                .define_context([antecedent, conjunction])
                .unwrap(),
        ];
        let plans = bases
            .into_iter()
            .map(|base| {
                let plan =
                    ImpIntro::prepare(&mut connection, base, antecedent, consequent).unwrap();
                (base, plan)
            })
            .collect::<Vec<_>>();

        connection
            .with_proof_session(|mut proof| {
                for (base, plan) in &plans {
                    let consequent = proof.prove_truth(plan.premise_context())?;
                    let introduced = plan.apply(&mut proof, &consequent).unwrap();
                    assert_eq!(introduced.context(), *base);
                    assert_eq!(introduced.conclusion(), implication);
                }
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn connective_rules_reject_wrong_premises_and_contexts() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let marker = connection.insert_equality(truth, truth).unwrap();
        let gamma = connection.define_context([truth]).unwrap();
        let delta = connection.define_context([marker]).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let p = connection.insert_application(identity, truth).unwrap();
        let q = truth;
        let (_, _conjunction, _, _) = canonical_and(&mut connection, p, q).unwrap();
        let (_, implication) = canonical_imp(&mut connection, p, q).unwrap();
        let and_intro = AndIntro::prepare(&mut connection, p, q).unwrap();
        let and_left = AndElim::left(&mut connection, p, q).unwrap();
        let imp_elim = ImpElim::prepare(&mut connection, p, q).unwrap();
        let imp_intro = ImpIntro::prepare(&mut connection, gamma, p, q).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(identity, truth)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                let truth_gamma = proof.prove_truth(gamma)?;
                let p_gamma = proof.convert_theorem(&truth_gamma, &reverse)?;
                let q_delta = proof.prove_truth(delta)?;
                assert!(matches!(
                    and_intro.apply(&mut proof, &p_gamma, &q_delta),
                    Err(DerivedRuleError::Proof(
                        ProofError::EqualitySubstitutionContextMismatch { .. }
                    ))
                ));
                assert!(matches!(
                    and_left.apply(&mut proof, &truth_gamma),
                    Err(DerivedRuleError::PremiseConclusion { .. })
                ));

                let q_premise = proof.prove_truth(imp_intro.premise_context())?;
                let implication_gamma = imp_intro.apply(&mut proof, &q_premise).unwrap();
                assert_eq!(implication_gamma.conclusion(), implication);
                let p_delta = proof.convert_theorem(&q_delta, &reverse)?;
                assert!(matches!(
                    imp_elim.apply(&mut proof, &implication_gamma, &p_delta),
                    Err(DerivedRuleError::Proof(
                        ProofError::MismatchedTheoremContexts { .. }
                    ))
                ));
                assert!(matches!(
                    imp_intro.apply(&mut proof, &q_delta),
                    Err(DerivedRuleError::UnexpectedContext { .. })
                ));
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    fn denied_and_intro() -> DerivedRuleError {
        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveEqualitySubstitution))
                .unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let plan = AndIntro::prepare(&mut connection, truth, truth).unwrap();
        connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_truth(ContextId::empty()).unwrap();
            match plan.apply(&mut proof, &theorem, &theorem) {
                Err(error) => error,
                Ok(_) => panic!("denied AND_INTRO unexpectedly succeeded"),
            }
        })
    }

    fn denied_and_elim() -> DerivedRuleError {
        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveConversionBeta)).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let (_, conjunction, left, right) = canonical_and(&mut connection, truth, truth).unwrap();
        assert_eq!(left, right);
        let plan = AndElim::left(&mut connection, truth, truth).unwrap();
        let context = connection.define_context([conjunction]).unwrap();
        connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_hypothesis(context, conjunction).unwrap();
            match plan.apply(&mut proof, &theorem) {
                Err(error) => error,
                Ok(_) => panic!("denied AND_ELIM unexpectedly succeeded"),
            }
        })
    }

    fn denied_imp_intro() -> DerivedRuleError {
        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveDeductionAntisymmetry))
                .unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let plan = ImpIntro::prepare(&mut connection, ContextId::empty(), truth, truth).unwrap();
        connection.with_proof_session(|mut proof| {
            let consequent = proof.prove_truth(plan.premise_context()).unwrap();
            match plan.apply(&mut proof, &consequent) {
                Err(error) => error,
                Ok(_) => panic!("denied IMP_INTRO unexpectedly succeeded"),
            }
        })
    }

    fn denied_imp_elim() -> DerivedRuleError {
        let mut connection =
            Connection::open_hol_in_memory(DenyOperation(Operation::ProveEqualityModusPonens))
                .unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let elim = ImpElim::prepare(&mut connection, truth, truth).unwrap();
        let context = connection.define_context([elim.implication]).unwrap();
        connection.with_proof_session(|mut proof| {
            let implication = proof.prove_hypothesis(context, elim.implication).unwrap();
            let antecedent = proof.prove_truth(context).unwrap();
            match elim.apply(&mut proof, &implication, &antecedent) {
                Err(error) => error,
                Ok(_) => panic!("denied IMP_ELIM unexpectedly succeeded"),
            }
        })
    }

    fn denied_imp_intro_preparation(operation: Operation) -> DerivedRulePreparationError {
        let mut connection = Connection::open_hol_in_memory(DenyOperation(operation)).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        match ImpIntro::prepare(&mut connection, ContextId::empty(), truth, truth) {
            Err(error) => error,
            Ok(_) => panic!("denied IMP_INTRO preparation unexpectedly succeeded"),
        }
    }

    #[test]
    fn connective_constituent_policy_denials_are_visible() {
        assert!(matches!(
            denied_and_intro(),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveEqualitySubstitution))
        ));
        assert!(matches!(
            denied_and_elim(),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveConversionBeta))
        ));
        assert!(matches!(
            denied_imp_intro(),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveDeductionAntisymmetry))
        ));
        assert!(matches!(
            denied_imp_elim(),
            DerivedRuleError::Proof(ProofError::Denied(Operation::ProveEqualityModusPonens))
        ));
        for operation in [Operation::ReadContext, Operation::DefineContext] {
            assert!(matches!(
                denied_imp_intro_preparation(operation),
                DerivedRulePreparationError::Context(ContextError::Denied(actual))
                    if actual == operation
            ));
        }
    }
}
