//! Small positive HOL derived rules assembled above the LCF kernel.
//!
//! Preparation interns only checked syntax needed by an implementation. Applying
//! a plan consumes branded premises from one [`ProofSession`] and returns a
//! theorem carrying that same generative brand. No derived result is persisted.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextId, Hol, Policy, ProofError, ProofSession, TermError, TermId, TermView,
    Theorem, TypeId,
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
        }
    }
}

impl StdError for DerivedRulePreparationError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Term(error) => Some(error),
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
}
