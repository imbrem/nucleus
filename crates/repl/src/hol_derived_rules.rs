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
    /// A requested weakening target does not contain every source assumption.
    ContextNotSubset {
        /// Context whose members must be preserved.
        source: ContextId,
        /// Proposed weakening target.
        target: ContextId,
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
            Self::ContextNotSubset { source, target } => write!(
                formatter,
                "context {} is not a subset of context {}",
                source.get(),
                target.get()
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
            | Self::VariableOccursInFixedTerm { .. }
            | Self::ContextNotSubset { .. } => None,
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

fn canonical_false<P: Policy>(
    connection: &mut Connection<Hol<P>>,
) -> Result<(TermId, TermId), TermError> {
    let bool_type = connection.insert_bool_type()?;
    let truth = connection.insert_bool_term(true)?;
    let proposition = connection.insert_bound_term(0, bool_type)?;
    let identity = connection.insert_lambda(bool_type, proposition)?;
    let constant_truth = connection.insert_lambda(bool_type, truth)?;
    let falsehood = connection.insert_equality(identity, constant_truth)?;
    Ok((identity, falsehood))
}

/// Prepared elimination for canonical logical false
/// `F := ALL_B (lambda p:bool. p)`.
///
/// This is an ordinary universal-elimination derivation. It introduces no
/// primitive false rule and does not use `MBOOL(false)`.
pub struct FalseElim {
    falsehood: TermId,
    identity: TermId,
    proposition: TermId,
    elimination: AllElim,
}

impl FalseElim {
    /// Prepares `FALSITY`: from `Gamma |- F`, derive `Gamma |- proposition`.
    ///
    /// # Errors
    ///
    /// Returns if `proposition` is not a closed checked Boolean term.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        let (identity, falsehood) = canonical_false(connection)?;
        Ok(Self {
            falsehood,
            identity,
            proposition,
            elimination: AllElim::prepare(connection, identity, proposition)?,
        })
    }

    /// Eliminates an exact canonical-false theorem without persistence.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise or rejected constituent LCF rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        falsehood: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(falsehood, self.falsehood)?;
        let applied = self.elimination.apply(proof, falsehood)?;
        let beta = proof.conversion_beta(self.identity, self.proposition)?;
        let result = proof.convert_theorem(&applied, &beta)?;
        require_result(&result, falsehood.context(), self.proposition)?;
        Ok(result)
    }
}

/// Prepared congruence beneath Hilbert choice.
///
/// From `Gamma |- P = Q`, derives `Gamma |- epsilon P = epsilon Q` by
/// Leibniz substitution through the closed predicate
/// `lambda R. epsilon P = epsilon R`. This deliberately does not add a kernel
/// epsilon-congruence rule.
pub struct EpsCongr {
    premise: TermId,
    left_epsilon: TermId,
    result: TermId,
    transport: LeibnizTransport,
}

impl EpsCongr {
    /// Prepares epsilon congruence for exact closed predicate endpoints.
    ///
    /// # Errors
    ///
    /// Returns if either endpoint is open, not a Boolean predicate, or has an
    /// incompatible type.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        left: TermId,
        right: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, left)?;
        require_closed(connection, right)?;
        let premise = connection.insert_equality(left, right)?;
        let left_epsilon = connection.insert_epsilon(left)?;
        let right_epsilon = connection.insert_epsilon(right)?;
        let result = connection.insert_equality(left_epsilon, right_epsilon)?;
        let predicate_type = connection.term_type(left)?;
        let variable = connection.insert_bound_term(0, predicate_type)?;
        let variable_epsilon = connection.insert_epsilon(variable)?;
        let body = connection.insert_equality(left_epsilon, variable_epsilon)?;
        let predicate = connection.insert_lambda(predicate_type, body)?;
        let reflexive = connection.insert_equality(left_epsilon, left_epsilon)?;
        let transport =
            LeibnizTransport::prepare(connection, left, right, predicate, reflexive, result)?;
        Ok(Self {
            premise,
            left_epsilon,
            result,
            transport,
        })
    }

    /// Applies epsilon congruence without persistence.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise or rejected constituent LCF rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        equality: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(equality, self.premise)?;
        let reflexive = proof.prove_reflexivity(equality.context(), self.left_epsilon)?;
        let result = self.transport.apply(proof, equality, &reflexive)?;
        require_result(&result, equality.context(), self.result)?;
        Ok(result)
    }
}

struct WeakenPlan {
    source: ContextId,
    target: ContextId,
    members: Vec<TermId>,
}

impl WeakenPlan {
    fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        source: ContextId,
        target: ContextId,
    ) -> Result<Self, DerivedRulePreparationError> {
        let members = connection.context_members(source)?;
        let target_members = connection.context_members(target)?;
        if members
            .iter()
            .any(|member| target_members.binary_search(member).is_err())
        {
            return Err(DerivedRulePreparationError::ContextNotSubset { source, target });
        }
        Ok(Self {
            source,
            target,
            members,
        })
    }

    fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        theorem: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        if theorem.context() != self.source {
            return Err(DerivedRuleError::UnexpectedContext {
                expected: self.source,
                actual: theorem.context(),
            });
        }
        let witnesses = self
            .members
            .iter()
            .map(|member| proof.prove_hypothesis(self.target, *member))
            .collect::<Result<Vec<_>, _>>()?;
        let implication = proof.prove_context_implication(self.target, self.source, &witnesses)?;
        let result = proof.weaken(&implication, theorem)?;
        require_result(&result, self.target, theorem.conclusion())?;
        Ok(result)
    }
}

struct ChurchOrSyntax {
    predicate: TermId,
    proposition: TermId,
    left_to_result: TermId,
    right_to_result: TermId,
    right_continuation: TermId,
    body: TermId,
}

fn canonical_imp_open<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    antecedent: TermId,
    consequent: TermId,
) -> Result<TermId, TermError> {
    let truth = connection.insert_bool_term(true)?;
    let conjunction = canonical_and(connection, truth, truth)?.0;
    let applied = apply2(connection, conjunction, antecedent, consequent)?;
    connection.insert_equality(applied, antecedent)
}

fn church_or<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    left: TermId,
    right: TermId,
    result: TermId,
) -> Result<ChurchOrSyntax, TermError> {
    let bool_type = connection.insert_bool_type()?;
    let left_to_result = canonical_imp(connection, left, result)?.1;
    let right_to_result = canonical_imp(connection, right, result)?.1;
    let right_continuation = canonical_imp(connection, right_to_result, result)?.1;
    let body = canonical_imp(connection, left_to_result, right_continuation)?.1;

    let bound_result = connection.insert_bound_term(0, bool_type)?;
    let bound_left_to_result = canonical_imp_open(connection, left, bound_result)?;
    let bound_right_to_result = canonical_imp_open(connection, right, bound_result)?;
    let bound_right_continuation =
        canonical_imp_open(connection, bound_right_to_result, bound_result)?;
    let bound_body =
        canonical_imp_open(connection, bound_left_to_result, bound_right_continuation)?;
    let predicate = connection.insert_lambda(bool_type, bound_body)?;
    let truth = connection.insert_bool_term(true)?;
    let constant_truth = connection.insert_lambda(bool_type, truth)?;
    let proposition = connection.insert_equality(predicate, constant_truth)?;
    Ok(ChurchOrSyntax {
        predicate,
        proposition,
        left_to_result,
        right_to_result,
        right_continuation,
        body,
    })
}

/// Prepared introduction for the Church encoding
/// `p OR q := ALL r. (p IMP r) IMP (q IMP r) IMP r`.
pub struct ChurchOrIntro {
    base: ContextId,
    selected: TermId,
    result_variable: TermId,
    syntax: ChurchOrSyntax,
    first_intro: ImpIntro,
    second_intro: ImpIntro,
    selected_elim: ImpElim,
    selected_weakening: WeakenPlan,
    all_intro: AllIntroApplied,
    choose_right: bool,
}

impl ChurchOrIntro {
    fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        left: TermId,
        right: TermId,
        result_variable: TermId,
        choose_right: bool,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_fresh_variable(connection, result_variable, &[left, right])?;
        let syntax = church_or(connection, left, right, result_variable)?;
        let first_intro = ImpIntro::prepare(
            connection,
            base,
            syntax.left_to_result,
            syntax.right_continuation,
        )?;
        let second_intro = ImpIntro::prepare(
            connection,
            first_intro.premise_context(),
            syntax.right_to_result,
            result_variable,
        )?;
        let selected = if choose_right { right } else { left };
        let selected_elim = ImpElim::prepare(connection, selected, result_variable)?;
        let selected_weakening =
            WeakenPlan::prepare(connection, base, second_intro.premise_context())?;
        let all_intro = AllIntroApplied::prepare(connection, syntax.predicate, result_variable)?;
        Ok(Self {
            base,
            selected,
            result_variable,
            syntax,
            first_intro,
            second_intro,
            selected_elim,
            selected_weakening,
            all_intro,
            choose_right,
        })
    }

    /// Prepares left introduction from `Gamma |- p`.
    ///
    /// # Errors
    ///
    /// Returns if the inputs are not exact closed Booleans, the result
    /// variable is not fresh, or an intermediate context cannot be defined.
    pub fn left<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        left: TermId,
        right: TermId,
        result_variable: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        Self::prepare(connection, base, left, right, result_variable, false)
    }

    /// Prepares right introduction from `Gamma |- q`.
    ///
    /// # Errors
    ///
    /// Returns if the inputs are not exact closed Booleans, the result
    /// variable is not fresh, or an intermediate context cannot be defined.
    pub fn right<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        left: TermId,
        right: TermId,
        result_variable: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        Self::prepare(connection, base, left, right, result_variable, true)
    }

    /// Introduces the exact Church disjunction without persistence.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise/context or rejected constituent LCF rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        selected: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_result(selected, self.base, self.selected)?;
        let target = self.second_intro.premise_context();
        let selected = self.selected_weakening.apply(proof, selected)?;
        let selected_implication = if self.choose_right {
            self.syntax.right_to_result
        } else {
            self.syntax.left_to_result
        };
        let implication = proof.prove_hypothesis(target, selected_implication)?;
        let result = self.selected_elim.apply(proof, &implication, &selected)?;
        let right_continuation = self.second_intro.apply(proof, &result)?;
        let body = self.first_intro.apply(proof, &right_continuation)?;
        require_result(&body, self.base, self.syntax.body)?;
        let beta = proof.conversion_beta(self.syntax.predicate, self.result_variable)?;
        let reverse = proof.conversion_symmetry(&beta)?;
        let application = proof.convert_theorem(&body, &reverse)?;
        let universal = self.all_intro.apply(proof, &application)?;
        require_result(&universal, self.base, self.syntax.proposition)?;
        Ok(universal)
    }
}

/// Prepared elimination for the exact Church disjunction.
pub struct ChurchOrElim {
    base: ContextId,
    result: TermId,
    syntax: ChurchOrSyntax,
    left_intro: ImpIntro,
    right_intro: ImpIntro,
    outer_elim: ImpElim,
    inner_elim: ImpElim,
    all_elim: AllElim,
}

impl ChurchOrElim {
    /// Prepares elimination into a closed Boolean result.
    ///
    /// # Errors
    ///
    /// Returns if an input is not a checked closed Boolean or an exact branch
    /// context cannot be defined.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        left: TermId,
        right: TermId,
        result: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        let syntax = church_or(connection, left, right, result)?;
        Ok(Self {
            base,
            result,
            left_intro: ImpIntro::prepare(connection, base, left, result)?,
            right_intro: ImpIntro::prepare(connection, base, right, result)?,
            outer_elim: ImpElim::prepare(
                connection,
                syntax.left_to_result,
                syntax.right_continuation,
            )?,
            inner_elim: ImpElim::prepare(connection, syntax.right_to_result, result)?,
            all_elim: AllElim::prepare(connection, syntax.predicate, result)?,
            syntax,
        })
    }

    /// Exact context required for the left branch.
    #[must_use]
    pub const fn left_context(&self) -> ContextId {
        self.left_intro.premise_context()
    }

    /// Exact context required for the right branch.
    #[must_use]
    pub const fn right_context(&self) -> ContextId {
        self.right_intro.premise_context()
    }

    /// Eliminates a Church disjunction using exact branch theorems.
    ///
    /// # Errors
    ///
    /// Returns for a wrong disjunction/branch shape or rejected constituent
    /// LCF rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        disjunction: &Theorem<'brand>,
        left: &Theorem<'brand>,
        right: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_result(disjunction, self.base, self.syntax.proposition)?;
        require_result(left, self.left_context(), self.result)?;
        require_result(right, self.right_context(), self.result)?;
        let left = self.left_intro.apply(proof, left)?;
        let right = self.right_intro.apply(proof, right)?;
        let application = self.all_elim.apply(proof, disjunction)?;
        let beta = proof.conversion_beta(self.syntax.predicate, self.result)?;
        let body = proof.convert_theorem(&application, &beta)?;
        let continuation = self.outer_elim.apply(proof, &body, &left)?;
        let result = self.inner_elim.apply(proof, &continuation, &right)?;
        require_result(&result, self.base, self.result)?;
        Ok(result)
    }
}

fn canonical_not<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    proposition: TermId,
) -> Result<TermId, TermError> {
    let (_, falsehood) = canonical_false(connection)?;
    connection.insert_equality(proposition, falsehood)
}

/// Prepared canonical negation introduction.
///
/// Given `Gamma union {p} |- F`, this derives
/// `Gamma minus {p} |- NOT p`, where `NOT p := p = F`. The subtraction makes
/// the exact finite-set behavior explicit when the caller's base already
/// contains the discharged proposition.
pub struct NotIntro {
    premise_context: ContextId,
    result_context: ContextId,
    falsehood: TermId,
    result: TermId,
    false_context: ContextId,
    false_elim: FalseElim,
}

impl NotIntro {
    /// Prepares canonical negation introduction from an explicit base context.
    ///
    /// # Errors
    ///
    /// Returns if the proposition is not a closed Boolean or a required exact
    /// context cannot be defined.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        base: ContextId,
        proposition: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        let (_, falsehood) = canonical_false(connection)?;
        let result = canonical_not(connection, proposition)?;
        let mut premise_members = connection.context_members(base)?;
        premise_members.push(proposition);
        let premise_context = connection.define_context(premise_members)?;
        let result_members = connection
            .context_members(base)?
            .into_iter()
            .filter(|member| *member != proposition)
            .collect::<Vec<_>>();
        let result_context = connection.define_context(result_members)?;
        let false_context = connection.define_context([falsehood])?;
        Ok(Self {
            premise_context,
            result_context,
            falsehood,
            result,
            false_context,
            false_elim: FalseElim::prepare(connection, proposition)?,
        })
    }

    /// Exact context required for the falsehood premise.
    #[must_use]
    pub const fn premise_context(&self) -> ContextId {
        self.premise_context
    }

    /// Exact post-discharge context (`base minus {p}`).
    #[must_use]
    pub const fn result_context(&self) -> ContextId {
        self.result_context
    }

    /// Introduces exact canonical negation without persistence.
    ///
    /// # Errors
    ///
    /// Returns for a wrong falsehood premise or rejected constituent LCF rule.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        falsehood: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_result(falsehood, self.premise_context, self.falsehood)?;
        let false_hypothesis = proof.prove_hypothesis(self.false_context, self.falsehood)?;
        let proposition = self.false_elim.apply(proof, &false_hypothesis)?;
        let result = proof.deduction_antisymmetry(&proposition, falsehood)?;
        require_result(&result, self.result_context, self.result)?;
        Ok(result)
    }
}

/// Prepared canonical negation elimination.
pub struct NotElim {
    proposition: TermId,
    negation: TermId,
    falsehood: TermId,
}

impl NotElim {
    /// Prepares `p`, `NOT p` elimination.
    ///
    /// # Errors
    ///
    /// Returns if `p` is not a checked closed Boolean proposition.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        let (_, falsehood) = canonical_false(connection)?;
        let negation = canonical_not(connection, proposition)?;
        Ok(Self {
            proposition,
            negation,
            falsehood,
        })
    }

    /// Eliminates same-context exact `p` and `NOT p` premises.
    ///
    /// # Errors
    ///
    /// Returns for a wrong premise/context or rejected equality modus ponens.
    pub fn apply<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
        proposition: &Theorem<'brand>,
        negation: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        require_conclusion(proposition, self.proposition)?;
        require_conclusion(negation, self.negation)?;
        let result = proof.equality_modus_ponens(negation, proposition)?;
        require_result(&result, proposition.context(), self.falsehood)?;
        Ok(result)
    }
}

fn church_or_operator<P: Policy>(connection: &mut Connection<Hol<P>>) -> Result<TermId, TermError> {
    let bool_type = connection.insert_bool_type()?;
    let left = connection.insert_bound_term(2, bool_type)?;
    let right = connection.insert_bound_term(1, bool_type)?;
    let result = connection.insert_bound_term(0, bool_type)?;
    let left_to_result = canonical_imp_open(connection, left, result)?;
    let right_to_result = canonical_imp_open(connection, right, result)?;
    let right_continuation = canonical_imp_open(connection, right_to_result, result)?;
    let body = canonical_imp_open(connection, left_to_result, right_continuation)?;
    let predicate = connection.insert_lambda(bool_type, body)?;
    let truth = connection.insert_bool_term(true)?;
    let constant_truth = connection.insert_lambda(bool_type, truth)?;
    let universal = connection.insert_equality(predicate, constant_truth)?;
    let right = connection.insert_lambda(bool_type, universal)?;
    connection.insert_lambda(bool_type, right)
}

fn normalize_church_or<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    operator: TermId,
    left: TermId,
    right: TermId,
) -> Result<covalence_nucleus::Conversion<'brand>, ProofError> {
    let first = proof.conversion_beta(operator, left)?;
    let right_reflexive = proof.conversion_reflexivity(right)?;
    let applied = proof.conversion_application(&first, &right_reflexive)?;
    let second = proof.conversion_beta(first.right(), right)?;
    proof.conversion_transitivity(&applied, &second)
}

/// Prepared Diaconescu derivation of Boolean excluded middle.
///
/// The proof uses only canonical `F`, Church disjunction, Hilbert choice,
/// function extensionality, and Leibniz-derived epsilon congruence. It adds no
/// Boolean-cases axiom, raw assumption, primitive proof rule, or persistence.
pub struct ExcludedMiddle {
    proposition: TermId,
    negation: TermId,
    result: TermId,
    truth: TermId,
    falsehood: TermId,
    operator: TermId,
    upper: TermId,
    lower: TermId,
    upper_choice: TermId,
    lower_choice: TermId,
    upper_member: TermId,
    lower_member: TermId,
    upper_seed_left: TermId,
    lower_seed_left: TermId,
    upper_equals_truth: TermId,
    lower_equals_false: TermId,
    upper_direct: TermId,
    lower_direct: TermId,
    point: TermId,
    point_equals_truth: TermId,
    point_equals_false: TermId,
    point_upper_member: TermId,
    point_lower_member: TermId,
    upper_seed_intro: ChurchOrIntro,
    lower_seed_intro: ChurchOrIntro,
    point_upper_intro: ChurchOrIntro,
    point_lower_intro: ChurchOrIntro,
    function_extensionality: FunExt,
    epsilon_congruence: EpsCongr,
    truth_upper_symmetry: EqSym,
    truth_to_lower: EqTrans,
    truth_to_false: EqTrans,
    not_truth_equals_false_intro: NotIntro,
    not_truth_equals_false_elim: NotElim,
    not_proposition_intro: NotIntro,
    result_right_intro: ChurchOrIntro,
    result_left_in_upper_context: ChurchOrIntro,
    result_left_in_upper_lower_context: ChurchOrIntro,
    upper_elimination: ChurchOrElim,
    lower_elimination: ChurchOrElim,
    empty_to_contradiction: WeakenPlan,
    empty_to_upper_case: WeakenPlan,
}

impl ExcludedMiddle {
    /// Exact proposition `p` selected at preparation time.
    #[must_use]
    pub const fn proposition(&self) -> TermId {
        self.proposition
    }

    /// Exact canonical `NOT p` node.
    #[must_use]
    pub const fn negation(&self) -> TermId {
        self.negation
    }

    /// Exact Church-encoded `p OR NOT p` conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.result
    }

    /// Prepares excluded middle for one exact closed proposition.
    ///
    /// `result_variable` is the fresh Boolean used by Church-OR introduction;
    /// `point` is a distinct fresh Boolean used for predicate extensionality.
    ///
    /// # Errors
    ///
    /// Returns if either variable is not exact/fresh, the proposition is not a
    /// closed Boolean, or an exact intermediate context cannot be prepared.
    #[expect(
        clippy::too_many_lines,
        reason = "the explicit Diaconescu plan keeps every exact intermediate coordinate auditable"
    )]
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
        result_variable: TermId,
        point: TermId,
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, proposition)?;
        require_fresh_variable(connection, result_variable, &[proposition, point])?;
        require_fresh_variable(connection, point, &[proposition, result_variable])?;
        let bool_type = connection.insert_bool_type().map_err(TermError::from)?;
        if connection.term_type(result_variable)? != bool_type
            || connection.term_type(point)? != bool_type
        {
            return Err(TermError::ApplicationTypeMismatch {
                expected: bool_type,
                actual: connection.term_type(point)?,
            }
            .into());
        }
        let truth = connection.insert_bool_term(true)?;
        let (_, falsehood) = canonical_false(connection)?;
        let negation = canonical_not(connection, proposition)?;
        let result = church_or(connection, proposition, negation, truth)?.proposition;
        let operator = church_or_operator(connection)?;

        let bound = connection.insert_bound_term(0, bool_type)?;
        let bound_equals_truth = connection.insert_equality(bound, truth)?;
        let upper_body = apply2(connection, operator, bound_equals_truth, proposition)?;
        let upper = connection.insert_lambda(bool_type, upper_body)?;
        let bound = connection.insert_bound_term(0, bool_type)?;
        let bound_equals_false = connection.insert_equality(bound, falsehood)?;
        let lower_body = apply2(connection, operator, bound_equals_false, proposition)?;
        let lower = connection.insert_lambda(bool_type, lower_body)?;
        let upper_choice = connection.insert_epsilon(upper)?;
        let lower_choice = connection.insert_epsilon(lower)?;
        let upper_member = connection.insert_application(upper, upper_choice)?;
        let lower_member = connection.insert_application(lower, lower_choice)?;
        let upper_equals_truth = connection.insert_equality(upper_choice, truth)?;
        let lower_equals_false = connection.insert_equality(lower_choice, falsehood)?;
        let upper_direct =
            church_or(connection, upper_equals_truth, proposition, truth)?.proposition;
        let lower_direct =
            church_or(connection, lower_equals_false, proposition, truth)?.proposition;

        let truth_equals_truth = connection.insert_equality(truth, truth)?;
        let false_equals_false = connection.insert_equality(falsehood, falsehood)?;
        let upper_seed_intro = ChurchOrIntro::left(
            connection,
            ContextId::empty(),
            truth_equals_truth,
            proposition,
            result_variable,
        )?;
        let lower_seed_intro = ChurchOrIntro::left(
            connection,
            ContextId::empty(),
            false_equals_false,
            proposition,
            result_variable,
        )?;

        let upper_case = connection.define_context([upper_equals_truth])?;
        let upper_proposition_case =
            connection.define_context([upper_equals_truth, proposition])?;
        let upper_lower_case =
            connection.define_context([upper_equals_truth, lower_equals_false])?;
        let contradiction_context =
            connection.define_context([upper_equals_truth, lower_equals_false, proposition])?;
        let proposition_context = connection.define_context([proposition])?;

        let point_equals_truth = connection.insert_equality(point, truth)?;
        let point_equals_false = connection.insert_equality(point, falsehood)?;
        church_or(connection, point_equals_truth, proposition, truth)?;
        church_or(connection, point_equals_false, proposition, truth)?;
        let point_upper_intro = ChurchOrIntro::right(
            connection,
            contradiction_context,
            point_equals_truth,
            proposition,
            result_variable,
        )?;
        let point_lower_intro = ChurchOrIntro::right(
            connection,
            contradiction_context,
            point_equals_false,
            proposition,
            result_variable,
        )?;
        let point_upper_member = connection.insert_application(upper, point)?;
        let point_lower_member = connection.insert_application(lower, point)?;
        let function_extensionality = FunExt::prepare(connection, upper, lower, point)?;
        let epsilon_congruence = EpsCongr::prepare(connection, upper, lower)?;
        let truth_upper_symmetry = EqSym::prepare(connection, upper_choice, truth)?;
        let truth_to_lower = EqTrans::prepare(connection, truth, upper_choice, lower_choice)?;
        let truth_to_false = EqTrans::prepare(connection, truth, lower_choice, falsehood)?;

        let truth_equals_false = connection.insert_equality(truth, falsehood)?;
        let not_truth_equals_false_intro =
            NotIntro::prepare(connection, ContextId::empty(), truth_equals_false)?;
        let not_truth_equals_false_elim = NotElim::prepare(connection, truth_equals_false)?;
        let not_proposition_intro = NotIntro::prepare(connection, upper_lower_case, proposition)?;
        if not_proposition_intro.premise_context() != contradiction_context {
            return Err(DerivedRulePreparationError::ContextNotSubset {
                source: contradiction_context,
                target: not_proposition_intro.premise_context(),
            });
        }

        let result_right_intro = ChurchOrIntro::right(
            connection,
            upper_lower_case,
            proposition,
            negation,
            result_variable,
        )?;
        let result_left_in_upper_context = ChurchOrIntro::left(
            connection,
            proposition_context,
            proposition,
            negation,
            result_variable,
        )?;
        let result_left_in_upper_lower_context = ChurchOrIntro::left(
            connection,
            upper_proposition_case,
            proposition,
            negation,
            result_variable,
        )?;
        let upper_elimination = ChurchOrElim::prepare(
            connection,
            ContextId::empty(),
            upper_equals_truth,
            proposition,
            result,
        )?;
        let lower_elimination = ChurchOrElim::prepare(
            connection,
            upper_case,
            lower_equals_false,
            proposition,
            result,
        )?;
        if upper_elimination.left_context() != upper_case
            || upper_elimination.right_context() != proposition_context
            || lower_elimination.left_context() != upper_lower_case
            || lower_elimination.right_context() != upper_proposition_case
        {
            return Err(DerivedRulePreparationError::ContextNotSubset {
                source: upper_elimination.left_context(),
                target: upper_case,
            });
        }
        let empty_to_contradiction =
            WeakenPlan::prepare(connection, ContextId::empty(), contradiction_context)?;
        let empty_to_upper_case = WeakenPlan::prepare(connection, ContextId::empty(), upper_case)?;

        Ok(Self {
            proposition,
            negation,
            result,
            truth,
            falsehood,
            operator,
            upper,
            lower,
            upper_choice,
            lower_choice,
            upper_member,
            lower_member,
            upper_seed_left: truth_equals_truth,
            lower_seed_left: false_equals_false,
            upper_equals_truth,
            lower_equals_false,
            upper_direct,
            lower_direct,
            point,
            point_equals_truth,
            point_equals_false,
            point_upper_member,
            point_lower_member,
            upper_seed_intro,
            lower_seed_intro,
            point_upper_intro,
            point_lower_intro,
            function_extensionality,
            epsilon_congruence,
            truth_upper_symmetry,
            truth_to_lower,
            truth_to_false,
            not_truth_equals_false_intro,
            not_truth_equals_false_elim,
            not_proposition_intro,
            result_right_intro,
            result_left_in_upper_context,
            result_left_in_upper_lower_context,
            upper_elimination,
            lower_elimination,
            empty_to_contradiction,
            empty_to_upper_case,
        })
    }

    /// Derives `empty |- p OR NOT p` without persistence.
    ///
    /// # Errors
    ///
    /// Returns if any exact intermediate shape/context differs or a
    /// constituent LCF rule is rejected.
    #[expect(
        clippy::too_many_lines,
        reason = "the linear proof script mirrors the checked Diaconescu derivation step for step"
    )]
    pub fn prove<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        let truth_reflexive = proof.prove_reflexivity(ContextId::empty(), self.truth)?;
        let upper_seed = self.upper_seed_intro.apply(proof, &truth_reflexive)?;
        let upper_seed_normal =
            normalize_church_or(proof, self.operator, self.upper_seed_left, self.proposition)?;
        let upper_seed_reverse = proof.conversion_symmetry(&upper_seed_normal)?;
        let upper_seed_operator = proof.convert_theorem(&upper_seed, &upper_seed_reverse)?;
        let upper_beta = proof.conversion_beta(self.upper, self.truth)?;
        let upper_beta_reverse = proof.conversion_symmetry(&upper_beta)?;
        let upper_application = proof.convert_theorem(&upper_seed_operator, &upper_beta_reverse)?;
        let upper_chosen = proof.choice(&upper_application)?;
        require_conclusion(&upper_chosen, self.upper_member)?;

        let false_reflexive = proof.prove_reflexivity(ContextId::empty(), self.falsehood)?;
        let lower_seed = self.lower_seed_intro.apply(proof, &false_reflexive)?;
        let lower_seed_normal =
            normalize_church_or(proof, self.operator, self.lower_seed_left, self.proposition)?;
        let lower_seed_reverse = proof.conversion_symmetry(&lower_seed_normal)?;
        let lower_seed_operator = proof.convert_theorem(&lower_seed, &lower_seed_reverse)?;
        let lower_beta = proof.conversion_beta(self.lower, self.falsehood)?;
        let lower_beta_reverse = proof.conversion_symmetry(&lower_beta)?;
        let lower_application = proof.convert_theorem(&lower_seed_operator, &lower_beta_reverse)?;
        let lower_chosen = proof.choice(&lower_application)?;
        require_conclusion(&lower_chosen, self.lower_member)?;

        let upper_choice_beta = proof.conversion_beta(self.upper, self.upper_choice)?;
        let upper_choice_operator = proof.convert_theorem(&upper_chosen, &upper_choice_beta)?;
        let upper_direct_normal = normalize_church_or(
            proof,
            self.operator,
            self.upper_equals_truth,
            self.proposition,
        )?;
        let upper_direct = proof.convert_theorem(&upper_choice_operator, &upper_direct_normal)?;
        require_conclusion(&upper_direct, self.upper_direct)?;

        let lower_choice_beta = proof.conversion_beta(self.lower, self.lower_choice)?;
        let lower_choice_operator = proof.convert_theorem(&lower_chosen, &lower_choice_beta)?;
        let lower_direct_normal = normalize_church_or(
            proof,
            self.operator,
            self.lower_equals_false,
            self.proposition,
        )?;
        let lower_direct = proof.convert_theorem(&lower_choice_operator, &lower_direct_normal)?;
        require_conclusion(&lower_direct, self.lower_direct)?;

        let proposition = proof.prove_hypothesis(
            self.not_proposition_intro.premise_context(),
            self.proposition,
        )?;
        let point_upper = self.point_upper_intro.apply(proof, &proposition)?;
        let point_upper_normal = normalize_church_or(
            proof,
            self.operator,
            self.point_equals_truth,
            self.proposition,
        )?;
        let point_upper_normal_reverse = proof.conversion_symmetry(&point_upper_normal)?;
        let point_upper_operator =
            proof.convert_theorem(&point_upper, &point_upper_normal_reverse)?;
        let point_upper_beta = proof.conversion_beta(self.upper, self.point)?;
        let point_upper_beta_reverse = proof.conversion_symmetry(&point_upper_beta)?;
        let point_upper_member =
            proof.convert_theorem(&point_upper_operator, &point_upper_beta_reverse)?;
        require_conclusion(&point_upper_member, self.point_upper_member)?;

        let point_lower = self.point_lower_intro.apply(proof, &proposition)?;
        let point_lower_normal = normalize_church_or(
            proof,
            self.operator,
            self.point_equals_false,
            self.proposition,
        )?;
        let point_lower_normal_reverse = proof.conversion_symmetry(&point_lower_normal)?;
        let point_lower_operator =
            proof.convert_theorem(&point_lower, &point_lower_normal_reverse)?;
        let point_lower_beta = proof.conversion_beta(self.lower, self.point)?;
        let point_lower_beta_reverse = proof.conversion_symmetry(&point_lower_beta)?;
        let point_lower_member =
            proof.convert_theorem(&point_lower_operator, &point_lower_beta_reverse)?;
        require_conclusion(&point_lower_member, self.point_lower_member)?;

        let pointwise = proof.deduction_antisymmetry(&point_upper_member, &point_lower_member)?;
        let predicates_equal = self.function_extensionality.apply(proof, &pointwise)?;
        let choices_equal = self.epsilon_congruence.apply(proof, &predicates_equal)?;
        let upper_equals_truth = proof.prove_hypothesis(
            self.not_proposition_intro.premise_context(),
            self.upper_equals_truth,
        )?;
        let truth_equals_upper = self
            .truth_upper_symmetry
            .apply(proof, &upper_equals_truth)?;
        let truth_equals_lower =
            self.truth_to_lower
                .apply(proof, &truth_equals_upper, &choices_equal)?;
        let lower_equals_false = proof.prove_hypothesis(
            self.not_proposition_intro.premise_context(),
            self.lower_equals_false,
        )?;
        let truth_equals_false =
            self.truth_to_false
                .apply(proof, &truth_equals_lower, &lower_equals_false)?;

        let truth_equals_false_hypothesis = proof.prove_hypothesis(
            self.not_truth_equals_false_intro.premise_context(),
            truth_equals_false.conclusion(),
        )?;
        let truth_in_inequality_context =
            proof.prove_truth(self.not_truth_equals_false_intro.premise_context())?;
        let canonical_false = proof
            .equality_modus_ponens(&truth_equals_false_hypothesis, &truth_in_inequality_context)?;
        let truth_not_false = self
            .not_truth_equals_false_intro
            .apply(proof, &canonical_false)?;
        let truth_not_false = self.empty_to_contradiction.apply(proof, &truth_not_false)?;
        let contradiction =
            self.not_truth_equals_false_elim
                .apply(proof, &truth_equals_false, &truth_not_false)?;
        let not_proposition = self.not_proposition_intro.apply(proof, &contradiction)?;
        let nonclassical_branch = self.result_right_intro.apply(proof, &not_proposition)?;

        let proposition_upper =
            proof.prove_hypothesis(self.result_left_in_upper_context.base, self.proposition)?;
        let proposition_branch = self
            .result_left_in_upper_context
            .apply(proof, &proposition_upper)?;
        let proposition_upper_lower = proof.prove_hypothesis(
            self.result_left_in_upper_lower_context.base,
            self.proposition,
        )?;
        let proposition_inner_branch = self
            .result_left_in_upper_lower_context
            .apply(proof, &proposition_upper_lower)?;
        let lower_direct = self.empty_to_upper_case.apply(proof, &lower_direct)?;
        let upper_branch = self.lower_elimination.apply(
            proof,
            &lower_direct,
            &nonclassical_branch,
            &proposition_inner_branch,
        )?;
        let result = self.upper_elimination.apply(
            proof,
            &upper_direct,
            &upper_branch,
            &proposition_branch,
        )?;
        require_result(&result, ContextId::empty(), self.result)?;
        Ok(result)
    }
}

/// Prepared classical quantifier duality
/// `NOT (ALL P) IMP EX (lambda x. NOT (P x))`.
///
/// `EX Q` is the existing Hilbert encoding `Q (epsilon Q)`. The proof invokes
/// [`ExcludedMiddle`] for the existential and for one fresh instance, then
/// uses only positive quantifier rules, canonical negation, and false
/// elimination.
pub struct NotAllToExistsNot {
    schematic_proposition: TermId,
    witness_variable: TermId,
    universal: TermId,
    negated_universal: TermId,
    negated_predicate: TermId,
    existential: TermId,
    negated_existential: TermId,
    instance: TermId,
    negated_instance: TermId,
    conclusion: TermId,
    implication_intro: ImpIntro,
    classical_lem: ExcludedMiddle,
    existential_lem_weakening: WeakenPlan,
    existential_cases: ChurchOrElim,
    instance_lem_weakening: WeakenPlan,
    instance_cases: ChurchOrElim,
    existential_negation_elim: NotElim,
    instance_false_elim: FalseElim,
    universal_intro: AllIntroApplied,
    universal_negation_elim: NotElim,
    existential_false_elim: FalseElim,
}

impl NotAllToExistsNot {
    /// Prepares the exact duality theorem for a closed predicate.
    ///
    /// `witness_variable` is a fresh exact `MFV` of the predicate domain.
    /// `classical_variables` supplies three distinct fresh Boolean `MFV`s: a
    /// schematic proposition plus the result and point variables for one
    /// reusable excluded-middle derivation.
    ///
    /// # Errors
    ///
    /// Returns if an input variable is not exact/fresh, `predicate` is not a
    /// closed Boolean-valued function, or exact intermediate contexts differ.
    pub fn prepare<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        predicate: TermId,
        witness_variable: TermId,
        classical_variables: [TermId; 3],
    ) -> Result<Self, DerivedRulePreparationError> {
        require_closed(connection, predicate)?;
        require_fresh_variable(connection, witness_variable, &[predicate])?;
        let truth = connection.insert_bool_term(true)?;
        let witness_type = connection.term_type(witness_variable)?;
        let constant_truth = connection.insert_lambda(witness_type, truth)?;
        let universal = connection.insert_equality(predicate, constant_truth)?;
        let negated_universal = canonical_not(connection, universal)?;

        let bound = connection.insert_bound_term(0, witness_type)?;
        let bound_instance = connection.insert_application(predicate, bound)?;
        let bound_negation = canonical_not(connection, bound_instance)?;
        let negated_predicate = connection.insert_lambda(witness_type, bound_negation)?;
        let epsilon = connection.insert_epsilon(negated_predicate)?;
        let existential = connection.insert_application(negated_predicate, epsilon)?;
        let negated_existential = canonical_not(connection, existential)?;
        let instance = connection.insert_application(predicate, witness_variable)?;
        let negated_instance = canonical_not(connection, instance)?;
        let conclusion = canonical_imp(connection, negated_universal, existential)?.1;

        let implication_intro = ImpIntro::prepare(
            connection,
            ContextId::empty(),
            negated_universal,
            existential,
        )?;
        let negated_universal_context = implication_intro.premise_context();
        let schematic_proposition = classical_variables[0];
        require_fresh_variable(
            connection,
            schematic_proposition,
            &[predicate, witness_variable],
        )?;
        let classical_lem = ExcludedMiddle::prepare(
            connection,
            schematic_proposition,
            classical_variables[1],
            classical_variables[2],
        )?;
        let existential_lem_weakening =
            WeakenPlan::prepare(connection, ContextId::empty(), negated_universal_context)?;
        let existential_cases = ChurchOrElim::prepare(
            connection,
            negated_universal_context,
            existential,
            negated_existential,
            existential,
        )?;
        let instance_base = existential_cases.right_context();
        let instance_lem_weakening =
            WeakenPlan::prepare(connection, ContextId::empty(), instance_base)?;
        let instance_cases = ChurchOrElim::prepare(
            connection,
            instance_base,
            instance,
            negated_instance,
            instance,
        )?;
        let existential_negation_elim = NotElim::prepare(connection, existential)?;
        let instance_false_elim = FalseElim::prepare(connection, instance)?;
        let universal_intro = AllIntroApplied::prepare(connection, predicate, witness_variable)?;
        let universal_negation_elim = NotElim::prepare(connection, universal)?;
        let existential_false_elim = FalseElim::prepare(connection, existential)?;
        Ok(Self {
            schematic_proposition,
            witness_variable,
            universal,
            negated_universal,
            negated_predicate,
            existential,
            negated_existential,
            instance,
            negated_instance,
            conclusion,
            implication_intro,
            classical_lem,
            existential_lem_weakening,
            existential_cases,
            instance_lem_weakening,
            instance_cases,
            existential_negation_elim,
            instance_false_elim,
            universal_intro,
            universal_negation_elim,
            existential_false_elim,
        })
    }

    /// Exact canonical duality conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Exact encoded existential `Q (epsilon Q)`.
    #[must_use]
    pub const fn existential(&self) -> TermId {
        self.existential
    }

    /// Derives the empty-context duality theorem without persistence.
    ///
    /// # Errors
    ///
    /// Returns if an exact intermediate theorem/context differs or a
    /// constituent LCF rule is rejected.
    pub fn prove<'brand, P: Policy>(
        &self,
        proof: &mut ProofSession<'brand, P>,
    ) -> Result<Theorem<'brand>, DerivedRuleError> {
        let classical_lem = self.classical_lem.prove(proof)?;
        let existential_lem = proof.instantiate_terms(
            &classical_lem,
            &[covalence_nucleus::TermInstantiation {
                variable: self.schematic_proposition,
                replacement: self.existential,
            }],
        )?;
        let existential_lem = self
            .existential_lem_weakening
            .apply(proof, &existential_lem)?;
        let existential_branch =
            proof.prove_hypothesis(self.existential_cases.left_context(), self.existential)?;

        let instance_lem = proof.instantiate_terms(
            &classical_lem,
            &[covalence_nucleus::TermInstantiation {
                variable: self.schematic_proposition,
                replacement: self.instance,
            }],
        )?;
        let instance_lem = self.instance_lem_weakening.apply(proof, &instance_lem)?;
        let instance_branch =
            proof.prove_hypothesis(self.instance_cases.left_context(), self.instance)?;

        let negated_instance =
            proof.prove_hypothesis(self.instance_cases.right_context(), self.negated_instance)?;
        let negated_predicate_beta =
            proof.conversion_beta(self.negated_predicate, self.witness_variable)?;
        let negated_predicate_beta_reverse = proof.conversion_symmetry(&negated_predicate_beta)?;
        let negated_predicate_instance =
            proof.convert_theorem(&negated_instance, &negated_predicate_beta_reverse)?;
        let existential = proof.choice(&negated_predicate_instance)?;
        require_conclusion(&existential, self.existential)?;
        let negated_existential = proof.prove_hypothesis(
            self.instance_cases.right_context(),
            self.negated_existential,
        )?;
        let falsehood =
            self.existential_negation_elim
                .apply(proof, &existential, &negated_existential)?;
        let instance_from_false = self.instance_false_elim.apply(proof, &falsehood)?;
        let instance = self.instance_cases.apply(
            proof,
            &instance_lem,
            &instance_branch,
            &instance_from_false,
        )?;
        let universal = self.universal_intro.apply(proof, &instance)?;
        require_conclusion(&universal, self.universal)?;
        let negated_universal = proof.prove_hypothesis(
            self.existential_cases.right_context(),
            self.negated_universal,
        )?;
        let falsehood =
            self.universal_negation_elim
                .apply(proof, &universal, &negated_universal)?;
        let existential_from_false = self.existential_false_elim.apply(proof, &falsehood)?;
        let existential = self.existential_cases.apply(
            proof,
            &existential_lem,
            &existential_branch,
            &existential_from_false,
        )?;
        let result = self.implication_intro.apply(proof, &existential)?;
        require_result(&result, ContextId::empty(), self.conclusion)?;
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

    #[test]
    fn canonical_false_elimination_and_epsilon_congruence_stay_above_lcf() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let (identity, falsehood) = canonical_false(&mut connection).unwrap();
        let arbitrary = connection.insert_equality(truth, falsehood).unwrap();
        let false_context = connection.define_context([falsehood]).unwrap();
        let false_elim = FalseElim::prepare(&mut connection, arbitrary).unwrap();

        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity_applied = connection.insert_application(identity, bound).unwrap();
        let expanded_identity = connection
            .insert_lambda(bool_type, identity_applied)
            .unwrap();
        let expanded_epsilon = connection.insert_epsilon(expanded_identity).unwrap();
        let identity_epsilon = connection.insert_epsilon(identity).unwrap();
        let epsilon_equality = connection
            .insert_equality(expanded_epsilon, identity_epsilon)
            .unwrap();
        let epsilon_congruence =
            EpsCongr::prepare(&mut connection, expanded_identity, identity).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let falsehood = proof.prove_hypothesis(false_context, falsehood)?;
                let eliminated = false_elim.apply(&mut proof, &falsehood).unwrap();
                assert_eq!(eliminated.context(), false_context);
                assert_eq!(eliminated.conclusion(), arbitrary);

                let eta = proof.conversion_eta(identity)?;
                assert_eq!(eta.left(), expanded_identity);
                let predicates_equal = proof.prove_conversion_equality(ContextId::empty(), &eta)?;
                let epsilons_equal = epsilon_congruence
                    .apply(&mut proof, &predicates_equal)
                    .unwrap();
                assert_eq!(epsilons_equal.context(), ContextId::empty());
                assert_eq!(epsilons_equal.conclusion(), epsilon_equality);
                Ok::<_, ProofError>(())
            })
            .unwrap();

        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 0);
    }

    #[test]
    fn church_or_introduction_and_elimination_preserve_exact_contexts() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let p = connection.insert_application(identity, truth).unwrap();
        let q = connection.insert_equality(truth, truth).unwrap();
        let result_variable = connection.insert_free_term(8801, bool_type).unwrap();
        let syntax = church_or(&mut connection, p, q, truth).unwrap();
        let left_intro =
            ChurchOrIntro::left(&mut connection, ContextId::empty(), p, q, result_variable)
                .unwrap();
        let right_intro =
            ChurchOrIntro::right(&mut connection, ContextId::empty(), p, q, result_variable)
                .unwrap();
        let elimination =
            ChurchOrElim::prepare(&mut connection, ContextId::empty(), p, q, truth).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let beta = proof.conversion_beta(identity, truth)?;
                let reverse = proof.conversion_symmetry(&beta)?;
                let truth_empty = proof.prove_truth(ContextId::empty())?;
                let p_empty = proof.convert_theorem(&truth_empty, &reverse)?;
                let left_or = left_intro.apply(&mut proof, &p_empty).unwrap();
                assert_eq!(left_or.context(), ContextId::empty());
                assert_eq!(left_or.conclusion(), syntax.proposition);

                let q_empty = proof.prove_reflexivity(ContextId::empty(), truth)?;
                let right_or = right_intro.apply(&mut proof, &q_empty).unwrap();
                assert_eq!(right_or.conclusion(), syntax.proposition);

                let left_branch = proof.prove_truth(elimination.left_context())?;
                let right_branch = proof.prove_truth(elimination.right_context())?;
                let eliminated = elimination
                    .apply(&mut proof, &left_or, &left_branch, &right_branch)
                    .unwrap();
                assert_eq!(eliminated.context(), ContextId::empty());
                assert_eq!(eliminated.conclusion(), truth);
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn canonical_negation_derives_true_not_equal_false() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let (_, falsehood) = canonical_false(&mut connection).unwrap();
        let truth_equals_false = connection.insert_equality(truth, falsehood).unwrap();
        let not_truth_equals_false = canonical_not(&mut connection, truth_equals_false).unwrap();
        let introduction =
            NotIntro::prepare(&mut connection, ContextId::empty(), truth_equals_false).unwrap();
        assert_eq!(introduction.result_context(), ContextId::empty());
        let elimination = NotElim::prepare(&mut connection, truth_equals_false).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let equality =
                    proof.prove_hypothesis(introduction.premise_context(), truth_equals_false)?;
                let truth = proof.prove_truth(introduction.premise_context())?;
                let falsehood = proof.equality_modus_ponens(&equality, &truth)?;
                let inequality = introduction.apply(&mut proof, &falsehood).unwrap();
                assert_eq!(inequality.context(), ContextId::empty());
                assert_eq!(inequality.conclusion(), not_truth_equals_false);

                // `NotElim` is exercised in a context where both exact premises
                // are available; no judgement is persisted.
                let both =
                    proof.prove_hypothesis(introduction.premise_context(), truth_equals_false)?;
                let inequality = WeakenPlan {
                    source: ContextId::empty(),
                    target: introduction.premise_context(),
                    members: Vec::new(),
                }
                .apply(&mut proof, &inequality)?;
                let contradiction = elimination.apply(&mut proof, &both, &inequality).unwrap();
                assert_eq!(contradiction.conclusion(), falsehood.conclusion());
                Ok::<_, DerivedRuleError>(())
            })
            .unwrap();
    }

    #[test]
    fn diaconescu_derives_excluded_middle_without_bool_cases_or_persistence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let proposition = connection.insert_application(identity, truth).unwrap();
        let result_variable = connection.insert_free_term(8811, bool_type).unwrap();
        let point = connection.insert_free_term(8812, bool_type).unwrap();
        let excluded_middle =
            ExcludedMiddle::prepare(&mut connection, proposition, result_variable, point).unwrap();

        connection.with_proof_session(|mut proof| {
            let theorem = excluded_middle.prove(&mut proof).unwrap();
            assert_eq!(theorem.context(), ContextId::empty());
            assert_eq!(theorem.conclusion(), excluded_middle.result);
        });
        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 0);
    }

    #[test]
    fn classical_not_all_to_exists_not_is_derived_without_persistence() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let predicate = connection.insert_lambda(bool_type, bound).unwrap();
        let witness = connection.insert_free_term(8820, bool_type).unwrap();
        let classical_variables = [
            connection.insert_free_term(8821, bool_type).unwrap(),
            connection.insert_free_term(8822, bool_type).unwrap(),
            connection.insert_free_term(8823, bool_type).unwrap(),
        ];
        let duality =
            NotAllToExistsNot::prepare(&mut connection, predicate, witness, classical_variables)
                .unwrap();

        connection.with_proof_session(|mut proof| {
            let theorem = duality.prove(&mut proof).unwrap();
            assert_eq!(theorem.context(), ContextId::empty());
            assert_eq!(theorem.conclusion(), duality.conclusion());
        });
        let snapshot = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(snapshot.image().counts().untrusted_judgement_rows, 0);
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
