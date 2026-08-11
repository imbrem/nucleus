use std::{error::Error, fmt};

use crate::{
    CheckError, Expr, RuleError, SubstError, TermEq, Tree, check_closed, check_type, open_bound,
};

/// Failure of a closed HOL theorem rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TheoremError {
    /// A supplied term was ill scoped, ill kinded, or ill typed.
    Check(CheckError),
    /// A term-equality premise was invalid for the requested rule.
    Equality(RuleError),
    /// Opening a subtype predicate failed.
    Substitution(SubstError),
    /// A premise conclusion did not have the required syntactic form.
    PremiseMismatch,
    /// A term equality was not closed or was not at Boolean type.
    ExpectedClosedBooleanEquality,
}

impl fmt::Display for TheoremError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Check(error) => error.fmt(formatter),
            Self::Equality(error) => error.fmt(formatter),
            Self::Substitution(error) => error.fmt(formatter),
            Self::PremiseMismatch => formatter.write_str("theorem premise does not match rule"),
            Self::ExpectedClosedBooleanEquality => {
                formatter.write_str("expected a closed Boolean term equality")
            }
        }
    }
}

impl Error for TheoremError {}

impl From<CheckError> for TheoremError {
    fn from(error: CheckError) -> Self {
        Self::Check(error)
    }
}

impl From<RuleError> for TheoremError {
    fn from(error: RuleError) -> Self {
        Self::Equality(error)
    }
}

impl From<SubstError> for TheoremError {
    fn from(error: SubstError) -> Self {
        Self::Substitution(error)
    }
}

/// Opaque theorem that a closed Boolean term is true under no hypotheses.
///
/// There is no public constructor and this type is never deserialized. The
/// current kernel deliberately postpones general free-variable and hypothesis
/// contexts.
#[derive(Clone, Debug)]
pub struct Theorem {
    conclusion: Tree,
}

impl Theorem {
    /// Truth introduction: `|- true`.
    #[must_use]
    pub fn truth() -> Self {
        Self {
            conclusion: Tree::bool(true),
        }
    }

    /// Boolean equality reflexivity for any closed well-typed term.
    ///
    /// # Errors
    ///
    /// Returns a checking error for an open or ill-typed term.
    pub fn eq_refl(term: Tree) -> Result<Self, TheoremError> {
        let r#type = check_closed(&term)?;
        Self::checked(Tree::eqn(r#type, term.clone(), term))
    }

    /// Equality modus ponens.
    ///
    /// From `|- x = y` and `|- predicate x`, derives `|- predicate y`.
    ///
    /// # Errors
    ///
    /// Rejects premises with the wrong shape, predicate, or types.
    pub fn eq_mp(predicate: Tree, equality: &Self, premise: &Self) -> Result<Self, TheoremError> {
        let Expr::Eqn(eqn) = equality.conclusion.expr() else {
            return Err(TheoremError::PremiseMismatch);
        };
        check_type(&eqn.r#type)?;
        let predicate_type = Tree::arr(eqn.r#type.clone(), Tree::bool_ty());
        if check_closed(&predicate)? != predicate_type {
            return Err(TheoremError::PremiseMismatch);
        }
        if premise.conclusion != Tree::app(predicate.clone(), eqn.left.clone()) {
            return Err(TheoremError::PremiseMismatch);
        }
        Self::checked(Tree::app(predicate, eqn.right.clone()))
    }

    /// Hilbert choice.
    ///
    /// From `|- predicate witness`, derives `|- predicate (eps predicate)`.
    ///
    /// # Errors
    ///
    /// Rejects ill-typed inputs or a premise with a different conclusion.
    pub fn choice(predicate: Tree, witness: Tree, premise: &Self) -> Result<Self, TheoremError> {
        let predicate_type = check_closed(&predicate)?;
        let Expr::Arr(parts) = predicate_type.expr() else {
            return Err(TheoremError::PremiseMismatch);
        };
        if parts.codomain != Tree::bool_ty()
            || check_closed(&witness)? != parts.domain
            || premise.conclusion != Tree::app(predicate.clone(), witness)
        {
            return Err(TheoremError::PremiseMismatch);
        }
        Self::checked(Tree::app(
            predicate.clone(),
            Tree::eps(parts.domain.clone(), predicate),
        ))
    }

    /// Converts a theorem along a closed Boolean term equality.
    ///
    /// # Errors
    ///
    /// Rejects an open/non-Boolean equality or the wrong left conclusion.
    pub fn convert(equality: &TermEq, theorem: &Self) -> Result<Self, TheoremError> {
        if !equality.bound().is_empty() || equality.r#type() != &Tree::bool_ty() {
            return Err(TheoremError::ExpectedClosedBooleanEquality);
        }
        if equality.left() != &theorem.conclusion {
            return Err(TheoremError::PremiseMismatch);
        }
        Self::checked(equality.right().clone())
    }

    /// Introduces Boolean equality from a closed term-equality certificate.
    ///
    /// # Errors
    ///
    /// Rejects an equality under a bound context.
    pub fn eq_of_term_eq(equality: &TermEq) -> Result<Self, TheoremError> {
        if !equality.bound().is_empty() {
            return Err(TheoremError::ExpectedClosedBooleanEquality);
        }
        Self::checked(Tree::eqn(
            equality.r#type().clone(),
            equality.left().clone(),
            equality.right().clone(),
        ))
    }

    /// Subtype abstraction/representation identity: `ABS (REP x) = x`.
    ///
    /// # Errors
    ///
    /// Rejects a value not having a well-formed subtype type.
    pub fn abs_rep(value: Tree) -> Result<Self, TheoremError> {
        let subtype = check_closed(&value)?;
        let Expr::Sub(parts) = subtype.expr() else {
            return Err(TheoremError::PremiseMismatch);
        };
        let represented = Tree::rep(
            parts.carrier.clone(),
            parts.predicate.clone(),
            value.clone(),
        );
        let abstracted = Tree::abs(parts.carrier.clone(), parts.predicate.clone(), represented);
        Self::checked(Tree::eqn(subtype, abstracted, value))
    }

    /// Predicate-guarded subtype representation/abstraction identity.
    ///
    /// From the instantiated predicate theorem, derives `REP (ABS x) = x`.
    ///
    /// # Errors
    ///
    /// Rejects malformed types/predicates/values or a different premise.
    pub fn rep_abs(
        carrier: Tree,
        predicate: Tree,
        value: Tree,
        premise: &Self,
    ) -> Result<Self, TheoremError> {
        check_type(&Tree::subtype(carrier.clone(), predicate.clone()))?;
        if check_closed(&value)? != carrier {
            return Err(TheoremError::PremiseMismatch);
        }
        let instantiated = open_bound(&predicate, &value)?;
        if premise.conclusion != instantiated {
            return Err(TheoremError::PremiseMismatch);
        }
        let abstracted = Tree::abs(carrier.clone(), predicate.clone(), value.clone());
        let represented = Tree::rep(carrier.clone(), predicate, abstracted);
        Self::checked(Tree::eqn(carrier, represented, value))
    }

    /// Injectivity of successor.
    ///
    /// # Errors
    ///
    /// Rejects a premise not shaped as `succ x = succ y` at `ind`.
    pub fn succ_injective(premise: &Self) -> Result<Self, TheoremError> {
        let Expr::Eqn(eqn) = premise.conclusion.expr() else {
            return Err(TheoremError::PremiseMismatch);
        };
        let (Expr::Succ(left), Expr::Succ(right)) = (eqn.left.expr(), eqn.right.expr()) else {
            return Err(TheoremError::PremiseMismatch);
        };
        if eqn.r#type != Tree::ind_ty() {
            return Err(TheoremError::PremiseMismatch);
        }
        Self::checked(Tree::eqn(
            Tree::ind_ty(),
            left.value.clone(),
            right.value.clone(),
        ))
    }

    /// Infinity axiom: zero is not a successor.
    ///
    /// # Errors
    ///
    /// Rejects a value not having type `ind`.
    pub fn zero_not_succ(value: Tree) -> Result<Self, TheoremError> {
        if check_closed(&value)? != Tree::ind_ty() {
            return Err(TheoremError::PremiseMismatch);
        }
        Self::checked(Tree::eqn(
            Tree::bool_ty(),
            Tree::eqn(Tree::ind_ty(), Tree::zero(), Tree::succ(value)),
            Tree::bool(false),
        ))
    }

    /// The closed Boolean conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> &Tree {
        &self.conclusion
    }

    fn checked(conclusion: Tree) -> Result<Self, TheoremError> {
        if check_closed(&conclusion)? == Tree::bool_ty() {
            Ok(Self { conclusion })
        } else {
            Err(TheoremError::PremiseMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn beta_premise(predicate: &Tree, argument: Tree) -> Theorem {
        let Expr::Lam(lambda) = predicate.expr() else {
            panic!("test predicate must be a lambda")
        };
        let beta =
            TermEq::beta(lambda.domain.clone(), lambda.body.clone(), argument).expect("beta");
        Theorem::convert(&beta.symm(), &Theorem::truth()).expect("beta premise")
    }

    #[test]
    fn truth_reflexivity_conversion_and_equality_mp() {
        let truth = Theorem::truth();
        assert_eq!(truth.conclusion(), &Tree::bool(true));

        let equality = Theorem::eq_refl(Tree::bool(true)).expect("equality theorem");
        let predicate = Tree::lam(Tree::bool_ty(), Tree::bound(0));
        let predicate_truth = beta_premise(&predicate, Tree::bool(true));
        let result =
            Theorem::eq_mp(predicate.clone(), &equality, &predicate_truth).expect("equality mp");
        assert_eq!(result.conclusion(), &Tree::app(predicate, Tree::bool(true)));

        let beta = TermEq::beta(Tree::bool_ty(), Tree::bound(0), Tree::bool(true)).expect("beta");
        let beta_theorem = Theorem::eq_of_term_eq(&beta).expect("equality introduction");
        assert!(matches!(beta_theorem.conclusion().expr(), Expr::Eqn(_)));
    }

    #[test]
    fn choice_and_subtype_rules_construct_closed_theorems() {
        let choice_predicate = Tree::lam(Tree::ind_ty(), Tree::bool(true));
        let premise = beta_premise(&choice_predicate, Tree::zero());
        let choice = Theorem::choice(choice_predicate, Tree::zero(), &premise).expect("choice");
        assert_eq!(
            check_closed(choice.conclusion()).expect("closed"),
            Tree::bool_ty()
        );

        let predicate = Tree::eqn(Tree::ind_ty(), Tree::bound(0), Tree::zero());
        let value = Tree::zero();
        let predicate_theorem = Theorem::eq_refl(value.clone()).expect("predicate theorem");
        let rep_abs = Theorem::rep_abs(
            Tree::ind_ty(),
            predicate.clone(),
            value.clone(),
            &predicate_theorem,
        )
        .expect("rep abs");
        assert_eq!(
            check_closed(rep_abs.conclusion()).expect("closed"),
            Tree::bool_ty()
        );

        let subtype_value = Tree::abs(Tree::ind_ty(), predicate, value);
        Theorem::abs_rep(subtype_value).expect("abs rep");
    }

    #[test]
    fn infinity_rules_construct_expected_theorems() {
        let successor_equality =
            TermEq::succ(&TermEq::refl(Tree::zero()).expect("refl")).expect("succ congruence");
        let premise = Theorem::eq_of_term_eq(&successor_equality).expect("premise");
        let injective = Theorem::succ_injective(&premise).expect("injective");
        assert_eq!(
            injective.conclusion(),
            &Tree::eqn(Tree::ind_ty(), Tree::zero(), Tree::zero())
        );

        Theorem::zero_not_succ(Tree::zero()).expect("zero not successor");
    }

    #[test]
    fn rules_reject_wrong_premises() {
        assert!(matches!(
            Theorem::choice(Tree::bool(true), Tree::bool(true), &Theorem::truth()),
            Err(TheoremError::PremiseMismatch)
        ));
        assert!(matches!(
            Theorem::succ_injective(&Theorem::truth()),
            Err(TheoremError::PremiseMismatch)
        ));
    }
}
