use std::{error::Error, fmt};

use crate::{
    CheckError, Expr, SubstError, Tree, check_closed, check_type, open_bound, substitution::weaken,
};

/// Failure of a primitive term-equality rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleError {
    /// A premise was ill scoped, ill kinded, or ill typed.
    Check(CheckError),
    /// A locally nameless operation failed on an extreme raw index.
    Substitution(SubstError),
    /// Premises belong to different bound contexts.
    ContextMismatch,
    /// Equality types do not agree.
    EqualityTypeMismatch,
    /// Transitivity premises have different middle terms.
    TransitivityMismatch,
    /// Application congruence did not receive a function equality.
    ExpectedFunctionEquality,
    /// The lambda rule did not receive an equality under the requested binder.
    BinderMismatch,
}

impl fmt::Display for RuleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Check(error) => error.fmt(formatter),
            Self::Substitution(error) => error.fmt(formatter),
            Self::ContextMismatch => formatter.write_str("equality contexts do not match"),
            Self::EqualityTypeMismatch => formatter.write_str("equality types do not match"),
            Self::TransitivityMismatch => {
                formatter.write_str("transitivity middle terms do not match")
            }
            Self::ExpectedFunctionEquality => {
                formatter.write_str("expected an equality between functions")
            }
            Self::BinderMismatch => formatter.write_str("lambda binder does not match context"),
        }
    }
}

impl Error for RuleError {}

impl From<CheckError> for RuleError {
    fn from(error: CheckError) -> Self {
        Self::Check(error)
    }
}

impl From<SubstError> for RuleError {
    fn from(error: SubstError) -> Self {
        Self::Substitution(error)
    }
}

/// Opaque certificate of ordinary HOL term equality.
///
/// Fields are private: certificates are available only through checked rules.
#[derive(Clone, Debug)]
pub struct TermEq {
    bound: Vec<Tree>,
    left: Tree,
    right: Tree,
    r#type: Tree,
}

impl TermEq {
    /// Reflexivity for a closed, well-typed term.
    ///
    /// # Errors
    ///
    /// Returns a checking error for malformed syntax.
    pub fn refl(term: Tree) -> Result<Self, RuleError> {
        Self::refl_in(Vec::new(), term)
    }

    /// Reflexivity under an explicit bound-variable context.
    ///
    /// This constructor supports lambda congruence without exposing theorem
    /// hypotheses or free-variable contexts.
    ///
    /// # Errors
    ///
    /// Returns a checking error for malformed context types or terms.
    pub fn refl_in(bound: Vec<Tree>, term: Tree) -> Result<Self, RuleError> {
        for r#type in &bound {
            check_type(r#type)?;
        }
        let r#type = crate::check::infer(&term, &bound)?;
        Ok(Self {
            bound,
            left: term.clone(),
            right: term,
            r#type,
        })
    }

    /// Symmetry.
    #[must_use]
    pub fn symm(&self) -> Self {
        Self {
            bound: self.bound.clone(),
            left: self.right.clone(),
            right: self.left.clone(),
            r#type: self.r#type.clone(),
        }
    }

    /// Transitivity.
    ///
    /// # Errors
    ///
    /// Rejects different contexts, types, or middle terms.
    pub fn trans(&self, next: &Self) -> Result<Self, RuleError> {
        self.require_same_context(next)?;
        if self.r#type != next.r#type {
            return Err(RuleError::EqualityTypeMismatch);
        }
        if self.right != next.left {
            return Err(RuleError::TransitivityMismatch);
        }
        Ok(Self {
            bound: self.bound.clone(),
            left: self.left.clone(),
            right: next.right.clone(),
            r#type: self.r#type.clone(),
        })
    }

    /// Application congruence.
    ///
    /// # Errors
    ///
    /// Rejects context/type mismatches and non-function premises.
    pub fn app(function: &Self, argument: &Self) -> Result<Self, RuleError> {
        function.require_same_context(argument)?;
        let Expr::Arr(function_type) = function.r#type.expr() else {
            return Err(RuleError::ExpectedFunctionEquality);
        };
        if function_type.domain != argument.r#type {
            return Err(RuleError::EqualityTypeMismatch);
        }
        Ok(Self {
            bound: function.bound.clone(),
            left: Tree::app(function.left.clone(), argument.left.clone()),
            right: Tree::app(function.right.clone(), argument.right.clone()),
            r#type: function_type.codomain.clone(),
        })
    }

    /// Successor congruence.
    ///
    /// # Errors
    ///
    /// Rejects an equality not at the individual type.
    pub fn succ(value: &Self) -> Result<Self, RuleError> {
        if value.r#type != Tree::ind_ty() {
            return Err(RuleError::EqualityTypeMismatch);
        }
        Ok(Self {
            bound: value.bound.clone(),
            left: Tree::succ(value.left.clone()),
            right: Tree::succ(value.right.clone()),
            r#type: Tree::ind_ty(),
        })
    }

    /// Lambda congruence, discharging the newest bound context entry.
    ///
    /// # Errors
    ///
    /// Rejects a missing or different binder.
    pub fn lam(domain: Tree, body: &Self) -> Result<Self, RuleError> {
        check_type(&domain)?;
        let Some((first, outer)) = body.bound.split_first() else {
            return Err(RuleError::BinderMismatch);
        };
        if *first != domain {
            return Err(RuleError::BinderMismatch);
        }
        Ok(Self {
            bound: outer.to_vec(),
            left: Tree::lam(domain.clone(), body.left.clone()),
            right: Tree::lam(domain.clone(), body.right.clone()),
            r#type: Tree::arr(domain, body.r#type.clone()),
        })
    }

    /// Closed beta equality `(fun x => body) argument = body[argument/x]`.
    ///
    /// # Errors
    ///
    /// Rejects an ill-typed body, argument, or opened result.
    pub fn beta(domain: Tree, body: Tree, argument: Tree) -> Result<Self, RuleError> {
        check_type(&domain)?;
        let body_type = crate::check::infer(&body, std::slice::from_ref(&domain))?;
        crate::check::check_expected(&argument, &[], &domain)?;
        let opened = open_bound(&body, &argument)?;
        crate::check::check_expected(&opened, &[], &body_type)?;
        Ok(Self {
            bound: Vec::new(),
            left: Tree::app(Tree::lam(domain, body), argument),
            right: opened,
            r#type: body_type,
        })
    }

    /// Closed eta equality `fun x => f x = f`.
    ///
    /// # Errors
    ///
    /// Rejects a non-function or ill-typed closed term.
    pub fn eta(function: Tree) -> Result<Self, RuleError> {
        let function_type = check_closed(&function)?;
        let Expr::Arr(parts) = function_type.expr() else {
            return Err(RuleError::ExpectedFunctionEquality);
        };
        let eta = Tree::lam(
            parts.domain.clone(),
            Tree::app(weaken(&function)?, Tree::bound(0)),
        );
        crate::check::check_expected(&eta, &[], &function_type)?;
        Ok(Self {
            bound: Vec::new(),
            left: eta,
            right: function,
            r#type: function_type,
        })
    }

    /// Bound context associated with the certificate.
    #[must_use]
    pub fn bound(&self) -> &[Tree] {
        &self.bound
    }

    /// Left side.
    #[must_use]
    pub const fn left(&self) -> &Tree {
        &self.left
    }

    /// Right side.
    #[must_use]
    pub const fn right(&self) -> &Tree {
        &self.right
    }

    /// Equality type.
    #[must_use]
    pub const fn r#type(&self) -> &Tree {
        &self.r#type
    }

    fn require_same_context(&self, other: &Self) -> Result<(), RuleError> {
        if self.bound == other.bound {
            Ok(())
        } else {
            Err(RuleError::ContextMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity(r#type: Tree) -> Tree {
        Tree::lam(r#type, Tree::bound(0))
    }

    #[test]
    fn ordinary_equality_rules_construct_expected_conclusions() {
        let truth = Tree::bool(true);
        let refl = TermEq::refl(truth.clone()).expect("refl");
        let symm = refl.symm();
        let trans = symm.trans(&refl).expect("trans");
        assert_eq!(trans.left(), &truth);
        assert_eq!(trans.right(), &truth);

        let function = TermEq::refl(identity(Tree::bool_ty())).expect("function refl");
        let argument = TermEq::refl(truth.clone()).expect("argument refl");
        let application = TermEq::app(&function, &argument).expect("app congruence");
        assert_eq!(application.r#type(), &Tree::bool_ty());

        let successor = TermEq::succ(&TermEq::refl(Tree::zero()).expect("zero refl"))
            .expect("successor congruence");
        assert_eq!(successor.left(), &Tree::succ(Tree::zero()));
    }

    #[test]
    fn lambda_beta_and_eta_rules_check_binders() {
        let body = TermEq::refl_in(vec![Tree::bool_ty()], Tree::bound(0)).expect("body");
        let lambda = TermEq::lam(Tree::bool_ty(), &body).expect("lambda");
        assert!(lambda.bound().is_empty());

        let beta = TermEq::beta(Tree::bool_ty(), Tree::bound(0), Tree::bool(true)).expect("beta");
        assert_eq!(beta.right(), &Tree::bool(true));

        let function = identity(Tree::bool_ty());
        let eta = TermEq::eta(function.clone()).expect("eta");
        assert_eq!(eta.right(), &function);
    }

    #[test]
    fn rules_reject_mismatched_premises() {
        let truth = TermEq::refl(Tree::bool(true)).expect("truth");
        let zero = TermEq::refl(Tree::zero()).expect("zero");
        assert!(matches!(
            truth.trans(&zero),
            Err(RuleError::EqualityTypeMismatch)
        ));
        assert!(matches!(
            TermEq::app(&truth, &truth),
            Err(RuleError::ExpectedFunctionEquality)
        ));
        assert!(matches!(
            TermEq::lam(Tree::ind_ty(), &truth),
            Err(RuleError::BinderMismatch)
        ));
    }
}
