//! Target-independent fold over validated IL premises.

use covalence_data_spectec::{IlBinding, IlIteration, IlPremise};

use crate::{ExpressionAlgebra, fold_expression};

/// Already-folded semantic children of one premise.
pub enum PremiseChildren<'a, Expression, Premise> {
    /// A relation invocation, including its locally bound rule body.
    Rule {
        /// Nested rule bindings in source order.
        bindings: &'a [IlBinding<'a>],
        /// Folded relation conclusion.
        conclusion: Expression,
        /// Folded nested premises in source order.
        premises: Vec<Premise>,
    },
    /// A boolean side condition.
    If(Expression),
    /// A pattern binding.
    Let {
        /// Folded binding pattern.
        left: Expression,
        /// Folded bound expression.
        right: Expression,
    },
    /// A fallback clause marker.
    Otherwise,
    /// An iterated premise and its named domain expressions.
    Iterated {
        /// Folded repeated premise.
        premise: Box<Premise>,
        /// Structural iteration shape.
        iteration: &'a IlIteration<'a>,
        /// Folded named domains in source order.
        domains: Vec<(&'a str, Expression)>,
    },
}

/// Algebra receiving each premise after all semantic children.
pub trait PremiseAlgebra<Expression> {
    /// Target premise produced by one node.
    type Premise;
    /// Target-specific or schema failure.
    type Error;

    /// Combines one premise with its already-folded children.
    ///
    /// # Errors
    ///
    /// Returns a target-specific failure when the premise cannot be lowered.
    fn premise(
        &mut self,
        source: &IlPremise<'_>,
        children: PremiseChildren<'_, Expression, Self::Premise>,
    ) -> Result<Self::Premise, Self::Error>;
}

/// Folds one complete premise bottom-up with caller-supplied algebras.
///
/// # Errors
///
/// Returns the first expression, schema, or target premise failure.
pub fn fold_premise<E, P>(
    premise: &IlPremise<'_>,
    expressions: &mut E,
    premises: &mut P,
) -> Result<P::Premise, P::Error>
where
    E: ExpressionAlgebra,
    P: PremiseAlgebra<E::Term, Error = E::Error>,
{
    let children = match premise {
        IlPremise::Rule(rule) => PremiseChildren::Rule {
            bindings: rule.bindings(),
            conclusion: fold_expression(rule.conclusion(), expressions)?,
            premises: rule
                .premises()
                .iter()
                .map(|child| fold_premise(child, expressions, premises))
                .collect::<Result<Vec<_>, _>>()?,
        },
        IlPremise::If(expression) => PremiseChildren::If(fold_expression(expression, expressions)?),
        IlPremise::Let { left, right } => PremiseChildren::Let {
            left: fold_expression(left, expressions)?,
            right: fold_expression(right, expressions)?,
        },
        IlPremise::Otherwise => PremiseChildren::Otherwise,
        IlPremise::Iterated {
            premise,
            iteration,
            domains,
        } => PremiseChildren::Iterated {
            premise: Box::new(fold_premise(premise, expressions, premises)?),
            iteration,
            domains: domains
                .iter()
                .map(|domain| {
                    fold_expression(domain.expression(), expressions)
                        .map(|term| (domain.name(), term))
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
    };
    premises.premise(premise, children)
}
