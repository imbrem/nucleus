use std::{error::Error, fmt};

use crate::{Expr, Tree};

/// Failure of a total locally nameless index operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubstError {
    /// Shifting a syntactic `u64` index would overflow.
    IndexOverflow,
}

impl fmt::Display for SubstError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("de Bruijn index overflow")
    }
}

impl Error for SubstError {}

/// Shifts every free de Bruijn index by one.
///
/// Types embedded in terms remain unchanged: subtype predicates have their own
/// fixed one-variable scope and cannot mention the ambient term binders.
///
/// # Errors
///
/// Returns [`SubstError::IndexOverflow`] for a maximal shifted raw index.
pub fn weaken(term: &Tree) -> Result<Tree, SubstError> {
    shift_from(term, 0)
}

fn shift_from(term: &Tree, cutoff: u64) -> Result<Tree, SubstError> {
    Ok(match term.expr() {
        Expr::Base(_) | Expr::BoolTy(_) | Expr::IndTy(_) | Expr::Arr(_) | Expr::Sub(_) => {
            term.clone()
        }
        Expr::Bound(node) if node.index >= cutoff => {
            Tree::bound(node.index.checked_add(1).ok_or(SubstError::IndexOverflow)?)
        }
        Expr::Bound(node) => Tree::bound(node.index),
        Expr::Free(node) => Tree::free(node.name),
        Expr::App(node) => Tree::app(
            shift_from(&node.function, cutoff)?,
            shift_from(&node.argument, cutoff)?,
        ),
        Expr::Lam(node) => Tree::lam(
            node.domain.clone(),
            shift_from(
                &node.body,
                cutoff.checked_add(1).ok_or(SubstError::IndexOverflow)?,
            )?,
        ),
        Expr::Bool(node) => Tree::bool(node.value),
        Expr::Zero(_) => Tree::zero(),
        Expr::Succ(node) => Tree::succ(shift_from(&node.value, cutoff)?),
        Expr::Eqn(node) => Tree::eqn(
            node.r#type.clone(),
            shift_from(&node.left, cutoff)?,
            shift_from(&node.right, cutoff)?,
        ),
        Expr::Eps(node) => Tree::eps(node.r#type.clone(), shift_from(&node.predicate, cutoff)?),
        Expr::Abs(node) => Tree::abs(
            node.carrier.clone(),
            node.predicate.clone(),
            shift_from(&node.value, cutoff)?,
        ),
        Expr::Rep(node) => Tree::rep(
            node.carrier.clone(),
            node.predicate.clone(),
            shift_from(&node.value, cutoff)?,
        ),
    })
}

/// Opens the newest binder in `body` with `argument`.
///
/// # Errors
///
/// Returns an index-overflow error while shifting the replacement beneath a
/// nested binder.
pub fn open_bound(body: &Tree, argument: &Tree) -> Result<Tree, SubstError> {
    substitute_at(body, argument, 0)
}

fn substitute_at(term: &Tree, argument: &Tree, depth: u64) -> Result<Tree, SubstError> {
    Ok(match term.expr() {
        Expr::Base(_) | Expr::BoolTy(_) | Expr::IndTy(_) | Expr::Arr(_) | Expr::Sub(_) => {
            term.clone()
        }
        Expr::Bound(node) if node.index == depth => shift_n(argument, 0, depth)?,
        Expr::Bound(node) if node.index > depth => Tree::bound(node.index - 1),
        Expr::Bound(node) => Tree::bound(node.index),
        Expr::Free(node) => Tree::free(node.name),
        Expr::App(node) => Tree::app(
            substitute_at(&node.function, argument, depth)?,
            substitute_at(&node.argument, argument, depth)?,
        ),
        Expr::Lam(node) => Tree::lam(
            node.domain.clone(),
            substitute_at(
                &node.body,
                argument,
                depth.checked_add(1).ok_or(SubstError::IndexOverflow)?,
            )?,
        ),
        Expr::Bool(node) => Tree::bool(node.value),
        Expr::Zero(_) => Tree::zero(),
        Expr::Succ(node) => Tree::succ(substitute_at(&node.value, argument, depth)?),
        Expr::Eqn(node) => Tree::eqn(
            node.r#type.clone(),
            substitute_at(&node.left, argument, depth)?,
            substitute_at(&node.right, argument, depth)?,
        ),
        Expr::Eps(node) => Tree::eps(
            node.r#type.clone(),
            substitute_at(&node.predicate, argument, depth)?,
        ),
        Expr::Abs(node) => Tree::abs(
            node.carrier.clone(),
            node.predicate.clone(),
            substitute_at(&node.value, argument, depth)?,
        ),
        Expr::Rep(node) => Tree::rep(
            node.carrier.clone(),
            node.predicate.clone(),
            substitute_at(&node.value, argument, depth)?,
        ),
    })
}

fn shift_n(term: &Tree, cutoff: u64, amount: u64) -> Result<Tree, SubstError> {
    if amount == 0 {
        return Ok(term.clone());
    }
    let shifted = shift_from(term, cutoff)?;
    shift_n(&shifted, cutoff, amount - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opening_avoids_capture_under_nested_lambdas() {
        let body = Tree::lam(Tree::bool_ty(), Tree::app(Tree::bound(1), Tree::bound(0)));
        let opened = open_bound(&body, &Tree::bound(0)).expect("open");
        assert_eq!(
            opened,
            Tree::lam(Tree::bool_ty(), Tree::app(Tree::bound(1), Tree::bound(0)))
        );
    }

    #[test]
    fn weakening_respects_lambda_cutoffs() {
        let term = Tree::lam(Tree::bool_ty(), Tree::app(Tree::bound(0), Tree::bound(1)));
        assert_eq!(
            weaken(&term).expect("weaken"),
            Tree::lam(Tree::bool_ty(), Tree::app(Tree::bound(0), Tree::bound(2)))
        );
    }
}
