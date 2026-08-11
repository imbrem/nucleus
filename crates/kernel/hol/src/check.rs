use std::{error::Error, fmt};

use crate::{Expr, Tree};

/// Failure while checking raw HOL syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckError {
    /// A term constructor appeared where a type was required.
    ExpectedType {
        /// Offending node tag.
        tag: &'static str,
    },
    /// A type constructor appeared where a term was required.
    ExpectedTerm {
        /// Offending node tag.
        tag: &'static str,
    },
    /// A de Bruijn index was outside the current binder context.
    UnboundIndex {
        /// Requested index.
        index: u64,
        /// Number of available binders.
        depth: usize,
    },
    /// Closed checking encountered a free variable.
    FreeVariable {
        /// Free-variable name.
        name: u64,
    },
    /// Application expected a function type.
    ExpectedFunction {
        /// Actual function-expression type.
        found: Tree,
    },
    /// A synthesized type differed from its required type.
    TypeMismatch {
        /// Required type.
        expected: Tree,
        /// Synthesized type.
        found: Tree,
    },
}

impl fmt::Display for CheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedType { tag } => write!(formatter, "expected a type, found {tag}"),
            Self::ExpectedTerm { tag } => write!(formatter, "expected a term, found {tag}"),
            Self::UnboundIndex { index, depth } => {
                write!(formatter, "bound index {index} is outside depth {depth}")
            }
            Self::FreeVariable { name } => {
                write!(formatter, "free variable {name} is not closed")
            }
            Self::ExpectedFunction { .. } => formatter.write_str("expected a function type"),
            Self::TypeMismatch { .. } => formatter.write_str("HOL type mismatch"),
        }
    }
}

impl Error for CheckError {}

/// Checks that a raw tree is a well-formed HOL type.
///
/// # Errors
///
/// Returns the first malformed type or subtype predicate.
pub fn check_type(r#type: &Tree) -> Result<(), CheckError> {
    check_type_inner(r#type)
}

fn check_type_inner(r#type: &Tree) -> Result<(), CheckError> {
    match r#type.expr() {
        Expr::Base(_) | Expr::BoolTy(_) | Expr::IndTy(_) => Ok(()),
        Expr::Arr(node) => {
            check_type_inner(&node.domain)?;
            check_type_inner(&node.codomain)
        }
        Expr::Sub(node) => check_subtype(&node.carrier, &node.predicate),
        other => Err(CheckError::ExpectedType { tag: other.tag() }),
    }
}

fn check_subtype(carrier: &Tree, predicate: &Tree) -> Result<(), CheckError> {
    check_type_inner(carrier)?;
    check_expected(predicate, std::slice::from_ref(carrier), &Tree::bool_ty())
}

/// Synthesizes the type of a term with no free or outer bound variables.
///
/// Lambda bodies and subtype predicates may still contain their locally bound
/// de Bruijn variables.
///
/// # Errors
///
/// Returns the first scope, kind, or type error.
pub fn check_closed(term: &Tree) -> Result<Tree, CheckError> {
    infer(term, &[])
}

pub(crate) fn infer(term: &Tree, bound: &[Tree]) -> Result<Tree, CheckError> {
    match term.expr() {
        Expr::Base(_) | Expr::BoolTy(_) | Expr::IndTy(_) | Expr::Arr(_) | Expr::Sub(_) => {
            Err(CheckError::ExpectedTerm {
                tag: term.expr().tag(),
            })
        }
        Expr::Bound(node) => {
            let index = usize::try_from(node.index).map_err(|_| CheckError::UnboundIndex {
                index: node.index,
                depth: bound.len(),
            })?;
            bound.get(index).cloned().ok_or(CheckError::UnboundIndex {
                index: node.index,
                depth: bound.len(),
            })
        }
        Expr::Free(node) => Err(CheckError::FreeVariable { name: node.name }),
        Expr::App(node) => {
            let function_type = infer(&node.function, bound)?;
            let Expr::Arr(function) = function_type.expr() else {
                return Err(CheckError::ExpectedFunction {
                    found: function_type,
                });
            };
            check_expected(&node.argument, bound, &function.domain)?;
            Ok(function.codomain.clone())
        }
        Expr::Lam(node) => {
            check_type_inner(&node.domain)?;
            let mut extended = Vec::with_capacity(bound.len() + 1);
            extended.push(node.domain.clone());
            extended.extend_from_slice(bound);
            let body_type = infer(&node.body, &extended)?;
            Ok(Tree::arr(node.domain.clone(), body_type))
        }
        Expr::Bool(_) => Ok(Tree::bool_ty()),
        Expr::Zero(_) => Ok(Tree::ind_ty()),
        Expr::Succ(node) => {
            check_expected(&node.value, bound, &Tree::ind_ty())?;
            Ok(Tree::ind_ty())
        }
        Expr::Eqn(node) => {
            check_type_inner(&node.r#type)?;
            check_expected(&node.left, bound, &node.r#type)?;
            check_expected(&node.right, bound, &node.r#type)?;
            Ok(Tree::bool_ty())
        }
        Expr::Eps(node) => {
            check_type_inner(&node.r#type)?;
            let predicate_type = Tree::arr(node.r#type.clone(), Tree::bool_ty());
            check_expected(&node.predicate, bound, &predicate_type)?;
            Ok(node.r#type.clone())
        }
        Expr::Abs(node) => {
            check_subtype(&node.carrier, &node.predicate)?;
            check_expected(&node.value, bound, &node.carrier)?;
            Ok(Tree::subtype(node.carrier.clone(), node.predicate.clone()))
        }
        Expr::Rep(node) => {
            check_subtype(&node.carrier, &node.predicate)?;
            let subtype = Tree::subtype(node.carrier.clone(), node.predicate.clone());
            check_expected(&node.value, bound, &subtype)?;
            Ok(node.carrier.clone())
        }
    }
}

pub(crate) fn check_expected(
    term: &Tree,
    bound: &[Tree],
    expected: &Tree,
) -> Result<(), CheckError> {
    let found = infer(term, bound)?;
    if found == *expected {
        Ok(())
    } else {
        Err(CheckError::TypeMismatch {
            expected: expected.clone(),
            found,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity(r#type: Tree) -> Tree {
        Tree::lam(r#type, Tree::bound(0))
    }

    #[test]
    fn checks_every_type_constructor() {
        let predicate = Tree::eqn(Tree::ind_ty(), Tree::bound(0), Tree::zero());
        for r#type in [
            Tree::base("atom"),
            Tree::bool_ty(),
            Tree::ind_ty(),
            Tree::arr(Tree::bool_ty(), Tree::ind_ty()),
            Tree::subtype(Tree::ind_ty(), predicate),
        ] {
            check_type(&r#type).expect("well-formed type");
        }
    }

    #[test]
    fn checks_every_term_constructor_in_a_closed_example() {
        let bool_ty = Tree::bool_ty();
        let ind_ty = Tree::ind_ty();
        let predicate = Tree::eqn(ind_ty.clone(), Tree::bound(0), Tree::zero());
        let subtype = Tree::subtype(ind_ty.clone(), predicate.clone());
        let terms = [
            (
                Tree::lam(bool_ty.clone(), Tree::bound(0)),
                Tree::arr(bool_ty.clone(), bool_ty.clone()),
            ),
            (
                Tree::app(identity(bool_ty.clone()), Tree::bool(true)),
                bool_ty.clone(),
            ),
            (Tree::bool(false), bool_ty.clone()),
            (Tree::zero(), ind_ty.clone()),
            (Tree::succ(Tree::zero()), ind_ty.clone()),
            (
                Tree::eqn(ind_ty.clone(), Tree::zero(), Tree::zero()),
                bool_ty.clone(),
            ),
            (
                Tree::eps(ind_ty.clone(), Tree::lam(ind_ty.clone(), Tree::bool(true))),
                ind_ty.clone(),
            ),
            (
                Tree::abs(ind_ty.clone(), predicate.clone(), Tree::zero()),
                subtype.clone(),
            ),
            (
                Tree::rep(
                    ind_ty.clone(),
                    predicate.clone(),
                    Tree::abs(ind_ty.clone(), predicate, Tree::zero()),
                ),
                ind_ty,
            ),
        ];

        for (term, expected) in terms {
            assert_eq!(check_closed(&term).expect("well-typed term"), expected);
        }
    }

    #[test]
    fn rejects_open_free_and_ill_typed_terms() {
        assert!(matches!(
            check_closed(&Tree::bound(0)),
            Err(CheckError::UnboundIndex { .. })
        ));
        assert!(matches!(
            check_closed(&Tree::free(7)),
            Err(CheckError::FreeVariable { name: 7 })
        ));
        assert!(matches!(
            check_closed(&Tree::app(Tree::bool(true), Tree::bool(false))),
            Err(CheckError::ExpectedFunction { .. })
        ));
        assert!(matches!(
            check_closed(&Tree::app(identity(Tree::ind_ty()), Tree::bool(false))),
            Err(CheckError::TypeMismatch { .. })
        ));
        assert!(matches!(
            check_type(&Tree::bool(true)),
            Err(CheckError::ExpectedType { .. })
        ));
    }
}
