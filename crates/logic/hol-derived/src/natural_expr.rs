//! Arithmetic expressions over the naturals.
//!
//! [`Expr`] is a plain syntax tree written with the usual Rust operators, so a
//! caller states `x * y + 5 - 3` and never touches arena rows:
//!
//! ```ignore
//! let x = Expr::atom(x_term);
//! let y = Expr::atom(y_term);
//! let goal = x * y + 5 - 3;
//! ```
//!
//! An expression carries no proof and names no kernel. Building the HOL term
//! and normalizing it are jobs for `NaturalNormalizer`.

use std::rc::Rc;

use covalence_logic_hol::Ref;

/// An arithmetic expression over the natural numbers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Expr(Rc<Node>);

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Node {
    /// A checked term of type `nat` the normalizer treats as opaque.
    Atom(Ref),
    /// A non-negative integer literal.
    Literal(u64),
    Add(Expr, Expr),
    Mul(Expr, Expr),
    Sub(Expr, Expr),
}

impl Expr {
    /// Wraps a checked term of type `nat`.
    #[must_use]
    pub fn atom(term: Ref) -> Self {
        Self(Rc::new(Node::Atom(term)))
    }

    /// A numeric literal.
    #[must_use]
    pub fn literal(value: u64) -> Self {
        Self(Rc::new(Node::Literal(value)))
    }

    pub(crate) fn node(&self) -> &Node {
        &self.0
    }

    /// One when `self` is at most `other`, zero otherwise.
    ///
    /// Truncated subtraction already decides the order: `a - b` is zero exactly
    /// when `a <= b`, and `1 - k` turns that into a flag. This is an encoding,
    /// not a new constant, so it needs nothing the semiring does not have.
    #[must_use]
    pub fn at_most(self, other: Self) -> Self {
        Self::literal(1) - (self - other)
    }

    /// One when `self` is below `other`, zero otherwise.
    #[must_use]
    pub fn below(self, other: Self) -> Self {
        (self + 1).at_most(other)
    }

    /// One when `self` and `other` are equal, zero otherwise.
    ///
    /// Each side bounds the other, and truncated subtraction makes the two
    /// differences vanish together only when the values agree.
    #[must_use]
    pub fn equals(self, other: Self) -> Self {
        Self::literal(1) - ((self.clone() - other.clone()) + (other - self))
    }

    /// `then_branch` when `flag` is one, `else_branch` when it is zero.
    ///
    /// The flag must be zero or one; the encodings above always are.
    #[must_use]
    pub fn select(flag: Self, then_branch: Self, else_branch: Self) -> Self {
        flag.clone() * then_branch + (Self::literal(1) - flag) * else_branch
    }
}

impl From<u64> for Expr {
    fn from(value: u64) -> Self {
        Self::literal(value)
    }
}

impl From<Ref> for Expr {
    fn from(term: Ref) -> Self {
        Self::atom(term)
    }
}

/// Implements one operator for `Expr`, `&Expr`, and a `u64` right operand.
macro_rules! operator {
    ($trait:ident, $method:ident, $node:ident) => {
        impl std::ops::$trait for Expr {
            type Output = Self;

            fn $method(self, other: Self) -> Self {
                Self(Rc::new(Node::$node(self, other)))
            }
        }

        impl std::ops::$trait<&Self> for Expr {
            type Output = Self;

            fn $method(self, other: &Self) -> Self {
                Self(Rc::new(Node::$node(self, other.clone())))
            }
        }

        impl std::ops::$trait<Expr> for &Expr {
            type Output = Expr;

            fn $method(self, other: Expr) -> Expr {
                Expr(Rc::new(Node::$node(self.clone(), other)))
            }
        }

        impl std::ops::$trait<Self> for &Expr {
            type Output = Expr;

            fn $method(self, other: Self) -> Expr {
                Expr(Rc::new(Node::$node(self.clone(), other.clone())))
            }
        }

        impl std::ops::$trait<u64> for Expr {
            type Output = Self;

            fn $method(self, other: u64) -> Self {
                Self(Rc::new(Node::$node(self, Self::literal(other))))
            }
        }

        impl std::ops::$trait<u64> for &Expr {
            type Output = Expr;

            fn $method(self, other: u64) -> Expr {
                Expr(Rc::new(Node::$node(self.clone(), Expr::literal(other))))
            }
        }
    };
}

operator!(Add, add, Add);
operator!(Mul, mul, Mul);
operator!(Sub, sub, Sub);
