use covalence_lib_serde::{Deserialize, Serialize};

/// Common behavior of one non-recursive expression node.
pub trait Node<I>: Sized {
    /// Stable experimental JSON tag for this node kind.
    const TAG: &'static str;

    /// Visits children in their semantic order without allocating.
    fn for_each_child(&self, visit: impl FnMut(&I));

    /// Maps the node's child indices without changing its tag or data.
    fn map_indices<J>(self, map: impl FnMut(I) -> J) -> Expr<J>;
}

/// The Boolean type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct BoolTy {}

impl<I> Node<I> for BoolTy {
    const TAG: &'static str = "ty.bool";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::BoolTy(self)
    }
}

/// A function type with domain followed by codomain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Arr<I> {
    /// Function domain.
    pub domain: I,
    /// Function codomain.
    pub codomain: I,
}

impl<I> Node<I> for Arr<I> {
    const TAG: &'static str = "ty.arr";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.domain);
        visit(&self.codomain);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Arr(Arr {
            domain: map(self.domain),
            codomain: map(self.codomain),
        })
    }
}

/// A locally bound de Bruijn variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Bound {
    /// Zero-based de Bruijn index.
    pub index: u64,
}

impl<I> Node<I> for Bound {
    const TAG: &'static str = "tm.bound";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Bound(self)
    }
}

/// Function application: function followed by argument.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct App<I> {
    /// Function expression.
    pub function: I,
    /// Argument expression.
    pub argument: I,
}

impl<I> Node<I> for App<I> {
    const TAG: &'static str = "tm.app";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.function);
        visit(&self.argument);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::App(App {
            function: map(self.function),
            argument: map(self.argument),
        })
    }
}

/// Lambda abstraction: domain followed by body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Lam<I> {
    /// Bound-variable type.
    pub domain: I,
    /// Lambda body.
    pub body: I,
}

impl<I> Node<I> for Lam<I> {
    const TAG: &'static str = "tm.lam";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.domain);
        visit(&self.body);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Lam(Lam {
            domain: map(self.domain),
            body: map(self.body),
        })
    }
}

/// Typed equality. Named `Eqn` to avoid collision with Rust's `Eq` trait.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Eqn<I> {
    /// Type of both operands.
    pub r#type: I,
    /// Left operand.
    pub left: I,
    /// Right operand.
    pub right: I,
}

impl<I> Node<I> for Eqn<I> {
    const TAG: &'static str = "tm.eq";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.r#type);
        visit(&self.left);
        visit(&self.right);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Eqn(Eqn {
            r#type: map(self.r#type),
            left: map(self.left),
            right: map(self.right),
        })
    }
}

/// One layer of the experimental HOL syntax.
///
/// New variants are added incrementally. Derived Serde deliberately keeps the
/// public sum type ordinary and easy to consume.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde", tag = "tag")]
pub enum Expr<I> {
    /// Boolean type.
    #[serde(rename = "ty.bool")]
    BoolTy(BoolTy),
    /// Function type.
    #[serde(rename = "ty.arr")]
    Arr(Arr<I>),
    /// Bound variable.
    #[serde(rename = "tm.bound")]
    Bound(Bound),
    /// Function application.
    #[serde(rename = "tm.app")]
    App(App<I>),
    /// Lambda abstraction.
    #[serde(rename = "tm.lam")]
    Lam(Lam<I>),
    /// Typed equality.
    #[serde(rename = "tm.eq")]
    Eqn(Eqn<I>),
}

impl<I> Expr<I> {
    /// Returns the experimental wire tag.
    #[must_use]
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::BoolTy(_) => <BoolTy as Node<I>>::TAG,
            Self::Arr(_) => <Arr<I> as Node<I>>::TAG,
            Self::Bound(_) => <Bound as Node<I>>::TAG,
            Self::App(_) => <App<I> as Node<I>>::TAG,
            Self::Lam(_) => <Lam<I> as Node<I>>::TAG,
            Self::Eqn(_) => <Eqn<I> as Node<I>>::TAG,
        }
    }

    /// Visits children in their semantic order without allocating.
    pub fn for_each_child(&self, visit: impl FnMut(&I)) {
        match self {
            Self::BoolTy(node) => node.for_each_child(visit),
            Self::Arr(node) => node.for_each_child(visit),
            Self::Bound(node) => node.for_each_child(visit),
            Self::App(node) => node.for_each_child(visit),
            Self::Lam(node) => node.for_each_child(visit),
            Self::Eqn(node) => node.for_each_child(visit),
        }
    }

    /// Returns the fixed child arity of this node.
    #[must_use]
    pub const fn child_count(&self) -> usize {
        match self {
            Self::BoolTy(_) | Self::Bound(_) => 0,
            Self::Arr(_) | Self::App(_) | Self::Lam(_) => 2,
            Self::Eqn(_) => 3,
        }
    }

    /// Maps child indices without changing the tag or non-child data.
    pub fn map_indices<J>(self, map: impl FnMut(I) -> J) -> Expr<J> {
        match self {
            Self::BoolTy(node) => node.map_indices(map),
            Self::Arr(node) => node.map_indices(map),
            Self::Bound(node) => node.map_indices(map),
            Self::App(node) => node.map_indices(map),
            Self::Lam(node) => node.map_indices(map),
            Self::Eqn(node) => node.map_indices(map),
        }
    }
}
