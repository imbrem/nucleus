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

/// A named primitive type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Base {
    /// Stable base-type name.
    pub name: String,
}

impl<I> Node<I> for Base {
    const TAG: &'static str = "ty.base";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Base(self)
    }
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

/// The distinguished infinite individual type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct IndTy {}

impl<I> Node<I> for IndTy {
    const TAG: &'static str = "ty.ind";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::IndTy(self)
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

/// Predicate subtype: carrier followed by its one-bound-variable predicate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Sub<I> {
    /// Carrier type.
    pub carrier: I,
    /// Predicate with one locally bound carrier variable.
    pub predicate: I,
}

impl<I> Node<I> for Sub<I> {
    const TAG: &'static str = "ty.sub";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.carrier);
        visit(&self.predicate);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Sub(Sub {
            carrier: map(self.carrier),
            predicate: map(self.predicate),
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

/// A free variable name. Closed checking rejects this node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Free {
    /// Stable free-variable name.
    pub name: u64,
}

impl<I> Node<I> for Free {
    const TAG: &'static str = "tm.free";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Free(self)
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

/// A Boolean literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct BoolLit {
    /// Literal value.
    pub value: bool,
}

impl<I> Node<I> for BoolLit {
    const TAG: &'static str = "tm.bool";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Bool(self)
    }
}

/// The zero literal of the individual type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Zero {}

impl<I> Node<I> for Zero {
    const TAG: &'static str = "tm.zero";

    fn for_each_child(&self, _visit: impl FnMut(&I)) {}

    fn map_indices<J>(self, _map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Zero(self)
    }
}

/// Successor on the individual type.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Succ<I> {
    /// Predecessor value.
    pub value: I,
}

impl<I> Node<I> for Succ<I> {
    const TAG: &'static str = "tm.succ";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.value);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Succ(Succ {
            value: map(self.value),
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

/// Hilbert choice: type followed by predicate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Eps<I> {
    /// Chosen value's type.
    pub r#type: I,
    /// Predicate of type `type -> bool`.
    pub predicate: I,
}

impl<I> Node<I> for Eps<I> {
    const TAG: &'static str = "tm.eps";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.r#type);
        visit(&self.predicate);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Eps(Eps {
            r#type: map(self.r#type),
            predicate: map(self.predicate),
        })
    }
}

/// Abstraction into a predicate subtype.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Abs<I> {
    /// Carrier type.
    pub carrier: I,
    /// Subtype predicate.
    pub predicate: I,
    /// Carrier value.
    pub value: I,
}

impl<I> Node<I> for Abs<I> {
    const TAG: &'static str = "tm.abs";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.carrier);
        visit(&self.predicate);
        visit(&self.value);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Abs(Abs {
            carrier: map(self.carrier),
            predicate: map(self.predicate),
            value: map(self.value),
        })
    }
}

/// Representation out of a predicate subtype.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde")]
pub struct Rep<I> {
    /// Carrier type.
    pub carrier: I,
    /// Subtype predicate.
    pub predicate: I,
    /// Subtype value.
    pub value: I,
}

impl<I> Node<I> for Rep<I> {
    const TAG: &'static str = "tm.rep";

    fn for_each_child(&self, mut visit: impl FnMut(&I)) {
        visit(&self.carrier);
        visit(&self.predicate);
        visit(&self.value);
    }

    fn map_indices<J>(self, mut map: impl FnMut(I) -> J) -> Expr<J> {
        Expr::Rep(Rep {
            carrier: map(self.carrier),
            predicate: map(self.predicate),
            value: map(self.value),
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
    /// Named primitive type.
    #[serde(rename = "ty.base")]
    Base(Base),
    /// Boolean type.
    #[serde(rename = "ty.bool")]
    BoolTy(BoolTy),
    /// Distinguished infinite individual type.
    #[serde(rename = "ty.ind")]
    IndTy(IndTy),
    /// Function type.
    #[serde(rename = "ty.arr")]
    Arr(Arr<I>),
    /// Predicate subtype.
    #[serde(rename = "ty.sub")]
    Sub(Sub<I>),
    /// Bound variable.
    #[serde(rename = "tm.bound")]
    Bound(Bound),
    /// Free variable.
    #[serde(rename = "tm.free")]
    Free(Free),
    /// Function application.
    #[serde(rename = "tm.app")]
    App(App<I>),
    /// Lambda abstraction.
    #[serde(rename = "tm.lam")]
    Lam(Lam<I>),
    /// Boolean literal.
    #[serde(rename = "tm.bool")]
    Bool(BoolLit),
    /// Zero literal.
    #[serde(rename = "tm.zero")]
    Zero(Zero),
    /// Successor.
    #[serde(rename = "tm.succ")]
    Succ(Succ<I>),
    /// Typed equality.
    #[serde(rename = "tm.eq")]
    Eqn(Eqn<I>),
    /// Hilbert choice.
    #[serde(rename = "tm.eps")]
    Eps(Eps<I>),
    /// Subtype abstraction.
    #[serde(rename = "tm.abs")]
    Abs(Abs<I>),
    /// Subtype representation.
    #[serde(rename = "tm.rep")]
    Rep(Rep<I>),
}

impl<I> Expr<I> {
    /// Returns the experimental wire tag.
    #[must_use]
    pub const fn tag(&self) -> &'static str {
        match self {
            Self::Base(_) => <Base as Node<I>>::TAG,
            Self::BoolTy(_) => <BoolTy as Node<I>>::TAG,
            Self::IndTy(_) => <IndTy as Node<I>>::TAG,
            Self::Arr(_) => <Arr<I> as Node<I>>::TAG,
            Self::Sub(_) => <Sub<I> as Node<I>>::TAG,
            Self::Bound(_) => <Bound as Node<I>>::TAG,
            Self::Free(_) => <Free as Node<I>>::TAG,
            Self::App(_) => <App<I> as Node<I>>::TAG,
            Self::Lam(_) => <Lam<I> as Node<I>>::TAG,
            Self::Bool(_) => <BoolLit as Node<I>>::TAG,
            Self::Zero(_) => <Zero as Node<I>>::TAG,
            Self::Succ(_) => <Succ<I> as Node<I>>::TAG,
            Self::Eqn(_) => <Eqn<I> as Node<I>>::TAG,
            Self::Eps(_) => <Eps<I> as Node<I>>::TAG,
            Self::Abs(_) => <Abs<I> as Node<I>>::TAG,
            Self::Rep(_) => <Rep<I> as Node<I>>::TAG,
        }
    }

    /// Visits children in their semantic order without allocating.
    pub fn for_each_child(&self, visit: impl FnMut(&I)) {
        match self {
            Self::Base(node) => node.for_each_child(visit),
            Self::BoolTy(node) => node.for_each_child(visit),
            Self::IndTy(node) => node.for_each_child(visit),
            Self::Arr(node) => node.for_each_child(visit),
            Self::Sub(node) => node.for_each_child(visit),
            Self::Bound(node) => node.for_each_child(visit),
            Self::Free(node) => node.for_each_child(visit),
            Self::App(node) => node.for_each_child(visit),
            Self::Lam(node) => node.for_each_child(visit),
            Self::Bool(node) => node.for_each_child(visit),
            Self::Zero(node) => node.for_each_child(visit),
            Self::Succ(node) => node.for_each_child(visit),
            Self::Eqn(node) => node.for_each_child(visit),
            Self::Eps(node) => node.for_each_child(visit),
            Self::Abs(node) => node.for_each_child(visit),
            Self::Rep(node) => node.for_each_child(visit),
        }
    }

    /// Returns the fixed child arity of this node.
    #[must_use]
    pub const fn child_count(&self) -> usize {
        match self {
            Self::Base(_)
            | Self::BoolTy(_)
            | Self::IndTy(_)
            | Self::Bound(_)
            | Self::Free(_)
            | Self::Bool(_)
            | Self::Zero(_) => 0,
            Self::Succ(_) => 1,
            Self::Arr(_) | Self::Sub(_) | Self::App(_) | Self::Lam(_) | Self::Eps(_) => 2,
            Self::Eqn(_) | Self::Abs(_) | Self::Rep(_) => 3,
        }
    }

    /// Maps child indices without changing the tag or non-child data.
    pub fn map_indices<J>(self, map: impl FnMut(I) -> J) -> Expr<J> {
        match self {
            Self::Base(node) => node.map_indices(map),
            Self::BoolTy(node) => node.map_indices(map),
            Self::IndTy(node) => node.map_indices(map),
            Self::Arr(node) => node.map_indices(map),
            Self::Sub(node) => node.map_indices(map),
            Self::Bound(node) => node.map_indices(map),
            Self::Free(node) => node.map_indices(map),
            Self::App(node) => node.map_indices(map),
            Self::Lam(node) => node.map_indices(map),
            Self::Bool(node) => node.map_indices(map),
            Self::Zero(node) => node.map_indices(map),
            Self::Succ(node) => node.map_indices(map),
            Self::Eqn(node) => node.map_indices(map),
            Self::Eps(node) => node.map_indices(map),
            Self::Abs(node) => node.map_indices(map),
            Self::Rep(node) => node.map_indices(map),
        }
    }
}
