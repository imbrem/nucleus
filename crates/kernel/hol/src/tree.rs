use std::sync::Arc;

use covalence_lib_serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{
    Abs, App, Arr, Base, BoolLit, BoolTy, Bound, Eps, Eqn, Expr, Free, IndTy, Lam, Rep, Sub, Succ,
    Zero,
};

/// A recursively shared HOL syntax tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tree(Arc<Expr<Self>>);

impl Tree {
    /// Wraps one expression layer in shared ownership.
    #[must_use]
    pub fn new(expr: Expr<Self>) -> Self {
        Self(Arc::new(expr))
    }

    /// Borrows the root expression layer.
    #[must_use]
    pub fn expr(&self) -> &Expr<Self> {
        &self.0
    }

    /// Tests whether two trees share the same root allocation.
    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    /// Visits the root's immediate children in semantic order.
    pub fn for_each_child(&self, visit: impl FnMut(&Self)) {
        self.0.for_each_child(visit);
    }

    /// Constructs the Boolean type.
    #[must_use]
    pub fn bool_ty() -> Self {
        Self::new(Expr::BoolTy(BoolTy {}))
    }

    /// Constructs a named primitive type.
    #[must_use]
    pub fn base(name: impl Into<String>) -> Self {
        Self::new(Expr::Base(Base { name: name.into() }))
    }

    /// Constructs the distinguished infinite individual type.
    #[must_use]
    pub fn ind_ty() -> Self {
        Self::new(Expr::IndTy(IndTy {}))
    }

    /// Constructs a function type.
    #[must_use]
    pub fn arr(domain: Self, codomain: Self) -> Self {
        Self::new(Expr::Arr(Arr { domain, codomain }))
    }

    /// Constructs a predicate subtype.
    #[must_use]
    pub fn subtype(carrier: Self, predicate: Self) -> Self {
        Self::new(Expr::Sub(Sub { carrier, predicate }))
    }

    /// Constructs a bound variable.
    #[must_use]
    pub fn bound(index: u64) -> Self {
        Self::new(Expr::Bound(Bound { index }))
    }

    /// Constructs a free variable.
    #[must_use]
    pub fn free(name: u64) -> Self {
        Self::new(Expr::Free(Free { name }))
    }

    /// Constructs an application.
    #[must_use]
    pub fn app(function: Self, argument: Self) -> Self {
        Self::new(Expr::App(App { function, argument }))
    }

    /// Constructs a lambda abstraction.
    #[must_use]
    pub fn lam(domain: Self, body: Self) -> Self {
        Self::new(Expr::Lam(Lam { domain, body }))
    }

    /// Constructs a Boolean literal.
    #[must_use]
    pub fn bool(value: bool) -> Self {
        Self::new(Expr::Bool(BoolLit { value }))
    }

    /// Constructs zero of the individual type.
    #[must_use]
    pub fn zero() -> Self {
        Self::new(Expr::Zero(Zero {}))
    }

    /// Constructs successor.
    #[must_use]
    pub fn succ(value: Self) -> Self {
        Self::new(Expr::Succ(Succ { value }))
    }

    /// Constructs typed equality.
    #[must_use]
    pub fn eqn(r#type: Self, left: Self, right: Self) -> Self {
        Self::new(Expr::Eqn(Eqn {
            r#type,
            left,
            right,
        }))
    }

    /// Constructs Hilbert choice.
    #[must_use]
    pub fn eps(r#type: Self, predicate: Self) -> Self {
        Self::new(Expr::Eps(Eps { r#type, predicate }))
    }

    /// Constructs subtype abstraction.
    #[must_use]
    pub fn abs(carrier: Self, predicate: Self, value: Self) -> Self {
        Self::new(Expr::Abs(Abs {
            carrier,
            predicate,
            value,
        }))
    }

    /// Constructs subtype representation.
    #[must_use]
    pub fn rep(carrier: Self, predicate: Self, value: Self) -> Self {
        Self::new(Expr::Rep(Rep {
            carrier,
            predicate,
            value,
        }))
    }
}

impl Serialize for Tree {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Tree {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Expr::deserialize(deserializer).map(Self::new)
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_json::{from_str, to_string};

    use super::*;

    #[test]
    fn clones_and_reused_children_share_allocations() {
        let child = Tree::bound(0);
        let cloned = child.clone();
        let application = Tree::app(child.clone(), cloned.clone());

        assert!(child.ptr_eq(&cloned));
        let mut children = Vec::new();
        application.for_each_child(|node| children.push(node.clone()));
        assert!(children[0].ptr_eq(&children[1]));
        assert!(children[0].ptr_eq(&child));
    }

    #[test]
    fn direct_tree_json_round_trips() {
        let term = Tree::app(Tree::lam(Tree::bool_ty(), Tree::bound(0)), Tree::bound(0));
        let json = to_string(&term).expect("serialize tree");

        let actual_json = from_str::<covalence_lib_json::Value>(&json).expect("parse output");
        let golden_json = from_str::<covalence_lib_json::Value>(include_str!("../tests/app.json"))
            .expect("parse golden");
        assert_eq!(actual_json, golden_json);
        assert_eq!(from_str::<Tree>(&json).expect("deserialize tree"), term);
    }

    #[test]
    fn all_variants_round_trip() {
        let predicate = Tree::eqn(Tree::ind_ty(), Tree::bound(0), Tree::zero());
        let nodes = [
            Tree::base("atom"),
            Tree::bool_ty(),
            Tree::ind_ty(),
            Tree::arr(Tree::bool_ty(), Tree::bool_ty()),
            Tree::subtype(Tree::ind_ty(), predicate.clone()),
            Tree::bound(u64::MAX),
            Tree::free(u64::MAX),
            Tree::app(Tree::bound(0), Tree::bound(1)),
            Tree::lam(Tree::bool_ty(), Tree::bound(0)),
            Tree::bool(true),
            Tree::zero(),
            Tree::succ(Tree::zero()),
            Tree::eqn(Tree::bool_ty(), Tree::bound(0), Tree::bound(1)),
            Tree::eps(Tree::ind_ty(), Tree::lam(Tree::ind_ty(), Tree::bool(true))),
            Tree::abs(Tree::ind_ty(), predicate.clone(), Tree::zero()),
            Tree::rep(
                Tree::ind_ty(),
                predicate.clone(),
                Tree::abs(Tree::ind_ty(), predicate, Tree::zero()),
            ),
        ];

        for node in nodes {
            let json = to_string(&node).expect("serialize node");
            assert_eq!(from_str::<Tree>(&json).expect("deserialize node"), node);
        }
    }

    #[test]
    fn malformed_tags_fields_and_indices_are_rejected() {
        for json in [
            r#"{"tag":"tm.unknown"}"#,
            r#"{"tag":"tm.app","function":{"tag":"tm.bound","index":0}}"#,
            r#"{"tag":"tm.bound","index":-1}"#,
            r#"{"tag":"tm.bound","index":0.5}"#,
        ] {
            assert!(from_str::<Tree>(json).is_err(), "accepted {json}");
        }
    }
}
