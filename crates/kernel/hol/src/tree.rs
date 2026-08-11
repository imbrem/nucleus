use std::sync::Arc;

use covalence_lib_serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{App, Arr, BoolTy, Bound, Eqn, Expr, Lam};

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

    /// Constructs a function type.
    #[must_use]
    pub fn arr(domain: Self, codomain: Self) -> Self {
        Self::new(Expr::Arr(Arr { domain, codomain }))
    }

    /// Constructs a bound variable.
    #[must_use]
    pub fn bound(index: u64) -> Self {
        Self::new(Expr::Bound(Bound { index }))
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

    /// Constructs typed equality.
    #[must_use]
    pub fn eqn(r#type: Self, left: Self, right: Self) -> Self {
        Self::new(Expr::Eqn(Eqn {
            r#type,
            left,
            right,
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

        assert_eq!(json, include_str!("../tests/app.json").trim());
        assert_eq!(from_str::<Tree>(&json).expect("deserialize tree"), term);
    }

    #[test]
    fn all_pilot_variants_round_trip() {
        let nodes = [
            Tree::bool_ty(),
            Tree::arr(Tree::bool_ty(), Tree::bool_ty()),
            Tree::bound(u64::MAX),
            Tree::app(Tree::bound(0), Tree::bound(1)),
            Tree::lam(Tree::bool_ty(), Tree::bound(0)),
            Tree::eqn(Tree::bool_ty(), Tree::bound(0), Tree::bound(1)),
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
