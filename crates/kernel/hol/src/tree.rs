//! The recursively shared tree representation.

use std::fmt;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::{CoreData, CoreTag, Hol, Repr};

/// A [`Hol`] node of the tree representation.
pub type TreeNode<M = ()> = Hol<TreeRepr<M>>;

/// The representation of [`Tree`]: children are shared pointers to nodes.
///
/// This type is a marker, never a value. `M` is the annotation a caller hangs
/// on each node; `()` means no annotation, which then never appears in JSON.
pub struct TreeRepr<M = ()>(PhantomData<M>);

impl<M> Repr for TreeRepr<M> {
    type Tag = CoreTag;
    type Index = Tree<M>;
    type Children = Vec<Tree<M>>;
    type Data = Option<CoreData>;
    type Meta = Option<M>;
}

/// A HOL syntax tree, holding its node behind [`Arc`].
///
/// Cloning is a pointer copy: descendants are shared, never copied, and a
/// subtree handed to two parents stays one node in memory. That sharing is
/// observable through [`Tree::ptr_eq`], but it is not preserved by JSON, which
/// expands a shared subtree once per occurrence.
///
/// Equality is structural rather than by pointer, though it short-circuits on
/// nodes that are already the same node.
pub struct Tree<M = ()>(Arc<TreeNode<M>>);

impl<M> Tree<M> {
    /// Builds a node from its four parts.
    ///
    /// The constructors below are the intended way in; this is the escape
    /// hatch for a tag whose arity or payload the caller is choosing itself.
    /// Nothing is validated either way.
    #[must_use]
    pub fn new(tag: CoreTag, children: Vec<Self>, data: Option<CoreData>, meta: Option<M>) -> Self {
        Self::from_node(Hol::new(tag, children, data, meta))
    }

    /// Shares an already-built node.
    #[must_use]
    pub fn from_node(node: TreeNode<M>) -> Self {
        Self(Arc::new(node))
    }

    /// Returns the shared node.
    #[must_use]
    pub fn node(&self) -> &TreeNode<M> {
        &self.0
    }

    /// Returns the node's constructor.
    #[must_use]
    pub fn tag(&self) -> CoreTag {
        *self.0.tag()
    }

    /// Returns the children in constructor order.
    ///
    /// Every child of every tag is reachable this way, so a traversal never
    /// needs to match on [`CoreTag`].
    #[must_use]
    pub fn children(&self) -> &[Self] {
        self.0.child_slice()
    }

    /// Returns the node's payload, if its constructor carries one.
    #[must_use]
    pub fn data(&self) -> Option<&CoreData> {
        self.0.data().as_ref()
    }

    /// Returns the node's annotation, if it has one.
    #[must_use]
    pub fn meta(&self) -> Option<&M> {
        self.0.meta().as_ref()
    }

    /// Returns whether two trees are the very same node.
    #[must_use]
    pub fn ptr_eq(left: &Self, right: &Self) -> bool {
        Arc::ptr_eq(&left.0, &right.0)
    }

    /// Returns a copy of this node carrying `meta`, sharing its children.
    #[must_use]
    pub fn with_meta(&self, meta: M) -> Self {
        Self::new(
            self.tag(),
            self.children().to_vec(),
            self.data().cloned(),
            Some(meta),
        )
    }

    fn leaf(tag: CoreTag, data: Option<CoreData>) -> Self {
        Self::new(tag, Vec::new(), data, None)
    }

    fn branch(tag: CoreTag, children: Vec<Self>) -> Self {
        Self::new(tag, children, None, None)
    }

    /// Builds `ty.base`: the uninterpreted base type called `name`.
    #[must_use]
    pub fn base(name: impl Into<String>) -> Self {
        Self::leaf(CoreTag::Base, Some(CoreData::Base { name: name.into() }))
    }

    /// Builds `ty.bool`: the type of Booleans.
    #[must_use]
    pub fn bool_ty() -> Self {
        Self::leaf(CoreTag::BoolTy, None)
    }

    /// Builds `ty.ind`: the infinite type of individuals.
    #[must_use]
    pub fn ind() -> Self {
        Self::leaf(CoreTag::Ind, None)
    }

    /// Builds `ty.arr`: the type of functions from `domain` to `codomain`.
    #[must_use]
    pub fn arr(domain: Self, codomain: Self) -> Self {
        Self::branch(CoreTag::Arr, vec![domain, codomain])
    }

    /// Builds `ty.sub`: the elements of `carrier` satisfying `predicate`.
    #[must_use]
    pub fn subtype(carrier: Self, predicate: Self) -> Self {
        Self::branch(CoreTag::Sub, vec![carrier, predicate])
    }

    /// Builds `tm.bound`: the variable `index` binders up.
    #[must_use]
    pub fn bound(index: u64) -> Self {
        Self::leaf(CoreTag::Bound, Some(CoreData::Bound { index }))
    }

    /// Builds `tm.free`: the free variable called `name`.
    #[must_use]
    pub fn free(name: u64) -> Self {
        Self::leaf(CoreTag::Free, Some(CoreData::Free { name }))
    }

    /// Builds `tm.app`: `function` applied to `argument`.
    #[must_use]
    pub fn app(function: Self, argument: Self) -> Self {
        Self::branch(CoreTag::App, vec![function, argument])
    }

    /// Builds `tm.lam`: the function taking a `domain` to `body`.
    #[must_use]
    pub fn lam(domain: Self, body: Self) -> Self {
        Self::branch(CoreTag::Lam, vec![domain, body])
    }

    /// Builds `tm.bool`: the Boolean literal `value`.
    #[must_use]
    pub fn bool(value: bool) -> Self {
        Self::leaf(CoreTag::Bool, Some(CoreData::Bool { value }))
    }

    /// Builds `tm.zero`.
    #[must_use]
    pub fn zero() -> Self {
        Self::leaf(CoreTag::Zero, None)
    }

    /// Builds `tm.succ`: the successor of `value`.
    #[must_use]
    pub fn succ(value: Self) -> Self {
        Self::branch(CoreTag::Succ, vec![value])
    }

    /// Builds `tm.eq`: `left` equals `right` at type `ty`.
    #[must_use]
    pub fn eqn(ty: Self, left: Self, right: Self) -> Self {
        Self::branch(CoreTag::Eqn, vec![ty, left, right])
    }

    /// Builds `tm.eps`: a chosen element of `ty` satisfying `predicate`.
    #[must_use]
    pub fn eps(ty: Self, predicate: Self) -> Self {
        Self::branch(CoreTag::Eps, vec![ty, predicate])
    }

    /// Builds `tm.abs`: `value` viewed as an element of the subtype.
    #[must_use]
    pub fn abs(carrier: Self, predicate: Self, value: Self) -> Self {
        Self::branch(CoreTag::Abs, vec![carrier, predicate, value])
    }

    /// Builds `tm.rep`: `value` viewed as an element of the carrier.
    #[must_use]
    pub fn rep(carrier: Self, predicate: Self, value: Self) -> Self {
        Self::branch(CoreTag::Rep, vec![carrier, predicate, value])
    }
}

impl<M> Clone for Tree<M> {
    /// Copies the pointer to the node; descendants are not cloned.
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<M: fmt::Debug> fmt::Debug for Tree<M> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

impl<M: PartialEq> PartialEq for Tree<M> {
    fn eq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other) || *self.0 == *other.0
    }
}

impl<M: Eq> Eq for Tree<M> {}

impl<M> From<TreeNode<M>> for Tree<M> {
    fn from(node: TreeNode<M>) -> Self {
        Self::from_node(node)
    }
}

#[cfg(test)]
mod tests {
    use super::{CoreData, CoreTag, Tree};

    /// A tree using every tag, with `shared` appearing twice.
    fn mixed() -> (Tree, Tree) {
        let shared = Tree::subtype(Tree::base("addr"), Tree::bound(0));
        let term = Tree::app(
            Tree::lam(
                Tree::arr(Tree::bool_ty(), Tree::ind()),
                Tree::eqn(
                    Tree::ind(),
                    Tree::succ(Tree::zero()),
                    Tree::abs(
                        shared.clone(),
                        Tree::bool(false),
                        Tree::rep(shared.clone(), Tree::bool(true), Tree::free(3)),
                    ),
                ),
            ),
            Tree::eps(shared.clone(), Tree::bool(true)),
        );

        (term, shared)
    }

    /// Visits every node, using only [`Tree::children`].
    fn visit(tree: &Tree, seen: &mut Vec<CoreTag>) {
        seen.push(tree.tag());
        for child in tree.children() {
            visit(child, seen);
        }
    }

    #[test]
    fn constructors_record_tag_arity_and_payload() {
        let application: Tree = Tree::app(Tree::bound(0), Tree::bool(true));

        assert_eq!(application.tag(), CoreTag::App);
        assert_eq!(application.children().len(), 2);
        assert_eq!(application.data(), None);
        assert_eq!(application.meta(), None);
        assert_eq!(
            application.children()[0].data(),
            Some(&CoreData::Bound { index: 0 })
        );
        assert_eq!(
            application.children()[1].data(),
            Some(&CoreData::Bool { value: true })
        );
        assert_eq!(
            Tree::<()>::base("addr").data(),
            Some(&CoreData::Base {
                name: "addr".to_owned()
            })
        );
        assert_eq!(
            Tree::<()>::free(9).data(),
            Some(&CoreData::Free { name: 9 })
        );
    }

    #[test]
    fn one_child_given_to_two_parents_stays_one_node() {
        let shared = Tree::<()>::zero();
        let left = Tree::succ(shared.clone());
        let right = Tree::eps(Tree::ind(), shared.clone());

        assert!(Tree::ptr_eq(&left.children()[0], &right.children()[1]));
        assert!(Tree::ptr_eq(&left.children()[0], &shared));
    }

    #[test]
    fn cloning_shares_the_root() {
        let tree = Tree::<()>::app(Tree::bound(0), Tree::bool(true));
        let clone = tree.clone();

        assert!(Tree::ptr_eq(&tree, &clone));
        for (original, cloned) in tree.children().iter().zip(clone.children()) {
            assert!(Tree::ptr_eq(original, cloned));
        }
    }

    #[test]
    fn rebuilding_a_parent_does_not_rebuild_its_children() {
        let child = Tree::<()>::bool(true);
        let parent = Tree::succ(child.clone());
        let rebuilt = Tree::succ(child.clone());

        assert!(!Tree::ptr_eq(&parent, &rebuilt));
        assert!(Tree::ptr_eq(&parent.children()[0], &rebuilt.children()[0]));
        assert_eq!(parent, rebuilt);
    }

    #[test]
    fn traversal_needs_only_children() {
        let (term, _) = mixed();
        let mut seen = Vec::new();
        visit(&term, &mut seen);

        assert_eq!(seen.len(), 25);
        for tag in [
            CoreTag::Base,
            CoreTag::BoolTy,
            CoreTag::Ind,
            CoreTag::Arr,
            CoreTag::Sub,
            CoreTag::Bound,
            CoreTag::Free,
            CoreTag::App,
            CoreTag::Lam,
            CoreTag::Bool,
            CoreTag::Zero,
            CoreTag::Succ,
            CoreTag::Eqn,
            CoreTag::Eps,
            CoreTag::Abs,
            CoreTag::Rep,
        ] {
            assert!(seen.contains(&tag), "{tag:?} was never visited");
        }
    }

    #[test]
    fn a_shared_subtree_is_visited_once_per_occurrence() {
        let (term, shared) = mixed();
        let mut seen = Vec::new();
        visit(&term, &mut seen);

        assert_eq!(
            seen.iter().filter(|tag| **tag == CoreTag::Sub).count(),
            3,
            "the shared subtype occurs three times"
        );
        assert_eq!(shared.tag(), CoreTag::Sub);
    }

    #[test]
    fn annotating_a_node_shares_its_children() {
        let tree = Tree::app(Tree::bound(0), Tree::bool(true));
        let annotated = tree.with_meta("root");

        assert_eq!(annotated.meta(), Some(&"root"));
        assert_eq!(annotated.tag(), tree.tag());
        assert!(!Tree::ptr_eq(&tree, &annotated));
        for (original, kept) in tree.children().iter().zip(annotated.children()) {
            assert!(Tree::ptr_eq(original, kept));
        }
    }
}
