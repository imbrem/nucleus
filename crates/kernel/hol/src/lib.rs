//! Representation-parametric higher-order logic syntax.
//!
//! A [`Hol`] node is a tag, its children, an optional constructor payload, and
//! an optional annotation. Every one of those four is supplied by a [`Repr`]
//! implementation, so the same node shape describes both the recursively
//! shared tree in this crate and, later, representations that store children
//! some other way.
//!
//! [`Tree`] is the only representation implemented here. Its children are held
//! behind [`Arc`](std::sync::Arc), so cloning a tree copies one pointer and
//! two parents can observably share a subtree. It round-trips through the
//! direct JSON encoding described on [`Tree`], whose shape is experimental and
//! carries no stability promise.
//!
//! This is syntax and nothing more. Nothing here checks arity, scoping, or
//! typing, and deserializing a tree establishes no judgment about it.
//!
//! ```
//! use covalence_kernel_hol::{CoreTag, Tree};
//!
//! // (fun (x : bool) => x) true
//! let identity = Tree::<()>::lam(Tree::bool_ty(), Tree::bound(0));
//! let applied = Tree::app(identity, Tree::bool(true));
//!
//! assert_eq!(applied.tag(), CoreTag::App);
//! assert_eq!(applied.children().len(), 2);
//! ```

use std::fmt;

mod json;
mod syntax;
mod tree;

pub use syntax::{CoreData, CoreTag};
pub use tree::{Tree, TreeNode, TreeRepr};

/// How a family of [`Hol`] nodes stores its parts.
///
/// The associated types are deliberately unconstrained: a representation is
/// free to make children a `Vec` of shared pointers, a range of arena
/// positions, or anything else, and to carry no payload or annotation at all.
pub trait Repr {
    /// The node's constructor label.
    type Tag;

    /// How a node names one of its children.
    type Index;

    /// A node's children, in constructor order.
    type Children;

    /// The constructor-specific payload of a node.
    type Data;

    /// The caller-defined annotation on a node.
    type Meta;
}

/// One syntax node stored as `R` stores it.
///
/// The four parts stay separate: reading a node's children, its payload, or
/// its annotation never requires matching on its tag.
pub struct Hol<R: Repr> {
    tag: R::Tag,
    children: R::Children,
    data: R::Data,
    meta: R::Meta,
}

impl<R: Repr> Hol<R> {
    /// Assembles a node from its four parts.
    ///
    /// No arity, scope, or type invariant is checked; a node is only a node.
    #[must_use]
    pub fn new(tag: R::Tag, children: R::Children, data: R::Data, meta: R::Meta) -> Self {
        Self {
            tag,
            children,
            data,
            meta,
        }
    }

    /// Returns the node's constructor label.
    #[must_use]
    pub fn tag(&self) -> &R::Tag {
        &self.tag
    }

    /// Returns the node's children, however this representation stores them.
    #[must_use]
    pub fn children(&self) -> &R::Children {
        &self.children
    }

    /// Returns the node's constructor payload.
    #[must_use]
    pub fn data(&self) -> &R::Data {
        &self.data
    }

    /// Returns the node's annotation.
    #[must_use]
    pub fn meta(&self) -> &R::Meta {
        &self.meta
    }

    /// Splits the node into its four parts.
    #[must_use]
    pub fn into_parts(self) -> (R::Tag, R::Children, R::Data, R::Meta) {
        (self.tag, self.children, self.data, self.meta)
    }
}

impl<R: Repr> Hol<R>
where
    R::Children: AsRef<[R::Index]>,
{
    /// Returns the children in constructor order.
    ///
    /// This is the tag-independent traversal: every child of every node is
    /// reachable without knowing which constructor produced it.
    #[must_use]
    pub fn child_slice(&self) -> &[R::Index] {
        self.children.as_ref()
    }

    /// Returns how many children the node has.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.child_slice().len()
    }
}

impl<R: Repr> Clone for Hol<R>
where
    R::Tag: Clone,
    R::Children: Clone,
    R::Data: Clone,
    R::Meta: Clone,
{
    fn clone(&self) -> Self {
        Self {
            tag: self.tag.clone(),
            children: self.children.clone(),
            data: self.data.clone(),
            meta: self.meta.clone(),
        }
    }
}

impl<R: Repr> fmt::Debug for Hol<R>
where
    R::Tag: fmt::Debug,
    R::Children: fmt::Debug,
    R::Data: fmt::Debug,
    R::Meta: fmt::Debug,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Hol")
            .field("tag", &self.tag)
            .field("children", &self.children)
            .field("data", &self.data)
            .field("meta", &self.meta)
            .finish()
    }
}

impl<R: Repr> PartialEq for Hol<R>
where
    R::Tag: PartialEq,
    R::Children: PartialEq,
    R::Data: PartialEq,
    R::Meta: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag
            && self.children == other.children
            && self.data == other.data
            && self.meta == other.meta
    }
}

impl<R: Repr> Eq for Hol<R>
where
    R::Tag: Eq,
    R::Children: Eq,
    R::Data: Eq,
    R::Meta: Eq,
{
}
