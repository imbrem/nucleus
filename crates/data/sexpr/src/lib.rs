//! Representation-neutral S-expression trees and structural views.
//!
//! An [`SExpr`] is either an atom or an ordered list of S-expressions. A
//! [`TExpr`] is either an atom or an ordered node with a tag and children.
//! Empty collections are valid, and child order and multiplicity are semantic.
//! Tags occupy a namespace distinct from atoms.
//! [`Symbol`] is the default owned representation for both atoms and tags;
//! callers can select domain-specific types through the generic parameters.
//!
//! [`SView`] and [`TView`] expose one valid node at a time without allocating.
//! Implementors validate external data, handles, acyclicity, and resource
//! limits before exposing an infallible view. The traits do not promise
//! ownership, mutation, construction, stable identity, random access,
//! serialization, interning, or any particular storage strategy.
//!
//! [`sax`] provides a streaming event boundary for constructing and emitting
//! values without requiring an intermediate tree. [`text`] provides one small,
//! documented textual dialect on top of that boundary.
//!
//! This crate intentionally contains no arena, matcher, unifier, or implicit
//! conversion between tagged and untagged trees.

#![deny(unsafe_code)]

pub use covalence_data_symbol::Symbol;

pub mod sax;
pub mod text;

/// A canonical owned S-expression.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SExpr<A = Symbol> {
    /// An atom.
    Atom(A),
    /// An ordered sequence of S-expressions.
    List(Vec<Self>),
}

impl<A> SExpr<A> {
    /// Constructs an atom.
    pub fn atom(atom: A) -> Self {
        Self::Atom(atom)
    }

    /// Constructs a list.
    pub fn list(children: impl Into<Vec<Self>>) -> Self {
        Self::List(children.into())
    }

    /// Borrows the atom, or returns `None` for a list.
    #[must_use]
    pub const fn as_atom(&self) -> Option<&A> {
        match self {
            Self::Atom(atom) => Some(atom),
            Self::List(_) => None,
        }
    }

    /// Borrows the list children, or returns `None` for an atom.
    #[must_use]
    pub fn as_list(&self) -> Option<&[Self]> {
        match self {
            Self::Atom(_) => None,
            Self::List(children) => Some(children),
        }
    }
}

/// A canonical owned tagged expression.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TExpr<T = Symbol, A = Symbol> {
    /// An atom.
    Atom(A),
    /// A tag and its ordered children.
    Node(T, Vec<Self>),
}

impl<T, A> TExpr<T, A> {
    /// Constructs an atom.
    pub fn atom(atom: A) -> Self {
        Self::Atom(atom)
    }

    /// Constructs a tagged node.
    pub fn node(tag: T, children: impl Into<Vec<Self>>) -> Self {
        Self::Node(tag, children.into())
    }

    /// Borrows the atom, or returns `None` for a node.
    #[must_use]
    pub const fn as_atom(&self) -> Option<&A> {
        match self {
            Self::Atom(atom) => Some(atom),
            Self::Node(_, _) => None,
        }
    }

    /// Borrows the tag and children, or returns `None` for an atom.
    #[must_use]
    pub fn as_node(&self) -> Option<(&T, &[Self])> {
        match self {
            Self::Atom(_) => None,
            Self::Node(tag, children) => Some((tag, children)),
        }
    }
}

/// A non-recursive observation of one S-expression layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SNode<A = Symbol, C = Vec<SExpr<A>>> {
    /// An atom.
    Atom(A),
    /// An ordered collection of children.
    List(C),
}

/// A non-recursive observation of one tagged-expression layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TNode<T = Symbol, A = Symbol, C = Vec<TExpr<T, A>>> {
    /// An atom.
    Atom(A),
    /// A tag and an ordered collection of children.
    Node(T, C),
}

/// Read-only structural observation of an S-expression.
///
/// `view` is infallible and allocation-free. Children are yielded in semantic
/// order, but need not be contiguous, clonable, double-ended, or addressable by
/// index. Implementors must only construct a view after validating fallible
/// external representations.
pub trait SView {
    /// The borrowed atom representation.
    type Atom: ?Sized;

    /// A lightweight view of a child.
    type Child<'a>: SView<Atom = Self::Atom> + 'a
    where
        Self: 'a;

    /// The ordered child iterator.
    type Children<'a>: Iterator<Item = Self::Child<'a>> + 'a
    where
        Self: 'a;

    /// Observes one layer without allocation.
    fn view(&self) -> SNode<&Self::Atom, Self::Children<'_>>;
}

/// Read-only structural observation of a tagged expression.
///
/// `view` is infallible and allocation-free. Tags and atoms are separate
/// associated types: this trait does not encode tags as atoms. Implementors
/// must validate fallible external representations before producing a view.
pub trait TView {
    /// The borrowed tag representation.
    type Tag: ?Sized;
    /// The borrowed atom representation.
    type Atom: ?Sized;

    /// A lightweight view of a child.
    type Child<'a>: TView<Tag = Self::Tag, Atom = Self::Atom> + 'a
    where
        Self: 'a;

    /// The ordered child iterator.
    type Children<'a>: Iterator<Item = Self::Child<'a>> + 'a
    where
        Self: 'a;

    /// Observes one layer without allocation.
    fn view(&self) -> TNode<&Self::Tag, &Self::Atom, Self::Children<'_>>;
}

impl<A> SView for SExpr<A> {
    type Atom = A;
    type Child<'a>
        = &'a Self
    where
        Self: 'a;
    type Children<'a>
        = std::slice::Iter<'a, Self>
    where
        Self: 'a;

    fn view(&self) -> SNode<&A, Self::Children<'_>> {
        match self {
            Self::Atom(atom) => SNode::Atom(atom),
            Self::List(children) => SNode::List(children.iter()),
        }
    }
}

impl<T, A> TView for TExpr<T, A> {
    type Tag = T;
    type Atom = A;
    type Child<'a>
        = &'a Self
    where
        Self: 'a;
    type Children<'a>
        = std::slice::Iter<'a, Self>
    where
        Self: 'a;

    fn view(&self) -> TNode<&T, &A, Self::Children<'_>> {
        match self {
            Self::Atom(atom) => TNode::Atom(atom),
            Self::Node(tag, children) => TNode::Node(tag, children.iter()),
        }
    }
}

impl<V: SView + ?Sized> SView for &V {
    type Atom = V::Atom;
    type Child<'a>
        = V::Child<'a>
    where
        Self: 'a;
    type Children<'a>
        = V::Children<'a>
    where
        Self: 'a;

    fn view(&self) -> SNode<&Self::Atom, Self::Children<'_>> {
        (**self).view()
    }
}

impl<V: TView + ?Sized> TView for &V {
    type Tag = V::Tag;
    type Atom = V::Atom;
    type Child<'a>
        = V::Child<'a>
    where
        Self: 'a;
    type Children<'a>
        = V::Children<'a>
    where
        Self: 'a;

    fn view(&self) -> TNode<&Self::Tag, &Self::Atom, Self::Children<'_>> {
        (**self).view()
    }
}

#[cfg(test)]
mod tests {
    use super::{SExpr, SNode, SView, Symbol, TExpr, TNode, TView};

    fn atoms<V>(root: V) -> Vec<String>
    where
        V: SView,
        V::Atom: ToString,
    {
        fn visit<V>(value: V, output: &mut Vec<String>)
        where
            V: SView,
            V::Atom: ToString,
        {
            match value.view() {
                SNode::Atom(atom) => output.push(atom.to_string()),
                SNode::List(children) => {
                    for child in children {
                        visit(child, output);
                    }
                }
            }
        }

        let mut output = Vec::new();
        visit(root, &mut output);
        output
    }

    #[test]
    fn owned_s_expressions_preserve_structure() {
        let expression = SExpr::list(vec![
            SExpr::atom("a"),
            SExpr::list(Vec::new()),
            SExpr::atom("a"),
            SExpr::list(vec![SExpr::atom("b")]),
        ]);

        assert_eq!(atoms(&expression), ["a", "a", "b"]);
        let children = expression.as_list().expect("a list");
        assert_eq!(children.len(), 4);
        assert_eq!(children[0].as_atom(), Some(&"a"));
        assert_eq!(children[1].as_list(), Some([].as_slice()));
    }

    #[test]
    fn symbols_are_the_default_owned_atom_and_tag() {
        let expression: SExpr = SExpr::atom(Symbol::new("atom"));
        let tagged: TExpr = TExpr::node(Symbol::new("tag"), vec![TExpr::atom(Symbol::new("atom"))]);

        assert_eq!(expression.as_atom().expect("atom").as_str(), "atom");
        assert_eq!(tagged.as_node().expect("node").0.as_str(), "tag");
    }

    #[test]
    fn tagged_nodes_keep_tags_and_atoms_separate() {
        let expression = TExpr::node(
            "tag",
            vec![
                TExpr::atom("tag"),
                TExpr::node("empty", Vec::<TExpr<&str, &str>>::new()),
            ],
        );

        match expression.view() {
            TNode::Node(tag, mut children) => {
                assert_eq!(*tag, "tag");
                assert!(matches!(
                    children.next().map(TView::view),
                    Some(TNode::Atom(atom)) if *atom == "tag"
                ));
                assert!(matches!(
                    children.next().map(TView::view),
                    Some(TNode::Node(child_tag, _)) if *child_tag == "empty"
                ));
                assert!(children.next().is_none());
            }
            TNode::Atom(_) => panic!("expected node"),
        }
    }

    /// An arena whose children are IDs rather than nested or contiguous values.
    struct Arena {
        nodes: Vec<Record>,
    }

    enum Record {
        Atom(String),
        List(Vec<usize>),
    }

    #[derive(Clone, Copy)]
    struct Indexed<'a> {
        arena: &'a Arena,
        id: usize,
    }

    struct IndexedChildren<'a, 'b> {
        arena: &'a Arena,
        ids: std::slice::Iter<'b, usize>,
    }

    impl<'a> Iterator for IndexedChildren<'a, '_> {
        type Item = Indexed<'a>;

        fn next(&mut self) -> Option<Self::Item> {
            self.ids.next().map(|id| Indexed {
                arena: self.arena,
                id: *id,
            })
        }
    }

    impl<'a> SView for Indexed<'a> {
        type Atom = str;
        type Child<'b>
            = Self
        where
            Self: 'b;
        type Children<'b>
            = IndexedChildren<'a, 'b>
        where
            Self: 'b;

        fn view(&self) -> SNode<&str, Self::Children<'_>> {
            match &self.arena.nodes[self.id] {
                Record::Atom(atom) => SNode::Atom(atom),
                Record::List(ids) => SNode::List(IndexedChildren {
                    arena: self.arena,
                    ids: ids.iter(),
                }),
            }
        }
    }

    #[test]
    fn generic_traversal_accepts_an_indexed_representation() {
        // Decoder/validator establishes that every ID is in range and the
        // reachable structure is an acyclic tree before constructing Indexed.
        let arena = Arena {
            nodes: vec![
                Record::Atom("first".into()),
                Record::Atom("second".into()),
                Record::List(vec![]),
                Record::List(vec![1, 2, 0, 1]),
            ],
        };

        assert_eq!(
            atoms(Indexed {
                arena: &arena,
                id: 3,
            }),
            ["second", "first", "second"]
        );
    }
}
