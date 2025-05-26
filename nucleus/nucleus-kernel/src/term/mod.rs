use arrayvec::ArrayVec;

use crate::kernel::{CtxId, TermId};

/// A node making up an expression
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum GNode<T> {
    // Basic Martin-Löf type formers
    /// A context variable
    Cv(CtxId, u32),
    /// A bound variable
    Bv(u16),
    /// A typing universe
    U(ULevel),
    /// A dependent function type
    Pi([T; 2]),
    /// A lambda abstraction
    Abs([T; 2]),
    /// An application
    App([T; 4]),
    /// A let-binding
    Let([T; 3]),
    /// The identity type
    Is([T; 3]),
    /// A type annotation
    //Note: we have room for a u64 of data here, think about this...
    Annot([T; 2]),

    // Propositional logic
    /// The boolean propositions
    Bool(bool),
    /// Dependent if-then-else
    Dite([T; 4]),
    /// Check whether the given type is nonempty
    Trunc([T; 1]),

    // Type theory
    /// Hilbert's ε operator
    Epsilon([T; 1]),

    // Builtins
    /// The type of natural numbers
    Nat,
    /// A small natural number
    SmallNat(u64),
    /// The type of integers
    Int,
    /// A small integer
    SmallInt(i64),
    // TODO:
    // - natural recursor
    // - integer recursor
    // - bitvectors
    // - bytes
    // - bytevectors
    // - arithmetic + logic operations
    // - constant handles

    // Structure types
    /// The structure type corresponding to a child context
    Struct(CtxId),
    /// The constructor for a structure type
    Mk(CtxId),
    /// A projection from a structure type
    Proj(CtxId, u32),

    // Data structures:
    //TODO:
    // - coproducts (or do we just implement these ourselves?)
    // - W-types/inductives (or do we just implement these ourselves?)

    // Syntactic operations
    /// Close a term from a child context
    Close(Close),

    // Contexts
    /// The null context
    NilCtx,
    /// Append a variable to the right of the current context, at the given depth
    ConsCtx(u16, [T; 2]),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Close {
    /// The number of binders ignored
    pub binders: u16,
    /// The number of parameters clsoed over
    pub params: u16,
    /// The source context
    pub src: CtxId,
    /// The term id of the closed term
    pub tm: TermId,
}

pub type Node32 = GNode<u32>;

impl<T> GNode<T> {
    /// Map this node's index type
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> GNode<U> {
        match self {
            GNode::Cv(c, x) => GNode::Cv(c, x),
            GNode::Bv(x) => GNode::Bv(x),
            GNode::U(x) => GNode::U(x),
            GNode::Pi([x, y]) => GNode::Pi([f(x), f(y)]),
            GNode::Abs([x, y]) => GNode::Abs([f(x), f(y)]),
            GNode::App([x, y, z, w]) => GNode::App([f(x), f(y), f(z), f(w)]),
            GNode::Let([x, y, z]) => GNode::Let([f(x), f(y), f(z)]),
            GNode::Is([x, y, z]) => GNode::Is([f(x), f(y), f(z)]),
            GNode::Annot([x, y]) => GNode::Annot([f(x), f(y)]),
            GNode::Bool(x) => GNode::Bool(x),
            GNode::Dite([x, y, z, w]) => GNode::Dite([f(x), f(y), f(z), f(w)]),
            GNode::Trunc([x]) => GNode::Trunc([f(x)]),
            GNode::Epsilon([x]) => GNode::Epsilon([f(x)]),
            GNode::Nat => GNode::Nat,
            GNode::SmallNat(x) => GNode::SmallNat(x),
            GNode::Int => GNode::Int,
            GNode::SmallInt(x) => GNode::SmallInt(x),
            GNode::Struct(x) => GNode::Struct(x),
            GNode::Mk(x) => GNode::Mk(x),
            GNode::Proj(x, y) => GNode::Proj(x, y),
            GNode::Close(c) => GNode::Close(c),
            GNode::NilCtx => GNode::NilCtx,
            GNode::ConsCtx(l, [x, y]) => GNode::ConsCtx(l, [f(x), f(y)]),
        }
    }

    /// Map this node's index type, or error
    pub fn map_err<U, E>(self, mut f: impl FnMut(T) -> Result<U, E>) -> Result<GNode<U>, E> {
        match self {
            GNode::Cv(c, x) => Ok(GNode::Cv(c, x)),
            GNode::Bv(x) => Ok(GNode::Bv(x)),
            GNode::U(x) => Ok(GNode::U(x)),
            GNode::Pi([x, y]) => Ok(GNode::Pi([f(x)?, f(y)?])),
            GNode::Abs([x, y]) => Ok(GNode::Abs([f(x)?, f(y)?])),
            GNode::App([x, y, z, w]) => Ok(GNode::App([f(x)?, f(y)?, f(z)?, f(w)?])),
            GNode::Let([x, y, z]) => Ok(GNode::Let([f(x)?, f(y)?, f(z)?])),
            GNode::Is([x, y, z]) => Ok(GNode::Is([f(x)?, f(y)?, f(z)?])),
            GNode::Annot([x, y]) => Ok(GNode::Annot([f(x)?, f(y)?])),
            GNode::Bool(x) => Ok(GNode::Bool(x)),
            GNode::Dite([x, y, z, w]) => Ok(GNode::Dite([f(x)?, f(y)?, f(z)?, f(w)?])),
            GNode::Trunc([x]) => Ok(GNode::Trunc([f(x)?])),
            GNode::Epsilon([x]) => Ok(GNode::Epsilon([f(x)?])),
            GNode::Nat => Ok(GNode::Nat),
            GNode::SmallNat(x) => Ok(GNode::SmallNat(x)),
            GNode::Int => Ok(GNode::Int),
            GNode::SmallInt(x) => Ok(GNode::SmallInt(x)),
            GNode::Struct(x) => Ok(GNode::Struct(x)),
            GNode::Mk(x) => Ok(GNode::Mk(x)),
            GNode::Proj(x, y) => Ok(GNode::Proj(x, y)),
            GNode::Close(c) => Ok(GNode::Close(c)),
            GNode::NilCtx => Ok(GNode::NilCtx),
            GNode::ConsCtx(l, [x, y]) => Ok(GNode::ConsCtx(l, [f(x)?, f(y)?])),
        }
    }

    /// Annotate this node's indices with their binders
    pub fn with_binders(self) -> GNode<(u16, T)> {
        match self {
            GNode::Cv(c, x) => GNode::Cv(c, x),
            GNode::Bv(x) => GNode::Bv(x),
            GNode::U(x) => GNode::U(x),
            GNode::Pi([x, y]) => GNode::Pi([(0, x), (1, y)]),
            GNode::Abs([x, y]) => GNode::Abs([(0, x), (1, y)]),
            GNode::App([x, y, z, w]) => GNode::App([(0, x), (1, y), (0, z), (0, w)]),
            GNode::Let([x, y, z]) => GNode::Let([(0, x), (0, y), (1, z)]),
            GNode::Is([x, y, z]) => GNode::Is([(0, x), (0, y), (0, z)]),
            GNode::Annot([x, y]) => GNode::Annot([(0, x), (0, y)]),
            GNode::Bool(x) => GNode::Bool(x),
            GNode::Dite([x, y, z, w]) => GNode::Dite([(0, x), (0, y), (1, z), (1, w)]),
            GNode::Trunc([x]) => GNode::Trunc([(0, x)]),
            GNode::Epsilon([x]) => GNode::Epsilon([(0, x)]),
            GNode::Nat => GNode::Nat,
            GNode::SmallNat(x) => GNode::SmallNat(x),
            GNode::Int => GNode::Int,
            GNode::SmallInt(x) => GNode::SmallInt(x),
            GNode::Struct(x) => GNode::Struct(x),
            GNode::Mk(x) => GNode::Mk(x),
            GNode::Proj(x, y) => GNode::Proj(x, y),
            GNode::Close(c) => GNode::Close(c),
            GNode::NilCtx => GNode::NilCtx,
            GNode::ConsCtx(l, [x, y]) => GNode::ConsCtx(l, [(0, x), (l, y)]),
        }
    }

    /// Borrow this node's index type
    pub fn as_ref(&self) -> GNode<&T> {
        match self {
            GNode::Cv(c, x) => GNode::Cv(*c, *x),
            GNode::Bv(x) => GNode::Bv(*x),
            GNode::U(x) => GNode::U(*x),
            GNode::Pi([x, y]) => GNode::Pi([x, y]),
            GNode::Abs([x, y]) => GNode::Abs([x, y]),
            GNode::App([x, y, z, w]) => GNode::App([x, y, z, w]),
            GNode::Let([x, y, z]) => GNode::Let([x, y, z]),
            GNode::Is([x, y, z]) => GNode::Is([x, y, z]),
            GNode::Annot([x, y]) => GNode::Annot([x, y]),
            GNode::Bool(x) => GNode::Bool(*x),
            GNode::Dite([x, y, z, w]) => GNode::Dite([x, y, z, w]),
            GNode::Trunc([x]) => GNode::Trunc([x]),
            GNode::Epsilon([x]) => GNode::Epsilon([x]),
            GNode::Nat => GNode::Nat,
            GNode::SmallNat(x) => GNode::SmallNat(*x),
            GNode::Int => GNode::Int,
            GNode::SmallInt(x) => GNode::SmallInt(*x),
            GNode::Struct(x) => GNode::Struct(*x),
            GNode::Mk(x) => GNode::Mk(*x),
            GNode::Proj(x, y) => GNode::Proj(*x, *y),
            GNode::Close(c) => GNode::Close(*c),
            GNode::NilCtx => GNode::NilCtx,
            GNode::ConsCtx(l, [x, y]) => GNode::ConsCtx(*l, [x, y]),
        }
    }

    /// Mutably borrow this node's index type
    pub fn as_mut(&mut self) -> GNode<&mut T> {
        match self {
            GNode::Cv(c, x) => GNode::Cv(*c, *x),
            GNode::Bv(x) => GNode::Bv(*x),
            GNode::U(x) => GNode::U(*x),
            GNode::Pi([x, y]) => GNode::Pi([x, y]),
            GNode::Abs([x, y]) => GNode::Abs([x, y]),
            GNode::App([x, y, z, w]) => GNode::App([x, y, z, w]),
            GNode::Let([x, y, z]) => GNode::Let([x, y, z]),
            GNode::Is([x, y, z]) => GNode::Is([x, y, z]),
            GNode::Annot([x, y]) => GNode::Annot([x, y]),
            GNode::Bool(x) => GNode::Bool(*x),
            GNode::Dite([x, y, z, w]) => GNode::Dite([x, y, z, w]),
            GNode::Trunc([x]) => GNode::Trunc([x]),
            GNode::Epsilon([x]) => GNode::Epsilon([x]),
            GNode::Nat => GNode::Nat,
            GNode::SmallNat(x) => GNode::SmallNat(*x),
            GNode::Int => GNode::Int,
            GNode::SmallInt(x) => GNode::SmallInt(*x),
            GNode::Struct(x) => GNode::Struct(*x),
            GNode::Mk(x) => GNode::Mk(*x),
            GNode::Proj(x, y) => GNode::Proj(*x, *y),
            GNode::Close(c) => GNode::Close(*c),
            GNode::NilCtx => GNode::NilCtx,
            GNode::ConsCtx(l, [x, y]) => GNode::ConsCtx(*l, [x, y]),
        }
    }

    /// Get this node's children
    pub fn children(&self) -> &[T] {
        match self {
            GNode::Pi(x) => &x[..],
            GNode::Abs(x) => &x[..],
            GNode::App(x) => &x[..],
            GNode::Let(x) => &x[..],
            GNode::Is(x) => &x[..],
            GNode::Annot(x) => &x[..],
            GNode::Dite(x) => &x[..],
            GNode::Trunc(x) => &x[..],
            GNode::Epsilon(x) => &x[..],
            _ => &[],
        }
    }

    /// Get this node's children
    pub fn children_mut(&mut self) -> &mut [T] {
        match self {
            GNode::Pi(x) => &mut x[..],
            GNode::Abs(x) => &mut x[..],
            GNode::App(x) => &mut x[..],
            GNode::Let(x) => &mut x[..],
            GNode::Is(x) => &mut x[..],
            GNode::Annot(x) => &mut x[..],
            GNode::Dite(x) => &mut x[..],
            GNode::Trunc(x) => &mut x[..],
            GNode::Epsilon(x) => &mut x[..],
            _ => &mut [],
        }
    }

    /// Get the number of binders for each child of this node
    pub fn binders(&self) -> ArrayVec<u16, 5> {
        match self {
            GNode::Pi(_) => [0, 1].into_iter().collect(),
            GNode::Abs(_) => [0, 1].into_iter().collect(),
            GNode::App(_) => [0, 1, 0, 0].into_iter().collect(),
            GNode::Let(_) => [0, 0, 1].into_iter().collect(),
            GNode::Is(_) => [0, 0, 0].into_iter().collect(),
            GNode::Annot(_) => [0, 0].into_iter().collect(),
            GNode::Dite(_) => [0, 0, 1, 1].into_iter().collect(),
            GNode::Trunc(_) => [1].into_iter().collect(),
            GNode::Epsilon(_) => [1].into_iter().collect(),
            GNode::ConsCtx(l, _) => [0, *l].into_iter().collect(),
            _ => ArrayVec::new(),
        }
    }

    /// Check whether two nodes are known-incompatible
    pub fn incompatible<U>(&self, other: &GNode<U>) -> bool {
        match (self, other) {
            (GNode::Bool(x), GNode::Bool(y)) => x != y,
            _ => false,
        }
    }
}

/// A typing universe
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct ULevel {
    level: u32,
}

impl ULevel {
    /// The universe level of propositions
    pub const PROP: Self = Self { level: 0 };

    /// The universe level of sets
    pub const SET: Self = Self { level: 1 };

    /// The maximum universe level
    pub const MAX: Self = Self { level: u32::MAX };

    /// The successor of this universe level
    ///
    /// # Panics
    /// If incrementing this universe level would overflow
    pub fn succ(&self) -> Self {
        Self {
            level: self.level.checked_add(1).expect("universe level overflow"),
        }
    }

    /// Take the maximum of two universe levels
    pub fn max(&self, other: ULevel) -> Self {
        Self {
            level: self.level.max(other.level),
        }
    }

    /// Take the impredicative maximum of two universe levels
    pub fn imax(&self, other: ULevel) -> Self {
        Self {
            level: if other.level == 0 {
                0
            } else {
                self.level.max(other.level)
            },
        }
    }
}
