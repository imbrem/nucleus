//! Sorts, tags, branded ids, and substrate-parametric syntax nodes.
//!
//! The tag vocabulary and per-tag coordinate meanings are fixed by
//! `hol/semantics.txt`. Node enums are parametric over a [`Substrate`],
//! the index family saying what a child reference is: [`Ids`] for
//! interned in-store children (the kernel's working substrate), with
//! in-memory tree substrates layered on top by later changes.

use std::marker::PhantomData;

/// Invariant lifetime brand tying ids to the view that produced them.
pub(crate) type Invariant<'v> = PhantomData<fn(&'v ()) -> &'v ()>;

/// Object tags, numbered exactly as in `hol/semantics.txt`.
pub(crate) mod tag {
    pub const K_STAR: i64 = 1;
    pub const K_ARR: i64 = 2;
    pub const TY_BV: i64 = 3;
    pub const TY_LAM: i64 = 4;
    pub const TY_APP: i64 = 5;
    pub const TY_ALL: i64 = 6;
    pub const TY_BOOL: i64 = 7;
    pub const TY_ARR: i64 = 8;
    pub const TY_SUB: i64 = 9;
    pub const TY_IND: i64 = 10;
    pub const TY_EXT: i64 = 11;
    pub const TM_BV: i64 = 12;
    pub const TM_APP: i64 = 13;
    pub const TM_LAM: i64 = 14;
    pub const TM_TYAPP: i64 = 15;
    pub const TM_TYLAM: i64 = 16;
    pub const TM_BOOL: i64 = 17;
    pub const TM_EQ: i64 = 18;
    pub const TM_EPS: i64 = 19;
    pub const TM_ABS: i64 = 20;
    pub const TM_REP: i64 = 21;
    pub const TM_EXT: i64 = 22;
    pub const KS: i64 = 23;
    pub const VS: i64 = 24;
    pub const HS: i64 = 25;
}

/// Sort classes of object rows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sort {
    /// Kinds (`K_*`).
    Kind,
    /// Types (`TY_*`).
    Type,
    /// Terms (`TM_*`).
    Term,
    /// Kind-context spines (`KS`).
    Kinds,
    /// Variable-context spines (`VS`).
    Vars,
    /// Hypothesis spines (`HS`).
    Hyps,
}

/// Returns the sort class of a tag, if the tag is known.
pub(crate) const fn sort_of_tag(tag: i64) -> Option<Sort> {
    match tag {
        tag::K_STAR..=tag::K_ARR => Some(Sort::Kind),
        tag::TY_BV..=tag::TY_EXT => Some(Sort::Type),
        tag::TM_BV..=tag::TM_EXT => Some(Sort::Term),
        tag::KS => Some(Sort::Kinds),
        tag::VS => Some(Sort::Vars),
        tag::HS => Some(Sort::Hyps),
        _ => None,
    }
}

macro_rules! branded_id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name<'v>(pub(crate) i64, pub(crate) Invariant<'v>);

        impl<'v> $name<'v> {
            /// Returns the raw row id for serialization and transport.
            ///
            /// A raw integer re-enters the kernel only through the view's
            /// checked `*_from_raw` operations.
            #[must_use]
            pub const fn raw(self) -> i64 {
                self.0
            }

            pub(crate) const fn new(raw: i64) -> Self {
                Self(raw, PhantomData)
            }
        }
    };
}

branded_id!(
    /// An interned kind, valid for the producing view's lifetime.
    KindId
);
branded_id!(
    /// An interned type, valid for the producing view's lifetime.
    TypeId
);
branded_id!(
    /// An interned term, valid for the producing view's lifetime.
    TermId
);
branded_id!(
    /// A kind-context spine (0 is the empty context).
    KindsId
);
branded_id!(
    /// A variable-context spine (0 is the empty context).
    VarsId
);
branded_id!(
    /// A canonical hypothesis spine (0 is the empty set).
    HypsId
);
branded_id!(
    /// A registered external source (`hol_source` row).
    SourceId
);

/// Index family for syntax nodes: what a child reference is.
pub trait Substrate {
    /// Kind children.
    type Kind;
    /// Type children.
    type Ty;
    /// Term children.
    type Tm;
    /// Source references.
    type Src;
}
// Node impls carry their bounds on the associated types rather than the
// trait, so recursive substrates (whose children mention the substrate's
// own node types) do not send trait-bound checking into a cycle.

/// The in-store substrate: children are interned branded ids.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Ids<'v>(Invariant<'v>);

impl<'v> Substrate for Ids<'v> {
    type Kind = KindId<'v>;
    type Ty = TypeId<'v>;
    type Tm = TermId<'v>;
    type Src = SourceId<'v>;
}

/// A kind node.
#[expect(missing_docs, reason = "constructors are specified in semantics.txt")]
pub enum Kind<S: Substrate> {
    Star,
    Arr(S::Kind, S::Kind),
}

/// A type node.
#[expect(missing_docs, reason = "constructors are specified in semantics.txt")]
pub enum Ty<S: Substrate> {
    Bv(u32),
    Lam(S::Kind, S::Ty),
    App(S::Ty, S::Ty),
    All(S::Kind, S::Ty),
    Bool,
    Arr(S::Ty, S::Ty),
    Sub(S::Ty, S::Tm),
    Ind,
    Ext(S::Src, u32),
}

/// Implements the standard node traits for one concrete substrate.
///
/// Generic impls with `where S::Kind: Clone`-style bounds send trait
/// resolution into a projection cycle for recursive substrates, so each
/// substrate instantiates these concretely instead.
/// Implements node traits for substrates whose children are all `Copy`.
macro_rules! impl_copy_node_traits {
    (impl($($generics:tt)*) $substrate:ty) => {
        #[expect(
            clippy::expl_impl_clone_on_copy,
            reason = "derive would demand bounds on the substrate marker"
        )]
        impl<$($generics)*> Clone for Kind<$substrate> {
            fn clone(&self) -> Self {
                *self
            }
        }
        #[expect(
            clippy::expl_impl_clone_on_copy,
            reason = "derive would demand bounds on the substrate marker"
        )]
        impl<$($generics)*> Clone for Ty<$substrate> {
            fn clone(&self) -> Self {
                *self
            }
        }
        #[expect(
            clippy::expl_impl_clone_on_copy,
            reason = "derive would demand bounds on the substrate marker"
        )]
        impl<$($generics)*> Clone for Tm<$substrate> {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl<$($generics)*> Copy for Kind<$substrate> {}
        impl<$($generics)*> Copy for Ty<$substrate> {}
        impl<$($generics)*> Copy for Tm<$substrate> {}
        $crate::hol::syntax::impl_node_traits!(shared impl($($generics)*) $substrate);
    };
}
macro_rules! impl_node_traits {
    (shared impl($($generics:tt)*) $substrate:ty) => {
        impl<$($generics)*> PartialEq for Kind<$substrate> {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::Star, Self::Star) => true,
                    (Self::Arr(a, b), Self::Arr(c, d)) => a == c && b == d,
                    _ => false,
                }
            }
        }

        impl<$($generics)*> Eq for Kind<$substrate> {}

        impl<$($generics)*> PartialEq for Ty<$substrate> {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::Bv(a), Self::Bv(b)) => a == b,
                    (Self::Lam(k, b), Self::Lam(l, c))
                    | (Self::All(k, b), Self::All(l, c)) => k == l && b == c,
                    (Self::App(f, x), Self::App(g, y))
                    | (Self::Arr(f, x), Self::Arr(g, y)) => f == g && x == y,
                    (Self::Bool, Self::Bool) | (Self::Ind, Self::Ind) => true,
                    (Self::Sub(a, p), Self::Sub(b, q)) => a == b && p == q,
                    (Self::Ext(s, i), Self::Ext(t, j)) => s == t && i == j,
                    _ => false,
                }
            }
        }

        impl<$($generics)*> Eq for Ty<$substrate> {}

        impl<$($generics)*> PartialEq for Tm<$substrate> {
            fn eq(&self, other: &Self) -> bool {
                match (self, other) {
                    (Self::Bv(a), Self::Bv(b)) => a == b,
                    (Self::App(f, x), Self::App(g, y))
                    | (Self::Eq(f, x), Self::Eq(g, y))
                    | (Self::Abs(f, x), Self::Abs(g, y))
                    | (Self::Rep(f, x), Self::Rep(g, y)) => f == g && x == y,
                    (Self::Lam(a, t), Self::Lam(b, u)) => a == b && t == u,
                    (Self::TyApp(f, x), Self::TyApp(g, y)) => f == g && x == y,
                    (Self::TyLam(k, t), Self::TyLam(l, u)) => k == l && t == u,
                    (Self::Bool(a), Self::Bool(b)) => a == b,
                    (Self::Eps(p), Self::Eps(q)) => p == q,
                    (Self::Ext(s, i, c), Self::Ext(t, j, d)) => {
                        s == t && i == j && c == d
                    }
                    _ => false,
                }
            }
        }

        impl<$($generics)*> Eq for Tm<$substrate> {}

        impl<$($generics)*> std::fmt::Debug for Kind<$substrate> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    Self::Star => f.write_str("Star"),
                    Self::Arr(a, b) => f.debug_tuple("Arr").field(a).field(b).finish(),
                }
            }
        }

        impl<$($generics)*> std::fmt::Debug for Ty<$substrate> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    Self::Bv(n) => f.debug_tuple("Bv").field(n).finish(),
                    Self::Lam(k, b) => f.debug_tuple("Lam").field(k).field(b).finish(),
                    Self::App(g, x) => f.debug_tuple("App").field(g).field(x).finish(),
                    Self::All(k, b) => f.debug_tuple("All").field(k).field(b).finish(),
                    Self::Bool => f.write_str("Bool"),
                    Self::Arr(a, b) => f.debug_tuple("Arr").field(a).field(b).finish(),
                    Self::Sub(a, p) => f.debug_tuple("Sub").field(a).field(p).finish(),
                    Self::Ind => f.write_str("Ind"),
                    Self::Ext(s, i) => f.debug_tuple("Ext").field(s).field(i).finish(),
                }
            }
        }

        impl<$($generics)*> std::fmt::Debug for Tm<$substrate> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    Self::Bv(n) => f.debug_tuple("Bv").field(n).finish(),
                    Self::App(g, x) => f.debug_tuple("App").field(g).field(x).finish(),
                    Self::Lam(a, t) => f.debug_tuple("Lam").field(a).field(t).finish(),
                    Self::TyApp(g, x) => {
                        f.debug_tuple("TyApp").field(g).field(x).finish()
                    }
                    Self::TyLam(k, t) => {
                        f.debug_tuple("TyLam").field(k).field(t).finish()
                    }
                    Self::Bool(b) => f.debug_tuple("Bool").field(b).finish(),
                    Self::Eq(l, r) => f.debug_tuple("Eq").field(l).field(r).finish(),
                    Self::Eps(p) => f.debug_tuple("Eps").field(p).finish(),
                    Self::Abs(p, x) => f.debug_tuple("Abs").field(p).field(x).finish(),
                    Self::Rep(p, x) => f.debug_tuple("Rep").field(p).field(x).finish(),
                    Self::Ext(s, i, c) => {
                        f.debug_tuple("Ext").field(s).field(i).field(c).finish()
                    }
                }
            }
        }
    };
}
pub(crate) use impl_node_traits;

impl_copy_node_traits!(impl('v) Ids<'v>);

/// A term node.
#[expect(missing_docs, reason = "constructors are specified in semantics.txt")]
pub enum Tm<S: Substrate> {
    Bv(u32),
    App(S::Tm, S::Tm),
    Lam(S::Ty, S::Tm),
    TyApp(S::Tm, S::Ty),
    TyLam(S::Kind, S::Tm),
    Bool(bool),
    Eq(S::Tm, S::Tm),
    Eps(S::Tm),
    Abs(S::Tm, S::Tm),
    Rep(S::Tm, S::Tm),
    Ext(S::Src, u32, S::Ty),
}
