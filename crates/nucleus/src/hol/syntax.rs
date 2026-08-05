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
    type Kind: Clone + std::fmt::Debug + Eq;
    /// Type children.
    type Ty: Clone + std::fmt::Debug + Eq;
    /// Term children.
    type Tm: Clone + std::fmt::Debug + Eq;
    /// Source references.
    type Src: Clone + std::fmt::Debug + Eq;
}

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
#[derive(Debug, Eq, PartialEq)]
#[expect(missing_docs, reason = "constructors are specified in semantics.txt")]
pub enum Kind<S: Substrate> {
    Star,
    Arr(S::Kind, S::Kind),
}

/// A type node.
#[derive(Debug, Eq, PartialEq)]
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

impl<S: Substrate> Clone for Kind<S> {
    fn clone(&self) -> Self {
        match self {
            Self::Star => Self::Star,
            Self::Arr(domain, codomain) => Self::Arr(domain.clone(), codomain.clone()),
        }
    }
}

impl<S: Substrate> Clone for Ty<S> {
    fn clone(&self) -> Self {
        match self {
            Self::Bv(index) => Self::Bv(*index),
            Self::Lam(kind, body) => Self::Lam(kind.clone(), body.clone()),
            Self::App(function, argument) => Self::App(function.clone(), argument.clone()),
            Self::All(kind, body) => Self::All(kind.clone(), body.clone()),
            Self::Bool => Self::Bool,
            Self::Arr(domain, codomain) => Self::Arr(domain.clone(), codomain.clone()),
            Self::Sub(carrier, predicate) => Self::Sub(carrier.clone(), predicate.clone()),
            Self::Ind => Self::Ind,
            Self::Ext(source, position) => Self::Ext(source.clone(), *position),
        }
    }
}

impl<S: Substrate> Clone for Tm<S> {
    fn clone(&self) -> Self {
        match self {
            Self::Bv(index) => Self::Bv(*index),
            Self::App(function, argument) => Self::App(function.clone(), argument.clone()),
            Self::Lam(domain, body) => Self::Lam(domain.clone(), body.clone()),
            Self::TyApp(function, argument) => Self::TyApp(function.clone(), argument.clone()),
            Self::TyLam(kind, body) => Self::TyLam(kind.clone(), body.clone()),
            Self::Bool(value) => Self::Bool(*value),
            Self::Eq(left, right) => Self::Eq(left.clone(), right.clone()),
            Self::Eps(predicate) => Self::Eps(predicate.clone()),
            Self::Abs(predicate, value) => Self::Abs(predicate.clone(), value.clone()),
            Self::Rep(predicate, value) => Self::Rep(predicate.clone(), value.clone()),
            Self::Ext(source, position, claim) => {
                Self::Ext(source.clone(), *position, claim.clone())
            }
        }
    }
}

impl<S: Substrate> Copy for Kind<S> where S::Kind: Copy {}

impl<S: Substrate> Copy for Ty<S>
where
    S::Kind: Copy,
    S::Ty: Copy,
    S::Tm: Copy,
    S::Src: Copy,
{
}

impl<S: Substrate> Copy for Tm<S>
where
    S::Kind: Copy,
    S::Ty: Copy,
    S::Tm: Copy,
    S::Src: Copy,
{
}

/// A term node.
#[derive(Debug, Eq, PartialEq)]
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
