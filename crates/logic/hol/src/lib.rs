//! Backend-neutral surface syntax and an LCF-style kernel boundary.

use std::error::Error;
use std::sync::Arc;

use covalence_lib_hash::O256;

mod tag;

pub use tag::{SurfaceTag, UnknownSurfaceTag};

/// Storage choices for indices held by surface syntax.
pub trait Repr: Sized + 'static {
    type Kind;
    type Ty;
    type Tm;
    type Var;
    type Ctx;
    type Link;
    type Prim;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Variable<R: Repr> {
    pub name: String,
    pub ty: R::Ty,
}

/// A context-free theorem context.  The spine lowers to nested `TM_AND`
/// propositions; unlike a map, order and sharing are explicit and canonical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Context<R: Repr> {
    Empty,
    And(R::Tm, R::Ctx),
}

impl<R: Repr> Context<R> {
    #[must_use]
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// Stack one premise in front of an existing context.
    #[must_use]
    pub const fn and(premise: R::Tm, rest: R::Ctx) -> Self {
        Self::And(premise, rest)
    }
}

impl<R: Repr> Default for Context<R> {
    fn default() -> Self {
        Self::empty()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind<R: Repr> {
    Star,
    Arr(R::Kind, R::Kind),
}

impl<R: Repr> Kind<R> {
    #[must_use]
    pub const fn tag(&self) -> SurfaceTag {
        match self {
            Self::Star => SurfaceTag::KindStar,
            Self::Arr(_, _) => SurfaceTag::KindArr,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ty<R: Repr> {
    Bool,
    Arr(R::Ty, R::Ty),
    App(R::Ty, R::Ty),
    Abs(R::Kind, R::Ty),
    Bv(R::Var),
    Sub(R::Ty, R::Tm),
    Model(R::Tm),
    Prim(R::Prim),
    Link(R::Link, R::Kind),
    Nat,
}

impl<R: Repr> Ty<R> {
    #[must_use]
    pub const fn tag(&self) -> SurfaceTag {
        match self {
            Self::Bool => SurfaceTag::TyBool,
            Self::Arr(_, _) => SurfaceTag::TyArr,
            Self::App(_, _) => SurfaceTag::TyApp,
            Self::Abs(_, _) => SurfaceTag::TyLam,
            Self::Bv(_) => SurfaceTag::TyBv,
            Self::Sub(_, _) => SurfaceTag::TySub,
            Self::Model(_) => SurfaceTag::TyModel,
            Self::Prim(_) => SurfaceTag::TyPrim,
            Self::Link(_, _) => SurfaceTag::TyLink,
            Self::Nat => SurfaceTag::TmNat,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tm<R: Repr> {
    Exists(R::Tm),
    Prim(R::Prim),
    Bv(R::Var),
    Fv(R::Var),
    App(R::Tm, R::Tm),
    Lam(R::Ty, R::Tm),
    Bool(bool),
    Eq(R::Ty, R::Tm, R::Tm),
    Eps(R::Ty, R::Tm),
    Abs(R::Ty, R::Tm, R::Tm),
    Rep(R::Ty, R::Tm, R::Tm),
    Link(R::Link, R::Ty),
    And(R::Tm, R::Tm),
    Inf,
    Zero,
    Succ,
    Nat(u64),
    Imp(R::Ctx, R::Tm),
}

impl<R: Repr> Tm<R> {
    #[must_use]
    pub const fn tag(&self) -> SurfaceTag {
        match self {
            Self::Exists(_) => SurfaceTag::TyExists,
            Self::Prim(_) => SurfaceTag::TmPrim,
            Self::Bv(_) => SurfaceTag::TmBv,
            Self::Fv(_) => SurfaceTag::TmFv,
            Self::App(_, _) => SurfaceTag::TmApp,
            Self::Lam(_, _) => SurfaceTag::TmLam,
            Self::Bool(_) => SurfaceTag::TmBool,
            Self::Eq(_, _, _) => SurfaceTag::TmEq,
            Self::Eps(_, _) => SurfaceTag::TmEps,
            Self::Abs(_, _, _) => SurfaceTag::TmAbs,
            Self::Rep(_, _, _) => SurfaceTag::TmRep,
            Self::Link(_, _) => SurfaceTag::TmLink,
            Self::And(_, _) => SurfaceTag::TmAnd,
            Self::Inf => SurfaceTag::TmInf,
            Self::Zero => SurfaceTag::TmZero,
            Self::Succ => SurfaceTag::TmSucc,
            Self::Nat(_) => SurfaceTag::TmLitNat,
            Self::Imp(_, _) => SurfaceTag::TmImp,
        }
    }
}

/// Heterogeneous storage wrapper; kernel APIs use the sort-specific enums directly.
pub enum AnyExpr<R: Repr> {
    Kind(Kind<R>),
    Ty(Ty<R>),
    Tm(Tm<R>),
}

impl<R: Repr> AnyExpr<R> {
    #[must_use]
    pub const fn tag(&self) -> SurfaceTag {
        match self {
            Self::Kind(kind) => kind.tag(),
            Self::Ty(ty) => ty.tag(),
            Self::Tm(term) => term.tag(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Format {
    CborTree,
}

/// Shared concrete link handle used by the default representation.
pub type Link = Arc<(O256, Format)>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArcRepr;

pub type ArcKind = Arc<Kind<ArcRepr>>;
pub type ArcTy = Arc<Ty<ArcRepr>>;
pub type ArcTm = Arc<Tm<ArcRepr>>;

impl Repr for ArcRepr {
    type Kind = ArcKind;
    type Ty = ArcTy;
    type Tm = ArcTm;
    type Var = Arc<Variable<Self>>;
    type Ctx = Arc<Context<Self>>;
    type Link = Link;
    type Prim = String;
}

mod sealed {
    pub trait Sealed {}
}

/// Root interface for checked/indexed expressions. Implementations come later.
pub trait ExprI: sealed::Sealed {
    fn tag(&self) -> SurfaceTag;
}

pub trait KindI: ExprI {}

pub trait TyI: ExprI {
    type Kind: KindI;

    fn kind(&self) -> &Self::Kind;
}

pub trait TmI: ExprI {
    type Ty: TyI;

    fn ty(&self) -> &Self::Ty;
}

/// Checked Boolean type used for propositions; no separate syntax node.
pub trait PropI: TyI {}

pub trait PredI: TmI<Ty: PropI> {}

pub trait CtxI: PredI {}

/// A proven predicate implication with explicit premises and conclusion.
pub trait ThmI: PredI {
    type Premises: CtxI<Ty: PropI>;
    type Conclusion: PredI<Ty: PropI>;

    fn premises(&self) -> &Self::Premises;
    fn conclusion(&self) -> &Self::Conclusion;
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BackendId(String);

impl BackendId {
    #[must_use]
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }
}

pub trait KernelBackend: Send + Sync + 'static {
    type Repr: Repr;
    type CheckedType: TyI;
    type CheckedTerm: TmI;
    type Theorem: ThmI;
    type Error: Error + Send + Sync + 'static;

    fn backend_id(&self) -> BackendId;

    /// # Errors
    /// Returns a diagnostic when the type is not well-kinded.
    fn check_type(&self, ty: &Ty<Self::Repr>) -> Result<Self::CheckedType, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when the term is not well-typed.
    fn check_term(
        &self,
        context: &<Self::Repr as Repr>::Ctx,
        term: &Tm<Self::Repr>,
    ) -> Result<Self::CheckedTerm, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when the variable cannot be opened as a term.
    fn open(
        &self,
        variable: <Self::Repr as Repr>::Var,
    ) -> Result<<Self::Repr as Repr>::Tm, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when closing would produce malformed scope.
    fn close(
        &self,
        body: <Self::Repr as Repr>::Tm,
    ) -> Result<<Self::Repr as Repr>::Tm, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when the application is ill-typed.
    fn app(
        &self,
        function: <Self::Repr as Repr>::Tm,
        argument: <Self::Repr as Repr>::Tm,
    ) -> Result<<Self::Repr as Repr>::Tm, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when the abstraction is ill-typed.
    fn abs(
        &self,
        domain: <Self::Repr as Repr>::Ty,
        body: <Self::Repr as Repr>::Tm,
    ) -> Result<<Self::Repr as Repr>::Tm, Self::Error>;

    /// # Errors
    /// Returns a diagnostic unless the checked term is a predicate.
    fn assume(&self, predicate: &Self::CheckedTerm) -> Result<Self::Theorem, Self::Error>;

    /// # Errors
    /// Returns a diagnostic for an incompatible checked-term handle.
    fn reflexivity(&self, term: &Self::CheckedTerm) -> Result<Self::Theorem, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when theorem types or backends differ.
    fn application_congruence(
        &self,
        function: &Self::Theorem,
        argument: &Self::Theorem,
    ) -> Result<Self::Theorem, Self::Error>;

    /// # Errors
    /// Returns a diagnostic when the checked terms do not form a beta redex.
    fn beta(
        &self,
        abstraction: &Self::CheckedTerm,
        argument: &Self::CheckedTerm,
    ) -> Result<Self::Theorem, Self::Error>;
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::mem::size_of;
    use std::sync::Arc;

    use super::{AnyExpr, ArcRepr, Context, Kind, Link, SurfaceTag, Tm, Ty};

    #[test]
    fn tags_are_unique_and_round_trip() {
        let mut ids = BTreeSet::new();
        let mut names = BTreeSet::new();

        for &tag in SurfaceTag::ALL {
            let id = u64::from(tag);
            let name = <&'static str>::from(tag);
            assert!(ids.insert(id));
            assert!(names.insert(name));
            assert_eq!(SurfaceTag::try_from(id), Ok(tag));
            assert_eq!(name.parse(), Ok(tag));
            assert_eq!(format!("{tag}"), name);
            assert_eq!(format!("{tag:?}"), name);
        }
    }

    #[test]
    fn default_indices_share_nodes_and_heterogeneous_storage_is_explicit() {
        let argument = Arc::new(Tm::<ArcRepr>::Bool(true));
        let application = Tm::<ArcRepr>::App(Arc::clone(&argument), Arc::clone(&argument));

        let Tm::App(left, right) = application else {
            panic!("expected application");
        };
        assert!(Arc::ptr_eq(&left, &right));

        let expressions = [
            AnyExpr::Kind(Kind::<ArcRepr>::Star),
            AnyExpr::Ty(Ty::<ArcRepr>::Bool),
            AnyExpr::Tm(Tm::<ArcRepr>::Bool(true)),
        ];
        assert_eq!(
            expressions.map(|expr| expr.tag()),
            [SurfaceTag::KindStar, SurfaceTag::TyBool, SurfaceTag::TmBool,]
        );
    }

    #[test]
    fn default_link_is_one_shared_pointer() {
        assert_eq!(size_of::<Link>(), size_of::<usize>());
    }

    #[test]
    fn contexts_are_explicit_conjunction_spines() {
        let rest = Arc::new(Context::<ArcRepr>::empty());
        let context = Context::<ArcRepr>::and(Arc::new(Tm::Inf), Arc::clone(&rest));

        let Context::And(premise, tail) = context else {
            panic!("expected a nonempty context");
        };
        assert_eq!(premise.tag(), SurfaceTag::TmInf);
        assert!(Arc::ptr_eq(&tail, &rest));
        assert_eq!(
            Tm::<ArcRepr>::And(Arc::new(Tm::Inf), Arc::new(Tm::Bool(true))).tag(),
            SurfaceTag::TmAnd,
        );
    }
}
