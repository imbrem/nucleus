//! Checked, representation-neutral surface syntax for the empty `HolE` language.

use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::Arc;

use covalence_lib_hash::O256;

mod cbor;
pub mod syntax;
mod tag;

pub use cbor::{
    DecodeError, kind_from_value, kind_to_value, tm_from_value, tm_to_value, ty_from_value,
    ty_to_value,
};
pub use covalence_lib_cbor::Value as CborValue;
pub use syntax::*;
pub use tag::{SurfaceTag, UnknownSurfaceTag};

/// A representation-owned syntax handle.
pub trait Ix: Clone + Debug + Eq {
    fn ptr_eq(&self, other: &Self) -> bool;

    fn definitely_eq(&self, other: &Self) -> bool {
        self.ptr_eq(other)
    }
}

mod sealed {
    pub trait Trusted {}
}

/// Representations trusted to preserve the invariants established by syntax
/// former constructors. This trait is intentionally sealed.
pub trait TrustedRepr: Repr + sealed::Trusted {}

/// A locally checked syntax former, independent of any representation.
pub trait ExprI: Sized {
    fn tag(&self) -> SurfaceTag;
}

pub trait KindI: ExprI {}

pub trait TyI: ExprI {
    type Kind;
    fn kind(&self) -> &Self::Kind;
}

pub trait TmI: ExprI {
    type Ty;
    fn ty(&self) -> &Self::Ty;
}

/// Allocation and one-step elimination for syntax storage.
#[allow(clippy::missing_errors_doc, clippy::wrong_self_convention)]
pub trait Repr: Sized + 'static {
    type Ix: Ix;
    type Name: Clone + Debug + Eq;

    /// The sole representation-specific allocation primitive.
    fn insert(&mut self, expr: Expr<Self>) -> Self::Ix;
    fn expr(&self, index: &Self::Ix) -> Expr<Self>;
    fn name(&mut self, value: String) -> Self::Name;
    fn name_str<'a>(&self, name: &'a Self::Name) -> &'a str;

    /// Allocates any locally checked syntax former.
    fn new<E>(&mut self, expr: E) -> Self::Ix
    where
        E: ExprI + Into<Expr<Self>>,
        Expr<Self>: ExprI,
    {
        self.insert(expr.into())
    }

    fn new_kind<E>(&mut self, expr: E) -> Kind<Self>
    where
        E: KindI + Into<Expr<Self>>,
        Expr<Self>: ExprI,
    {
        Kind::from_index(self.new(expr))
    }

    fn new_ty<E>(&mut self, expr: E) -> Ty<Self>
    where
        E: TyI<Kind = Kind<Self>> + Into<Expr<Self>>,
        Expr<Self>: ExprI,
    {
        let kind = expr.kind().clone();
        Ty::from_index(self.new(expr), kind)
    }

    fn new_tm<E>(&mut self, expr: E) -> Tm<Self>
    where
        E: TmI<Ty = Ty<Self>> + Into<Expr<Self>>,
        Expr<Self>: ExprI,
    {
        let ty = expr.ty().clone();
        Tm::from_index(self.new(expr), ty)
    }

    fn ix_eq(&self, left: &Self::Ix, right: &Self::Ix) -> bool {
        left.definitely_eq(right)
    }

    fn kind_star(&mut self) -> Kind<Self>
    where
        Self: TrustedRepr,
    {
        self.new_kind(syntax::kind::KindStar::new())
    }

    fn kind_arr(&mut self, domain: Kind<Self>, codomain: Kind<Self>) -> Kind<Self>
    where
        Self: TrustedRepr,
    {
        self.new_kind(syntax::kind::KindArr::new(domain, codomain))
    }

    fn ty_bool(&mut self, kind: Kind<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::ty::TyBool::new(self, kind)?;
        Ok(self.new_ty(former))
    }

    fn ty_arr(&mut self, domain: Ty<Self>, codomain: Ty<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::ty::TyArr::new(self, domain, codomain)?;
        Ok(self.new_ty(former))
    }

    fn ty_app(&mut self, function: Ty<Self>, argument: Ty<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::ty::TyApp::new(self, function, argument)?;
        Ok(self.new_ty(former))
    }

    fn ty_lam(&mut self, domain: Kind<Self>, body: Ty<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let result_kind = self.kind_arr(domain.clone(), body.kind().clone());
        let former = syntax::ty::TyLam::new(self, domain, body, result_kind)?;
        Ok(self.new_ty(former))
    }

    fn ty_bv(&mut self, variable: TypeVariable<Self>) -> Ty<Self>
    where
        Self: TrustedRepr,
    {
        self.new_ty(syntax::ty::TyBv::new(variable))
    }

    fn ty_sub(&mut self, carrier: Ty<Self>, predicate: Tm<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::ty::TySub::new(self, carrier, predicate)?;
        Ok(self.new_ty(former))
    }

    fn ty_model(&mut self, kind: Kind<Self>, predicate: Tm<Self>) -> Result<Ty<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::ty::TyModel::new(self, kind, predicate)?;
        Ok(self.new_ty(former))
    }

    fn ty_link(&mut self, source: O256, format: Format, kind: Kind<Self>) -> Ty<Self>
    where
        Self: TrustedRepr,
    {
        self.new_ty(syntax::ty::TyLink::new(source, format, kind))
    }

    fn tm_bv(&mut self, index: Bv, ty: Ty<Self>) -> Tm<Self>
    where
        Self: TrustedRepr,
    {
        self.new_tm(syntax::tm::TmBv::new(index, ty))
    }

    fn tm_fv(&mut self, variable: Variable<Self>) -> Tm<Self>
    where
        Self: TrustedRepr,
    {
        self.new_tm(syntax::tm::TmFv::new(variable))
    }

    fn tm_bool(&mut self, ty: Ty<Self>, value: bool) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TmBool::new(self, ty, value)?;
        Ok(self.new_tm(former))
    }

    fn tm_app(&mut self, function: Tm<Self>, argument: Tm<Self>) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TmApp::new(self, function, argument)?;
        Ok(self.new_tm(former))
    }

    fn tm_lam(&mut self, domain: Ty<Self>, body: Tm<Self>) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let result_ty = self.ty_arr(domain.clone(), body.ty().clone())?;
        let former = syntax::tm::TmLam::new(self, domain, body, result_ty)?;
        Ok(self.new_tm(former))
    }

    fn tm_eq(
        &mut self,
        ty: Ty<Self>,
        left: Tm<Self>,
        right: Tm<Self>,
    ) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TmEq::new(self, ty, left, right)?;
        Ok(self.new_tm(former))
    }

    fn tm_eps(&mut self, ty: Ty<Self>, predicate: Tm<Self>) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TmEps::new(self, ty, predicate)?;
        Ok(self.new_tm(former))
    }

    fn tm_abs(
        &mut self,
        carrier: Ty<Self>,
        predicate: Tm<Self>,
        value: Tm<Self>,
    ) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let subtype = self.ty_sub(carrier.clone(), predicate.clone())?;
        let former = syntax::tm::TmAbs::new(self, carrier, predicate, value, subtype)?;
        Ok(self.new_tm(former))
    }

    fn tm_rep(
        &mut self,
        carrier: Ty<Self>,
        predicate: Tm<Self>,
        value: Tm<Self>,
    ) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TmRep::new(self, carrier, predicate, value)?;
        Ok(self.new_tm(former))
    }

    fn ty_exists(&mut self, ty: Ty<Self>, predicate: Tm<Self>) -> Result<Tm<Self>, BuildError>
    where
        Self: TrustedRepr,
    {
        let former = syntax::tm::TyExists::new(self, ty, predicate)?;
        Ok(self.new_tm(former))
    }

    fn tm_link(&mut self, source: O256, format: Format, ty: Ty<Self>) -> Tm<Self>
    where
        Self: TrustedRepr,
    {
        self.new_tm(syntax::tm::TmLink::new(source, format, ty))
    }
}

macro_rules! plain_index {
    ($name:ident) => {
        pub struct $name<R: Repr> {
            index: R::Ix,
        }

        impl<R: Repr> $name<R> {
            pub(crate) fn from_index(index: R::Ix) -> Self {
                Self { index }
            }

            #[must_use]
            pub fn index(&self) -> &R::Ix {
                &self.index
            }

            #[must_use]
            pub fn ptr_eq(&self, other: &Self) -> bool {
                self.index.ptr_eq(&other.index)
            }
        }

        impl<R: Repr> Clone for $name<R> {
            fn clone(&self) -> Self {
                Self::from_index(self.index.clone())
            }
        }

        impl<R: Repr<Ix: Copy>> Copy for $name<R> {}

        impl<R: Repr> Debug for $name<R> {
            fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
                Debug::fmt(&self.index, formatter)
            }
        }

        impl<R: Repr> PartialEq for $name<R> {
            fn eq(&self, other: &Self) -> bool {
                self.index == other.index
            }
        }

        impl<R: Repr> Eq for $name<R> {}
    };
}

plain_index!(Kind);

pub struct Ty<R: Repr> {
    index: R::Ix,
    kind: Kind<R>,
}

impl<R: Repr> Ty<R> {
    pub(crate) fn from_index(index: R::Ix, kind: Kind<R>) -> Self {
        Self { index, kind }
    }
    pub fn index(&self) -> &R::Ix {
        &self.index
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.index.ptr_eq(&other.index)
    }
    pub(crate) fn is_bool(&self, repr: &R) -> bool {
        matches!(repr.expr(&self.index), Expr::TyBool(_))
    }
    pub(crate) fn as_arr(&self, repr: &R) -> Option<(Self, Self)> {
        let Expr::TyArr(former) = repr.expr(&self.index) else {
            return None;
        };
        Some((former.domain().clone(), former.codomain().clone()))
    }
}

impl<R: Repr> Clone for Ty<R> {
    fn clone(&self) -> Self {
        Self::from_index(self.index.clone(), self.kind.clone())
    }
}
impl<R: Repr<Ix: Copy>> Copy for Ty<R> {}
impl<R: Repr> Debug for Ty<R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.index, f)
    }
}
impl<R: Repr> PartialEq for Ty<R> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}
impl<R: Repr> Eq for Ty<R> {}

pub struct Tm<R: Repr> {
    index: R::Ix,
    ty: Ty<R>,
}

impl<R: Repr> Tm<R> {
    pub(crate) fn from_index(index: R::Ix, ty: Ty<R>) -> Self {
        Self { index, ty }
    }
    pub fn index(&self) -> &R::Ix {
        &self.index
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.index.ptr_eq(&other.index)
    }
}

impl<R: Repr> Clone for Tm<R> {
    fn clone(&self) -> Self {
        Self::from_index(self.index.clone(), self.ty.clone())
    }
}
impl<R: Repr<Ix: Copy>> Copy for Tm<R> {}
impl<R: Repr> Debug for Tm<R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.index, f)
    }
}
impl<R: Repr> PartialEq for Tm<R> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}
impl<R: Repr> Eq for Tm<R> {}

impl<R: Repr> Kind<R> {
    pub(crate) fn is_star(&self, repr: &R) -> bool {
        matches!(repr.expr(&self.index), Expr::KindStar(_))
    }
    pub(crate) fn as_arr(&self, repr: &R) -> Option<(Self, Self)> {
        let Expr::KindArr(former) = repr.expr(&self.index) else {
            return None;
        };
        Some((former.domain().clone(), former.codomain().clone()))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Sort<R: Repr> {
    Term(Ty<R>),
    Type(Kind<R>),
    Kind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bv(u64);
impl Bv {
    #[must_use]
    pub const fn new(index: u64) -> Self {
        Self(index)
    }
    #[must_use]
    pub const fn index(self) -> u64 {
        self.0
    }
    /// # Panics
    /// Panics when the shifted index exceeds `u64::MAX`.
    #[must_use]
    pub fn shift(self, amount: u64) -> Self {
        Self(
            self.0
                .checked_add(amount)
                .expect("bound-variable index overflow"),
        )
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Variable<R: Repr> {
    pub name: R::Name,
    pub ty: Ty<R>,
}
impl<R: Repr> Clone for Variable<R> {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            ty: self.ty.clone(),
        }
    }
}
impl<R: Repr<Ix: Copy, Name: Copy>> Copy for Variable<R> {}

#[derive(Debug, Eq, PartialEq)]
pub struct TypeVariable<R: Repr> {
    pub index: Bv,
    pub kind: Kind<R>,
}
impl<R: Repr> Clone for TypeVariable<R> {
    fn clone(&self) -> Self {
        Self {
            index: self.index,
            kind: self.kind.clone(),
        }
    }
}
impl<R: Repr<Ix: Copy>> Copy for TypeVariable<R> {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr<R: Repr> {
    KindStar(KindStar),
    KindArr(KindArr<R>),
    TyBool(TyBool<R>),
    TyArr(TyArr<R>),
    TyApp(TyApp<R>),
    TyLam(TyLam<R>),
    TyBv(TyBv<R>),
    TySub(TySub<R>),
    TyModel(TyModel<R>),
    TyLink(TyLink<R>),
    TyExists(TyExists<R>),
    TmBv(TmBv<R>),
    TmFv(TmFv<R>),
    TmApp(TmApp<R>),
    TmLam(TmLam<R>),
    TmBool(TmBool<R>),
    TmEq(TmEq<R>),
    TmEps(TmEps<R>),
    TmAbs(TmAbs<R>),
    TmRep(TmRep<R>),
    TmLink(TmLink<R>),
}

impl<R: TrustedRepr> ExprI for Expr<R> {
    fn tag(&self) -> SurfaceTag {
        match self {
            Self::KindStar(x) => x.tag(),
            Self::KindArr(x) => x.tag(),
            Self::TyBool(x) => x.tag(),
            Self::TyArr(x) => x.tag(),
            Self::TyApp(x) => x.tag(),
            Self::TyLam(x) => x.tag(),
            Self::TyBv(x) => x.tag(),
            Self::TySub(x) => x.tag(),
            Self::TyModel(x) => x.tag(),
            Self::TyLink(x) => x.tag(),
            Self::TyExists(x) => x.tag(),
            Self::TmBv(x) => x.tag(),
            Self::TmFv(x) => x.tag(),
            Self::TmApp(x) => x.tag(),
            Self::TmLam(x) => x.tag(),
            Self::TmBool(x) => x.tag(),
            Self::TmEq(x) => x.tag(),
            Self::TmEps(x) => x.tag(),
            Self::TmAbs(x) => x.tag(),
            Self::TmRep(x) => x.tag(),
            Self::TmLink(x) => x.tag(),
        }
    }
}

impl<R: TrustedRepr> Expr<R> {
    pub fn sort(&self) -> Sort<R> {
        match self {
            Self::KindStar(_) | Self::KindArr(_) => Sort::Kind,
            Self::TyBool(x) => Sort::Type(x.kind().clone()),
            Self::TyArr(x) => Sort::Type(x.kind().clone()),
            Self::TyApp(x) => Sort::Type(x.kind().clone()),
            Self::TyLam(x) => Sort::Type(x.kind().clone()),
            Self::TyBv(x) => Sort::Type(x.kind().clone()),
            Self::TySub(x) => Sort::Type(x.kind().clone()),
            Self::TyModel(x) => Sort::Type(x.kind().clone()),
            Self::TyLink(x) => Sort::Type(x.kind().clone()),
            Self::TyExists(x) => Sort::Term(x.ty().clone()),
            Self::TmBv(x) => Sort::Term(x.ty().clone()),
            Self::TmFv(x) => Sort::Term(x.ty().clone()),
            Self::TmApp(x) => Sort::Term(x.ty().clone()),
            Self::TmLam(x) => Sort::Term(x.ty().clone()),
            Self::TmBool(x) => Sort::Term(x.ty().clone()),
            Self::TmEq(x) => Sort::Term(x.ty().clone()),
            Self::TmEps(x) => Sort::Term(x.ty().clone()),
            Self::TmAbs(x) => Sort::Term(x.ty().clone()),
            Self::TmRep(x) => Sort::Term(x.ty().clone()),
            Self::TmLink(x) => Sort::Term(x.ty().clone()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Format {
    Blob = 0,
    CborTree = 1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    ExpectedStar,
    ExpectedBool,
    ExpectedFunction,
    TypeMismatch,
    KindMismatch,
}
impl Display for BuildError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "invalid HolE constructor: {self:?}")
    }
}
impl Error for BuildError {}

#[derive(Clone, Debug)]
pub struct ArcIx(Arc<Expr<ArcRepr>>);
impl Ix for ArcIx {
    fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    fn definitely_eq(&self, other: &Self) -> bool {
        self.ptr_eq(other) || self.0 == other.0
    }
}
impl PartialEq for ArcIx {
    fn eq(&self, other: &Self) -> bool {
        self.definitely_eq(other)
    }
}
impl Eq for ArcIx {}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ArcRepr;
impl ArcRepr {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}
impl sealed::Trusted for ArcRepr {}
impl TrustedRepr for ArcRepr {}
impl Repr for ArcRepr {
    type Ix = ArcIx;
    type Name = Arc<str>;
    fn insert(&mut self, expr: Expr<Self>) -> Self::Ix {
        ArcIx(Arc::new(expr))
    }
    fn expr(&self, index: &Self::Ix) -> Expr<Self> {
        index.0.as_ref().clone()
    }
    fn name(&mut self, value: String) -> Self::Name {
        Arc::from(value)
    }
    fn name_str<'a>(&self, name: &'a Self::Name) -> &'a str {
        name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bool_ty(repr: &mut ArcRepr) -> Ty<ArcRepr> {
        let star = repr.kind_star();
        repr.ty_bool(star).unwrap()
    }

    #[test]
    fn checked_constructors_reject_an_ill_typed_application() {
        let mut repr = ArcRepr::new();
        let bool_ty = bool_ty(&mut repr);
        let function = repr.tm_bool(bool_ty.clone(), true).unwrap();
        let argument = repr.tm_bool(bool_ty, false).unwrap();

        assert_eq!(
            repr.tm_app(function, argument),
            Err(BuildError::ExpectedFunction)
        );
    }

    #[test]
    fn equality_derives_its_operand_type() {
        let mut repr = ArcRepr::new();
        let bool_ty = bool_ty(&mut repr);
        let truth = repr.tm_bool(bool_ty.clone(), true).unwrap();
        let falsehood = repr.tm_bool(bool_ty.clone(), false).unwrap();
        assert!(
            repr.tm_eq(bool_ty.clone(), truth.clone(), falsehood)
                .is_ok()
        );

        let bound = repr.tm_bv(Bv::new(0), bool_ty.clone());
        let identity = repr.tm_lam(bool_ty.clone(), bound).unwrap();
        assert_eq!(
            repr.tm_eq(bool_ty, truth, identity),
            Err(BuildError::TypeMismatch)
        );
    }

    #[test]
    fn cbor_values_round_trip_through_checked_constructors() {
        let mut repr = ArcRepr::new();
        let bool_ty = bool_ty(&mut repr);
        let variable = repr.tm_fv(Variable {
            name: Arc::from("p"),
            ty: bool_ty,
        });
        let encoded = tm_to_value(&repr, &variable);
        let decoded = tm_from_value(&mut repr, encoded.clone()).unwrap();

        assert_eq!(tm_to_value(&repr, &decoded), encoded);
        assert!(repr.ix_eq(variable.ty().index(), decoded.ty().index()));
    }

    #[test]
    fn cbor_rejects_a_forged_result_annotation() {
        let mut repr = ArcRepr::new();
        let star = repr.kind_star();
        let bool_ty = repr.ty_bool(star.clone()).unwrap();
        let truth = repr.tm_bool(bool_ty.clone(), true).unwrap();
        let bound = repr.tm_bv(Bv::new(0), bool_ty.clone());
        let identity = repr.tm_lam(bool_ty.clone(), bound).unwrap();
        let application = repr.tm_app(identity, truth).unwrap();
        let CborValue::Array(mut encoded) = tm_to_value(&repr, &application) else {
            unreachable!();
        };
        encoded[3] = kind_to_value(&repr, &star);

        assert!(tm_from_value(&mut repr, CborValue::Array(encoded)).is_err());
    }
}
