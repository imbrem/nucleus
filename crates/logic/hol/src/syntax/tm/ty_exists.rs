use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.tyExists`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyExists<R: Repr> {
    predicate: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TyExists<R> {
    /// # Errors
    /// Returns an error unless both the predicate and result are Boolean.
    pub fn new(repr: &R, ty: Ty<R>, predicate: Tm<R>) -> Result<Self, BuildError> {
        if !ty.is_bool(repr) || !predicate.ty().is_bool(repr) {
            return Err(BuildError::ExpectedBool);
        }
        Ok(Self { predicate, ty })
    }
    pub fn predicate(&self) -> &Tm<R> {
        &self.predicate
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TyExists<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyExists
    }
}
impl<R: TrustedRepr> TmI for TyExists<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TyExists<R>> for Expr<R> {
    fn from(value: TyExists<R>) -> Self {
        Self::TyExists(value)
    }
}
