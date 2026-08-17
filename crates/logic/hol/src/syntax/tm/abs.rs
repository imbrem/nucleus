use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.abs`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmAbs<R: Repr> {
    value: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmAbs<R> {
    /// # Errors
    /// Returns an error unless `ty` is a subtype whose carrier is the value's type.
    pub fn new(repr: &R, ty: Ty<R>, value: Tm<R>) -> Result<Self, BuildError> {
        let Expr::TySub(subtype) = repr.expr(ty.index()) else {
            return Err(BuildError::TypeMismatch);
        };
        if !repr.ty_eq(subtype.carrier(), value.ty()) {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self { value, ty })
    }
    pub fn value(&self) -> &Tm<R> {
        &self.value
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmAbs<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmAbs
    }
}
impl<R: TrustedRepr> TmI for TmAbs<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmAbs<R>> for Expr<R> {
    fn from(value: TmAbs<R>) -> Self {
        Self::TmAbs(value)
    }
}
