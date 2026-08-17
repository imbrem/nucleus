use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.eq`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmEq<R: Repr> {
    left: Tm<R>,
    right: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmEq<R> {
    /// # Errors
    /// Returns an error unless both operands have the same type and the result is Boolean.
    pub fn new(repr: &R, ty: Ty<R>, left: Tm<R>, right: Tm<R>) -> Result<Self, BuildError> {
        if !ty.is_bool(repr) {
            return Err(BuildError::ExpectedBool);
        }
        if !repr.ty_eq(left.ty(), right.ty()) {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self { left, right, ty })
    }
    pub fn left(&self) -> &Tm<R> {
        &self.left
    }
    pub fn right(&self) -> &Tm<R> {
        &self.right
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmEq<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmEq
    }
}
impl<R: TrustedRepr> TmI for TmEq<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmEq<R>> for Expr<R> {
    fn from(value: TmEq<R>) -> Self {
        Self::TmEq(value)
    }
}
