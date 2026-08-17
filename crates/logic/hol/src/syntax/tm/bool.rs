use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.bool`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmBool<R: Repr> {
    value: bool,
    ty: Ty<R>,
}
impl<R: Repr> TmBool<R> {
    /// # Errors
    /// Returns [`BuildError::ExpectedBool`] unless `ty` is the Boolean type.
    pub fn new(repr: &R, ty: Ty<R>, value: bool) -> Result<Self, BuildError> {
        if !ty.is_bool(repr) {
            return Err(BuildError::ExpectedBool);
        }
        Ok(Self { value, ty })
    }
    pub fn value(&self) -> bool {
        self.value
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmBool<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmBool
    }
}
impl<R: TrustedRepr> TmI for TmBool<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmBool<R>> for Expr<R> {
    fn from(value: TmBool<R>) -> Self {
        Self::TmBool(value)
    }
}
