use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, TrustedRepr, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.boolTy`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyBool<R: Repr> {
    kind: Kind<R>,
}
impl<R: Repr> TyBool<R> {
    /// # Errors
    /// Returns [`BuildError::ExpectedStar`] unless `kind` is `*`.
    pub fn new(repr: &R, kind: Kind<R>) -> Result<Self, BuildError> {
        if !kind.is_star(repr) {
            return Err(BuildError::ExpectedStar);
        }
        Ok(Self { kind })
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> TyI for TyBool<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> ExprI for TyBool<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyBool
    }
}
impl<R: Repr> From<TyBool<R>> for Expr<R> {
    fn from(value: TyBool<R>) -> Self {
        Self::TyBool(value)
    }
}
