use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, TrustedRepr, Ty, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.arr`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyArr<R: Repr> {
    domain: Ty<R>,
    codomain: Ty<R>,
    kind: Kind<R>,
}
impl<R: Repr> TyArr<R> {
    /// # Errors
    /// Returns [`BuildError::ExpectedStar`] unless both operands are ordinary types.
    pub fn new(repr: &R, domain: Ty<R>, codomain: Ty<R>) -> Result<Self, BuildError> {
        if !domain.kind().is_star(repr) || !codomain.kind().is_star(repr) {
            return Err(BuildError::ExpectedStar);
        }
        let kind = domain.kind().clone();
        Ok(Self {
            domain,
            codomain,
            kind,
        })
    }
    pub fn domain(&self) -> &Ty<R> {
        &self.domain
    }
    pub fn codomain(&self) -> &Ty<R> {
        &self.codomain
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> TyI for TyArr<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> ExprI for TyArr<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyArr
    }
}
impl<R: Repr> From<TyArr<R>> for Expr<R> {
    fn from(value: TyArr<R>) -> Self {
        Self::TyArr(value)
    }
}
