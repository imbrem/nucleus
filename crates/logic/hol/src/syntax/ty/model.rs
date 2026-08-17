use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, Tm, TrustedRepr, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.model`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyModel<R: Repr> {
    predicate: Tm<R>,
    kind: Kind<R>,
}
impl<R: Repr> TyModel<R> {
    /// # Errors
    /// Returns an error unless `kind` is `*` and `predicate` is Boolean.
    pub fn new(repr: &R, kind: Kind<R>, predicate: Tm<R>) -> Result<Self, BuildError> {
        if !kind.is_star(repr) {
            return Err(BuildError::ExpectedStar);
        }
        if !predicate.ty().is_bool(repr) {
            return Err(BuildError::ExpectedBool);
        }
        Ok(Self { predicate, kind })
    }
    pub fn predicate(&self) -> &Tm<R> {
        &self.predicate
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> ExprI for TyModel<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyModel
    }
}
impl<R: TrustedRepr> TyI for TyModel<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: Repr> From<TyModel<R>> for Expr<R> {
    fn from(value: TyModel<R>) -> Self {
        Self::TyModel(value)
    }
}
