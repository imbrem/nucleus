use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.eps`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmEps<R: Repr> {
    predicate: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmEps<R> {
    /// # Errors
    /// Returns an error unless `predicate` has type `ty → bool`.
    pub fn new(repr: &R, ty: Ty<R>, predicate: Tm<R>) -> Result<Self, BuildError> {
        if !repr.ty_eq_pred(predicate.ty(), &ty) {
            return Err(BuildError::TypeMismatch);
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
impl<R: TrustedRepr> ExprI for TmEps<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmEps
    }
}
impl<R: TrustedRepr> TmI for TmEps<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmEps<R>> for Expr<R> {
    fn from(value: TmEps<R>) -> Self {
        Self::TmEps(value)
    }
}
