use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.lam`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmLam<R: Repr> {
    domain: Ty<R>,
    body: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmLam<R> {
    /// # Errors
    /// Returns an error unless `ty` is the arrow from `domain` to the body's type.
    pub fn new(repr: &R, domain: Ty<R>, body: Tm<R>, ty: Ty<R>) -> Result<Self, BuildError> {
        let Some((actual_domain, actual_codomain)) = ty.as_arr(repr) else {
            return Err(BuildError::ExpectedFunction);
        };
        if !repr.ty_eq(&actual_domain, &domain) || !repr.ty_eq(&actual_codomain, body.ty()) {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self { domain, body, ty })
    }
    pub fn domain(&self) -> &Ty<R> {
        &self.domain
    }
    pub fn body(&self) -> &Tm<R> {
        &self.body
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmLam<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmLam
    }
}
impl<R: TrustedRepr> TmI for TmLam<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmLam<R>> for Expr<R> {
    fn from(value: TmLam<R>) -> Self {
        Self::TmLam(value)
    }
}
