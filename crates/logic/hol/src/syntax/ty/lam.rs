use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, TrustedRepr, Ty, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.tyLam`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyLam<R: Repr> {
    domain: Kind<R>,
    body: Ty<R>,
    kind: Kind<R>,
}
impl<R: Repr> TyLam<R> {
    /// # Errors
    /// Returns an error unless `kind` is the arrow from `domain` to the body's kind.
    pub fn new(repr: &R, domain: Kind<R>, body: Ty<R>, kind: Kind<R>) -> Result<Self, BuildError> {
        let Some((actual_domain, actual_codomain)) = kind.as_arr(repr) else {
            return Err(BuildError::ExpectedFunction);
        };
        if !repr.ix_eq(actual_domain.index(), domain.index())
            || !repr.ix_eq(actual_codomain.index(), body.kind().index())
        {
            return Err(BuildError::KindMismatch);
        }
        Ok(Self { domain, body, kind })
    }

    pub fn domain(&self) -> &Kind<R> {
        &self.domain
    }

    pub fn body(&self) -> &Ty<R> {
        &self.body
    }

    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}

impl<R: TrustedRepr> ExprI for TyLam<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyLam
    }
}

impl<R: TrustedRepr> TyI for TyLam<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}

impl<R: Repr> From<TyLam<R>> for Expr<R> {
    fn from(value: TyLam<R>) -> Self {
        Self::TyLam(value)
    }
}
