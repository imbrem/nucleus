use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, TrustedRepr, Ty, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.tyApp`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyApp<R: Repr> {
    function: Ty<R>,
    argument: Ty<R>,
    kind: Kind<R>,
}
impl<R: Repr> TyApp<R> {
    /// # Errors
    /// Returns an error unless `function` accepts the kind of `argument`.
    pub fn new(repr: &R, function: Ty<R>, argument: Ty<R>) -> Result<Self, BuildError> {
        let Some((domain, kind)) = function.kind().as_arr(repr) else {
            return Err(BuildError::ExpectedFunction);
        };
        if !repr.ix_eq(domain.index(), argument.kind().index()) {
            return Err(BuildError::KindMismatch);
        }
        Ok(Self {
            function,
            argument,
            kind,
        })
    }
    pub fn function(&self) -> &Ty<R> {
        &self.function
    }
    pub fn argument(&self) -> &Ty<R> {
        &self.argument
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> ExprI for TyApp<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyApp
    }
}
impl<R: TrustedRepr> TyI for TyApp<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: Repr> From<TyApp<R>> for Expr<R> {
    fn from(value: TyApp<R>) -> Self {
        Self::TyApp(value)
    }
}
