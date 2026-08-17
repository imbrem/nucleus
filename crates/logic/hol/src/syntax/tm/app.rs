use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.app`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmApp<R: Repr> {
    function: Tm<R>,
    argument: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmApp<R> {
    /// # Errors
    /// Returns an error unless `function` accepts the type of `argument`.
    pub fn new(repr: &R, function: Tm<R>, argument: Tm<R>) -> Result<Self, BuildError> {
        let Some((domain, ty)) = function.ty().as_arr(repr) else {
            return Err(BuildError::ExpectedFunction);
        };
        if !repr.ix_eq(domain.index(), argument.ty().index()) {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self {
            function,
            argument,
            ty,
        })
    }
    pub fn function(&self) -> &Tm<R> {
        &self.function
    }
    pub fn argument(&self) -> &Tm<R> {
        &self.argument
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmApp<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmApp
    }
}
impl<R: TrustedRepr> TmI for TmApp<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmApp<R>> for Expr<R> {
    fn from(value: TmApp<R>) -> Self {
        Self::TmApp(value)
    }
}
