use crate::{Expr, ExprI, Repr, SurfaceTag, TmI, TrustedRepr, Ty, Variable};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.fv`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmFv<R: Repr> {
    variable: Variable<R>,
}
impl<R: Repr> TmFv<R> {
    pub fn new(variable: Variable<R>) -> Self {
        Self { variable }
    }
    pub fn variable(&self) -> &Variable<R> {
        &self.variable
    }
}
impl<R: TrustedRepr> ExprI for TmFv<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmFv
    }
}
impl<R: TrustedRepr> TmI for TmFv<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.variable.ty
    }
}
impl<R: Repr> From<TmFv<R>> for Expr<R> {
    fn from(value: TmFv<R>) -> Self {
        Self::TmFv(value)
    }
}
