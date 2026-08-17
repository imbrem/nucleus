use crate::{Expr, ExprI, Kind, Repr, SurfaceTag, TrustedRepr, TyI, TypeVariable};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.tyBv`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyBv<R: Repr> {
    variable: TypeVariable<R>,
}
impl<R: Repr> TyBv<R> {
    pub fn new(variable: TypeVariable<R>) -> Self {
        Self { variable }
    }
    pub fn variable(&self) -> &TypeVariable<R> {
        &self.variable
    }
}
impl<R: TrustedRepr> ExprI for TyBv<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyBv
    }
}
impl<R: TrustedRepr> TyI for TyBv<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.variable.kind
    }
}
impl<R: Repr> From<TyBv<R>> for Expr<R> {
    fn from(value: TyBv<R>) -> Self {
        Self::TyBv(value)
    }
}
