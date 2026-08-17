use crate::{Bv, Expr, ExprI, Repr, SurfaceTag, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.bv`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmBv<R: Repr> {
    index: Bv,
    ty: Ty<R>,
}
impl<R: Repr> TmBv<R> {
    pub fn new(index: Bv, ty: Ty<R>) -> Self {
        Self { index, ty }
    }
    pub fn index(&self) -> Bv {
        self.index
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmBv<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmBv
    }
}
impl<R: TrustedRepr> TmI for TmBv<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmBv<R>> for Expr<R> {
    fn from(value: TmBv<R>) -> Self {
        Self::TmBv(value)
    }
}
