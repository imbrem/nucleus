use crate::{Expr, ExprI, Format, Repr, SurfaceTag, TmI, TrustedRepr, Ty};
use covalence_lib_hash::O256;

/// Surface link resolving to a closed Lean `HolE` term of the recorded type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmLink<R: Repr> {
    source: O256,
    format: Format,
    ty: Ty<R>,
}
impl<R: Repr> TmLink<R> {
    pub fn new(source: O256, format: Format, ty: Ty<R>) -> Self {
        Self { source, format, ty }
    }
    pub fn source(&self) -> O256 {
        self.source
    }
    pub fn format(&self) -> Format {
        self.format
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmLink<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmLink
    }
}
impl<R: TrustedRepr> TmI for TmLink<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmLink<R>> for Expr<R> {
    fn from(value: TmLink<R>) -> Self {
        Self::TmLink(value)
    }
}
