use crate::{Expr, ExprI, Format, Kind, Repr, SurfaceTag, TrustedRepr, TyI};
use covalence_lib_hash::O256;

/// Surface link resolving to a closed Lean `HolE` type of the recorded kind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TyLink<R: Repr> {
    source: O256,
    format: Format,
    kind: Kind<R>,
}
impl<R: Repr> TyLink<R> {
    pub fn new(source: O256, format: Format, kind: Kind<R>) -> Self {
        Self {
            source,
            format,
            kind,
        }
    }
    pub fn source(&self) -> O256 {
        self.source
    }
    pub fn format(&self) -> Format {
        self.format
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: TrustedRepr> ExprI for TyLink<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TyLink
    }
}
impl<R: TrustedRepr> TyI for TyLink<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: Repr> From<TyLink<R>> for Expr<R> {
    fn from(value: TyLink<R>) -> Self {
        Self::TyLink(value)
    }
}
