use crate::{Expr, ExprI, Kind, KindI, Repr, SurfaceTag, TrustedRepr};

/// Rust counterpart of Lean `Nucleus.Hol.Kind.arr`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KindArr<R: Repr> {
    domain: Kind<R>,
    codomain: Kind<R>,
}
impl<R: Repr> KindArr<R> {
    #[must_use]
    pub fn new(domain: Kind<R>, codomain: Kind<R>) -> Self {
        Self { domain, codomain }
    }
    pub fn domain(&self) -> &Kind<R> {
        &self.domain
    }
    pub fn codomain(&self) -> &Kind<R> {
        &self.codomain
    }
}
impl<R: TrustedRepr> KindI for KindArr<R> {}
impl<R: TrustedRepr> ExprI for KindArr<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::KindArr
    }
}
impl<R: Repr> From<KindArr<R>> for Expr<R> {
    fn from(value: KindArr<R>) -> Self {
        Self::KindArr(value)
    }
}
