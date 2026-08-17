use crate::{Expr, ExprI, KindI, Repr, SurfaceTag};

/// Rust counterpart of Lean `Nucleus.Hol.Kind.star`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct KindStar;
impl KindStar {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}
impl ExprI for KindStar {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::KindStar
    }
}
impl KindI for KindStar {}
impl<R: Repr> From<KindStar> for Expr<R> {
    fn from(value: KindStar) -> Self {
        Self::KindStar(value)
    }
}
