use crate::{Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Surface type conversion.
///
/// This lowers to `value` when its source and target types are equal. Otherwise
/// it denotes an arbitrary well-formed inhabitant of `target`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmCast<R: Repr> {
    value: Tm<R>,
    target: Ty<R>,
}

impl<R: Repr> TmCast<R> {
    #[must_use]
    pub fn new(value: Tm<R>, target: Ty<R>) -> Self {
        Self { value, target }
    }

    pub fn value(&self) -> &Tm<R> {
        &self.value
    }

    pub fn target(&self) -> &Ty<R> {
        &self.target
    }

    pub fn is_identity(&self, repr: &R) -> bool {
        repr.ty_eq(self.value.ty(), &self.target)
    }
}

impl<R: TrustedRepr> ExprI for TmCast<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmCast
    }
}

impl<R: TrustedRepr> TmI for TmCast<R> {
    type Ty = Ty<R>;

    fn ty(&self) -> &Ty<R> {
        &self.target
    }
}

impl<R: Repr> From<TmCast<R>> for Expr<R> {
    fn from(value: TmCast<R>) -> Self {
        Self::TmCast(value)
    }
}
