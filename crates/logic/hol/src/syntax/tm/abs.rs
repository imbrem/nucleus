use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.abs`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmAbs<R: Repr> {
    carrier: Ty<R>,
    predicate: Tm<R>,
    value: Tm<R>,
    ty: Ty<R>,
}
impl<R: Repr> TmAbs<R> {
    /// # Errors
    /// Returns an error unless the value has the carrier type and `ty` is the matching subtype.
    pub fn new(
        repr: &R,
        carrier: Ty<R>,
        predicate: Tm<R>,
        value: Tm<R>,
        ty: Ty<R>,
    ) -> Result<Self, BuildError> {
        if !repr.ty_eq(&carrier, value.ty()) {
            return Err(BuildError::TypeMismatch);
        }
        let Expr::TySub(subtype) = repr.expr(ty.index()) else {
            return Err(BuildError::TypeMismatch);
        };
        if !repr.ty_eq(subtype.carrier(), &carrier)
            || !repr.ix_eq(subtype.predicate().index(), predicate.index())
        {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self {
            carrier,
            predicate,
            value,
            ty,
        })
    }
    pub fn carrier(&self) -> &Ty<R> {
        &self.carrier
    }
    pub fn predicate(&self) -> &Tm<R> {
        &self.predicate
    }
    pub fn value(&self) -> &Tm<R> {
        &self.value
    }
    pub fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: TrustedRepr> ExprI for TmAbs<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmAbs
    }
}
impl<R: TrustedRepr> TmI for TmAbs<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.ty
    }
}
impl<R: Repr> From<TmAbs<R>> for Expr<R> {
    fn from(value: TmAbs<R>) -> Self {
        Self::TmAbs(value)
    }
}
