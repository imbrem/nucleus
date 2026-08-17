use crate::{BuildError, Expr, ExprI, Repr, SurfaceTag, Tm, TmI, TrustedRepr, Ty};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.rep`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TmRep<R: Repr> {
    carrier: Ty<R>,
    predicate: Tm<R>,
    value: Tm<R>,
}
impl<R: Repr> TmRep<R> {
    /// # Errors
    /// Returns an error unless `value` has the subtype determined by carrier and predicate.
    pub fn new(
        repr: &R,
        carrier: Ty<R>,
        predicate: Tm<R>,
        value: Tm<R>,
    ) -> Result<Self, BuildError> {
        let Expr::TySub(subtype) = repr.expr(value.ty().index()) else {
            return Err(BuildError::TypeMismatch);
        };
        if !repr.ix_eq(subtype.carrier().index(), carrier.index())
            || !repr.ix_eq(subtype.predicate().index(), predicate.index())
        {
            return Err(BuildError::TypeMismatch);
        }
        Ok(Self {
            carrier,
            predicate,
            value,
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
}
impl<R: TrustedRepr> ExprI for TmRep<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TmRep
    }
}
impl<R: TrustedRepr> TmI for TmRep<R> {
    type Ty = Ty<R>;
    fn ty(&self) -> &Ty<R> {
        &self.carrier
    }
}
impl<R: Repr> From<TmRep<R>> for Expr<R> {
    fn from(value: TmRep<R>) -> Self {
        Self::TmRep(value)
    }
}
