use crate::{BuildError, Expr, ExprI, Kind, Repr, SurfaceTag, Tm, TrustedRepr, Ty, TyI};

/// Rust counterpart of Lean `Nucleus.HolE.Expr.sub`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TySub<R: Repr> {
    carrier: Ty<R>,
    predicate: Tm<R>,
    kind: Kind<R>,
}

impl<R: Repr> TySub<R> {
    /// # Errors
    /// Returns an error unless the carrier is ordinary and the predicate is Boolean.
    pub fn new(repr: &R, carrier: Ty<R>, predicate: Tm<R>) -> Result<Self, BuildError> {
        if !carrier.kind().is_star(repr) {
            return Err(BuildError::ExpectedStar);
        }
        if !predicate.ty().is_bool(repr) {
            return Err(BuildError::ExpectedBool);
        }
        let kind = carrier.kind().clone();
        Ok(Self {
            carrier,
            predicate,
            kind,
        })
    }

    pub fn carrier(&self) -> &Ty<R> {
        &self.carrier
    }
    pub fn predicate(&self) -> &Tm<R> {
        &self.predicate
    }
    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}

impl<R: TrustedRepr> ExprI for TySub<R> {
    fn tag(&self) -> SurfaceTag {
        SurfaceTag::TySub
    }
}
impl<R: TrustedRepr> TyI for TySub<R> {
    type Kind = Kind<R>;
    fn kind(&self) -> &Kind<R> {
        &self.kind
    }
}
impl<R: Repr> From<TySub<R>> for Expr<R> {
    fn from(value: TySub<R>) -> Self {
        Self::TySub(value)
    }
}
