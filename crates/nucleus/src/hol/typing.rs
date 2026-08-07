//! Deep syntax trees, substitution, and type synthesis.
//!
//! [`Deep`] is the in-memory tree substrate the kernel works over when a
//! rule must rewrite syntax: premises are loaded from the store, lifted or
//! substituted structurally, and interned back bottom-up. The operations
//! follow `Substitution.lean` of the reference development, with one
//! deliberate strengthening carried through from `semantics.txt`: term
//! substitution and opening track the number of *type* binders crossed and
//! type-lift substituted values accordingly, because `TM_TYLAM` types its
//! body under the lifted variable context.
//!
//! This prototype re-expands stored DAGs into trees per operation (bounded
//! by [`MAX_DEPTH`]); per-id memoization and an id-leaf layered substrate
//! are planned optimizations, not semantic choices.

use covalence_lib_error::snafu::OptionExt;

use super::syntax::{Kind, KindId, KindsId, Substrate, TermId, Tm, Ty, TypeId, VarsId};
use super::view::{
    DepthExceededSnafu, HolError, HolView, KindMismatchSnafu, TypeMismatchSnafu,
    UnboundVariableSnafu,
};
use super::{Operation, Policy};

/// Maximum syntax depth accepted when expanding stored objects.
pub const MAX_DEPTH: usize = 512;

/// The in-memory tree substrate; source references stay raw coordinates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Deep;

super::syntax::impl_node_traits!(shared impl() Deep);

#[expect(
    clippy::expl_impl_clone_on_copy,
    reason = "clippy 1.97 false positive: Kind<Deep> is not Copy (Box children); \
              verified by direct trait probe"
)]
impl Clone for Kind<Deep> {
    fn clone(&self) -> Self {
        match self {
            Self::Star => Self::Star,
            Self::Arr(a, b) => Self::Arr(a.clone(), b.clone()),
        }
    }
}

#[expect(
    clippy::expl_impl_clone_on_copy,
    reason = "clippy 1.97 false positive: Kind<Deep> is not Copy (Box children); \
              verified by direct trait probe"
)]
impl Clone for Ty<Deep> {
    fn clone(&self) -> Self {
        match self {
            Self::Bv(n) => Self::Bv(*n),
            Self::Lam(k, b) => Self::Lam(k.clone(), b.clone()),
            Self::App(f, x) => Self::App(f.clone(), x.clone()),
            Self::All(k, b) => Self::All(k.clone(), b.clone()),
            Self::Bool => Self::Bool,
            Self::Arr(a, b) => Self::Arr(a.clone(), b.clone()),
            Self::Sub(a, p) => Self::Sub(a.clone(), p.clone()),
            Self::Ind => Self::Ind,
            Self::Ext(s, i) => Self::Ext(*s, *i),
        }
    }
}

#[expect(
    clippy::expl_impl_clone_on_copy,
    reason = "clippy 1.97 false positive: Kind<Deep> is not Copy (Box children); \
              verified by direct trait probe"
)]
impl Clone for Tm<Deep> {
    fn clone(&self) -> Self {
        match self {
            Self::Bv(n) => Self::Bv(*n),
            Self::App(f, x) => Self::App(f.clone(), x.clone()),
            Self::Lam(a, t) => Self::Lam(a.clone(), t.clone()),
            Self::TyApp(f, x) => Self::TyApp(f.clone(), x.clone()),
            Self::TyLam(k, t) => Self::TyLam(k.clone(), t.clone()),
            Self::Bool(b) => Self::Bool(*b),
            Self::Eq(l, r) => Self::Eq(l.clone(), r.clone()),
            Self::Eps(p) => Self::Eps(p.clone()),
            Self::Abs(p, x) => Self::Abs(p.clone(), x.clone()),
            Self::Rep(p, x) => Self::Rep(p.clone(), x.clone()),
            Self::Ext(s, i, c) => Self::Ext(*s, *i, c.clone()),
        }
    }
}

impl Substrate for Deep {
    type Kind = Box<Kind<Deep>>;
    type Ty = Box<Ty<Deep>>;
    type Tm = Box<Tm<Deep>>;
    type Src = i64;
}

/// An owned kind tree.
pub type DeepKind = Box<Kind<Deep>>;
/// An owned type tree.
pub type DeepTy = Box<Ty<Deep>>;
/// An owned term tree.
pub type DeepTm = Box<Tm<Deep>>;

fn shifted(index: u32, amount: u32, cutoff: u32) -> u32 {
    if index >= cutoff {
        index + amount
    } else {
        index
    }
}

/// Lifts type de Bruijn indices at or above `cutoff` by `amount`.
#[must_use]
pub fn lift_ty_in_ty(ty: &Ty<Deep>, amount: u32, cutoff: u32) -> Ty<Deep> {
    match ty {
        Ty::Bv(index) => Ty::Bv(shifted(*index, amount, cutoff)),
        Ty::Lam(kind, body) => Ty::Lam(
            kind.clone(),
            Box::new(lift_ty_in_ty(body, amount, cutoff + 1)),
        ),
        Ty::App(function, argument) => Ty::App(
            Box::new(lift_ty_in_ty(function, amount, cutoff)),
            Box::new(lift_ty_in_ty(argument, amount, cutoff)),
        ),
        Ty::All(kind, body) => Ty::All(
            kind.clone(),
            Box::new(lift_ty_in_ty(body, amount, cutoff + 1)),
        ),
        Ty::Bool => Ty::Bool,
        Ty::Arr(domain, codomain) => Ty::Arr(
            Box::new(lift_ty_in_ty(domain, amount, cutoff)),
            Box::new(lift_ty_in_ty(codomain, amount, cutoff)),
        ),
        Ty::Sub(carrier, predicate) => Ty::Sub(
            Box::new(lift_ty_in_ty(carrier, amount, cutoff)),
            Box::new(lift_ty_in_tm(predicate, amount, cutoff)),
        ),
        Ty::Ind => Ty::Ind,
        Ty::Ext(source, position) => Ty::Ext(*source, *position),
    }
}

/// Lifts type de Bruijn indices inside a term.
#[must_use]
pub fn lift_ty_in_tm(tm: &Tm<Deep>, amount: u32, cutoff: u32) -> Tm<Deep> {
    match tm {
        Tm::Bv(index) => Tm::Bv(*index),
        Tm::App(function, argument) => Tm::App(
            Box::new(lift_ty_in_tm(function, amount, cutoff)),
            Box::new(lift_ty_in_tm(argument, amount, cutoff)),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            Box::new(lift_ty_in_ty(domain, amount, cutoff)),
            Box::new(lift_ty_in_tm(body, amount, cutoff)),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(lift_ty_in_tm(function, amount, cutoff)),
            Box::new(lift_ty_in_ty(argument, amount, cutoff)),
        ),
        Tm::TyLam(kind, body) => Tm::TyLam(
            kind.clone(),
            Box::new(lift_ty_in_tm(body, amount, cutoff + 1)),
        ),
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(lift_ty_in_tm(left, amount, cutoff)),
            Box::new(lift_ty_in_tm(right, amount, cutoff)),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(lift_ty_in_tm(predicate, amount, cutoff))),
        Tm::Abs(predicate, value) => Tm::Abs(
            Box::new(lift_ty_in_tm(predicate, amount, cutoff)),
            Box::new(lift_ty_in_tm(value, amount, cutoff)),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            Box::new(lift_ty_in_tm(predicate, amount, cutoff)),
            Box::new(lift_ty_in_tm(value, amount, cutoff)),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(
            *source,
            *position,
            Box::new(lift_ty_in_ty(claim, amount, cutoff)),
        ),
    }
}

/// Lifts term de Bruijn indices at or above `cutoff` by `amount`.
///
/// Subtype predicates (`Abs`/`Rep`) live in their own closed one-variable
/// context and are untouched, exactly as in the reference development.
#[must_use]
pub fn lift_tm_in_tm(tm: &Tm<Deep>, amount: u32, cutoff: u32) -> Tm<Deep> {
    match tm {
        Tm::Bv(index) => Tm::Bv(shifted(*index, amount, cutoff)),
        Tm::App(function, argument) => Tm::App(
            Box::new(lift_tm_in_tm(function, amount, cutoff)),
            Box::new(lift_tm_in_tm(argument, amount, cutoff)),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            domain.clone(),
            Box::new(lift_tm_in_tm(body, amount, cutoff + 1)),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(lift_tm_in_tm(function, amount, cutoff)),
            argument.clone(),
        ),
        Tm::TyLam(kind, body) => {
            Tm::TyLam(kind.clone(), Box::new(lift_tm_in_tm(body, amount, cutoff)))
        }
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(lift_tm_in_tm(left, amount, cutoff)),
            Box::new(lift_tm_in_tm(right, amount, cutoff)),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(lift_tm_in_tm(predicate, amount, cutoff))),
        Tm::Abs(predicate, value) => Tm::Abs(
            predicate.clone(),
            Box::new(lift_tm_in_tm(value, amount, cutoff)),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            predicate.clone(),
            Box::new(lift_tm_in_tm(value, amount, cutoff)),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(*source, *position, claim.clone()),
    }
}

/// Simultaneously substitutes `values` for all free type variables of a type.
///
/// Under `depth` type binders, `TY_BV(depth + i)` becomes `values[i]`
/// lifted by `depth`; deeper references than `values` covers are unbound.
///
/// # Errors
///
/// Fails with an unbound-variable error when the values do not cover a
/// free index.
pub fn subst_ty_in_ty(ty: &Ty<Deep>, values: &[DeepTy], depth: u32) -> Result<Ty<Deep>, HolError> {
    Ok(match ty {
        Ty::Bv(index) => {
            if *index < depth {
                Ty::Bv(*index)
            } else {
                let position = (*index - depth) as usize;
                let value = values
                    .get(position)
                    .context(UnboundVariableSnafu { index: *index })?;
                lift_ty_in_ty(value, depth, 0)
            }
        }
        Ty::Lam(kind, body) => Ty::Lam(
            kind.clone(),
            Box::new(subst_ty_in_ty(body, values, depth + 1)?),
        ),
        Ty::App(function, argument) => Ty::App(
            Box::new(subst_ty_in_ty(function, values, depth)?),
            Box::new(subst_ty_in_ty(argument, values, depth)?),
        ),
        Ty::All(kind, body) => Ty::All(
            kind.clone(),
            Box::new(subst_ty_in_ty(body, values, depth + 1)?),
        ),
        Ty::Bool => Ty::Bool,
        Ty::Arr(domain, codomain) => Ty::Arr(
            Box::new(subst_ty_in_ty(domain, values, depth)?),
            Box::new(subst_ty_in_ty(codomain, values, depth)?),
        ),
        Ty::Sub(carrier, predicate) => Ty::Sub(
            Box::new(subst_ty_in_ty(carrier, values, depth)?),
            Box::new(subst_ty_in_tm(predicate, values, depth)?),
        ),
        Ty::Ind => Ty::Ind,
        Ty::Ext(source, position) => Ty::Ext(*source, *position),
    })
}

/// Simultaneously substitutes type variables inside a term.
///
/// # Errors
///
/// Fails with an unbound-variable error when the values do not cover a
/// free index.
pub fn subst_ty_in_tm(tm: &Tm<Deep>, values: &[DeepTy], depth: u32) -> Result<Tm<Deep>, HolError> {
    Ok(match tm {
        Tm::Bv(index) => Tm::Bv(*index),
        Tm::App(function, argument) => Tm::App(
            Box::new(subst_ty_in_tm(function, values, depth)?),
            Box::new(subst_ty_in_tm(argument, values, depth)?),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            Box::new(subst_ty_in_ty(domain, values, depth)?),
            Box::new(subst_ty_in_tm(body, values, depth)?),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(subst_ty_in_tm(function, values, depth)?),
            Box::new(subst_ty_in_ty(argument, values, depth)?),
        ),
        Tm::TyLam(kind, body) => Tm::TyLam(
            kind.clone(),
            Box::new(subst_ty_in_tm(body, values, depth + 1)?),
        ),
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(subst_ty_in_tm(left, values, depth)?),
            Box::new(subst_ty_in_tm(right, values, depth)?),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(subst_ty_in_tm(predicate, values, depth)?)),
        Tm::Abs(predicate, value) => Tm::Abs(
            Box::new(subst_ty_in_tm(predicate, values, depth)?),
            Box::new(subst_ty_in_tm(value, values, depth)?),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            Box::new(subst_ty_in_tm(predicate, values, depth)?),
            Box::new(subst_ty_in_tm(value, values, depth)?),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(
            *source,
            *position,
            Box::new(subst_ty_in_ty(claim, values, depth)?),
        ),
    })
}

/// Simultaneously substitutes `values` for all free term variables.
///
/// `term_depth` counts term binders crossed and `type_depth` type binders
/// crossed; substituted values are lifted by both, which is what makes
/// substitution capture-avoiding under `TM_TYLAM`'s lifted context.
///
/// # Errors
///
/// Fails with an unbound-variable error when the values do not cover a
/// free index.
pub fn subst_tm_in_tm(
    tm: &Tm<Deep>,
    values: &[DeepTm],
    term_depth: u32,
    type_depth: u32,
) -> Result<Tm<Deep>, HolError> {
    Ok(match tm {
        Tm::Bv(index) => {
            if *index < term_depth {
                Tm::Bv(*index)
            } else {
                let position = (*index - term_depth) as usize;
                let value = values
                    .get(position)
                    .context(UnboundVariableSnafu { index: *index })?;
                let lifted = lift_tm_in_tm(value, term_depth, 0);
                lift_ty_in_tm(&lifted, type_depth, 0)
            }
        }
        Tm::App(function, argument) => Tm::App(
            Box::new(subst_tm_in_tm(function, values, term_depth, type_depth)?),
            Box::new(subst_tm_in_tm(argument, values, term_depth, type_depth)?),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            domain.clone(),
            Box::new(subst_tm_in_tm(body, values, term_depth + 1, type_depth)?),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(subst_tm_in_tm(function, values, term_depth, type_depth)?),
            argument.clone(),
        ),
        Tm::TyLam(kind, body) => Tm::TyLam(
            kind.clone(),
            Box::new(subst_tm_in_tm(body, values, term_depth, type_depth + 1)?),
        ),
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(subst_tm_in_tm(left, values, term_depth, type_depth)?),
            Box::new(subst_tm_in_tm(right, values, term_depth, type_depth)?),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(subst_tm_in_tm(
            predicate, values, term_depth, type_depth,
        )?)),
        Tm::Abs(predicate, value) => Tm::Abs(
            predicate.clone(),
            Box::new(subst_tm_in_tm(value, values, term_depth, type_depth)?),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            predicate.clone(),
            Box::new(subst_tm_in_tm(value, values, term_depth, type_depth)?),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(*source, *position, claim.clone()),
    })
}

/// Opens a type binder: substitutes `value` for `TY_BV 0`, decrementing
/// the remaining free type variables.
#[must_use]
pub fn open_ty_in_ty(body: &Ty<Deep>, value: &Ty<Deep>) -> Ty<Deep> {
    open_ty_in_ty_at(body, value, 0)
}

fn open_ty_in_ty_at(body: &Ty<Deep>, value: &Ty<Deep>, depth: u32) -> Ty<Deep> {
    match body {
        Ty::Bv(index) => match (*index).cmp(&depth) {
            std::cmp::Ordering::Less => Ty::Bv(*index),
            std::cmp::Ordering::Equal => lift_ty_in_ty(value, depth, 0),
            std::cmp::Ordering::Greater => Ty::Bv(*index - 1),
        },
        Ty::Lam(kind, inner) => Ty::Lam(
            kind.clone(),
            Box::new(open_ty_in_ty_at(inner, value, depth + 1)),
        ),
        Ty::App(function, argument) => Ty::App(
            Box::new(open_ty_in_ty_at(function, value, depth)),
            Box::new(open_ty_in_ty_at(argument, value, depth)),
        ),
        Ty::All(kind, inner) => Ty::All(
            kind.clone(),
            Box::new(open_ty_in_ty_at(inner, value, depth + 1)),
        ),
        Ty::Bool => Ty::Bool,
        Ty::Arr(domain, codomain) => Ty::Arr(
            Box::new(open_ty_in_ty_at(domain, value, depth)),
            Box::new(open_ty_in_ty_at(codomain, value, depth)),
        ),
        Ty::Sub(carrier, predicate) => Ty::Sub(
            Box::new(open_ty_in_ty_at(carrier, value, depth)),
            Box::new(open_ty_in_tm_at(predicate, value, depth)),
        ),
        Ty::Ind => Ty::Ind,
        Ty::Ext(source, position) => Ty::Ext(*source, *position),
    }
}

/// Opens a type binder through a term body.
#[must_use]
pub fn open_ty_in_tm(body: &Tm<Deep>, value: &Ty<Deep>) -> Tm<Deep> {
    open_ty_in_tm_at(body, value, 0)
}

fn open_ty_in_tm_at(body: &Tm<Deep>, value: &Ty<Deep>, depth: u32) -> Tm<Deep> {
    match body {
        Tm::Bv(index) => Tm::Bv(*index),
        Tm::App(function, argument) => Tm::App(
            Box::new(open_ty_in_tm_at(function, value, depth)),
            Box::new(open_ty_in_tm_at(argument, value, depth)),
        ),
        Tm::Lam(domain, inner) => Tm::Lam(
            Box::new(open_ty_in_ty_at(domain, value, depth)),
            Box::new(open_ty_in_tm_at(inner, value, depth)),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(open_ty_in_tm_at(function, value, depth)),
            Box::new(open_ty_in_ty_at(argument, value, depth)),
        ),
        Tm::TyLam(kind, inner) => Tm::TyLam(
            kind.clone(),
            Box::new(open_ty_in_tm_at(inner, value, depth + 1)),
        ),
        Tm::Bool(literal) => Tm::Bool(*literal),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(open_ty_in_tm_at(left, value, depth)),
            Box::new(open_ty_in_tm_at(right, value, depth)),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(open_ty_in_tm_at(predicate, value, depth))),
        Tm::Abs(predicate, inner) => Tm::Abs(
            Box::new(open_ty_in_tm_at(predicate, value, depth)),
            Box::new(open_ty_in_tm_at(inner, value, depth)),
        ),
        Tm::Rep(predicate, inner) => Tm::Rep(
            Box::new(open_ty_in_tm_at(predicate, value, depth)),
            Box::new(open_ty_in_tm_at(inner, value, depth)),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(
            *source,
            *position,
            Box::new(open_ty_in_ty_at(claim, value, depth)),
        ),
    }
}

/// Opens a term binder: substitutes `value` for `TM_BV 0`, decrementing
/// the remaining free term variables.
#[must_use]
pub fn open_tm_in_tm(body: &Tm<Deep>, value: &Tm<Deep>) -> Tm<Deep> {
    open_tm_in_tm_at(body, value, 0, 0)
}

fn open_tm_in_tm_at(
    body: &Tm<Deep>,
    value: &Tm<Deep>,
    term_depth: u32,
    type_depth: u32,
) -> Tm<Deep> {
    match body {
        Tm::Bv(index) => match (*index).cmp(&term_depth) {
            std::cmp::Ordering::Less => Tm::Bv(*index),
            std::cmp::Ordering::Equal => {
                let lifted = lift_tm_in_tm(value, term_depth, 0);
                lift_ty_in_tm(&lifted, type_depth, 0)
            }
            std::cmp::Ordering::Greater => Tm::Bv(*index - 1),
        },
        Tm::App(function, argument) => Tm::App(
            Box::new(open_tm_in_tm_at(function, value, term_depth, type_depth)),
            Box::new(open_tm_in_tm_at(argument, value, term_depth, type_depth)),
        ),
        Tm::Lam(domain, inner) => Tm::Lam(
            domain.clone(),
            Box::new(open_tm_in_tm_at(inner, value, term_depth + 1, type_depth)),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(open_tm_in_tm_at(function, value, term_depth, type_depth)),
            argument.clone(),
        ),
        Tm::TyLam(kind, inner) => Tm::TyLam(
            kind.clone(),
            Box::new(open_tm_in_tm_at(inner, value, term_depth, type_depth + 1)),
        ),
        Tm::Bool(literal) => Tm::Bool(*literal),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(open_tm_in_tm_at(left, value, term_depth, type_depth)),
            Box::new(open_tm_in_tm_at(right, value, term_depth, type_depth)),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(open_tm_in_tm_at(
            predicate, value, term_depth, type_depth,
        ))),
        Tm::Abs(predicate, inner) => Tm::Abs(
            predicate.clone(),
            Box::new(open_tm_in_tm_at(inner, value, term_depth, type_depth)),
        ),
        Tm::Rep(predicate, inner) => Tm::Rep(
            predicate.clone(),
            Box::new(open_tm_in_tm_at(inner, value, term_depth, type_depth)),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(*source, *position, claim.clone()),
    }
}

/// Strengthens a term out of the innermost variable's scope: lowers every
/// free term index by one, returning `None` if the term mentions `TM_BV 0`.
#[must_use]
pub fn strengthen_tm_in_tm(tm: &Tm<Deep>) -> Option<Tm<Deep>> {
    strengthen_tm_at(tm, 0)
}

fn strengthen_tm_at(tm: &Tm<Deep>, cutoff: u32) -> Option<Tm<Deep>> {
    Some(match tm {
        Tm::Bv(index) => match (*index).cmp(&cutoff) {
            std::cmp::Ordering::Less => Tm::Bv(*index),
            std::cmp::Ordering::Equal => return None,
            std::cmp::Ordering::Greater => Tm::Bv(*index - 1),
        },
        Tm::App(function, argument) => Tm::App(
            Box::new(strengthen_tm_at(function, cutoff)?),
            Box::new(strengthen_tm_at(argument, cutoff)?),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            domain.clone(),
            Box::new(strengthen_tm_at(body, cutoff + 1)?),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(strengthen_tm_at(function, cutoff)?),
            argument.clone(),
        ),
        Tm::TyLam(kind, body) => Tm::TyLam(kind.clone(), Box::new(strengthen_tm_at(body, cutoff)?)),
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(strengthen_tm_at(left, cutoff)?),
            Box::new(strengthen_tm_at(right, cutoff)?),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(strengthen_tm_at(predicate, cutoff)?)),
        Tm::Abs(predicate, value) => Tm::Abs(
            predicate.clone(),
            Box::new(strengthen_tm_at(value, cutoff)?),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            predicate.clone(),
            Box::new(strengthen_tm_at(value, cutoff)?),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(*source, *position, claim.clone()),
    })
}

/// Strengthens a type out of the innermost kind variable's scope: lowers
/// every free type index by one, returning `None` on a `TY_BV 0` use.
#[must_use]
pub fn strengthen_ty_in_ty(ty: &Ty<Deep>) -> Option<Ty<Deep>> {
    strengthen_ty_at(ty, 0)
}

/// Strengthens a term out of the innermost kind variable's scope.
#[must_use]
pub fn strengthen_ty_in_tm(tm: &Tm<Deep>) -> Option<Tm<Deep>> {
    strengthen_ty_in_tm_at(tm, 0)
}

fn strengthen_ty_at(ty: &Ty<Deep>, cutoff: u32) -> Option<Ty<Deep>> {
    Some(match ty {
        Ty::Bv(index) => match (*index).cmp(&cutoff) {
            std::cmp::Ordering::Less => Ty::Bv(*index),
            std::cmp::Ordering::Equal => return None,
            std::cmp::Ordering::Greater => Ty::Bv(*index - 1),
        },
        Ty::Lam(kind, body) => Ty::Lam(kind.clone(), Box::new(strengthen_ty_at(body, cutoff + 1)?)),
        Ty::App(function, argument) => Ty::App(
            Box::new(strengthen_ty_at(function, cutoff)?),
            Box::new(strengthen_ty_at(argument, cutoff)?),
        ),
        Ty::All(kind, body) => Ty::All(kind.clone(), Box::new(strengthen_ty_at(body, cutoff + 1)?)),
        Ty::Bool => Ty::Bool,
        Ty::Arr(domain, codomain) => Ty::Arr(
            Box::new(strengthen_ty_at(domain, cutoff)?),
            Box::new(strengthen_ty_at(codomain, cutoff)?),
        ),
        Ty::Sub(carrier, predicate) => Ty::Sub(
            Box::new(strengthen_ty_at(carrier, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(predicate, cutoff)?),
        ),
        Ty::Ind => Ty::Ind,
        Ty::Ext(source, position) => Ty::Ext(*source, *position),
    })
}

fn strengthen_ty_in_tm_at(tm: &Tm<Deep>, cutoff: u32) -> Option<Tm<Deep>> {
    Some(match tm {
        Tm::Bv(index) => Tm::Bv(*index),
        Tm::App(function, argument) => Tm::App(
            Box::new(strengthen_ty_in_tm_at(function, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(argument, cutoff)?),
        ),
        Tm::Lam(domain, body) => Tm::Lam(
            Box::new(strengthen_ty_at(domain, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(body, cutoff)?),
        ),
        Tm::TyApp(function, argument) => Tm::TyApp(
            Box::new(strengthen_ty_in_tm_at(function, cutoff)?),
            Box::new(strengthen_ty_at(argument, cutoff)?),
        ),
        Tm::TyLam(kind, body) => Tm::TyLam(
            kind.clone(),
            Box::new(strengthen_ty_in_tm_at(body, cutoff + 1)?),
        ),
        Tm::Bool(value) => Tm::Bool(*value),
        Tm::Eq(left, right) => Tm::Eq(
            Box::new(strengthen_ty_in_tm_at(left, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(right, cutoff)?),
        ),
        Tm::Eps(predicate) => Tm::Eps(Box::new(strengthen_ty_in_tm_at(predicate, cutoff)?)),
        Tm::Abs(predicate, value) => Tm::Abs(
            Box::new(strengthen_ty_in_tm_at(predicate, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(value, cutoff)?),
        ),
        Tm::Rep(predicate, value) => Tm::Rep(
            Box::new(strengthen_ty_in_tm_at(predicate, cutoff)?),
            Box::new(strengthen_ty_in_tm_at(value, cutoff)?),
        ),
        Tm::Ext(source, position, claim) => Tm::Ext(
            *source,
            *position,
            Box::new(strengthen_ty_at(claim, cutoff)?),
        ),
    })
}

impl<'v, P: Policy> HolView<'v, P> {
    // ------------------------------------------------------------------
    // Loading and interning deep trees.
    // ------------------------------------------------------------------

    /// Expands a stored kind into an owned tree.
    ///
    /// # Errors
    ///
    /// Fails on malformed rows or when [`MAX_DEPTH`] is exceeded.
    pub fn load_kind(&self, id: KindId<'v>) -> Result<DeepKind, HolError> {
        self.load_kind_at(id, 0)
    }

    fn load_kind_at(&self, id: KindId<'v>, depth: usize) -> Result<DeepKind, HolError> {
        if depth > MAX_DEPTH {
            return DepthExceededSnafu.fail();
        }
        Ok(Box::new(match self.kind_node(id)? {
            Kind::Star => Kind::Star,
            Kind::Arr(domain, codomain) => Kind::Arr(
                self.load_kind_at(domain, depth + 1)?,
                self.load_kind_at(codomain, depth + 1)?,
            ),
        }))
    }

    /// Expands a stored type into an owned tree.
    ///
    /// # Errors
    ///
    /// Fails on malformed rows or when [`MAX_DEPTH`] is exceeded.
    pub fn load_ty(&self, id: TypeId<'v>) -> Result<DeepTy, HolError> {
        self.load_ty_at(id, 0)
    }

    fn load_ty_at(&self, id: TypeId<'v>, depth: usize) -> Result<DeepTy, HolError> {
        if depth > MAX_DEPTH {
            return DepthExceededSnafu.fail();
        }
        Ok(Box::new(match self.ty_node(id)? {
            Ty::Bv(index) => Ty::Bv(index),
            Ty::Lam(kind, body) => Ty::Lam(
                self.load_kind_at(kind, depth + 1)?,
                self.load_ty_at(body, depth + 1)?,
            ),
            Ty::App(function, argument) => Ty::App(
                self.load_ty_at(function, depth + 1)?,
                self.load_ty_at(argument, depth + 1)?,
            ),
            Ty::All(kind, body) => Ty::All(
                self.load_kind_at(kind, depth + 1)?,
                self.load_ty_at(body, depth + 1)?,
            ),
            Ty::Bool => Ty::Bool,
            Ty::Arr(domain, codomain) => Ty::Arr(
                self.load_ty_at(domain, depth + 1)?,
                self.load_ty_at(codomain, depth + 1)?,
            ),
            Ty::Sub(carrier, predicate) => Ty::Sub(
                self.load_ty_at(carrier, depth + 1)?,
                self.load_tm_at(predicate, depth + 1)?,
            ),
            Ty::Ind => Ty::Ind,
            Ty::Ext(source, position) => Ty::Ext(source.raw(), position),
        }))
    }

    /// Expands a stored term into an owned tree.
    ///
    /// # Errors
    ///
    /// Fails on malformed rows or when [`MAX_DEPTH`] is exceeded.
    pub fn load_tm(&self, id: TermId<'v>) -> Result<DeepTm, HolError> {
        self.load_tm_at(id, 0)
    }

    fn load_tm_at(&self, id: TermId<'v>, depth: usize) -> Result<DeepTm, HolError> {
        if depth > MAX_DEPTH {
            return DepthExceededSnafu.fail();
        }
        Ok(Box::new(match self.tm_node(id)? {
            Tm::Bv(index) => Tm::Bv(index),
            Tm::App(function, argument) => Tm::App(
                self.load_tm_at(function, depth + 1)?,
                self.load_tm_at(argument, depth + 1)?,
            ),
            Tm::Lam(domain, body) => Tm::Lam(
                self.load_ty_at(domain, depth + 1)?,
                self.load_tm_at(body, depth + 1)?,
            ),
            Tm::TyApp(function, argument) => Tm::TyApp(
                self.load_tm_at(function, depth + 1)?,
                self.load_ty_at(argument, depth + 1)?,
            ),
            Tm::TyLam(kind, body) => Tm::TyLam(
                self.load_kind_at(kind, depth + 1)?,
                self.load_tm_at(body, depth + 1)?,
            ),
            Tm::Bool(value) => Tm::Bool(value),
            Tm::Eq(left, right) => Tm::Eq(
                self.load_tm_at(left, depth + 1)?,
                self.load_tm_at(right, depth + 1)?,
            ),
            Tm::Eps(predicate) => Tm::Eps(self.load_tm_at(predicate, depth + 1)?),
            Tm::Abs(predicate, value) => Tm::Abs(
                self.load_tm_at(predicate, depth + 1)?,
                self.load_tm_at(value, depth + 1)?,
            ),
            Tm::Rep(predicate, value) => Tm::Rep(
                self.load_tm_at(predicate, depth + 1)?,
                self.load_tm_at(value, depth + 1)?,
            ),
            Tm::Ext(source, position, claim) => {
                Tm::Ext(source.raw(), position, self.load_ty_at(claim, depth + 1)?)
            }
        }))
    }

    /// Interns an owned kind tree bottom-up.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn intern_kind(&self, kind: &Kind<Deep>) -> Result<KindId<'v>, HolError> {
        match kind {
            Kind::Star => self.kind(Kind::Star),
            Kind::Arr(domain, codomain) => {
                let domain = self.intern_kind(domain)?;
                let codomain = self.intern_kind(codomain)?;
                self.kind(Kind::Arr(domain, codomain))
            }
        }
    }

    /// Interns an owned type tree bottom-up.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning, a source reference is not
    /// registered, or storage fails.
    pub fn intern_ty(&self, ty: &Ty<Deep>) -> Result<TypeId<'v>, HolError> {
        match ty {
            Ty::Bv(index) => self.ty(Ty::Bv(*index)),
            Ty::Lam(kind, body) => {
                let kind = self.intern_kind(kind)?;
                let body = self.intern_ty(body)?;
                self.ty(Ty::Lam(kind, body))
            }
            Ty::App(function, argument) => {
                let function = self.intern_ty(function)?;
                let argument = self.intern_ty(argument)?;
                self.ty(Ty::App(function, argument))
            }
            Ty::All(kind, body) => {
                let kind = self.intern_kind(kind)?;
                let body = self.intern_ty(body)?;
                self.ty(Ty::All(kind, body))
            }
            Ty::Bool => self.ty(Ty::Bool),
            Ty::Arr(domain, codomain) => {
                let domain = self.intern_ty(domain)?;
                let codomain = self.intern_ty(codomain)?;
                self.ty(Ty::Arr(domain, codomain))
            }
            Ty::Sub(carrier, predicate) => {
                let carrier = self.intern_ty(carrier)?;
                let predicate = self.intern_tm(predicate)?;
                self.ty(Ty::Sub(carrier, predicate))
            }
            Ty::Ind => self.ty(Ty::Ind),
            Ty::Ext(source, position) => {
                let source = self.source_from_raw(*source)?;
                self.ty(Ty::Ext(source, *position))
            }
        }
    }

    /// Interns an owned term tree bottom-up.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning, a source reference is not
    /// registered, or storage fails.
    pub fn intern_tm(&self, tm: &Tm<Deep>) -> Result<TermId<'v>, HolError> {
        match tm {
            Tm::Bv(index) => self.tm(Tm::Bv(*index)),
            Tm::App(function, argument) => {
                let function = self.intern_tm(function)?;
                let argument = self.intern_tm(argument)?;
                self.tm(Tm::App(function, argument))
            }
            Tm::Lam(domain, body) => {
                let domain = self.intern_ty(domain)?;
                let body = self.intern_tm(body)?;
                self.tm(Tm::Lam(domain, body))
            }
            Tm::TyApp(function, argument) => {
                let function = self.intern_tm(function)?;
                let argument = self.intern_ty(argument)?;
                self.tm(Tm::TyApp(function, argument))
            }
            Tm::TyLam(kind, body) => {
                let kind = self.intern_kind(kind)?;
                let body = self.intern_tm(body)?;
                self.tm(Tm::TyLam(kind, body))
            }
            Tm::Bool(value) => self.tm(Tm::Bool(*value)),
            Tm::Eq(left, right) => {
                let left = self.intern_tm(left)?;
                let right = self.intern_tm(right)?;
                self.tm(Tm::Eq(left, right))
            }
            Tm::Eps(predicate) => {
                let predicate = self.intern_tm(predicate)?;
                self.tm(Tm::Eps(predicate))
            }
            Tm::Abs(predicate, value) => {
                let predicate = self.intern_tm(predicate)?;
                let value = self.intern_tm(value)?;
                self.tm(Tm::Abs(predicate, value))
            }
            Tm::Rep(predicate, value) => {
                let predicate = self.intern_tm(predicate)?;
                let value = self.intern_tm(value)?;
                self.tm(Tm::Rep(predicate, value))
            }
            Tm::Ext(source, position, claim) => {
                let source = self.source_from_raw(*source)?;
                let claim = self.intern_ty(claim)?;
                self.tm(Tm::Ext(source, *position, claim))
            }
        }
    }

    // ------------------------------------------------------------------
    // Environments.
    // ------------------------------------------------------------------

    /// Loads a kind-context spine as an environment, innermost last.
    pub(crate) fn load_kind_env(&self, spine: KindsId<'v>) -> Result<Vec<DeepKind>, HolError> {
        let mut env = Vec::new();
        for entry in self.kinds_entries(spine)? {
            env.push(self.load_kind(entry)?);
        }
        env.reverse();
        Ok(env)
    }

    /// Loads a variable-context spine as an environment, innermost last.
    pub(crate) fn load_var_env(&self, spine: VarsId<'v>) -> Result<Vec<DeepTy>, HolError> {
        let mut env = Vec::new();
        for entry in self.vars_entries(spine)? {
            env.push(self.load_ty(entry)?);
        }
        env.reverse();
        Ok(env)
    }

    // ------------------------------------------------------------------
    // Synthesis.
    // ------------------------------------------------------------------

    /// Synthesizes the kind of a stored type under a kind context.
    ///
    /// # Errors
    ///
    /// Fails if the type is ill-formed under the context.
    pub fn kind_of(&self, kinds: KindsId<'v>, ty: TypeId<'v>) -> Result<KindId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let mut delta = self.load_kind_env(kinds)?;
        let tree = self.load_ty(ty)?;
        let kind = self.kind_of_deep(&mut delta, &tree)?;
        self.intern_kind(&kind)
    }

    /// Synthesizes the type of a stored term under kind and var contexts.
    ///
    /// # Errors
    ///
    /// Fails if the term is ill-formed under the contexts.
    pub fn type_of(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        tm: TermId<'v>,
    ) -> Result<TypeId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let mut delta = self.load_kind_env(kinds)?;
        let mut gamma = self.load_var_env(vars)?;
        let tree = self.load_tm(tm)?;
        let ty = self.type_of_deep(&mut delta, &mut gamma, &tree)?;
        self.intern_ty(&ty)
    }

    /// Kind synthesis over owned trees; the environment holds the
    /// innermost binder last.
    pub(crate) fn kind_of_deep(
        &self,
        delta: &mut Vec<DeepKind>,
        ty: &Ty<Deep>,
    ) -> Result<DeepKind, HolError> {
        Ok(match ty {
            Ty::Bv(index) => {
                let position = delta
                    .len()
                    .checked_sub(1 + *index as usize)
                    .context(UnboundVariableSnafu { index: *index })?;
                delta[position].clone()
            }
            Ty::Lam(kind, body) => {
                delta.push(kind.clone());
                let codomain = self.kind_of_deep(delta, body);
                delta.pop();
                Box::new(Kind::Arr(kind.clone(), codomain?))
            }
            Ty::App(function, argument) => {
                let function_kind = self.kind_of_deep(delta, function)?;
                let argument_kind = self.kind_of_deep(delta, argument)?;
                match *function_kind {
                    Kind::Arr(domain, codomain) if domain == argument_kind => codomain,
                    _ => return KindMismatchSnafu.fail(),
                }
            }
            Ty::All(kind, body) => {
                delta.push(kind.clone());
                let body_kind = self.kind_of_deep(delta, body);
                delta.pop();
                if matches!(*body_kind?, Kind::Star) {
                    Box::new(Kind::Star)
                } else {
                    return KindMismatchSnafu.fail();
                }
            }
            Ty::Bool | Ty::Ind | Ty::Ext(..) => Box::new(Kind::Star),
            Ty::Arr(domain, codomain) => {
                let domain_kind = self.kind_of_deep(delta, domain)?;
                let codomain_kind = self.kind_of_deep(delta, codomain)?;
                if matches!(*domain_kind, Kind::Star) && matches!(*codomain_kind, Kind::Star) {
                    Box::new(Kind::Star)
                } else {
                    return KindMismatchSnafu.fail();
                }
            }
            Ty::Sub(carrier, predicate) => {
                let carrier_kind = self.kind_of_deep(delta, carrier)?;
                if !matches!(*carrier_kind, Kind::Star) {
                    return KindMismatchSnafu.fail();
                }
                let mut local = vec![carrier.clone()];
                let predicate_ty = self.type_of_deep(delta, &mut local, predicate)?;
                if matches!(*predicate_ty, Ty::Bool) {
                    Box::new(Kind::Star)
                } else {
                    return TypeMismatchSnafu.fail();
                }
            }
        })
    }

    /// Type synthesis over owned trees; environments hold the innermost
    /// binder last.
    pub(crate) fn type_of_deep(
        &self,
        delta: &mut Vec<DeepKind>,
        gamma: &mut Vec<DeepTy>,
        tm: &Tm<Deep>,
    ) -> Result<DeepTy, HolError> {
        Ok(match tm {
            Tm::Bv(index) => {
                let position = gamma
                    .len()
                    .checked_sub(1 + *index as usize)
                    .context(UnboundVariableSnafu { index: *index })?;
                gamma[position].clone()
            }
            Tm::App(function, argument) => {
                let function_ty = self.type_of_deep(delta, gamma, function)?;
                let argument_ty = self.type_of_deep(delta, gamma, argument)?;
                match *function_ty {
                    Ty::Arr(domain, codomain) if domain == argument_ty => codomain,
                    _ => return TypeMismatchSnafu.fail(),
                }
            }
            Tm::Lam(domain, body) => {
                let domain_kind = self.kind_of_deep(delta, domain)?;
                if !matches!(*domain_kind, Kind::Star) {
                    return KindMismatchSnafu.fail();
                }
                gamma.push(domain.clone());
                let codomain = self.type_of_deep(delta, gamma, body);
                gamma.pop();
                Box::new(Ty::Arr(domain.clone(), codomain?))
            }
            Tm::TyApp(function, argument) => {
                let function_ty = self.type_of_deep(delta, gamma, function)?;
                let Ty::All(kind, body) = *function_ty else {
                    return TypeMismatchSnafu.fail();
                };
                let argument_kind = self.kind_of_deep(delta, argument)?;
                if argument_kind != kind {
                    return KindMismatchSnafu.fail();
                }
                Box::new(open_ty_in_ty(&body, argument))
            }
            Tm::TyLam(kind, body) => {
                delta.push(kind.clone());
                let mut lifted: Vec<DeepTy> = gamma
                    .iter()
                    .map(|entry| Box::new(lift_ty_in_ty(entry, 1, 0)))
                    .collect();
                let body_ty = self.type_of_deep(delta, &mut lifted, body);
                delta.pop();
                Box::new(Ty::All(kind.clone(), body_ty?))
            }
            Tm::Bool(_) => Box::new(Ty::Bool),
            Tm::Eq(left, right) => {
                let left_ty = self.type_of_deep(delta, gamma, left)?;
                let right_ty = self.type_of_deep(delta, gamma, right)?;
                if left_ty == right_ty {
                    Box::new(Ty::Bool)
                } else {
                    return TypeMismatchSnafu.fail();
                }
            }
            Tm::Eps(predicate) => {
                let predicate_ty = self.type_of_deep(delta, gamma, predicate)?;
                match *predicate_ty {
                    Ty::Arr(domain, codomain) if matches!(*codomain, Ty::Bool) => domain,
                    _ => return TypeMismatchSnafu.fail(),
                }
            }
            Tm::Abs(predicate, value) => {
                let carrier = self.type_of_deep(delta, gamma, value)?;
                let mut local = vec![carrier.clone()];
                let predicate_ty = self.type_of_deep(delta, &mut local, predicate)?;
                if !matches!(*predicate_ty, Ty::Bool) {
                    return TypeMismatchSnafu.fail();
                }
                Box::new(Ty::Sub(carrier, predicate.clone()))
            }
            Tm::Rep(predicate, value) => {
                let value_ty = self.type_of_deep(delta, gamma, value)?;
                let Ty::Sub(carrier, stored) = *value_ty else {
                    return TypeMismatchSnafu.fail();
                };
                if stored != *predicate {
                    return TypeMismatchSnafu.fail();
                }
                carrier
            }
            Tm::Ext(_, _, claim) => {
                let claim_kind = self.kind_of_deep(delta, claim)?;
                if matches!(*claim_kind, Kind::Star) {
                    claim.clone()
                } else {
                    return KindMismatchSnafu.fail();
                }
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::syntax::{Kind as KindNode, Tm as TmNode, Ty as TyNode};
    use super::super::{AllowAll, Hol};
    use super::*;

    fn open() -> Hol<AllowAll> {
        Hol::open_in_memory(AllowAll).expect("open kernel-state database")
    }

    #[test]
    fn identity_lambda_synthesizes_its_arrow_type() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(TyNode::Bool).expect("bool");
        let body = hol.tm(TmNode::Bv(0)).expect("bv0");
        let identity = hol.tm(TmNode::Lam(bool_ty, body)).expect("lam");
        let arrow = hol
            .type_of(hol.empty_kinds(), hol.empty_vars(), identity)
            .expect("synthesize");
        let expected = hol.ty(TyNode::Arr(bool_ty, bool_ty)).expect("arrow");
        assert_eq!(arrow, expected);
    }

    #[test]
    fn unbound_variables_are_rejected() {
        let connection = open();
        let hol = connection.view();
        let stray = hol.tm(TmNode::Bv(3)).expect("stray");
        assert!(matches!(
            hol.type_of(hol.empty_kinds(), hol.empty_vars(), stray),
            Err(HolError::UnboundVariable { .. })
        ));
    }

    #[test]
    fn application_requires_matching_domain() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(TyNode::Bool).expect("bool");
        let ind_ty = hol.ty(TyNode::Ind).expect("ind");
        let body = hol.tm(TmNode::Bv(0)).expect("bv0");
        let identity = hol.tm(TmNode::Lam(ind_ty, body)).expect("lam over ind");
        let truth = hol.tm(TmNode::Bool(true)).expect("true");
        let application = hol.tm(TmNode::App(identity, truth)).expect("app");
        assert!(matches!(
            hol.type_of(hol.empty_kinds(), hol.empty_vars(), application),
            Err(HolError::TypeMismatch)
        ));
        let _ = bool_ty;
    }

    #[test]
    fn lifting_respects_amount_and_cutoff() {
        // The memoization-shaped regression: the shift amount and cutoff
        // are both semantic parameters.
        let below = Ty::<Deep>::Bv(0);
        let at = Ty::<Deep>::Bv(1);
        let above = Ty::<Deep>::Bv(5);
        assert_eq!(lift_ty_in_ty(&below, 2, 1), Ty::Bv(0));
        assert_eq!(lift_ty_in_ty(&at, 2, 1), Ty::Bv(3));
        assert_eq!(lift_ty_in_ty(&above, 2, 1), Ty::Bv(7));
        assert_eq!(lift_ty_in_ty(&at, 3, 1), Ty::Bv(4));
    }

    #[test]
    fn opening_a_type_binder_decrements_outer_variables() {
        // (all *. BV1 -> BV0)[X := bool] under one ambient binder.
        let body = Ty::<Deep>::Arr(Box::new(Ty::Bv(1)), Box::new(Ty::Bv(0)));
        let opened = open_ty_in_ty(&body, &Ty::Bool);
        assert_eq!(opened, Ty::Arr(Box::new(Ty::Bv(0)), Box::new(Ty::Bool)));
    }

    #[test]
    fn term_opening_lifts_across_crossed_binders() {
        // Substituting BV0 := (free var BV0) under one lambda must lift the
        // free reference past the crossed binder.
        let body = Tm::<Deep>::Lam(
            Box::new(Ty::Bool),
            Box::new(Tm::App(Box::new(Tm::Bv(1)), Box::new(Tm::Bv(0)))),
        );
        let value = Tm::<Deep>::Bv(0);
        let opened = open_tm_in_tm(&body, &value);
        assert_eq!(
            opened,
            Tm::Lam(
                Box::new(Ty::Bool),
                Box::new(Tm::App(Box::new(Tm::Bv(1)), Box::new(Tm::Bv(0)))),
            )
        );
    }

    #[test]
    fn tylam_types_its_body_under_the_lifted_context() {
        // Delta = [*], Gamma = [TY_BV 0]: under TYLAM the entry must lift
        // to TY_BV 1, so the synthesized universal body references it as
        // BV 1, never capturing the new binder.
        let connection = open();
        let hol = connection.view();
        let star = hol.kind(KindNode::Star).expect("star");
        let tyvar = hol.ty(TyNode::Bv(0)).expect("tyvar");
        let kinds = hol.kinds(&[star]).expect("kinds");
        let vars = hol.vars(&[tyvar]).expect("vars");
        let body = hol.tm(TmNode::Bv(0)).expect("bv0");
        let tylam = hol.tm(TmNode::TyLam(star, body)).expect("tylam");
        let synthesized = hol.type_of(kinds, vars, tylam).expect("synthesize");
        let lifted = hol.ty(TyNode::Bv(1)).expect("lifted var");
        let expected = hol.ty(TyNode::All(star, lifted)).expect("universal");
        assert_eq!(synthesized, expected);
    }

    #[test]
    fn type_application_opens_the_universal_body() {
        // (TYLAM *. lam (BV0) BV0)[bool] : bool -> bool.
        let connection = open();
        let hol = connection.view();
        let star = hol.kind(KindNode::Star).expect("star");
        let tyvar = hol.ty(TyNode::Bv(0)).expect("tyvar");
        let inner = hol.tm(TmNode::Bv(0)).expect("bv0");
        let lam = hol.tm(TmNode::Lam(tyvar, inner)).expect("polymorphic id");
        let tylam = hol.tm(TmNode::TyLam(star, lam)).expect("tylam");
        let bool_ty = hol.ty(TyNode::Bool).expect("bool");
        let applied = hol.tm(TmNode::TyApp(tylam, bool_ty)).expect("tyapp");
        let synthesized = hol
            .type_of(hol.empty_kinds(), hol.empty_vars(), applied)
            .expect("synthesize");
        let expected = hol.ty(TyNode::Arr(bool_ty, bool_ty)).expect("arrow");
        assert_eq!(synthesized, expected);
    }

    #[test]
    fn subtype_predicates_type_in_their_own_context() {
        // abs (BV0) true : sub bool (BV0); rep round-trips to bool.
        let connection = open();
        let hol = connection.view();
        let predicate = hol.tm(TmNode::Bv(0)).expect("pred");
        let truth = hol.tm(TmNode::Bool(true)).expect("true");
        let abs = hol.tm(TmNode::Abs(predicate, truth)).expect("abs");
        let bool_ty = hol.ty(TyNode::Bool).expect("bool");
        let sub = hol.ty(TyNode::Sub(bool_ty, predicate)).expect("sub");
        let synthesized = hol
            .type_of(hol.empty_kinds(), hol.empty_vars(), abs)
            .expect("synthesize abs");
        assert_eq!(synthesized, sub);

        let rep = hol.tm(TmNode::Rep(predicate, abs)).expect("rep");
        let back = hol
            .type_of(hol.empty_kinds(), hol.empty_vars(), rep)
            .expect("synthesize rep");
        assert_eq!(back, bool_ty);
    }
}
