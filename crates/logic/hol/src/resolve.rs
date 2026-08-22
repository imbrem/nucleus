//! Fuel-bounded resolution of raw Ethane rows.

use std::sync::Arc;

use crate::{Arena, Import, ImportId, Link, Ref, Sort, row::Expr};

/// Supplies an arena for a content-addressed link.
///
/// Returning `Ok(None)` means the object is currently unavailable and may be
/// retried later. Resolver failures are not cached by this representation.
pub trait Resolver {
    type Error;

    /// Return the linked arena when it is currently available.
    ///
    /// # Errors
    ///
    /// Returns a resolver-specific error when lookup itself fails. Temporary
    /// absence is represented by `Ok(None)`.
    fn resolve(&self, link: &Link) -> Result<Option<Arc<Arena>>, Self::Error>;
}

/// A resolver suitable for the checked kernel's fixed Lean `Resolver` model.
///
/// A successful lookup is immutable: after `resolve(link)` returns arena
/// `A`, every later successful lookup of the same link must return `A`.
/// Absence and errors may remain retryable.
///
/// Implementations are sealed because violating successful-result stability
/// can invalidate retained checked equality and import witnesses.
#[allow(private_bounds)]
pub trait TrustedResolver: Resolver + trusted_resolver::Sealed {}

pub(crate) mod trusted_resolver {
    pub trait Sealed {}
}

/// A recoverable failure while resolving one row graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolveError<E> {
    FuelExhausted,
    MissingReference(Ref),
    MissingImport(ImportId),
    NullImport(ImportId),
    Unavailable(Link),
    Resolver(E),
    CategoryMismatch { expected: Sort, actual: Sort },
    IllSorted,
    IllTyped,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Kind {
    Star,
    Arr(Box<Self>, Box<Self>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Syntax {
    BoolTy,
    Arr(Box<Self>, Box<Self>),
    TyApp {
        domain: Kind,
        codomain: Kind,
        function: Box<Self>,
        argument: Box<Self>,
    },
    TyLam {
        domain: Kind,
        codomain: Kind,
        name: u64,
        body: Box<Self>,
    },
    TyFv {
        name: u64,
        kind: Kind,
    },
    TyExists {
        name: u64,
        predicate: Box<Self>,
    },
    Model {
        name: u64,
        predicate: Box<Self>,
    },
    TmFv {
        name: u64,
        ty: Box<Self>,
    },
    App(Box<Self>, Box<Self>),
    Lam {
        name: u64,
        domain: Box<Self>,
        body: Box<Self>,
    },
    Bool(bool),
    Eq {
        ty: Box<Self>,
        left: Box<Self>,
        right: Box<Self>,
    },
    Eps {
        ty: Box<Self>,
        predicate: Box<Self>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Value {
    Kind(Kind),
    Ty { kind: Kind, expression: Syntax },
    Tm { ty: Syntax, expression: Syntax },
}

/// Locally nameless image used only by the root-beta checker.
///
/// Type and term binders have independent De Bruijn indices. Constructor
/// annotations recoverable from children are omitted, just as they are from
/// the corresponding Lean `HolE.Expr` constructors.
#[derive(Clone, Debug, Eq, PartialEq)]
enum LoweredSyntax {
    BoolTy,
    Arr(Box<Self>, Box<Self>),
    TyApp(Box<Self>, Box<Self>),
    TyLam(Box<Self>),
    TyBv(usize),
    TyExists(Box<Self>),
    Model(Box<Self>),
    TmFv {
        name: u64,
        ty: Box<Self>,
    },
    TmBv(usize),
    App(Box<Self>, Box<Self>),
    Lam {
        domain: Box<Self>,
        body: Box<Self>,
    },
    Bool(bool),
    Eq {
        ty: Box<Self>,
        left: Box<Self>,
        right: Box<Self>,
    },
    Eps {
        ty: Box<Self>,
        predicate: Box<Self>,
    },
}

impl LoweredSyntax {
    /// Open the term variable at `depth`. The replacement was lowered in the
    /// empty term scope, so it has no free De Bruijn indices to shift.
    fn open_bound(&self, replacement: &Self, depth: usize) -> Self {
        match self {
            Self::TmBv(index) if *index == depth => replacement.clone(),
            Self::TmBv(index) if *index > depth => Self::TmBv(index - 1),
            Self::TmBv(index) => Self::TmBv(*index),
            // Term substitution does not enter types. `tyExists` also stores
            // a term at independent term depth zero, so ambient term
            // substitution leaves its predicate untouched.
            Self::BoolTy
            | Self::Arr(..)
            | Self::TyApp(..)
            | Self::TyLam(..)
            | Self::TyBv(_)
            | Self::TyExists(_)
            | Self::Model(_) => self.clone(),
            Self::TmFv { name, ty } => Self::TmFv {
                name: *name,
                ty: ty.clone(),
            },
            Self::App(function, argument) => Self::App(
                Box::new(function.open_bound(replacement, depth)),
                Box::new(argument.open_bound(replacement, depth)),
            ),
            Self::Lam { domain, body } => Self::Lam {
                domain: domain.clone(),
                body: Box::new(body.open_bound(replacement, depth + 1)),
            },
            Self::Bool(value) => Self::Bool(*value),
            Self::Eq { ty, left, right } => Self::Eq {
                ty: ty.clone(),
                left: Box::new(left.open_bound(replacement, depth)),
                right: Box::new(right.open_bound(replacement, depth)),
            },
            Self::Eps { ty, predicate } => Self::Eps {
                ty: ty.clone(),
                predicate: Box::new(predicate.open_bound(replacement, depth)),
            },
        }
    }
}

impl Value {
    const fn sort(&self) -> Sort {
        match self {
            Self::Kind(_) => Sort::Kind,
            Self::Ty { .. } => Sort::Ty,
            Self::Tm { .. } => Sort::Tm,
        }
    }

    pub(crate) fn is_well_formed(&self) -> bool {
        match self {
            Self::Kind(_) => true,
            Self::Ty { kind, expression } => expression.infer_family(&[]) == Some(kind.clone()),
            Self::Tm { ty, expression } => {
                ty.infer_family(&[]) == Some(Kind::Star)
                    && expression.infer_term(&[]) == Some(ty.clone())
            }
        }
    }

    pub(crate) fn has_sort(&self, classifier: &Self) -> bool {
        match (self, classifier) {
            (Self::Ty { kind: expected, .. }, Self::Kind(actual)) => expected == actual,
            (
                Self::Tm { ty: expected, .. },
                Self::Ty {
                    kind: Kind::Star,
                    expression: actual,
                },
            ) => expected == actual,
            _ => false,
        }
    }

    /// Check one general root beta contraction modulo alpha conversion.
    ///
    /// Both named endpoints are lowered to the same locally nameless form
    /// used by Lean. Opening the lowered body is capture avoiding without a
    /// fresh-name operation in the checked kernel.
    pub(crate) fn is_root_beta_to(&self, target: &Self) -> bool {
        let (
            Self::Tm {
                ty: source_ty,
                expression: Syntax::App(function, argument),
            },
            Self::Tm {
                ty: target_ty,
                expression: target_expression,
            },
        ) = (self, target)
        else {
            return false;
        };
        let Syntax::Lam { name, domain, body } = function.as_ref() else {
            return false;
        };
        if source_ty != target_ty || !self.is_well_formed() {
            return false;
        }

        let mut type_scope = Vec::new();
        if domain.lower_family(&mut type_scope).is_none() {
            return false;
        }
        let mut body_scope = vec![(*name, domain.as_ref().clone())];
        let Some(lowered_body) = body.lower_term(&mut type_scope, &mut body_scope) else {
            return false;
        };
        let mut argument_scope = Vec::new();
        let Some(lowered_argument) = argument.lower_term(&mut type_scope, &mut argument_scope)
        else {
            return false;
        };
        let mut target_scope = Vec::new();
        let Some(lowered_target) = target_expression.lower_term(&mut type_scope, &mut target_scope)
        else {
            return false;
        };
        lowered_target == lowered_body.open_bound(&lowered_argument, 0)
    }
}

impl Syntax {
    /// Lower a named family exactly as `HolE.Named.lowerFam` does.
    fn lower_family(&self, scope: &mut Vec<(u64, Kind)>) -> Option<LoweredSyntax> {
        Some(match self {
            Self::BoolTy => LoweredSyntax::BoolTy,
            Self::Arr(domain, codomain) => LoweredSyntax::Arr(
                Box::new(domain.lower_family(scope)?),
                Box::new(codomain.lower_family(scope)?),
            ),
            Self::TyApp {
                function, argument, ..
            } => LoweredSyntax::TyApp(
                Box::new(function.lower_family(scope)?),
                Box::new(argument.lower_family(scope)?),
            ),
            Self::TyLam {
                domain, name, body, ..
            } => {
                scope.push((*name, domain.clone()));
                let lowered = body.lower_family(scope);
                scope.pop();
                LoweredSyntax::TyLam(Box::new(lowered?))
            }
            Self::TyFv { name, kind } => {
                let index = scope
                    .iter()
                    .rev()
                    .position(|entry| entry == &(*name, kind.clone()))?;
                LoweredSyntax::TyBv(index)
            }
            Self::Model { name, predicate } => {
                scope.push((*name, Kind::Star));
                let mut term_scope = Vec::new();
                let lowered = predicate.lower_term(scope, &mut term_scope);
                scope.pop();
                LoweredSyntax::Model(Box::new(lowered?))
            }
            Self::TyExists { .. }
            | Self::TmFv { .. }
            | Self::App(..)
            | Self::Lam { .. }
            | Self::Bool(_)
            | Self::Eq { .. }
            | Self::Eps { .. } => return None,
        })
    }

    /// Lower a named term exactly as `HolE.Named.lowerTm` does.
    fn lower_term(
        &self,
        type_scope: &mut Vec<(u64, Kind)>,
        term_scope: &mut Vec<(u64, Syntax)>,
    ) -> Option<LoweredSyntax> {
        Some(match self {
            Self::TyExists { name, predicate } => {
                type_scope.push((*name, Kind::Star));
                let mut reset_term_scope = Vec::new();
                let lowered = predicate.lower_term(type_scope, &mut reset_term_scope);
                type_scope.pop();
                LoweredSyntax::TyExists(Box::new(lowered?))
            }
            Self::TmFv { name, ty } => {
                if let Some(index) = term_scope
                    .iter()
                    .rev()
                    .position(|entry| entry == &(*name, ty.as_ref().clone()))
                {
                    LoweredSyntax::TmBv(index)
                } else {
                    LoweredSyntax::TmFv {
                        name: *name,
                        ty: Box::new(ty.lower_family(type_scope)?),
                    }
                }
            }
            Self::App(function, argument) => LoweredSyntax::App(
                Box::new(function.lower_term(type_scope, term_scope)?),
                Box::new(argument.lower_term(type_scope, term_scope)?),
            ),
            Self::Lam { name, domain, body } => {
                let lowered_domain = domain.lower_family(type_scope)?;
                term_scope.push((*name, domain.as_ref().clone()));
                let lowered_body = body.lower_term(type_scope, term_scope);
                term_scope.pop();
                LoweredSyntax::Lam {
                    domain: Box::new(lowered_domain),
                    body: Box::new(lowered_body?),
                }
            }
            Self::Bool(value) => LoweredSyntax::Bool(*value),
            Self::Eq { ty, left, right } => LoweredSyntax::Eq {
                ty: Box::new(ty.lower_family(type_scope)?),
                left: Box::new(left.lower_term(type_scope, term_scope)?),
                right: Box::new(right.lower_term(type_scope, term_scope)?),
            },
            Self::Eps { ty, predicate } => LoweredSyntax::Eps {
                ty: Box::new(ty.lower_family(type_scope)?),
                predicate: Box::new(predicate.lower_term(type_scope, term_scope)?),
            },
            Self::BoolTy
            | Self::Arr(..)
            | Self::TyApp { .. }
            | Self::TyLam { .. }
            | Self::TyFv { .. }
            | Self::Model { .. } => return None,
        })
    }

    // Mirrors `OneBased.inferNamedFam`. A type variable is kinded exactly when
    // its syntactic (name, kind) pair is bound by an enclosing type constructor.
    fn infer_family(&self, scope: &[(u64, Kind)]) -> Option<Kind> {
        Some(match self {
            Self::BoolTy => Kind::Star,
            Self::Arr(domain, codomain) => {
                if domain.infer_family(scope)? != Kind::Star
                    || codomain.infer_family(scope)? != Kind::Star
                {
                    return None;
                }
                Kind::Star
            }
            Self::TyApp {
                domain,
                codomain,
                function,
                argument,
            } => {
                let expected = Kind::Arr(Box::new(domain.clone()), Box::new(codomain.clone()));
                if function.infer_family(scope)? != expected
                    || argument.infer_family(scope)? != *domain
                {
                    return None;
                }
                codomain.clone()
            }
            Self::TyLam {
                domain,
                codomain,
                name,
                body,
            } => {
                let mut extended = scope.to_vec();
                extended.push((*name, domain.clone()));
                if body.infer_family(&extended)? != *codomain {
                    return None;
                }
                Kind::Arr(Box::new(domain.clone()), Box::new(codomain.clone()))
            }
            Self::TyFv { name, kind } => {
                if !scope
                    .iter()
                    .rev()
                    .any(|bound| bound == &(*name, kind.clone()))
                {
                    return None;
                }
                kind.clone()
            }
            Self::Model { name, predicate } => {
                let mut extended = scope.to_vec();
                extended.push((*name, Kind::Star));
                if predicate.infer_term(&extended)? != Self::BoolTy {
                    return None;
                }
                Kind::Star
            }
            Self::TyExists { .. }
            | Self::TmFv { .. }
            | Self::App(..)
            | Self::Lam { .. }
            | Self::Bool(_)
            | Self::Eq { .. }
            | Self::Eps { .. } => return None,
        })
    }

    // Mirrors `OneBased.inferNamedTm`. Term binders need no separate environment:
    // exact (name, type) capture preserves the type already carried by a free
    // variable occurrence.
    fn infer_term(&self, scope: &[(u64, Kind)]) -> Option<Self> {
        Some(match self {
            Self::TyExists { name, predicate } => {
                let mut extended = scope.to_vec();
                extended.push((*name, Kind::Star));
                if predicate.infer_term(&extended)? != Self::BoolTy {
                    return None;
                }
                Self::BoolTy
            }
            Self::TmFv { ty, .. } => {
                if ty.infer_family(scope)? != Kind::Star {
                    return None;
                }
                ty.as_ref().clone()
            }
            Self::App(function, argument) => {
                let Self::Arr(domain, codomain) = function.infer_term(scope)? else {
                    return None;
                };
                if argument.infer_term(scope)? != *domain {
                    return None;
                }
                *codomain
            }
            Self::Lam { domain, body, .. } => {
                if domain.infer_family(scope)? != Kind::Star {
                    return None;
                }
                let codomain = body.infer_term(scope)?;
                Self::Arr(domain.clone(), Box::new(codomain))
            }
            Self::Bool(_) => Self::BoolTy,
            Self::Eq {
                ty, left, right, ..
            } => {
                if ty.infer_family(scope)? != Kind::Star
                    || left.infer_term(scope)? != **ty
                    || right.infer_term(scope)? != **ty
                {
                    return None;
                }
                Self::BoolTy
            }
            Self::Eps { ty, predicate } => {
                if ty.infer_family(scope)? != Kind::Star
                    || predicate.infer_term(scope)? != Self::Arr(ty.clone(), Box::new(Self::BoolTy))
                {
                    return None;
                }
                ty.as_ref().clone()
            }
            Self::BoolTy
            | Self::Arr(..)
            | Self::TyApp { .. }
            | Self::TyLam { .. }
            | Self::TyFv { .. }
            | Self::Model { .. } => return None,
        })
    }
}

impl Arena {
    /// Resolve and classify one local reference.
    ///
    /// Every local or imported edge consumes one unit of fuel. This prevents
    /// cycles from becoming an unrecoverable failure.
    ///
    /// # Errors
    ///
    /// Returns a precise, retryable resolution error for unavailable imports,
    /// bad references, category mismatches, ill-sorted rows, or fuel exhaustion.
    pub fn resolve_sort<R: Resolver>(
        &self,
        resolver: &R,
        reference: Ref,
        fuel: usize,
    ) -> Result<Sort, ResolveError<R::Error>> {
        resolve_at(self, resolver, reference, fuel).map(|value| value.sort())
    }

    /// Resolve one row and run the logical kind/type checker.
    ///
    /// This is the Rust implementation of `OneBased.Value.rustCheck`; its Lean
    /// soundness theorem is `OneBased.Value.rustCheck_sound`.
    ///
    /// # Errors
    ///
    /// Returns `IllTyped` when resolution succeeds but the value is not closed
    /// and well formed in the empty binder scopes.
    pub fn check_wf<R: Resolver>(
        &self,
        resolver: &R,
        reference: Ref,
        fuel: usize,
    ) -> Result<Sort, ResolveError<R::Error>> {
        let value = resolve_at(self, resolver, reference, fuel)?;
        if value.is_well_formed() {
            Ok(value.sort())
        } else {
            Err(ResolveError::IllTyped)
        }
    }
}

pub(crate) fn resolve_at<R: Resolver>(
    arena: &Arena,
    resolver: &R,
    reference: Ref,
    fuel: usize,
) -> Result<Value, ResolveError<R::Error>> {
    let remaining = fuel.checked_sub(1).ok_or(ResolveError::FuelExhausted)?;
    let row = arena
        .row(reference)
        .ok_or(ResolveError::MissingReference(reference))?;

    let local = |child| resolve_at(arena, resolver, child, remaining);
    let foreign = |source: ImportId, foreign: Ref| {
        let entry = arena
            .import(source)
            .ok_or(ResolveError::MissingImport(source))?;
        match entry {
            Import::Null => Err(ResolveError::NullImport(source)),
            Import::Literal(imported) => resolve_at(imported, resolver, foreign, remaining),
            Import::Link(link) => {
                let imported = resolver
                    .resolve(link)
                    .map_err(ResolveError::Resolver)?
                    .ok_or(ResolveError::Unavailable(*link))?;
                resolve_at(&imported, resolver, foreign, remaining)
            }
        }
    };

    elaborate(row.expr(), local, foreign)
}

fn expect_kind<E>(value: Value) -> Result<Kind, ResolveError<E>> {
    match value {
        Value::Kind(kind) => Ok(kind),
        value => Err(ResolveError::CategoryMismatch {
            expected: Sort::Kind,
            actual: value.sort(),
        }),
    }
}

fn expect_ty<E>(value: Value) -> Result<(Kind, Syntax), ResolveError<E>> {
    match value {
        Value::Ty { kind, expression } => Ok((kind, expression)),
        value => Err(ResolveError::CategoryMismatch {
            expected: Sort::Ty,
            actual: value.sort(),
        }),
    }
}

fn expect_tm<E>(value: Value) -> Result<(Syntax, Syntax), ResolveError<E>> {
    match value {
        Value::Tm { ty, expression } => Ok((ty, expression)),
        value => Err(ResolveError::CategoryMismatch {
            expected: Sort::Tm,
            actual: value.sort(),
        }),
    }
}

// Keeping the constructor table together makes its correspondence with
// `OneBased.elaborateExpr` directly auditable.
#[allow(clippy::too_many_lines)]
fn elaborate<E>(
    expression: &Expr,
    mut local: impl FnMut(Ref) -> Result<Value, ResolveError<E>>,
    mut foreign: impl FnMut(ImportId, Ref) -> Result<Value, ResolveError<E>>,
) -> Result<Value, ResolveError<E>> {
    Ok(match *expression {
        Expr::KindStar => Value::Kind(Kind::Star),
        Expr::KindArr(domain, codomain) => Value::Kind(Kind::Arr(
            Box::new(expect_kind(local(domain)?)?),
            Box::new(expect_kind(local(codomain)?)?),
        )),
        Expr::BoolTy => Value::Ty {
            kind: Kind::Star,
            expression: Syntax::BoolTy,
        },
        Expr::TyArr(domain, codomain) => {
            let (domain_kind, domain) = expect_ty(local(domain)?)?;
            let (codomain_kind, codomain) = expect_ty(local(codomain)?)?;
            if domain_kind != Kind::Star || codomain_kind != Kind::Star {
                return Err(ResolveError::IllSorted);
            }
            Value::Ty {
                kind: Kind::Star,
                expression: Syntax::Arr(Box::new(domain), Box::new(codomain)),
            }
        }
        Expr::TyApp(function, argument) => {
            let (function_kind, function) = expect_ty(local(function)?)?;
            let (argument_kind, argument) = expect_ty(local(argument)?)?;
            let Kind::Arr(domain, codomain) = function_kind else {
                return Err(ResolveError::IllSorted);
            };
            if argument_kind != *domain {
                return Err(ResolveError::IllSorted);
            }
            Value::Ty {
                kind: (*codomain).clone(),
                expression: Syntax::TyApp {
                    domain: *domain,
                    codomain: *codomain,
                    function: Box::new(function),
                    argument: Box::new(argument),
                },
            }
        }
        Expr::TyLam(binder, body) => {
            let (domain, binder) = expect_ty(local(binder)?)?;
            let Syntax::TyFv { name, kind } = binder else {
                return Err(ResolveError::IllSorted);
            };
            if kind != domain {
                return Err(ResolveError::IllSorted);
            }
            let (codomain, body) = expect_ty(local(body)?)?;
            Value::Ty {
                kind: Kind::Arr(Box::new(domain.clone()), Box::new(codomain.clone())),
                expression: Syntax::TyLam {
                    domain,
                    codomain,
                    name,
                    body: Box::new(body),
                },
            }
        }
        Expr::TyFv { name, kind } => {
            let kind = expect_kind(local(kind)?)?;
            Value::Ty {
                kind: kind.clone(),
                expression: Syntax::TyFv { name, kind },
            }
        }
        Expr::TyExists { name, predicate } => {
            let (ty, predicate) = expect_tm(local(predicate)?)?;
            if ty != Syntax::BoolTy {
                return Err(ResolveError::IllSorted);
            }
            Value::Tm {
                ty: Syntax::BoolTy,
                expression: Syntax::TyExists {
                    name,
                    predicate: Box::new(predicate),
                },
            }
        }
        Expr::Model { name, predicate } => {
            let (ty, predicate) = expect_tm(local(predicate)?)?;
            if ty != Syntax::BoolTy {
                return Err(ResolveError::IllSorted);
            }
            Value::Ty {
                kind: Kind::Star,
                expression: Syntax::Model {
                    name,
                    predicate: Box::new(predicate),
                },
            }
        }
        Expr::TmFv { name, ty } => {
            let (kind, ty) = expect_ty(local(ty)?)?;
            if kind != Kind::Star {
                return Err(ResolveError::IllSorted);
            }
            Value::Tm {
                ty: ty.clone(),
                expression: Syntax::TmFv {
                    name,
                    ty: Box::new(ty),
                },
            }
        }
        Expr::App(function, argument) => {
            let (function_ty, function) = expect_tm(local(function)?)?;
            let (argument_ty, argument) = expect_tm(local(argument)?)?;
            let Syntax::Arr(domain, codomain) = function_ty else {
                return Err(ResolveError::IllSorted);
            };
            if argument_ty != *domain {
                return Err(ResolveError::IllSorted);
            }
            Value::Tm {
                ty: (*codomain).clone(),
                expression: Syntax::App(Box::new(function), Box::new(argument)),
            }
        }
        Expr::Lam(binder, body) => {
            let (domain, binder) = expect_tm(local(binder)?)?;
            let Syntax::TmFv { name, ty } = binder else {
                return Err(ResolveError::IllSorted);
            };
            if *ty != domain {
                return Err(ResolveError::IllSorted);
            }
            let (codomain, body) = expect_tm(local(body)?)?;
            Value::Tm {
                ty: Syntax::Arr(Box::new(domain.clone()), Box::new(codomain)),
                expression: Syntax::Lam {
                    name,
                    domain: Box::new(domain),
                    body: Box::new(body),
                },
            }
        }
        Expr::Bool(value) => Value::Tm {
            ty: Syntax::BoolTy,
            expression: Syntax::Bool(value),
        },
        Expr::Eq(left, right) => {
            let (ty, left) = expect_tm(local(left)?)?;
            let (actual, right) = expect_tm(local(right)?)?;
            if actual != ty {
                return Err(ResolveError::IllSorted);
            }
            Value::Tm {
                ty: Syntax::BoolTy,
                expression: Syntax::Eq {
                    ty: Box::new(ty),
                    left: Box::new(left),
                    right: Box::new(right),
                },
            }
        }
        Expr::Eps { ty, predicate } => {
            let (kind, ty) = expect_ty(local(ty)?)?;
            let (predicate_ty, predicate) = expect_tm(local(predicate)?)?;
            if kind != Kind::Star {
                return Err(ResolveError::IllSorted);
            }
            let Syntax::Arr(domain, codomain) = predicate_ty else {
                return Err(ResolveError::IllSorted);
            };
            if *domain != ty || *codomain != Syntax::BoolTy {
                return Err(ResolveError::IllSorted);
            }
            Value::Tm {
                ty: ty.clone(),
                expression: Syntax::Eps {
                    ty: Box::new(ty),
                    predicate: Box::new(predicate),
                },
            }
        }
        Expr::TmRef { src, ix } => {
            let value = foreign(src, ix)?;
            if value.sort() != Sort::Tm {
                return Err(ResolveError::CategoryMismatch {
                    expected: Sort::Tm,
                    actual: value.sort(),
                });
            }
            value
        }
        Expr::TyRef { src, ix } => {
            let value = foreign(src, ix)?;
            if value.sort() != Sort::Ty {
                return Err(ResolveError::CategoryMismatch {
                    expected: Sort::Ty,
                    actual: value.sort(),
                });
            }
            value
        }
        Expr::KindRef { src, ix } => {
            let value = foreign(src, ix)?;
            if value.sort() != Sort::Kind {
                return Err(ResolveError::CategoryMismatch {
                    expected: Sort::Kind,
                    actual: value.sort(),
                });
            }
            value
        }
    })
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use covalence_lib_hash::O256;

    use super::*;
    use crate::{LinkFormat, row::Row};

    const fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    const fn import(value: u64) -> ImportId {
        ImportId::new(value).unwrap()
    }

    struct NoLinks;

    impl Resolver for NoLinks {
        type Error = Infallible;

        fn resolve(&self, _: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
            Ok(None)
        }
    }

    #[test]
    fn implicit_lambda_application_and_equality_annotations_are_recovered() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                Row::new(Expr::BoolTy),
                Row::new(Expr::TmFv {
                    name: 7,
                    ty: reference(1),
                }),
                Row::new(Expr::Lam(reference(2), reference(2))),
                Row::new(Expr::Bool(true)),
                Row::new(Expr::App(reference(3), reference(4))),
                Row::new(Expr::Eq(reference(5), reference(4))),
            ],
            [],
            vec![],
            vec![],
        );

        assert_eq!(arena.resolve_sort(&NoLinks, reference(3), 4), Ok(Sort::Tm));
        assert_eq!(arena.resolve_sort(&NoLinks, reference(5), 5), Ok(Sort::Tm));
        assert_eq!(arena.resolve_sort(&NoLinks, reference(6), 6), Ok(Sort::Tm));
        assert_eq!(arena.check_wf(&NoLinks, reference(3), 4), Ok(Sort::Tm));
        assert_eq!(arena.check_wf(&NoLinks, reference(5), 5), Ok(Sort::Tm));
        assert_eq!(arena.check_wf(&NoLinks, reference(6), 6), Ok(Sort::Tm));
    }

    #[test]
    fn implicit_type_application_and_lambda_kinds_are_recovered() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                Row::new(Expr::KindStar),
                Row::new(Expr::TyFv {
                    name: 3,
                    kind: reference(1),
                }),
                Row::new(Expr::TyLam(reference(2), reference(2))),
                Row::new(Expr::BoolTy),
                Row::new(Expr::TyApp(reference(3), reference(4))),
            ],
            [],
            vec![],
            vec![],
        );

        assert_eq!(arena.resolve_sort(&NoLinks, reference(3), 4), Ok(Sort::Ty));
        assert_eq!(arena.resolve_sort(&NoLinks, reference(5), 5), Ok(Sort::Ty));
        assert_eq!(arena.check_wf(&NoLinks, reference(3), 4), Ok(Sort::Ty));
        assert_eq!(arena.check_wf(&NoLinks, reference(5), 5), Ok(Sort::Ty));
        assert_eq!(
            arena.check_wf(&NoLinks, reference(2), 3),
            Err(ResolveError::IllTyped)
        );
    }

    struct OneLink {
        link: Link,
        arena: Arc<Arena>,
    }

    impl Resolver for OneLink {
        type Error = Infallible;

        fn resolve(&self, link: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
            Ok((link == &self.link).then(|| Arc::clone(&self.arena)))
        }
    }

    #[test]
    fn literal_and_successful_link_imports_resolve_identically() {
        let imported = Arena::from_parts(
            vec![],
            [],
            vec![Row::new(Expr::Bool(true))],
            [],
            vec![],
            vec![],
        );
        let link = Link {
            format: LinkFormat::Cbor,
            blake3: O256::from_array([0x5a; 32]),
        };
        let resolver = OneLink {
            link,
            arena: Arc::new(imported.clone()),
        };
        let literal = Arena::from_parts(
            vec![Import::Literal(Box::new(imported))],
            [],
            vec![Row::new(Expr::TmRef {
                src: import(1),
                ix: reference(1),
            })],
            [],
            vec![],
            vec![],
        );
        let linked = Arena::from_parts(
            vec![Import::Link(link)],
            [],
            vec![Row::new(Expr::TmRef {
                src: import(1),
                ix: reference(1),
            })],
            [],
            vec![],
            vec![],
        );

        assert_eq!(
            literal.resolve_sort(&resolver, reference(1), 3),
            Ok(Sort::Tm)
        );
        assert_eq!(
            linked.resolve_sort(&resolver, reference(1), 3),
            Ok(Sort::Tm)
        );
        assert_eq!(
            linked.resolve_sort(&NoLinks, reference(1), 3),
            Err(ResolveError::Unavailable(link))
        );
    }
}
