//! Direct CBOR-value encoding for checked surface syntax.
//!
//! Every node is a definite array `[tag, fields..]`. Child expressions are
//! nested CBOR values. A type's final field is its kind; a term's final field
//! is its type, except where that annotation is already an unambiguous field
//! (`TM_EPS`, `TM_REP`, `TM_CAST`, and free variables). `TM_EQ` contains only its two
//! operands and Boolean result type: the checked constructor derives the
//! operand type and verifies that both sides agree.
//!
//! Decoding is intentionally concrete and auditable. It destructures a CBOR
//! [`Value`], recursively decodes children, then calls only checked [`Repr`]
//! methods. It never inserts an unchecked [`Expr`] directly.

use std::error::Error;
use std::fmt::{self, Display, Formatter};

use covalence_lib_cbor::Value;
use covalence_lib_hash::O256;

use crate::{
    BuildError, Bv, Expr, Format, Kind, Repr, SurfaceTag, Tm, TrustedRepr, Ty, TypeVariable,
    Variable,
};

const MAX_DEPTH: usize = 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    ExpectedArray,
    ExpectedInteger,
    ExpectedBool,
    ExpectedText,
    ExpectedBytes,
    WrongArity {
        tag: u64,
        expected: usize,
        actual: usize,
    },
    UnknownTag(u64),
    UnexpectedTag {
        expected: &'static str,
        actual: SurfaceTag,
    },
    InvalidHashLength(usize),
    UnknownFormat(u64),
    AnnotationMismatch,
    DepthLimit,
    Build(BuildError),
}

impl Display for DecodeError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "invalid HolE CBOR value: {self:?}")
    }
}

impl Error for DecodeError {}

impl From<BuildError> for DecodeError {
    fn from(error: BuildError) -> Self {
        Self::Build(error)
    }
}

#[must_use]
pub fn kind_to_value<R: TrustedRepr>(repr: &R, value: &Kind<R>) -> Value {
    encode_kind(repr, value)
}

/// Decodes a checked kind from a CBOR value.
///
/// # Errors
/// Returns an error for malformed data, an invalid constructor, or excessive nesting.
pub fn kind_from_value<R: TrustedRepr>(repr: &mut R, value: Value) -> Result<Kind<R>, DecodeError> {
    decode_kind(repr, value, 0)
}

#[must_use]
pub fn ty_to_value<R: TrustedRepr>(repr: &R, value: &Ty<R>) -> Value {
    encode_ty(repr, value)
}

/// Decodes a checked type from a CBOR value.
///
/// # Errors
/// Returns an error for malformed data, an invalid constructor, or excessive nesting.
pub fn ty_from_value<R: TrustedRepr>(repr: &mut R, value: Value) -> Result<Ty<R>, DecodeError> {
    decode_ty(repr, value, 0)
}

#[must_use]
pub fn tm_to_value<R: TrustedRepr>(repr: &R, value: &Tm<R>) -> Value {
    encode_tm(repr, value)
}

/// Decodes a checked term from a CBOR value.
///
/// # Errors
/// Returns an error for malformed data, an ill-typed constructor, or excessive nesting.
pub fn tm_from_value<R: TrustedRepr>(repr: &mut R, value: Value) -> Result<Tm<R>, DecodeError> {
    decode_tm(repr, value, 0)
}

fn tagged(tag: SurfaceTag, children: impl IntoIterator<Item = Value>) -> Value {
    let mut values = vec![Value::from(u64::from(tag))];
    values.extend(children);
    Value::Array(values)
}

fn encode_kind<R: TrustedRepr>(repr: &R, value: &Kind<R>) -> Value {
    match repr.expr(value.index()) {
        Expr::KindStar(_) => tagged(SurfaceTag::KindStar, []),
        Expr::KindArr(value) => tagged(
            SurfaceTag::KindArr,
            [
                encode_kind(repr, value.domain()),
                encode_kind(repr, value.codomain()),
            ],
        ),
        _ => unreachable!("Kind points to a non-kind expression"),
    }
}

fn encode_ty<R: TrustedRepr>(repr: &R, value: &Ty<R>) -> Value {
    let kind = || encode_kind(repr, value.kind());
    match repr.expr(value.index()) {
        Expr::TyBool(_) => tagged(SurfaceTag::TyBool, [kind()]),
        Expr::TyArr(x) => tagged(
            SurfaceTag::TyArr,
            [
                encode_ty(repr, x.domain()),
                encode_ty(repr, x.codomain()),
                kind(),
            ],
        ),
        Expr::TyApp(x) => tagged(
            SurfaceTag::TyApp,
            [
                encode_ty(repr, x.function()),
                encode_ty(repr, x.argument()),
                kind(),
            ],
        ),
        Expr::TyLam(x) => tagged(
            SurfaceTag::TyLam,
            [
                encode_kind(repr, x.domain()),
                encode_ty(repr, x.body()),
                kind(),
            ],
        ),
        Expr::TyBv(x) => tagged(
            SurfaceTag::TyBv,
            [Value::from(x.variable().index.index()), kind()],
        ),
        Expr::TySub(x) => tagged(
            SurfaceTag::TySub,
            [
                encode_ty(repr, x.carrier()),
                encode_tm(repr, x.predicate()),
                kind(),
            ],
        ),
        Expr::TyModel(x) => tagged(
            SurfaceTag::TyModel,
            [encode_tm(repr, x.predicate()), kind()],
        ),
        Expr::TyLink(x) => tagged(
            SurfaceTag::TyLink,
            [
                Value::Bytes(x.source().into_bytes().to_vec()),
                Value::from(x.format() as u8),
                kind(),
            ],
        ),
        _ => unreachable!("Ty points to a non-type expression"),
    }
}

fn encode_tm<R: TrustedRepr>(repr: &R, value: &Tm<R>) -> Value {
    let ty = || encode_ty(repr, value.ty());
    match repr.expr(value.index()) {
        Expr::TyExists(x) => tagged(SurfaceTag::TyExists, [encode_tm(repr, x.predicate()), ty()]),
        Expr::TmBv(x) => tagged(SurfaceTag::TmBv, [Value::from(x.index().index()), ty()]),
        Expr::TmFv(x) => tagged(
            SurfaceTag::TmFv,
            [Value::Text(repr.name_str(&x.variable().name).into()), ty()],
        ),
        Expr::TmApp(x) => tagged(
            SurfaceTag::TmApp,
            [
                encode_tm(repr, x.function()),
                encode_tm(repr, x.argument()),
                ty(),
            ],
        ),
        Expr::TmLam(x) => tagged(
            SurfaceTag::TmLam,
            [encode_ty(repr, x.domain()), encode_tm(repr, x.body()), ty()],
        ),
        Expr::TmBool(x) => tagged(SurfaceTag::TmBool, [Value::Bool(x.value()), ty()]),
        Expr::TmEq(x) => tagged(
            SurfaceTag::TmEq,
            [encode_tm(repr, x.left()), encode_tm(repr, x.right()), ty()],
        ),
        Expr::TmEps(x) => tagged(
            SurfaceTag::TmEps,
            [encode_ty(repr, x.ty()), encode_tm(repr, x.predicate())],
        ),
        Expr::TmAbs(x) => tagged(
            SurfaceTag::TmAbs,
            [
                encode_ty(repr, x.carrier()),
                encode_tm(repr, x.predicate()),
                encode_tm(repr, x.value()),
                ty(),
            ],
        ),
        Expr::TmRep(x) => tagged(
            SurfaceTag::TmRep,
            [
                encode_ty(repr, x.carrier()),
                encode_tm(repr, x.predicate()),
                encode_tm(repr, x.value()),
            ],
        ),
        Expr::TmLink(x) => tagged(
            SurfaceTag::TmLink,
            [
                Value::Bytes(x.source().into_bytes().to_vec()),
                Value::from(x.format() as u8),
                ty(),
            ],
        ),
        Expr::TmCast(x) => tagged(
            SurfaceTag::TmCast,
            [encode_tm(repr, x.value()), encode_ty(repr, x.target())],
        ),
        _ => unreachable!("Tm points to a non-term expression"),
    }
}

fn split(value: Value, depth: usize) -> Result<(SurfaceTag, Vec<Value>), DecodeError> {
    if depth >= MAX_DEPTH {
        return Err(DecodeError::DepthLimit);
    }
    let Value::Array(mut values) = value else {
        return Err(DecodeError::ExpectedArray);
    };
    if values.is_empty() {
        return Err(DecodeError::ExpectedInteger);
    }
    let tag_value = values.remove(0);
    let Value::Integer(integer) = tag_value else {
        return Err(DecodeError::ExpectedInteger);
    };
    let id: u64 = integer
        .try_into()
        .map_err(|_| DecodeError::ExpectedInteger)?;
    let tag = SurfaceTag::try_from(id).map_err(|_| DecodeError::UnknownTag(id))?;
    Ok((tag, values))
}

fn exact<const N: usize>(tag: SurfaceTag, values: Vec<Value>) -> Result<[Value; N], DecodeError> {
    let actual = values.len();
    values.try_into().map_err(|_| DecodeError::WrongArity {
        tag: tag.into(),
        expected: N,
        actual,
    })
}

fn uint(value: &Value) -> Result<u64, DecodeError> {
    let Value::Integer(value) = value else {
        return Err(DecodeError::ExpectedInteger);
    };
    (*value)
        .try_into()
        .map_err(|_| DecodeError::ExpectedInteger)
}

fn format(value: &Value) -> Result<Format, DecodeError> {
    match uint(value)? {
        0 => Ok(Format::Blob),
        1 => Ok(Format::CborTree),
        value => Err(DecodeError::UnknownFormat(value)),
    }
}

fn source(value: Value) -> Result<O256, DecodeError> {
    let Value::Bytes(value) = value else {
        return Err(DecodeError::ExpectedBytes);
    };
    let actual = value.len();
    let bytes: [u8; 32] = value
        .try_into()
        .map_err(|_| DecodeError::InvalidHashLength(actual))?;
    Ok(O256::from_array(bytes))
}

fn same<R: Repr>(repr: &R, left: &R::Ix, right: &R::Ix) -> Result<(), DecodeError> {
    if repr.ix_eq(left, right) {
        Ok(())
    } else {
        Err(DecodeError::AnnotationMismatch)
    }
}

fn same_ty<R: Repr>(repr: &R, left: &Ty<R>, right: &Ty<R>) -> Result<(), DecodeError> {
    if repr.ty_eq(left, right) {
        Ok(())
    } else {
        Err(DecodeError::AnnotationMismatch)
    }
}

fn decode_kind<R: TrustedRepr>(
    repr: &mut R,
    value: Value,
    depth: usize,
) -> Result<Kind<R>, DecodeError> {
    let (tag, values) = split(value, depth)?;
    match tag {
        SurfaceTag::KindStar => {
            let [] = exact::<0>(tag, values)?;
            Ok(repr.kind_star())
        }
        SurfaceTag::KindArr => {
            let [domain, codomain] = exact(tag, values)?;
            let domain = decode_kind(repr, domain, depth + 1)?;
            let codomain = decode_kind(repr, codomain, depth + 1)?;
            Ok(repr.kind_arr(domain, codomain))
        }
        actual => Err(DecodeError::UnexpectedTag {
            expected: "kind",
            actual,
        }),
    }
}

fn decode_ty<R: TrustedRepr>(
    repr: &mut R,
    value: Value,
    depth: usize,
) -> Result<Ty<R>, DecodeError> {
    let (tag, values) = split(value, depth)?;
    let result = match tag {
        SurfaceTag::TyBool => {
            let [kind] = exact(tag, values)?;
            let kind = decode_kind(repr, kind, depth + 1)?;
            repr.ty_bool(kind)?
        }
        SurfaceTag::TyArr => {
            let [a, b, annotation] = exact(tag, values)?;
            let a = decode_ty(repr, a, depth + 1)?;
            let b = decode_ty(repr, b, depth + 1)?;
            let annotation = decode_kind(repr, annotation, depth + 1)?;
            let result = repr.ty_arr(a, b)?;
            same(repr, result.kind().index(), annotation.index())?;
            result
        }
        SurfaceTag::TyApp => {
            let [f, a, annotation] = exact(tag, values)?;
            let f = decode_ty(repr, f, depth + 1)?;
            let a = decode_ty(repr, a, depth + 1)?;
            let annotation = decode_kind(repr, annotation, depth + 1)?;
            let result = repr.ty_app(f, a)?;
            same(repr, result.kind().index(), annotation.index())?;
            result
        }
        SurfaceTag::TyLam => {
            let [domain, body, annotation] = exact(tag, values)?;
            let domain = decode_kind(repr, domain, depth + 1)?;
            let body = decode_ty(repr, body, depth + 1)?;
            let annotation = decode_kind(repr, annotation, depth + 1)?;
            let result = repr.ty_lam(domain, body)?;
            same(repr, result.kind().index(), annotation.index())?;
            result
        }
        SurfaceTag::TyBv => {
            let [index, kind] = exact(tag, values)?;
            let kind = decode_kind(repr, kind, depth + 1)?;
            repr.ty_bv(TypeVariable {
                index: Bv::new(uint(&index)?),
                kind,
            })
        }
        SurfaceTag::TySub => {
            let [carrier, predicate, annotation] = exact(tag, values)?;
            let carrier = decode_ty(repr, carrier, depth + 1)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            let annotation = decode_kind(repr, annotation, depth + 1)?;
            let result = repr.ty_sub(carrier, predicate)?;
            same(repr, result.kind().index(), annotation.index())?;
            result
        }
        SurfaceTag::TyModel => {
            let [predicate, annotation] = exact(tag, values)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            let annotation = decode_kind(repr, annotation, depth + 1)?;
            repr.ty_model(annotation, predicate)?
        }
        SurfaceTag::TyLink => {
            let [source_value, format_value, kind] = exact(tag, values)?;
            let source = source(source_value)?;
            let format = format(&format_value)?;
            let kind = decode_kind(repr, kind, depth + 1)?;
            repr.ty_link(source, format, kind)
        }
        actual => {
            return Err(DecodeError::UnexpectedTag {
                expected: "type",
                actual,
            });
        }
    };
    Ok(result)
}

fn decode_tm<R: TrustedRepr>(
    repr: &mut R,
    value: Value,
    depth: usize,
) -> Result<Tm<R>, DecodeError> {
    let (tag, values) = split(value, depth)?;
    let result = match tag {
        SurfaceTag::TyExists => {
            let [predicate, annotation] = exact(tag, values)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            let annotation = decode_ty(repr, annotation, depth + 1)?;
            repr.ty_exists(annotation, predicate)?
        }
        SurfaceTag::TmBv => {
            let [index, ty] = exact(tag, values)?;
            let index = Bv::new(uint(&index)?);
            let ty = decode_ty(repr, ty, depth + 1)?;
            repr.tm_bv(index, ty)
        }
        SurfaceTag::TmFv => {
            let [name, ty] = exact(tag, values)?;
            let Value::Text(name) = name else {
                return Err(DecodeError::ExpectedText);
            };
            let ty = decode_ty(repr, ty, depth + 1)?;
            let name = repr.name(name);
            repr.tm_fv(Variable { name, ty })
        }
        SurfaceTag::TmApp => {
            let [f, a, annotation] = exact(tag, values)?;
            let f = decode_tm(repr, f, depth + 1)?;
            let a = decode_tm(repr, a, depth + 1)?;
            let annotation = decode_ty(repr, annotation, depth + 1)?;
            repr.tm_app(f, a, annotation)?
        }
        SurfaceTag::TmLam => {
            let [domain, body, annotation] = exact(tag, values)?;
            let domain = decode_ty(repr, domain, depth + 1)?;
            let body = decode_tm(repr, body, depth + 1)?;
            let annotation = decode_ty(repr, annotation, depth + 1)?;
            let result = repr.tm_lam(domain, body)?;
            same_ty(repr, result.ty(), &annotation)?;
            result
        }
        SurfaceTag::TmBool => {
            let [value, ty] = exact(tag, values)?;
            let Value::Bool(value) = value else {
                return Err(DecodeError::ExpectedBool);
            };
            let ty = decode_ty(repr, ty, depth + 1)?;
            repr.tm_bool(ty, value)?
        }
        SurfaceTag::TmEq => {
            let [left, right, ty] = exact(tag, values)?;
            let left = decode_tm(repr, left, depth + 1)?;
            let right = decode_tm(repr, right, depth + 1)?;
            let ty = decode_ty(repr, ty, depth + 1)?;
            repr.tm_eq(ty, left, right)?
        }
        SurfaceTag::TmEps => {
            let [ty, predicate] = exact(tag, values)?;
            let ty = decode_ty(repr, ty, depth + 1)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            repr.tm_eps(ty, predicate)?
        }
        SurfaceTag::TmAbs => {
            let [carrier, predicate, value, annotation] = exact(tag, values)?;
            let carrier = decode_ty(repr, carrier, depth + 1)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            let value = decode_tm(repr, value, depth + 1)?;
            let annotation = decode_ty(repr, annotation, depth + 1)?;
            let result = repr.tm_abs(carrier, predicate, value)?;
            same_ty(repr, result.ty(), &annotation)?;
            result
        }
        SurfaceTag::TmRep => {
            let [carrier, predicate, value] = exact(tag, values)?;
            let carrier = decode_ty(repr, carrier, depth + 1)?;
            let predicate = decode_tm(repr, predicate, depth + 1)?;
            let value = decode_tm(repr, value, depth + 1)?;
            repr.tm_rep(carrier, predicate, value)?
        }
        SurfaceTag::TmLink => {
            let [source_value, format_value, ty] = exact(tag, values)?;
            let source = source(source_value)?;
            let format = format(&format_value)?;
            let ty = decode_ty(repr, ty, depth + 1)?;
            repr.tm_link(source, format, ty)
        }
        SurfaceTag::TmCast => {
            let [value, target] = exact(tag, values)?;
            let value = decode_tm(repr, value, depth + 1)?;
            let target = decode_ty(repr, target, depth + 1)?;
            repr.tm_cast(value, target)
        }
        actual => {
            return Err(DecodeError::UnexpectedTag {
                expected: "term",
                actual,
            });
        }
    };
    Ok(result)
}
