//! Canonical array-based CBOR for HOL terms, types, and links.

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io::Cursor;
use std::sync::Arc;

pub use covalence_lib_cbor::Value as CborValue;
use covalence_lib_hash::O256;

use CborValue as Value;

use crate::{
    App, ArcKind, ArcRepr, ArcTm, ArcTy, Bv, Context, Format, Kind, Link, SurfaceTag, Tm, Ty,
    TypeVariable, Variable,
};

const MAX_DEPTH: usize = 1024;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CborError {
    Codec(String),
    NonCanonical,
    TrailingData,
    Expected(&'static str),
    WrongArity { expected: usize, actual: usize },
    UnknownTag(u64),
    UnexpectedTag(SurfaceTag),
    InvalidHashLength(usize),
    UnsupportedFormat(u64),
    NotImplemented(&'static str),
    DepthLimit,
}

impl Display for CborError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Codec(error) => write!(formatter, "CBOR codec error: {error}"),
            Self::NonCanonical => formatter.write_str("CBOR input is not canonical"),
            Self::TrailingData => formatter.write_str("trailing bytes after CBOR object"),
            Self::Expected(expected) => write!(formatter, "expected CBOR {expected}"),
            Self::WrongArity { expected, actual } => {
                write!(formatter, "expected {expected} node fields, found {actual}")
            }
            Self::UnknownTag(tag) => write!(formatter, "unknown HOL surface tag {tag}"),
            Self::UnexpectedTag(tag) => write!(formatter, "unexpected HOL surface tag {tag}"),
            Self::InvalidHashLength(length) => {
                write!(formatter, "link hash must contain 32 bytes, found {length}")
            }
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported link format {format}")
            }
            Self::NotImplemented(feature) => write!(formatter, "{feature} is not implemented"),
            Self::DepthLimit => formatter.write_str("HOL CBOR nesting limit exceeded"),
        }
    }
}

impl Error for CborError {}

/// Conversion between a syntax object and the shared CBOR data model.
///
/// Byte-level framing and canonicality are deliberately separate: syntax
/// formers compose through this interface without depending on an I/O codec.
pub trait CborObject: Sized {
    #[must_use]
    fn encode(&self) -> Value;

    /// # Errors
    ///
    /// Returns an error when `value` is not this object's canonical shape.
    fn decode(value: Value) -> Result<Self, CborError>;
}

fn node(tag: SurfaceTag, fields: impl IntoIterator<Item = Value>) -> Value {
    let mut values = vec![Value::Integer(u64::from(tag).into())];
    values.extend(fields);
    Value::Array(values)
}

fn split_node(value: Value) -> Result<(SurfaceTag, Vec<Value>), CborError> {
    let Value::Array(mut values) = value else {
        return Err(CborError::Expected("array node"));
    };
    if values.is_empty() {
        return Err(CborError::Expected("nonempty array node"));
    }
    let raw = take_u64(&values.remove(0))?;
    let tag = SurfaceTag::try_from(raw).map_err(|_| CborError::UnknownTag(raw))?;
    Ok((tag, values))
}

fn fields<const N: usize>(values: Vec<Value>) -> Result<[Value; N], CborError> {
    let actual = values.len();
    values.try_into().map_err(|_| CborError::WrongArity {
        expected: N,
        actual,
    })
}

fn take_u64(value: &Value) -> Result<u64, CborError> {
    let Value::Integer(integer) = value else {
        return Err(CborError::Expected("unsigned integer"));
    };
    (*integer)
        .try_into()
        .map_err(|_| CborError::Expected("unsigned 64-bit integer"))
}

fn nested(depth: usize) -> Result<usize, CborError> {
    depth
        .checked_add(1)
        .filter(|value| *value <= MAX_DEPTH)
        .ok_or(CborError::DepthLimit)
}

fn encode_value(value: &Value) -> Result<Vec<u8>, CborError> {
    let mut bytes = Vec::new();
    covalence_lib_cbor::into_writer(value, &mut bytes)
        .map_err(|error| CborError::Codec(error.to_string()))?;
    Ok(bytes)
}

fn decode_value(bytes: &[u8]) -> Result<Value, CborError> {
    let mut cursor = Cursor::new(bytes);
    let value: Value = covalence_lib_cbor::from_reader(&mut cursor)
        .map_err(|error| CborError::Codec(error.to_string()))?;
    if cursor.position() != bytes.len() as u64 {
        return Err(CborError::TrailingData);
    }
    if encode_value(&value)? != bytes {
        return Err(CborError::NonCanonical);
    }
    Ok(value)
}

fn kind_to_value(kind: &Kind<ArcRepr>) -> Value {
    match kind {
        Kind::Star => node(SurfaceTag::KindStar, []),
        Kind::Arr(domain, codomain) => node(
            SurfaceTag::KindArr,
            [kind_to_value(domain), kind_to_value(codomain)],
        ),
    }
}

fn kind_from_value(value: Value, depth: usize) -> Result<ArcKind, CborError> {
    let depth = nested(depth)?;
    let (tag, values) = split_node(value)?;
    match tag {
        SurfaceTag::KindStar => {
            fields::<0>(values)?;
            Ok(Arc::new(Kind::Star))
        }
        SurfaceTag::KindArr => {
            let [domain, codomain] = fields(values)?;
            Ok(Arc::new(Kind::Arr(
                kind_from_value(domain, depth)?,
                kind_from_value(codomain, depth)?,
            )))
        }
        _ => Err(CborError::UnexpectedTag(tag)),
    }
}

fn link_fields(link: &Link) -> [Value; 2] {
    [
        Value::Bytes(link.0.as_ref().to_vec()),
        Value::Integer(u64::from(link.1 as u8).into()),
    ]
}

fn link_from_fields(hash: Value, format: &Value) -> Result<Link, CborError> {
    let Value::Bytes(hash) = hash else {
        return Err(CborError::Expected("link hash bytes"));
    };
    let length = hash.len();
    let hash: [u8; 32] = hash
        .try_into()
        .map_err(|_| CborError::InvalidHashLength(length))?;
    let format = match take_u64(format)? {
        0 => return Err(CborError::NotImplemented("BLOB link decoding")),
        1 => Format::CborTree,
        value => return Err(CborError::UnsupportedFormat(value)),
    };
    Ok(Arc::new((O256::from_array(hash), format)))
}

#[must_use]
pub fn type_to_value(ty: &Ty<ArcRepr>) -> Value {
    match ty {
        Ty::Bool => node(SurfaceTag::TyBool, []),
        Ty::Arr(domain, codomain) => node(
            SurfaceTag::TyArr,
            [type_to_value(domain), type_to_value(codomain)],
        ),
        Ty::App(application) => application.encode(),
        Ty::Abs(domain, body) => node(
            SurfaceTag::TyLam,
            [kind_to_value(domain), type_to_value(body)],
        ),
        Ty::Bv(variable) => node(
            SurfaceTag::TyBv,
            [
                Value::Integer(variable.index.index().into()),
                kind_to_value(&variable.kind),
            ],
        ),
        Ty::Sub(carrier, predicate) => node(
            SurfaceTag::TySub,
            [type_to_value(carrier), term_to_value(predicate)],
        ),
        Ty::Model(predicate) => node(SurfaceTag::TyModel, [term_to_value(predicate)]),
        Ty::Prim(primitive) => node(SurfaceTag::TyPrim, [Value::Text(primitive.clone())]),
        Ty::Link(link, kind) => node(
            SurfaceTag::TyLink,
            link_fields(link).into_iter().chain([kind_to_value(kind)]),
        ),
        Ty::Nat => node(SurfaceTag::TmNat, []),
    }
}

/// Decodes a HOL type from its CBOR data-model representation.
///
/// # Errors
///
/// Returns an error for malformed, unknown, or excessively nested syntax.
pub fn type_from_value(value: Value) -> Result<ArcTy, CborError> {
    type_from_value_at(value, 0)
}

fn type_from_value_at(value: Value, depth: usize) -> Result<ArcTy, CborError> {
    let depth = nested(depth)?;
    let (tag, values) = split_node(value)?;
    let ty = match tag {
        SurfaceTag::TyBool => {
            fields::<0>(values)?;
            Ty::Bool
        }
        SurfaceTag::TyArr => {
            let [domain, codomain] = fields(values)?;
            Ty::Arr(
                type_from_value_at(domain, depth)?,
                type_from_value_at(codomain, depth)?,
            )
        }
        SurfaceTag::TyApp => {
            let [function, argument] = fields(values)?;
            Ty::App(App::new(
                type_from_value_at(function, depth)?,
                type_from_value_at(argument, depth)?,
            ))
        }
        SurfaceTag::TyLam => {
            let [domain, body] = fields(values)?;
            Ty::Abs(
                kind_from_value(domain, depth)?,
                type_from_value_at(body, depth)?,
            )
        }
        SurfaceTag::TyBv => {
            let [index, kind] = fields(values)?;
            Ty::Bv(Arc::new(TypeVariable {
                index: Bv::new(take_u64(&index)?),
                kind: kind_from_value(kind, depth)?,
            }))
        }
        SurfaceTag::TySub => {
            let [carrier, predicate] = fields(values)?;
            Ty::Sub(
                type_from_value_at(carrier, depth)?,
                term_from_value_at(predicate, depth)?,
            )
        }
        SurfaceTag::TyModel => {
            let [predicate] = fields(values)?;
            Ty::Model(term_from_value_at(predicate, depth)?)
        }
        SurfaceTag::TyPrim => {
            let [primitive] = fields(values)?;
            let Value::Text(primitive) = primitive else {
                return Err(CborError::Expected("primitive text"));
            };
            Ty::Prim(primitive)
        }
        SurfaceTag::TyLink => {
            let [source, format, kind] = fields(values)?;
            Ty::Link(
                link_from_fields(source, &format)?,
                kind_from_value(kind, depth)?,
            )
        }
        SurfaceTag::TmNat => {
            fields::<0>(values)?;
            Ty::Nat
        }
        _ => return Err(CborError::UnexpectedTag(tag)),
    };
    Ok(Arc::new(ty))
}

fn context_to_value(context: &Context<ArcRepr>) -> Value {
    match context {
        Context::Empty => node(SurfaceTag::TmBool, [Value::Bool(true)]),
        Context::And(premise, rest) => node(
            SurfaceTag::TmAnd,
            [term_to_value(premise), context_to_value(rest)],
        ),
    }
}

fn context_from_value(value: Value, depth: usize) -> Result<Arc<Context<ArcRepr>>, CborError> {
    let depth = nested(depth)?;
    let (tag, values) = split_node(value)?;
    match tag {
        SurfaceTag::TmBool => {
            let [value] = fields(values)?;
            if value == Value::Bool(true) {
                Ok(Arc::new(Context::Empty))
            } else {
                Err(CborError::Expected("true empty context"))
            }
        }
        SurfaceTag::TmAnd => {
            let [premise, rest] = fields(values)?;
            Ok(Arc::new(Context::And(
                term_from_value_at(premise, depth)?,
                context_from_value(rest, depth)?,
            )))
        }
        _ => Err(CborError::UnexpectedTag(tag)),
    }
}

#[must_use]
pub fn term_to_value(term: &Tm<ArcRepr>) -> Value {
    match term {
        Tm::Exists(body) => node(SurfaceTag::TyExists, [term_to_value(body)]),
        Tm::Prim(primitive) => node(SurfaceTag::TmPrim, [Value::Text(primitive.clone())]),
        Tm::Bv(index) => node(SurfaceTag::TmBv, [Value::Integer(index.index().into())]),
        Tm::Fv(variable) => node(
            SurfaceTag::TmFv,
            [
                Value::Text(variable.name.clone()),
                type_to_value(&variable.ty),
            ],
        ),
        Tm::App(application) => application.encode(),
        Tm::Lam(domain, body) => node(
            SurfaceTag::TmLam,
            [type_to_value(domain), term_to_value(body)],
        ),
        Tm::Bool(value) => node(SurfaceTag::TmBool, [Value::Bool(*value)]),
        Tm::Eq(ty, left, right) => node(
            SurfaceTag::TmEq,
            [type_to_value(ty), term_to_value(left), term_to_value(right)],
        ),
        Tm::Eps(ty, predicate) => node(
            SurfaceTag::TmEps,
            [type_to_value(ty), term_to_value(predicate)],
        ),
        Tm::Abs(ty, predicate, representation) => node(
            SurfaceTag::TmAbs,
            [
                type_to_value(ty),
                term_to_value(predicate),
                term_to_value(representation),
            ],
        ),
        Tm::Rep(ty, predicate, abstraction) => node(
            SurfaceTag::TmRep,
            [
                type_to_value(ty),
                term_to_value(predicate),
                term_to_value(abstraction),
            ],
        ),
        Tm::Link(link, ty) => node(
            SurfaceTag::TmLink,
            link_fields(link).into_iter().chain([type_to_value(ty)]),
        ),
        Tm::And(left, right) => node(
            SurfaceTag::TmAnd,
            [term_to_value(left), term_to_value(right)],
        ),
        Tm::Inf => node(SurfaceTag::TmInf, []),
        Tm::Zero => node(SurfaceTag::TmZero, []),
        Tm::Succ => node(SurfaceTag::TmSucc, []),
        Tm::Nat(value) => node(SurfaceTag::TmLitNat, [Value::Integer((*value).into())]),
        Tm::Imp(context, conclusion) => node(
            SurfaceTag::TmImp,
            [context_to_value(context), term_to_value(conclusion)],
        ),
    }
}

/// Decodes a HOL term from its CBOR data-model representation.
///
/// # Errors
///
/// Returns an error for malformed, unknown, or excessively nested syntax.
pub fn term_from_value(value: Value) -> Result<ArcTm, CborError> {
    term_from_value_at(value, 0)
}

#[allow(clippy::too_many_lines)]
fn term_from_value_at(value: Value, depth: usize) -> Result<ArcTm, CborError> {
    let depth = nested(depth)?;
    let (tag, values) = split_node(value)?;
    let term = match tag {
        SurfaceTag::TyExists => {
            let [body] = fields(values)?;
            Tm::Exists(term_from_value_at(body, depth)?)
        }
        SurfaceTag::TmPrim => {
            let [primitive] = fields(values)?;
            let Value::Text(primitive) = primitive else {
                return Err(CborError::Expected("primitive text"));
            };
            Tm::Prim(primitive)
        }
        SurfaceTag::TmBv => {
            let [index] = fields(values)?;
            Tm::Bv(Bv::new(take_u64(&index)?))
        }
        SurfaceTag::TmFv => {
            let [name, ty] = fields(values)?;
            let Value::Text(name) = name else {
                return Err(CborError::Expected("free-variable name text"));
            };
            Tm::Fv(Arc::new(Variable {
                name,
                ty: type_from_value_at(ty, depth)?,
            }))
        }
        SurfaceTag::TmApp => {
            let [function, argument] = fields(values)?;
            Tm::App(App::new(
                term_from_value_at(function, depth)?,
                term_from_value_at(argument, depth)?,
            ))
        }
        SurfaceTag::TmLam => {
            let [domain, body] = fields(values)?;
            Tm::Lam(
                type_from_value_at(domain, depth)?,
                term_from_value_at(body, depth)?,
            )
        }
        SurfaceTag::TmBool => {
            let [value] = fields(values)?;
            let Value::Bool(value) = value else {
                return Err(CborError::Expected("Boolean"));
            };
            Tm::Bool(value)
        }
        SurfaceTag::TmEq => {
            let [ty, left, right] = fields(values)?;
            Tm::Eq(
                type_from_value_at(ty, depth)?,
                term_from_value_at(left, depth)?,
                term_from_value_at(right, depth)?,
            )
        }
        SurfaceTag::TmEps => {
            let [ty, predicate] = fields(values)?;
            Tm::Eps(
                type_from_value_at(ty, depth)?,
                term_from_value_at(predicate, depth)?,
            )
        }
        SurfaceTag::TmAbs => {
            let [ty, predicate, representation] = fields(values)?;
            Tm::Abs(
                type_from_value_at(ty, depth)?,
                term_from_value_at(predicate, depth)?,
                term_from_value_at(representation, depth)?,
            )
        }
        SurfaceTag::TmRep => {
            let [ty, predicate, abstraction] = fields(values)?;
            Tm::Rep(
                type_from_value_at(ty, depth)?,
                term_from_value_at(predicate, depth)?,
                term_from_value_at(abstraction, depth)?,
            )
        }
        SurfaceTag::TmLink => {
            let [source, format, ty] = fields(values)?;
            Tm::Link(
                link_from_fields(source, &format)?,
                type_from_value_at(ty, depth)?,
            )
        }
        SurfaceTag::TmAnd => {
            let [left, right] = fields(values)?;
            Tm::And(
                term_from_value_at(left, depth)?,
                term_from_value_at(right, depth)?,
            )
        }
        SurfaceTag::TmInf => {
            fields::<0>(values)?;
            Tm::Inf
        }
        SurfaceTag::TmZero => {
            fields::<0>(values)?;
            Tm::Zero
        }
        SurfaceTag::TmSucc => {
            fields::<0>(values)?;
            Tm::Succ
        }
        SurfaceTag::TmLitNat => {
            let [value] = fields(values)?;
            Tm::Nat(take_u64(&value)?)
        }
        SurfaceTag::TmImp => {
            let [context, conclusion] = fields(values)?;
            Tm::Imp(
                context_from_value(context, depth)?,
                term_from_value_at(conclusion, depth)?,
            )
        }
        _ => return Err(CborError::UnexpectedTag(tag)),
    };
    Ok(Arc::new(term))
}

impl CborObject for ArcKind {
    fn encode(&self) -> Value {
        kind_to_value(self)
    }

    fn decode(value: Value) -> Result<Self, CborError> {
        kind_from_value(value, 0)
    }
}

impl CborObject for App<ArcTy> {
    fn encode(&self) -> Value {
        node(
            SurfaceTag::TyApp,
            [type_to_value(&self.function), type_to_value(&self.argument)],
        )
    }

    fn decode(value: Value) -> Result<Self, CborError> {
        let (tag, values) = split_node(value)?;
        if tag != SurfaceTag::TyApp {
            return Err(CborError::UnexpectedTag(tag));
        }
        let [function, argument] = fields(values)?;
        Ok(Self::new(
            type_from_value_at(function, 0)?,
            type_from_value_at(argument, 0)?,
        ))
    }
}

impl CborObject for App<ArcTm> {
    fn encode(&self) -> Value {
        node(
            SurfaceTag::TmApp,
            [term_to_value(&self.function), term_to_value(&self.argument)],
        )
    }

    fn decode(value: Value) -> Result<Self, CborError> {
        let (tag, values) = split_node(value)?;
        if tag != SurfaceTag::TmApp {
            return Err(CborError::UnexpectedTag(tag));
        }
        let [function, argument] = fields(values)?;
        Ok(Self::new(
            term_from_value_at(function, 0)?,
            term_from_value_at(argument, 0)?,
        ))
    }
}

impl CborObject for ArcTy {
    fn encode(&self) -> Value {
        type_to_value(self)
    }

    fn decode(value: Value) -> Result<Self, CborError> {
        type_from_value(value)
    }
}

impl CborObject for ArcTm {
    fn encode(&self) -> Value {
        term_to_value(self)
    }

    fn decode(value: Value) -> Result<Self, CborError> {
        term_from_value(value)
    }
}

#[must_use = "serialization errors must be handled"]
/// Encodes a HOL type as canonical CBOR.
///
/// # Errors
///
/// Returns an error if the shared CBOR encoder rejects the value.
pub fn encode_type(ty: &Ty<ArcRepr>) -> Result<Vec<u8>, CborError> {
    encode_value(&type_to_value(ty))
}

/// Decodes a HOL type from canonical CBOR.
///
/// # Errors
///
/// Returns an error for malformed, non-canonical, trailing, or invalid syntax.
pub fn decode_type(bytes: &[u8]) -> Result<ArcTy, CborError> {
    type_from_value(decode_value(bytes)?)
}

#[must_use = "serialization errors must be handled"]
/// Encodes a HOL term as canonical CBOR.
///
/// # Errors
///
/// Returns an error if the shared CBOR encoder rejects the value.
pub fn encode_term(term: &Tm<ArcRepr>) -> Result<Vec<u8>, CborError> {
    encode_value(&term_to_value(term))
}

/// Decodes a HOL term from canonical CBOR.
///
/// # Errors
///
/// Returns an error for malformed, non-canonical, trailing, or invalid syntax.
pub fn decode_term(bytes: &[u8]) -> Result<ArcTm, CborError> {
    term_from_value(decode_value(bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_link() -> Link {
        Arc::new((O256::from_array([0xab; 32]), Format::CborTree))
    }

    #[test]
    fn links_are_flat_fields_of_their_syntax_node() {
        let term = Arc::new(Tm::Link(sample_link(), Arc::new(Ty::Bool)));
        let Value::Array(fields) = term.encode() else {
            panic!("expected a link array");
        };
        assert_eq!(fields.len(), 4);
        assert_eq!(
            fields[0],
            Value::Integer(u64::from(SurfaceTag::TmLink).into())
        );
        assert_eq!(fields[1], Value::Bytes(vec![0xab; 32]));
        assert_eq!(fields[2], Value::Integer(1_u64.into()));
        assert_eq!(
            ArcTm::decode(Value::Array(fields)).unwrap().encode(),
            term.encode()
        );
    }

    #[test]
    fn types_round_trip_with_kinded_variables_and_links() {
        let star = Arc::new(Kind::Star);
        let ty = Ty::Arr(
            Arc::new(Ty::Bv(Arc::new(TypeVariable {
                index: Bv::new(7),
                kind: Arc::clone(&star),
            }))),
            Arc::new(Ty::Link(sample_link(), star)),
        );
        let encoded = encode_type(&ty).unwrap();
        assert_eq!(
            encode_type(&decode_type(&encoded).unwrap()).unwrap(),
            encoded
        );
    }

    #[test]
    fn terms_and_context_spines_round_trip() {
        let context = Arc::new(Context::And(Arc::new(Tm::Inf), Arc::new(Context::Empty)));
        let term = Tm::Imp(
            context,
            Arc::new(Tm::And(
                Arc::new(Tm::Link(sample_link(), Arc::new(Ty::Bool))),
                Arc::new(Tm::Nat(1_000)),
            )),
        );
        let encoded = encode_term(&term).unwrap();
        assert_eq!(
            encode_term(&decode_term(&encoded).unwrap()).unwrap(),
            encoded
        );
    }

    #[test]
    fn decoder_rejects_noncanonical_and_trailing_bytes() {
        assert!(matches!(
            decode_term(&[0x81, 0x19, 0x00, 0x42]),
            Err(CborError::NonCanonical)
        ));
        let mut encoded = encode_term(&Tm::<ArcRepr>::Inf).unwrap();
        encoded.push(0);
        assert!(matches!(
            decode_term(&encoded),
            Err(CborError::TrailingData)
        ));
    }

    #[test]
    fn decoder_rejects_bad_link_hashes_and_formats() {
        let bool_ty = node(SurfaceTag::TyBool, []);
        assert!(matches!(
            term_from_value(node(
                SurfaceTag::TmLink,
                [
                    Value::Bytes(vec![0]),
                    Value::Integer(1_u64.into()),
                    bool_ty.clone()
                ],
            )),
            Err(CborError::InvalidHashLength(1))
        ));
        assert!(matches!(
            term_from_value(node(
                SurfaceTag::TmLink,
                [
                    Value::Bytes(vec![0; 32]),
                    Value::Integer(0_u64.into()),
                    bool_ty.clone()
                ],
            )),
            Err(CborError::NotImplemented("BLOB link decoding"))
        ));
        assert!(matches!(
            term_from_value(node(
                SurfaceTag::TmLink,
                [
                    Value::Bytes(vec![0; 32]),
                    Value::Integer(2_u64.into()),
                    bool_ty
                ],
            )),
            Err(CborError::UnsupportedFormat(2))
        ));
    }
}
