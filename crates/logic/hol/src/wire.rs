//! Untrusted D0 dense-arena wire values.
//!
//! This module mirrors the root-only Boolean subset of Lean's
//! `Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor.decodeSyntax?`. Signed indices
//! use the intended i64-bounded profile of
//! `Nucleus.Hol.Ethane.Amber.Serialization.intIndex` (the Lean companion must
//! enforce the same bound), and row envelopes correspond to
//! `Nucleus.Hol.Ethane.Amber.SyntaxRow.ofView?`.
//!
//! Successful decoding establishes only wire shape. It never constructs a
//! checked [`crate::Kernel`] or establishes arena validity or logical
//! soundness.

use std::collections::BTreeSet;

use covalence_data_cbor::{Value, ValueKind};

/// One exactly representable signed wire index.
///
/// The generic CBOR value remains arbitrary precision. Constructing `RawDense`
/// narrows its offset to the exact `i64` domain and rejects overflow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignedIndex(i64);

impl SignedIndex {
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One raw row admitted by the D0 wire-shape decoder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RawRow {
    BoolTy,
    Bool(bool),
}

/// A self-contained dense arena decoded from an untrusted CBOR value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RawDense {
    offset: SignedIndex,
    defs: Vec<RawRow>,
}

impl RawDense {
    /// Decodes the strict root-only D0 envelope.
    ///
    /// Exactly the fields `tag`, `parent`, `offset`, and `defs` are accepted.
    /// The parent must be CBOR null. Rows are checked against the exact D0
    /// Boolean tags, envelope arities, child order, and extra-field shape.
    ///
    /// This is a deliberately strict profile of Lean
    /// `Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor.decodeSyntax?`: the generic
    /// Lean decoder reserves and ignores unique extension fields, while this
    /// MVP entry point rejects them.
    ///
    /// # Errors
    ///
    /// Returns a precise [`DecodeError`] for malformed or unsupported input.
    pub fn decode_root(value: &Value) -> Result<Self, DecodeError> {
        let ValueKind::Map(fields) = value.kind() else {
            return Err(DecodeError::ExpectedObject);
        };

        let mut seen = BTreeSet::new();
        let mut tag = None;
        let mut parent = None;
        let mut offset = None;
        let mut defs = None;
        for (key, value) in fields.iter() {
            let ValueKind::Text(key) = key.kind() else {
                return Err(DecodeError::NonTextField);
            };
            if !seen.insert(key.as_ref()) {
                return Err(DecodeError::DuplicateField(key.to_string()));
            }
            match key.as_ref() {
                "tag" => tag = Some(value),
                "parent" => parent = Some(value),
                "offset" => offset = Some(value),
                "defs" => defs = Some(value),
                _ => return Err(DecodeError::UnknownField(key.to_string())),
            }
        }

        match required(tag, "tag")?.kind() {
            ValueKind::Text(tag) if tag.as_ref() == "arena.dense" => {}
            _ => return Err(DecodeError::WrongObjectTag),
        }
        if !matches!(required(parent, "parent")?.kind(), ValueKind::Simple(22)) {
            return Err(DecodeError::ParentNotRoot);
        }
        let offset = decode_index(required(offset, "offset")?)?;
        let ValueKind::Array(defs) = required(defs, "defs")?.kind() else {
            return Err(DecodeError::ExpectedDefsArray);
        };
        let defs = defs
            .iter()
            .enumerate()
            .map(|(index, row)| {
                decode_row(row).map_err(|reason| DecodeError::InvalidRow { index, reason })
            })
            .collect::<Result<_, _>>()?;
        Ok(Self { offset, defs })
    }

    #[must_use]
    pub const fn offset(&self) -> SignedIndex {
        self.offset
    }

    #[must_use]
    pub fn defs(&self) -> &[RawRow] {
        &self.defs
    }
}

/// A strict root dense-decoding failure.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    ExpectedObject,
    NonTextField,
    DuplicateField(String),
    UnknownField(String),
    MissingField(&'static str),
    WrongObjectTag,
    ParentNotRoot,
    InvalidOffset,
    OffsetOverflow,
    ExpectedDefsArray,
    InvalidRow { index: usize, reason: RowError },
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "invalid Ethane dense D0 object: {self:?}")
    }
}

impl std::error::Error for DecodeError {}

/// A malformed or unsupported D0 row.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowError {
    ExpectedEnvelope,
    WrongEnvelopeArity,
    ExpectedTag,
    UnknownTag,
    ExpectedChildren,
    ExpectedExtra,
    WrongArity,
    ExpectedBoolExtra,
}

fn required<'a>(value: Option<&'a Value>, field: &'static str) -> Result<&'a Value, DecodeError> {
    value.ok_or(DecodeError::MissingField(field))
}

fn decode_index(value: &Value) -> Result<SignedIndex, DecodeError> {
    match value.kind() {
        ValueKind::Integer(value) => i64::try_from(value)
            .map(SignedIndex)
            .map_err(|_| DecodeError::OffsetOverflow),
        _ => Err(DecodeError::InvalidOffset),
    }
}

fn decode_row(value: &Value) -> Result<RawRow, RowError> {
    let ValueKind::Array(envelope) = value.kind() else {
        return Err(RowError::ExpectedEnvelope);
    };
    let [tag, children, extra] = envelope.as_ref() else {
        return Err(RowError::WrongEnvelopeArity);
    };
    let ValueKind::Text(tag) = tag.kind() else {
        return Err(RowError::ExpectedTag);
    };
    let ValueKind::Array(children) = children.kind() else {
        return Err(RowError::ExpectedChildren);
    };
    let ValueKind::Array(extra) = extra.kind() else {
        return Err(RowError::ExpectedExtra);
    };

    match tag.as_ref() {
        "ty.bool" if children.is_empty() && extra.is_empty() => Ok(RawRow::BoolTy),
        "tm.bool" if !children.is_empty() => Err(RowError::WrongArity),
        "tm.bool" => decode_bool_extra(extra),
        "ty.bool" => Err(RowError::WrongArity),
        _ => Err(RowError::UnknownTag),
    }
}

fn decode_bool_extra(extra: &[Value]) -> Result<RawRow, RowError> {
    let [field] = extra else {
        return Err(RowError::WrongArity);
    };
    let ValueKind::Array(field) = field.kind() else {
        return Err(RowError::ExpectedBoolExtra);
    };
    let [tag, value] = field.as_ref() else {
        return Err(RowError::ExpectedBoolExtra);
    };
    let (ValueKind::Text(tag), ValueKind::Simple(value)) = (tag.kind(), value.kind()) else {
        return Err(RowError::ExpectedBoolExtra);
    };
    if tag.as_ref() != "extra.bool" {
        return Err(RowError::ExpectedBoolExtra);
    }
    match value {
        20 => Ok(RawRow::Bool(false)),
        21 => Ok(RawRow::Bool(true)),
        _ => Err(RowError::ExpectedBoolExtra),
    }
}

#[cfg(test)]
mod tests {
    use covalence_data_cbor::{Int, Value};

    use super::{DecodeError, RawDense, RawRow, RowError};

    fn bool_ty() -> Value {
        Value::array([
            Value::from("ty.bool"),
            Value::array(Vec::<Value>::new()),
            Value::array(Vec::<Value>::new()),
        ])
    }

    fn bool_const(value: bool) -> Value {
        Value::array([
            Value::from("tm.bool"),
            Value::array(Vec::<Value>::new()),
            Value::array([Value::array([
                Value::from("extra.bool"),
                Value::bool(value),
            ])]),
        ])
    }

    fn root_fields(offset: Value, defs: Vec<Value>) -> Vec<(Value, Value)> {
        vec![
            (Value::from("tag"), Value::from("arena.dense")),
            (Value::from("parent"), Value::null()),
            (Value::from("offset"), offset),
            (Value::from("defs"), Value::array(defs)),
        ]
    }

    fn root(offset: Value, defs: Vec<Value>) -> Value {
        Value::map(root_fields(offset, defs))
    }

    #[test]
    fn decodes_root_boolean_rows_and_i64_boundaries() {
        let positive = RawDense::decode_root(&root(
            Value::from(i64::MAX),
            vec![bool_ty(), bool_const(false), bool_const(true)],
        ))
        .unwrap();
        assert_eq!(positive.offset().get(), i64::MAX);
        assert_eq!(
            positive.defs(),
            &[RawRow::BoolTy, RawRow::Bool(false), RawRow::Bool(true)]
        );

        let negative = RawDense::decode_root(&root(Value::from(i64::MIN), vec![])).unwrap();
        assert_eq!(negative.offset().get(), i64::MIN);
    }

    #[test]
    fn rejects_parent_unknown_duplicate_and_missing_fields() {
        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields[1].1 = Value::array(Vec::<Value>::new());
        let parented = Value::map(fields);
        assert_eq!(
            RawDense::decode_root(&parented),
            Err(DecodeError::ParentNotRoot)
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.push((Value::from("metadata"), Value::null()));
        let unknown = Value::map(fields);
        assert_eq!(
            RawDense::decode_root(&unknown),
            Err(DecodeError::UnknownField("metadata".to_owned()))
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.push((Value::from("defs"), Value::array(Vec::<Value>::new())));
        let duplicate = Value::map(fields);
        assert_eq!(
            RawDense::decode_root(&duplicate),
            Err(DecodeError::DuplicateField("defs".to_owned()))
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.pop();
        let missing = Value::map(fields);
        assert_eq!(
            RawDense::decode_root(&missing),
            Err(DecodeError::MissingField("defs"))
        );
    }

    #[test]
    fn accepts_arbitrary_integer_values_inside_i64() {
        let positive = Value::from(Int::from(42_i64));
        assert_eq!(
            RawDense::decode_root(&root(positive, vec![]))
                .unwrap()
                .offset()
                .get(),
            42
        );
        let negative = Value::from(Int::from(-42_i64));
        assert_eq!(
            RawDense::decode_root(&root(negative, vec![]))
                .unwrap()
                .offset()
                .get(),
            -42
        );
    }

    #[test]
    fn rejects_arbitrary_bignum_overflow_and_wrong_boolean_shapes() {
        for bytes in [[1_u8; 33], [0xfe_u8; 33]] {
            let arbitrary = Int::from_canonical_bytes(&bytes).unwrap();
            assert_eq!(
                RawDense::decode_root(&root(Value::from(arbitrary), vec![])),
                Err(DecodeError::OffsetOverflow)
            );
        }

        let bad_bool = Value::array([
            Value::from("tm.bool"),
            Value::array([Value::from(0_i64)]),
            Value::array(Vec::<Value>::new()),
        ]);
        assert_eq!(
            RawDense::decode_root(&root(Value::from(0_i64), vec![bad_bool])),
            Err(DecodeError::InvalidRow {
                index: 0,
                reason: RowError::WrongArity
            })
        );
    }

    #[test]
    fn rejects_offsets_one_step_outside_i64() {
        for overflow in [i128::from(i64::MAX) + 1, i128::from(i64::MIN) - 1] {
            let value = Value::from(Int::from(overflow));
            assert_eq!(
                RawDense::decode_root(&root(value, vec![])),
                Err(DecodeError::OffsetOverflow)
            );
        }
    }
}
