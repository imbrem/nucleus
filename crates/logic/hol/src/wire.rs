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

use covalence_lib_cbor::Value;

/// One exactly representable signed wire index.
///
/// CBOR major type 1 retains its standard `-1-n` meaning. D0 narrows both
/// native CBOR integer forms to the exact `i64` domain and rejects overflow.
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
        let Value::Map(fields) = value else {
            return Err(DecodeError::ExpectedObject);
        };

        let mut seen = BTreeSet::new();
        let mut tag = None;
        let mut parent = None;
        let mut offset = None;
        let mut defs = None;
        for (key, value) in fields {
            let Value::Text(key) = key else {
                return Err(DecodeError::NonTextField);
            };
            if !seen.insert(key.as_str()) {
                return Err(DecodeError::DuplicateField(key.clone()));
            }
            match key.as_str() {
                "tag" => tag = Some(value),
                "parent" => parent = Some(value),
                "offset" => offset = Some(value),
                "defs" => defs = Some(value),
                _ => return Err(DecodeError::UnknownField(key.clone())),
            }
        }

        match required(tag, "tag")? {
            Value::Text(tag) if tag == "arena.dense" => {}
            _ => return Err(DecodeError::WrongObjectTag),
        }
        if !matches!(required(parent, "parent")?, Value::Null) {
            return Err(DecodeError::ParentNotRoot);
        }
        let offset = decode_index(required(offset, "offset")?)?;
        let Value::Array(defs) = required(defs, "defs")? else {
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
    let Value::Integer(value) = value else {
        return Err(DecodeError::InvalidOffset);
    };
    let value = i128::from(*value);
    i64::try_from(value)
        .map(SignedIndex)
        .map_err(|_| DecodeError::OffsetOverflow)
}

fn decode_row(value: &Value) -> Result<RawRow, RowError> {
    let Value::Array(envelope) = value else {
        return Err(RowError::ExpectedEnvelope);
    };
    let [tag, children, extra] = envelope.as_slice() else {
        return Err(RowError::WrongEnvelopeArity);
    };
    let Value::Text(tag) = tag else {
        return Err(RowError::ExpectedTag);
    };
    let Value::Array(children) = children else {
        return Err(RowError::ExpectedChildren);
    };
    let Value::Array(extra) = extra else {
        return Err(RowError::ExpectedExtra);
    };

    match tag.as_str() {
        "ty.bool" if children.is_empty() && extra.is_empty() => Ok(RawRow::BoolTy),
        "tm.bool" if !children.is_empty() => Err(RowError::WrongArity),
        "tm.bool" => match extra.as_slice() {
            [Value::Array(field)] => match field.as_slice() {
                [Value::Text(tag), Value::Bool(value)] if tag == "extra.bool" => {
                    Ok(RawRow::Bool(*value))
                }
                _ => Err(RowError::ExpectedBoolExtra),
            },
            _ => Err(RowError::WrongArity),
        },
        "ty.bool" => Err(RowError::WrongArity),
        _ => Err(RowError::UnknownTag),
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_cbor::Value;

    use super::{DecodeError, RawDense, RawRow, RowError};

    fn bool_ty() -> Value {
        Value::Array(vec![
            Value::Text("ty.bool".to_owned()),
            Value::Array(vec![]),
            Value::Array(vec![]),
        ])
    }

    fn bool_const(value: bool) -> Value {
        Value::Array(vec![
            Value::Text("tm.bool".to_owned()),
            Value::Array(vec![]),
            Value::Array(vec![Value::Array(vec![
                Value::Text("extra.bool".to_owned()),
                Value::Bool(value),
            ])]),
        ])
    }

    fn root(offset: Value, defs: Vec<Value>) -> Value {
        Value::Map(vec![
            (
                Value::Text("tag".to_owned()),
                Value::Text("arena.dense".to_owned()),
            ),
            (Value::Text("parent".to_owned()), Value::Null),
            (Value::Text("offset".to_owned()), offset),
            (Value::Text("defs".to_owned()), Value::Array(defs)),
        ])
    }

    #[test]
    fn decodes_root_boolean_rows_and_i64_boundaries() {
        let positive = RawDense::decode_root(&root(
            Value::Integer(i64::MAX.into()),
            vec![bool_ty(), bool_const(false), bool_const(true)],
        ))
        .unwrap();
        assert_eq!(positive.offset().get(), i64::MAX);
        assert_eq!(
            positive.defs(),
            &[RawRow::BoolTy, RawRow::Bool(false), RawRow::Bool(true)]
        );

        let negative =
            RawDense::decode_root(&root(Value::Integer(i64::MIN.into()), vec![])).unwrap();
        assert_eq!(negative.offset().get(), i64::MIN);
    }

    #[test]
    fn rejects_parent_unknown_duplicate_and_missing_fields() {
        let mut parented = root(Value::Integer(0.into()), vec![]);
        let Value::Map(fields) = &mut parented else {
            unreachable!()
        };
        fields[1].1 = Value::Array(vec![]);
        assert_eq!(
            RawDense::decode_root(&parented),
            Err(DecodeError::ParentNotRoot)
        );

        let mut unknown = root(Value::Integer(0.into()), vec![]);
        let Value::Map(fields) = &mut unknown else {
            unreachable!()
        };
        fields.push((Value::Text("metadata".to_owned()), Value::Null));
        assert_eq!(
            RawDense::decode_root(&unknown),
            Err(DecodeError::UnknownField("metadata".to_owned()))
        );

        let mut duplicate = root(Value::Integer(0.into()), vec![]);
        let Value::Map(fields) = &mut duplicate else {
            unreachable!()
        };
        fields.push((Value::Text("defs".to_owned()), Value::Array(vec![])));
        assert_eq!(
            RawDense::decode_root(&duplicate),
            Err(DecodeError::DuplicateField("defs".to_owned()))
        );

        let mut missing = root(Value::Integer(0.into()), vec![]);
        let Value::Map(fields) = &mut missing else {
            unreachable!()
        };
        fields.pop();
        assert_eq!(
            RawDense::decode_root(&missing),
            Err(DecodeError::MissingField("defs"))
        );
    }

    #[test]
    fn rejects_non_native_offsets_and_wrong_boolean_shapes() {
        let tagged_bignum = Value::Tag(2, Box::new(Value::Bytes(vec![1; 9])));
        assert_eq!(
            RawDense::decode_root(&root(tagged_bignum, vec![])),
            Err(DecodeError::InvalidOffset)
        );

        let bad_bool = Value::Array(vec![
            Value::Text("tm.bool".to_owned()),
            Value::Array(vec![Value::Integer(0.into())]),
            Value::Array(vec![]),
        ]);
        assert_eq!(
            RawDense::decode_root(&root(Value::Integer(0.into()), vec![bad_bool])),
            Err(DecodeError::InvalidRow {
                index: 0,
                reason: RowError::WrongArity
            })
        );
    }

    #[test]
    fn rejects_offsets_one_step_outside_i64() {
        for overflow in [i128::from(i64::MAX) + 1, i128::from(i64::MIN) - 1] {
            let value = Value::Integer(overflow.try_into().unwrap());
            assert_eq!(
                RawDense::decode_root(&root(value, vec![])),
                Err(DecodeError::OffsetOverflow)
            );
        }
    }
}
