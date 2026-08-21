//! Untrusted D0 dense-arena wire decoding.
//!
//! This module mirrors the root-only Boolean subset of Lean's
//! `Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor.decodeSyntax?`. Signed indices
//! use the intended i64-bounded profile of
//! `Nucleus.Hol.Ethane.Amber.Serialization.intIndex`, and row envelopes
//! correspond to `Nucleus.Hol.Ethane.Amber.SyntaxRow.ofView?`.
//!
//! Successful decoding establishes only wire shape and returns a bare
//! [`crate::dense::Arena`]. It never constructs a checked [`crate::Kernel`] or
//! establishes arena validity or logical soundness.

use std::collections::BTreeSet;

use covalence_data_cbor::{Value, ValueKind};

use crate::{Row, dense};

/// Decodes the strict root-only D0 envelope into an untrusted dense arena.
///
/// Exactly the fields `tag`, `parent`, `offset`, and `defs` are accepted. The
/// parent must be CBOR null. Rows are checked against the exact shared D0
/// Boolean row vocabulary.
///
/// This is a deliberately strict profile of Lean
/// `Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor.decodeSyntax?`: the generic Lean
/// decoder reserves and ignores unique extension fields, while this MVP entry
/// point rejects them.
///
/// # Errors
///
/// Returns a precise [`DecodeError`] for malformed or unsupported input.
pub fn decode_root(value: &Value) -> Result<dense::Arena, DecodeError> {
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
    let rows = defs
        .iter()
        .enumerate()
        .map(|(index, row)| {
            decode_row(row).map_err(|reason| DecodeError::InvalidRow { index, reason })
        })
        .collect::<Result<_, _>>()?;
    Ok(dense::Arena::from_untrusted(offset, rows))
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

fn decode_index(value: &Value) -> Result<i64, DecodeError> {
    match value.kind() {
        ValueKind::Integer(value) => i64::try_from(value).map_err(|_| DecodeError::OffsetOverflow),
        _ => Err(DecodeError::InvalidOffset),
    }
}

fn decode_row(value: &Value) -> Result<Row, RowError> {
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
        "ty.bool" if children.is_empty() && extra.is_empty() => Ok(Row::BoolTy),
        "tm.bool" if !children.is_empty() => Err(RowError::WrongArity),
        "tm.bool" => decode_bool_extra(extra),
        "ty.bool" => Err(RowError::WrongArity),
        _ => Err(RowError::UnknownTag),
    }
}

fn decode_bool_extra(extra: &[Value]) -> Result<Row, RowError> {
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
        20 => Ok(Row::Bool(false)),
        21 => Ok(Row::Bool(true)),
        _ => Err(RowError::ExpectedBoolExtra),
    }
}

#[cfg(test)]
mod tests {
    use covalence_data_cbor::{Int, Value};

    use crate::Row;

    use super::{DecodeError, RowError, decode_root};

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
    fn decodes_untrusted_dense_arena_with_shared_rows() {
        let arena = decode_root(&root(
            Value::from(i64::MAX),
            vec![bool_ty(), bool_const(false), bool_const(true)],
        ))
        .unwrap();
        assert_eq!(arena.offset(), i64::MAX);
        assert_eq!(
            arena.rows(),
            &[Row::BoolTy, Row::Bool(false), Row::Bool(true)]
        );

        let minimum = decode_root(&root(Value::from(i64::MIN), vec![])).unwrap();
        assert_eq!(minimum.offset(), i64::MIN);
    }

    #[test]
    fn rejects_parent_unknown_duplicate_and_missing_fields() {
        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields[1].1 = Value::array(Vec::<Value>::new());
        assert_eq!(
            decode_root(&Value::map(fields)),
            Err(DecodeError::ParentNotRoot)
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.push((Value::from("metadata"), Value::null()));
        assert_eq!(
            decode_root(&Value::map(fields)),
            Err(DecodeError::UnknownField("metadata".to_owned()))
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.push((Value::from("defs"), Value::array(Vec::<Value>::new())));
        assert_eq!(
            decode_root(&Value::map(fields)),
            Err(DecodeError::DuplicateField("defs".to_owned()))
        );

        let mut fields = root_fields(Value::from(0_i64), vec![]);
        fields.pop();
        assert_eq!(
            decode_root(&Value::map(fields)),
            Err(DecodeError::MissingField("defs"))
        );
    }

    #[test]
    fn preserves_bigint_then_checks_i64() {
        for value in [42_i64, -42] {
            assert_eq!(
                decode_root(&root(Value::from(Int::from(value)), vec![]))
                    .unwrap()
                    .offset(),
                value
            );
        }
        for bytes in [[1_u8; 33], [0xfe_u8; 33]] {
            let arbitrary = Int::from_canonical_bytes(&bytes).unwrap();
            assert_eq!(
                decode_root(&root(Value::from(arbitrary), vec![])),
                Err(DecodeError::OffsetOverflow)
            );
        }
        for overflow in [i128::from(i64::MAX) + 1, i128::from(i64::MIN) - 1] {
            assert_eq!(
                decode_root(&root(Value::from(Int::from(overflow)), vec![])),
                Err(DecodeError::OffsetOverflow)
            );
        }
    }

    #[test]
    fn rejects_wrong_boolean_shape() {
        let bad_bool = Value::array([
            Value::from("tm.bool"),
            Value::array([Value::from(0_i64)]),
            Value::array(Vec::<Value>::new()),
        ]);
        assert_eq!(
            decode_root(&root(Value::from(0_i64), vec![bad_bool])),
            Err(DecodeError::InvalidRow {
                index: 0,
                reason: RowError::WrongArity
            })
        );
    }
}
