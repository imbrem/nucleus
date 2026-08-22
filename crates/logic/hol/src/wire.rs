//! Serde-backed CBOR helpers for raw arenas.

use std::io::{Read, Write};

use crate::Arena;

/// Deserializes an unvalidated arena.
///
/// # Errors
///
/// Returns an error for malformed CBOR or a row whose tag, arity, or payload
/// does not match the Ethane row vocabulary.
pub fn deserialize(reader: impl Read) -> Result<Arena, DecodeError> {
    covalence_lib_cbor::from_reader(reader).map_err(|error| DecodeError(error.to_string()))
}

/// Serializes a raw arena through its derived Serde representation.
///
/// # Errors
///
/// Returns an error if the writer rejects the encoded bytes.
pub fn serialize(arena: &Arena, writer: impl Write) -> Result<(), EncodeError> {
    covalence_lib_cbor::into_writer(arena, writer).map_err(|error| EncodeError(error.to_string()))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeError(String);

impl std::fmt::Display for DecodeError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "invalid Ethane arena: {}", self.0)
    }
}

impl std::error::Error for DecodeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodeError(String);

impl std::fmt::Display for EncodeError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "could not encode Ethane arena: {}", self.0)
    }
}

impl std::error::Error for EncodeError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::row::{Expr, Row};
    use covalence_lib_cbor::{Value, from_reader, into_writer};

    #[test]
    fn dense_uses_one_derived_tagged_enum() {
        let arena = Arena::from_rows(-1, vec![Row::new(Expr::Bool(true)).with_sort(3)]);
        let mut bytes = Vec::new();
        serialize(&arena, &mut bytes).unwrap();

        let value: Value = from_reader(bytes.as_slice()).unwrap();
        let Value::Map(fields) = value else {
            panic!("arena must be a CBOR map")
        };
        assert!(fields.contains(&(Value::Text("tag".into()), Value::Text("arena.dense".into()))));
        assert!(fields.contains(&(Value::Text("parent".into()), Value::Null)));
        assert_eq!(deserialize(bytes.as_slice()).unwrap(), arena);
    }

    #[test]
    fn serde_rejects_non_null_parent() {
        let value = Value::Map(vec![
            (Value::Text("tag".into()), Value::Text("arena.dense".into())),
            (Value::Text("parent".into()), Value::Integer(0.into())),
            (Value::Text("offset".into()), Value::Integer(0.into())),
            (Value::Text("defs".into()), Value::Array(Vec::new())),
        ]);
        let mut bytes = Vec::new();
        into_writer(&value, &mut bytes).unwrap();
        assert!(deserialize(bytes.as_slice()).is_err());
    }
}
