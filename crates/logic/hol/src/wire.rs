//! Serde-backed CBOR helpers for raw arenas.

use std::io::{Read, Write};

use crate::Arena;

/// Deserializes an unvalidated arena from the complete contents of `reader`.
///
/// Decoding is whole-object: bytes after the arena are a decode failure, not
/// padding. Two byte strings that differ only in a suffix would otherwise be
/// two content addresses for one arena.
///
/// # Errors
///
/// Returns an error for malformed CBOR, a representation invariant failure, or
/// any byte left unread once the arena has been decoded.
pub fn deserialize(mut reader: impl Read) -> Result<Arena, DecodeError> {
    let arena = covalence_lib_cbor::from_reader(&mut reader)
        .map_err(|error| DecodeError(error.to_string()))?;
    if reader_is_exhausted(&mut reader)? {
        Ok(arena)
    } else {
        Err(DecodeError("trailing bytes after the arena".to_owned()))
    }
}

fn reader_is_exhausted(reader: &mut impl Read) -> Result<bool, DecodeError> {
    let mut trailing = [0_u8; 1];
    loop {
        return match reader.read(&mut trailing) {
            Ok(0) => Ok(true),
            Ok(_) => Ok(false),
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => Err(DecodeError(error.to_string())),
        };
    }
}

/// Serializes a raw arena through its exact Serde view.
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
    use crate::{
        Import, ImportId, Link, LinkFormat, Meta, Ref,
        row::{Expr, Row},
    };
    use covalence_lib_cbor::{Value, from_reader, into_writer};
    use covalence_lib_hash::O256;

    const fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    const fn import(value: u64) -> ImportId {
        ImportId::new(value).unwrap()
    }

    fn sample() -> Arena {
        Arena::from_parts(
            vec![
                Import::Null,
                Import::Literal(Box::new(Arena::empty())),
                Import::Link(Link {
                    format: LinkFormat::Cbor,
                    blake3: O256::from_array([0x51; 32]),
                }),
            ],
            ["ax.z".into(), "ax.a".into(), "ax.z".into()],
            vec![
                Row::new(Expr::KindStar),
                Row::new(Expr::TmRef {
                    src: import(2),
                    ix: reference(3),
                })
                .with_eq(reference(1))
                .with_sort(reference(1)),
            ],
            [reference(2), reference(1), reference(2)],
            vec![Meta::Valid { src: import(3) }],
            vec![Meta::Wf {
                src: import(2),
                ix: reference(3),
                sort: reference(1),
            }],
        )
    }

    #[test]
    fn complete_object_round_trips_and_normalizes_sets() {
        let arena = sample();
        let mut bytes = Vec::new();
        serialize(&arena, &mut bytes).unwrap();
        assert_eq!(deserialize(bytes.as_slice()).unwrap(), arena);
        assert_eq!(
            arena.context().collect::<Vec<_>>(),
            [reference(1), reference(2)]
        );
        assert_eq!(arena.axioms().collect::<Vec<_>>(), ["ax.a", "ax.z"]);

        let value: Value = from_reader(bytes.as_slice()).unwrap();
        let Value::Map(fields) = value else {
            panic!("arena must be a CBOR map")
        };
        assert!(fields.contains(&(Value::Text("tag".into()), Value::Text("arena".into()))));
    }

    #[test]
    fn each_import_round_trips() {
        for import in sample().imports().iter().cloned() {
            let arena = Arena::from_parts(vec![import], [], vec![], [], vec![], vec![]);
            let mut bytes = Vec::new();
            serialize(&arena, &mut bytes).unwrap();
            assert!(
                deserialize(bytes.as_slice()).is_ok(),
                "{:#?}",
                from_reader::<Value, _>(bytes.as_slice()).unwrap()
            );
        }
    }

    #[test]
    fn zero_references_and_unknown_metadata_are_rejected() {
        fn invalid(field: &str, value: Value) -> bool {
            let object = Value::Map(vec![
                (Value::Text("tag".into()), Value::Text("arena".into())),
                (Value::Text("imports".into()), Value::Array(Vec::new())),
                (Value::Text("axs".into()), Value::Array(Vec::new())),
                (Value::Text("defs".into()), Value::Array(Vec::new())),
                (Value::Text("ctx".into()), Value::Array(Vec::new())),
                (Value::Text("assume".into()), Value::Array(Vec::new())),
                (Value::Text("assert".into()), Value::Array(Vec::new())),
            ]);
            let Value::Map(mut fields) = object else {
                unreachable!()
            };
            let entry = fields
                .iter_mut()
                .find(|(key, _)| key == &Value::Text(field.into()))
                .unwrap();
            entry.1 = value;
            let mut bytes = Vec::new();
            into_writer(&Value::Map(fields), &mut bytes).unwrap();
            deserialize(bytes.as_slice()).is_err()
        }

        assert!(invalid("ctx", Value::Array(vec![Value::Integer(0.into())])));
        assert!(invalid(
            "assume",
            Value::Array(vec![Value::Map(vec![
                (
                    Value::Text("tag".into()),
                    Value::Text("meta.unknown".into())
                ),
                (Value::Text("src".into()), Value::Integer(1.into())),
            ])]),
        ));
    }
}
