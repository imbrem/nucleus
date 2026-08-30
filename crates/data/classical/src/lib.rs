//! Untrusted wire codec for checked tagged-classical arenas.
//!
//! The wire object is a closed, link-free ATProto-style record. Machine words
//! and roots are exact eight-byte big-endian blobs. Decoding validates the
//! complete arena and returns checked syntax only; it cannot create a theorem.

use covalence_lib_cbor::Value;
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_classical::tagged::{Arena, Checked, Ref, RuntimeError, Word};

/// Stable discriminator for the version-one tagged-classical arena object.
pub const TYPE_NAME: &str = "io.github.imbrem.nucleus.classicalArenaV1";

const WORD_BYTES: usize = 8;
const RESERVED_BYTES: usize = 4 * WORD_BYTES;

/// Failure to decode and validate a tagged-classical arena object.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DecodeError {
    /// The bytes are not one complete CBOR data item.
    #[snafu(display("could not decode tagged-classical CBOR: {source}"))]
    Cbor {
        /// Underlying CBOR decoder failure.
        source: covalence_lib_cbor::de::Error<std::io::Error>,
    },
    /// Bytes remained after the first complete CBOR item.
    #[snafu(display("trailing bytes after tagged-classical CBOR object"))]
    TrailingBytes,
    /// The data item does not have the exact closed record shape.
    #[snafu(display("invalid tagged-classical CBOR schema: {reason}"))]
    Schema {
        /// Rejected schema invariant.
        reason: &'static str,
    },
    /// The raw arena fails its allocator, ownership, or syntax checks.
    #[snafu(display("invalid tagged-classical CBOR arena: {source}"))]
    Runtime {
        /// Underlying complete arena validation failure.
        source: RuntimeError,
    },
    /// The parsed tree could not be deterministically re-encoded.
    #[snafu(display("could not re-encode tagged-classical CBOR: {source}"))]
    Reencode {
        /// Underlying deterministic encoder failure.
        source: EncodeError,
    },
    /// The bytes do not use the one deterministic DRISL representation.
    #[snafu(display("tagged-classical CBOR encoding is not canonical"))]
    Noncanonical,
}

/// Failure to encode a checked tagged-classical arena.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("could not encode tagged-classical CBOR: {source}"))]
pub struct EncodeError {
    /// Underlying CBOR encoder failure.
    source: covalence_lib_cbor::ser::Error<std::io::Error>,
}

/// Decodes one exact deterministic DRISL object and validates its arena.
///
/// This establishes checked syntax only. Only the sealed kernel API can turn
/// checked syntax into theorem facts.
///
/// # Errors
///
/// Returns an error for malformed or trailing CBOR, noncanonical bytes, a
/// schema mismatch, or an arena that fails complete runtime validation.
pub fn decode_checked(bytes: &[u8]) -> Result<Checked, DecodeError> {
    let mut remaining = bytes;
    let value: Value = covalence_lib_cbor::from_reader(&mut remaining).context(CborSnafu)?;
    if !remaining.is_empty() {
        return Err(DecodeError::TrailingBytes);
    }

    let arena = arena_from_value(&value)?;
    let checked = Checked::check(arena).context(RuntimeSnafu)?;
    let canonical = encode_checked(&checked).context(ReencodeSnafu)?;
    if canonical != bytes {
        return Err(DecodeError::Noncanonical);
    }
    Ok(checked)
}

/// Encodes checked syntax as the unique deterministic version-one DRISL bytes.
///
/// # Errors
///
/// Returns an error only if the in-memory CBOR writer rejects the value.
pub fn encode_checked(checked: &Checked) -> Result<Vec<u8>, EncodeError> {
    let mut bytes = Vec::new();
    covalence_lib_cbor::into_writer(&arena_value(checked.arena()), &mut bytes)
        .context(EncodeSnafu)?;
    Ok(bytes)
}

fn arena_value(arena: &Arena) -> Value {
    let mut words = Vec::new();
    for word in arena.words() {
        words.extend_from_slice(&word.raw().to_be_bytes());
    }
    let roots = arena
        .roots()
        .iter()
        .map(|(premise, conclusion)| {
            Value::Map(vec![
                field(
                    "premise",
                    Value::Bytes(premise.word().raw().to_be_bytes().to_vec()),
                ),
                field(
                    "conclusion",
                    Value::Bytes(conclusion.word().raw().to_be_bytes().to_vec()),
                ),
            ])
        })
        .collect();

    Value::Map(vec![
        field("$type", Value::Text(TYPE_NAME.to_owned())),
        field("roots", Value::Array(roots)),
        field("words", Value::Bytes(words)),
        field(
            "freeRoot",
            Value::Bytes(arena.free_root().raw().to_be_bytes().to_vec()),
        ),
    ])
}

fn field(name: &str, value: Value) -> (Value, Value) {
    (Value::Text(name.to_owned()), value)
}

fn arena_from_value(value: &Value) -> Result<Arena, DecodeError> {
    let Value::Map(fields) = value else {
        return schema("top-level item must be a map");
    };
    let [type_field, roots_field, words_field, free_root_field] = fields.as_slice() else {
        return schema("top-level map must have exactly four fields");
    };
    if type_field.0 != Value::Text("$type".to_owned())
        || type_field.1 != Value::Text(TYPE_NAME.to_owned())
    {
        return schema("first field must be the exact $type discriminator");
    }
    if roots_field.0 != Value::Text("roots".to_owned()) {
        return schema("second field must be roots");
    }
    if words_field.0 != Value::Text("words".to_owned()) {
        return schema("third field must be words");
    }
    if free_root_field.0 != Value::Text("freeRoot".to_owned()) {
        return schema("fourth field must be freeRoot");
    }

    let Value::Array(root_values) = &roots_field.1 else {
        return schema("roots must be an array");
    };
    let mut roots = Vec::with_capacity(root_values.len());
    for root in root_values {
        roots.push(root_from_value(root)?);
    }

    let Value::Bytes(word_bytes) = &words_field.1 else {
        return schema("words must be a byte string");
    };
    if word_bytes.len() < RESERVED_BYTES || !word_bytes.len().is_multiple_of(WORD_BYTES) {
        return schema("words must contain at least four complete 64-bit words");
    }
    let words = word_bytes
        .chunks_exact(WORD_BYTES)
        .map(|bytes| {
            let raw = u64::from_be_bytes(bytes.try_into().expect("chunk width is exact"));
            Word::from_raw(raw)
        })
        .collect();

    let Value::Bytes(free_root_bytes) = &free_root_field.1 else {
        return schema("freeRoot must be a byte string");
    };
    let free_root = Word::from_raw(raw_word(free_root_bytes, "freeRoot must be eight bytes")?);

    Ok(Arena::new(words, free_root, roots))
}

fn root_from_value(value: &Value) -> Result<(Ref, Ref), DecodeError> {
    let Value::Map(fields) = value else {
        return schema("each root must be a map");
    };
    let [premise_field, conclusion_field] = fields.as_slice() else {
        return schema("each root must have exactly two fields");
    };
    if premise_field.0 != Value::Text("premise".to_owned()) {
        return schema("first root field must be premise");
    }
    if conclusion_field.0 != Value::Text("conclusion".to_owned()) {
        return schema("second root field must be conclusion");
    }
    let Value::Bytes(premise_bytes) = &premise_field.1 else {
        return schema("premise must be a byte string");
    };
    let Value::Bytes(conclusion_bytes) = &conclusion_field.1 else {
        return schema("conclusion must be a byte string");
    };
    let premise = Ref::new(Word::from_raw(raw_word(
        premise_bytes,
        "premise must be eight bytes",
    )?))
    .map_err(|_| DecodeError::Schema {
        reason: "premise must be a nonzero reference",
    })?;
    let conclusion = Ref::new(Word::from_raw(raw_word(
        conclusion_bytes,
        "conclusion must be eight bytes",
    )?))
    .map_err(|_| DecodeError::Schema {
        reason: "conclusion must be a nonzero reference",
    })?;
    Ok((premise, conclusion))
}

fn raw_word(bytes: &[u8], reason: &'static str) -> Result<u64, DecodeError> {
    bytes
        .try_into()
        .map(u64::from_be_bytes)
        .map_err(|_| DecodeError::Schema { reason })
}

fn schema<T>(reason: &'static str) -> Result<T, DecodeError> {
    Err(DecodeError::Schema { reason })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_logic_classical::tagged::{Formula, Sequent, pack};

    fn empty() -> Checked {
        Checked::check(Arena::new(vec![Word::ZERO; 4], Word::ZERO, vec![])).unwrap()
    }

    fn sample() -> Checked {
        pack(&[Sequent {
            premise: Formula::Literal {
                atom: 1,
                negative: false,
            },
            conclusion: Formula::Or {
                negative: true,
                children: vec![Formula::Literal {
                    atom: 2,
                    negative: false,
                }],
            },
        }])
        .unwrap()
    }

    #[test]
    fn exact_empty_bytes_match_the_formal_codec() {
        let expected = [
            0xa4, 0x65, b'$', b't', b'y', b'p', b'e', 0x78, 0x29, b'i', b'o', b'.', b'g', b'i',
            b't', b'h', b'u', b'b', b'.', b'i', b'm', b'b', b'r', b'e', b'm', b'.', b'n', b'u',
            b'c', b'l', b'e', b'u', b's', b'.', b'c', b'l', b'a', b's', b's', b'i', b'c', b'a',
            b'l', b'A', b'r', b'e', b'n', b'a', b'V', b'1', 0x65, b'r', b'o', b'o', b't', b's',
            0x80, 0x65, b'w', b'o', b'r', b'd', b's', 0x58, 0x20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x68, b'f', b'r', b'e',
            b'e', b'R', b'o', b'o', b't', 0x48, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let encoded = encode_checked(&empty()).unwrap();
        assert_eq!(encoded, expected);
        assert_eq!(decode_checked(&encoded).unwrap(), empty());
    }

    #[test]
    fn checked_syntax_round_trips() {
        let checked = sample();
        let encoded = encode_checked(&checked).unwrap();
        let decoded = decode_checked(&encoded).unwrap();
        assert_eq!(decoded, checked);
        assert_eq!(decoded.arena(), checked.arena());
    }

    #[test]
    fn intrusive_allocator_state_round_trips_exactly() {
        let root = Word::pointer(4, 0, false).unwrap();
        let small = Word::pointer(12, 0, false).unwrap();
        let checked = Checked::check(Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                root,
                root,
                Word::natural(1).unwrap(),
                small,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                small,
                small,
                Word::ZERO,
            ],
            root,
            vec![],
        ))
        .unwrap();

        let decoded = decode_checked(&encode_checked(&checked).unwrap()).unwrap();
        assert_eq!(decoded.arena(), checked.arena());
        assert_eq!(decoded.free_blocks(), checked.free_blocks());
    }

    #[test]
    fn malformed_schema_and_runtime_are_rejected() {
        let mut short_words = arena_value(empty().arena());
        let Value::Map(fields) = &mut short_words else {
            unreachable!()
        };
        fields[2].1 = Value::Bytes(vec![0; 24]);
        assert_value_rejected(&short_words);

        let mut partial_word = arena_value(empty().arena());
        let Value::Map(fields) = &mut partial_word else {
            unreachable!()
        };
        fields[2].1 = Value::Bytes(vec![0; 33]);
        assert_value_rejected(&partial_word);

        let mut bad_reserved_word = arena_value(empty().arena());
        let Value::Map(fields) = &mut bad_reserved_word else {
            unreachable!()
        };
        let Value::Bytes(words) = &mut fields[2].1 else {
            unreachable!()
        };
        words[7] = 1;
        assert_value_rejected(&bad_reserved_word);

        let mut unknown_field = arena_value(empty().arena());
        let Value::Map(fields) = &mut unknown_field else {
            unreachable!()
        };
        fields.push(field("extra", Value::Null));
        assert_value_rejected(&unknown_field);
    }

    #[test]
    fn zero_roots_wrong_order_and_trailing_bytes_are_rejected() {
        let zero_root = Value::Map(vec![
            field("premise", Value::Bytes(vec![0; 8])),
            field("conclusion", Value::Bytes(vec![0; 8])),
        ]);
        let mut value = arena_value(empty().arena());
        let Value::Map(fields) = &mut value else {
            unreachable!()
        };
        fields[1].1 = Value::Array(vec![zero_root]);
        assert_value_rejected(&value);

        let mut wrong_order = arena_value(empty().arena());
        let Value::Map(fields) = &mut wrong_order else {
            unreachable!()
        };
        fields.swap(0, 1);
        assert_value_rejected(&wrong_order);

        let mut trailing = encode_checked(&empty()).unwrap();
        trailing.push(0);
        assert!(matches!(
            decode_checked(&trailing),
            Err(DecodeError::TrailingBytes)
        ));
    }

    #[test]
    fn nonminimal_container_encoding_is_rejected() {
        let canonical = encode_checked(&empty()).unwrap();
        assert_eq!(canonical[0], 0xa4);
        let mut noncanonical = vec![0xb8, 0x04];
        noncanonical.extend_from_slice(&canonical[1..]);
        assert!(matches!(
            decode_checked(&noncanonical),
            Err(DecodeError::Noncanonical)
        ));
    }

    fn assert_value_rejected(value: &Value) {
        let mut encoded = Vec::new();
        covalence_lib_cbor::into_writer(value, &mut encoded).unwrap();
        assert!(decode_checked(&encoded).is_err());
    }
}
