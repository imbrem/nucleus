//! Untrusted wire codec for checked tagged-classical arenas.
//!
//! The wire object is a closed, link-free ATProto-style record. Machine words
//! and roots are exact eight-byte big-endian blobs. Decoding validates the
//! complete arena and returns checked syntax only; it cannot create a theorem.

use std::collections::BTreeMap;

use covalence_data_cbor::drisl::{self, Policy, Value};
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
    /// The bytes are not one complete canonical `ATProto` DRISL item.
    #[snafu(display("could not decode tagged-classical DRISL: {source}"))]
    Drisl {
        /// Reusable profile/canonicality failure.
        source: drisl::DecodeError,
    },
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
}

/// Failure to encode a checked tagged-classical arena.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("could not encode tagged-classical CBOR: {source}"))]
pub struct EncodeError {
    /// Underlying reusable DRISL encoder failure.
    source: drisl::EncodeError,
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
    let value = drisl::decode(Policy::ATPROTO, bytes).context(DrislSnafu)?;
    let arena = arena_from_value(&value)?;
    Checked::check(arena).context(RuntimeSnafu)
}

/// Encodes checked syntax as the unique deterministic version-one DRISL bytes.
///
/// # Errors
///
/// Returns an error only if the reusable DRISL encoder rejects the value.
pub fn encode_checked(checked: &Checked) -> Result<Vec<u8>, EncodeError> {
    drisl::encode(Policy::ATPROTO, &arena_value(checked.arena())).context(EncodeSnafu)
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
            Value::Map(BTreeMap::from([
                field(
                    "premise",
                    Value::Bytes(premise.word().raw().to_be_bytes().to_vec()),
                ),
                field(
                    "conclusion",
                    Value::Bytes(conclusion.word().raw().to_be_bytes().to_vec()),
                ),
            ]))
        })
        .collect();

    Value::Map(BTreeMap::from([
        field("$type", Value::Text(TYPE_NAME.to_owned())),
        field("roots", Value::Array(roots)),
        field("words", Value::Bytes(words)),
        field(
            "freeRoot",
            Value::Bytes(arena.free_root().raw().to_be_bytes().to_vec()),
        ),
    ]))
}

fn field(name: &str, value: Value) -> (String, Value) {
    (name.to_owned(), value)
}

fn arena_from_value(value: &Value) -> Result<Arena, DecodeError> {
    let Value::Map(fields) = value else {
        return schema("top-level item must be a map");
    };
    if fields.len() != 4 {
        return schema("top-level map must have exactly four fields");
    }
    if fields.get("$type") != Some(&Value::Text(TYPE_NAME.to_owned())) {
        return schema("$type must be the exact classical-arena discriminator");
    }
    let Some(Value::Array(root_values)) = fields.get("roots") else {
        return schema("roots must be an array");
    };
    let mut roots = Vec::with_capacity(root_values.len());
    for root in root_values {
        roots.push(root_from_value(root)?);
    }

    let Some(Value::Bytes(word_bytes)) = fields.get("words") else {
        return schema("words must be a byte string");
    };
    if word_bytes.len() < RESERVED_BYTES || !word_bytes.len().is_multiple_of(WORD_BYTES) {
        return schema("words must contain at least four complete 64-bit words");
    }
    let mut words = Vec::with_capacity(word_bytes.len() / WORD_BYTES);
    for bytes in word_bytes.chunks_exact(WORD_BYTES) {
        let Ok(bytes) = <&[u8; WORD_BYTES]>::try_from(bytes) else {
            return schema("words must contain complete 64-bit words");
        };
        words.push(Word::from_raw(u64::from_be_bytes(*bytes)));
    }

    let Some(Value::Bytes(free_root_bytes)) = fields.get("freeRoot") else {
        return schema("freeRoot must be a byte string");
    };
    let free_root = Word::from_raw(raw_word(free_root_bytes, "freeRoot must be eight bytes")?);

    Ok(Arena::new(words, free_root, roots))
}

fn root_from_value(value: &Value) -> Result<(Ref, Ref), DecodeError> {
    let Value::Map(fields) = value else {
        return schema("each root must be a map");
    };
    if fields.len() != 2 {
        return schema("each root must have exactly two fields");
    }
    let Some(Value::Bytes(premise_bytes)) = fields.get("premise") else {
        return schema("premise must be a byte string");
    };
    let Some(Value::Bytes(conclusion_bytes)) = fields.get("conclusion") else {
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

    fn formula_corpus() -> Vec<Formula> {
        let literals = vec![
            Formula::Literal {
                atom: 0,
                negative: false,
            },
            Formula::Literal {
                atom: 1,
                negative: true,
            },
            Formula::Literal {
                atom: (1_u64 << 60) - 1,
                negative: false,
            },
        ];
        let mut formulas = literals.clone();
        for negative in [false, true] {
            formulas.push(Formula::And {
                negative,
                children: Vec::new(),
            });
            formulas.push(Formula::Or {
                negative,
                children: literals.clone(),
            });
            formulas.push(Formula::Sat {
                negative,
                children: vec![
                    Formula::And {
                        negative: !negative,
                        children: literals.clone(),
                    },
                    Formula::Or {
                        negative,
                        children: literals.clone(),
                    },
                ],
            });
        }
        formulas
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
    fn every_constructor_polarity_and_root_pair_round_trips_stably() {
        let formulas = formula_corpus();
        let sequents = formulas
            .iter()
            .enumerate()
            .flat_map(|(left_index, premise)| {
                formulas
                    .iter()
                    .enumerate()
                    .map(move |(right_index, conclusion)| Sequent {
                        premise: if left_index.is_multiple_of(2) {
                            premise.clone()
                        } else {
                            premise.clone().negated()
                        },
                        conclusion: if right_index.is_multiple_of(2) {
                            conclusion.clone()
                        } else {
                            conclusion.clone().negated()
                        },
                    })
            })
            .collect::<Vec<_>>();
        let checked = pack(&sequents).unwrap();
        let encoded = encode_checked(&checked).unwrap();
        let decoded = decode_checked(&encoded).unwrap();
        assert_eq!(decoded.sequents(), sequents);
        assert_eq!(decoded.arena(), checked.arena());
        assert_eq!(encode_checked(&decoded).unwrap(), encoded);
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
        *fields.get_mut("words").unwrap() = Value::Bytes(vec![0; 24]);
        assert_value_rejected(&short_words);

        let mut partial_word = arena_value(empty().arena());
        let Value::Map(fields) = &mut partial_word else {
            unreachable!()
        };
        *fields.get_mut("words").unwrap() = Value::Bytes(vec![0; 33]);
        assert_value_rejected(&partial_word);

        let mut bad_reserved_word = arena_value(empty().arena());
        let Value::Map(fields) = &mut bad_reserved_word else {
            unreachable!()
        };
        let Value::Bytes(words) = fields.get_mut("words").unwrap() else {
            unreachable!()
        };
        words[7] = 1;
        assert_value_rejected(&bad_reserved_word);

        let mut unknown_field = arena_value(empty().arena());
        let Value::Map(fields) = &mut unknown_field else {
            unreachable!()
        };
        fields.insert("extra".to_owned(), Value::Null);
        assert_value_rejected(&unknown_field);
    }

    #[test]
    fn zero_roots_and_invalid_drisl_are_rejected() {
        let zero_root = Value::Map(BTreeMap::from([
            field("premise", Value::Bytes(vec![0; 8])),
            field("conclusion", Value::Bytes(vec![0; 8])),
        ]));
        let mut value = arena_value(empty().arena());
        let Value::Map(fields) = &mut value else {
            unreachable!()
        };
        *fields.get_mut("roots").unwrap() = Value::Array(vec![zero_root]);
        assert_value_rejected(&value);

        let mut trailing = encode_checked(&empty()).unwrap();
        trailing.push(0);
        assert!(matches!(
            decode_checked(&trailing),
            Err(DecodeError::Drisl { .. })
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
            Err(DecodeError::Drisl { .. })
        ));
    }

    fn assert_value_rejected(value: &Value) {
        let encoded = drisl::encode(Policy::ATPROTO, value).unwrap();
        assert!(decode_checked(&encoded).is_err());
    }
}
