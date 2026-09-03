//! Wire codec for checked classical syntax.
//!
//! The wire object contains a canonical dense snapshot of 32-bit words and
//! roots. Decoding validates syntax but creates no theorem fact.

use std::collections::BTreeMap;

use covalence_data_cbor::drisl::{self, Policy, Value};
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_classical::{Checked, RuntimeError};

/// Discriminator for the version-two classical arena object.
pub const TYPE_NAME: &str = "io.github.imbrem.nucleus.classicalArenaV2";

const WORD_BYTES: usize = 4;
const RESERVED_BYTES: usize = 4 * WORD_BYTES;
type Snapshot = (Vec<u32>, Vec<(u32, u32)>);

/// Failure to decode and validate a classical snapshot.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DecodeError {
    /// The bytes are not one complete canonical `ATProto` DRISL item.
    #[snafu(display("could not decode classical DRISL: {source}"))]
    Drisl {
        /// Reusable profile/canonicality failure.
        source: drisl::DecodeError,
    },
    /// The data item does not have the exact closed record shape.
    #[snafu(display("invalid classical CBOR schema: {reason}"))]
    Schema {
        /// Rejected schema invariant.
        reason: &'static str,
    },
    /// The snapshot fails its ownership or syntax checks.
    #[snafu(display("invalid classical CBOR snapshot: {source}"))]
    Runtime {
        /// Snapshot validation failure.
        source: RuntimeError,
    },
}

/// Failure to encode checked classical syntax.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("could not encode classical CBOR: {source}"))]
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
    let (words, roots) = snapshot_from_value(&value)?;
    Checked::from_snapshot(words, roots).context(RuntimeSnafu)
}

/// Encodes checked syntax as deterministic version-two DRISL bytes.
///
/// # Errors
///
/// Returns an error only if the reusable DRISL encoder rejects the value.
pub fn encode_checked(checked: &Checked) -> Result<Vec<u8>, EncodeError> {
    let (words, roots) = checked.snapshot();
    drisl::encode(Policy::ATPROTO, &snapshot_value(&words, &roots)).context(EncodeSnafu)
}

fn snapshot_value(words: &[u32], roots: &[(u32, u32)]) -> Value {
    let mut word_bytes = Vec::new();
    for word in words.iter().copied() {
        word_bytes.extend_from_slice(&word.to_be_bytes());
    }
    let roots = roots
        .iter()
        .map(|(premise, conclusion)| {
            Value::Map(BTreeMap::from([
                field("premise", Value::Bytes(premise.to_be_bytes().to_vec())),
                field(
                    "conclusion",
                    Value::Bytes(conclusion.to_be_bytes().to_vec()),
                ),
            ]))
        })
        .collect();

    Value::Map(BTreeMap::from([
        field("$type", Value::Text(TYPE_NAME.to_owned())),
        field("roots", Value::Array(roots)),
        field("words", Value::Bytes(word_bytes)),
    ]))
}

fn field(name: &str, value: Value) -> (String, Value) {
    (name.to_owned(), value)
}

fn snapshot_from_value(value: &Value) -> Result<Snapshot, DecodeError> {
    let Value::Map(fields) = value else {
        return schema("top-level item must be a map");
    };
    if fields.len() != 3 {
        return schema("top-level map must have exactly three fields");
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
        return schema("words must contain at least four complete 32-bit words");
    }
    let mut words = Vec::with_capacity(word_bytes.len() / WORD_BYTES);
    for bytes in word_bytes.chunks_exact(WORD_BYTES) {
        let Ok(bytes) = <&[u8; WORD_BYTES]>::try_from(bytes) else {
            return schema("words must contain complete 32-bit words");
        };
        words.push(u32::from_be_bytes(*bytes));
    }
    Ok((words, roots))
}

fn root_from_value(value: &Value) -> Result<(u32, u32), DecodeError> {
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
    let premise = raw_word(premise_bytes, "premise must be four bytes")?;
    let conclusion = raw_word(conclusion_bytes, "conclusion must be four bytes")?;
    Ok((premise, conclusion))
}

fn raw_word(bytes: &[u8], reason: &'static str) -> Result<u32, DecodeError> {
    bytes
        .try_into()
        .map(u32::from_be_bytes)
        .map_err(|_| DecodeError::Schema { reason })
}

fn schema<T>(reason: &'static str) -> Result<T, DecodeError> {
    Err(DecodeError::Schema { reason })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_logic_classical::{Formula, Sequent, pack};

    fn empty() -> Checked {
        pack(&[]).unwrap()
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
                atom: (1_u32 << 29) - 1,
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
            0xa3, 0x65, b'$', b't', b'y', b'p', b'e', 0x78, 0x29, b'i', b'o', b'.', b'g', b'i',
            b't', b'h', b'u', b'b', b'.', b'i', b'm', b'b', b'r', b'e', b'm', b'.', b'n', b'u',
            b'c', b'l', b'e', b'u', b's', b'.', b'c', b'l', b'a', b's', b's', b'i', b'c', b'a',
            b'l', b'A', b'r', b'e', b'n', b'a', b'V', b'2', 0x65, b'r', b'o', b'o', b't', b's',
            0x80, 0x65, b'w', b'o', b'r', b'd', b's', 0x50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
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
        assert_eq!(decoded.snapshot(), checked.snapshot());
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
        assert_eq!(decoded.decode_sequents().unwrap(), sequents);
        assert_eq!(decoded.snapshot(), checked.snapshot());
        assert_eq!(encode_checked(&decoded).unwrap(), encoded);
    }

    #[test]
    fn malformed_schema_and_runtime_are_rejected() {
        let (words, roots) = empty().snapshot();
        let mut short_words = snapshot_value(&words, &roots);
        let Value::Map(fields) = &mut short_words else {
            unreachable!()
        };
        *fields.get_mut("words").unwrap() = Value::Bytes(vec![0; 12]);
        assert_value_rejected(&short_words);

        let mut partial_word = snapshot_value(&words, &roots);
        let Value::Map(fields) = &mut partial_word else {
            unreachable!()
        };
        *fields.get_mut("words").unwrap() = Value::Bytes(vec![0; 17]);
        assert_value_rejected(&partial_word);

        let mut noncanonical = snapshot_value(&words, &roots);
        let Value::Map(fields) = &mut noncanonical else {
            unreachable!()
        };
        let Value::Bytes(word_bytes) = fields.get_mut("words").unwrap() else {
            unreachable!()
        };
        word_bytes.extend_from_slice(&0_u32.to_be_bytes());
        assert_value_rejected(&noncanonical);

        let mut bad_reserved_word = snapshot_value(&words, &roots);
        let Value::Map(fields) = &mut bad_reserved_word else {
            unreachable!()
        };
        let Value::Bytes(word_bytes) = fields.get_mut("words").unwrap() else {
            unreachable!()
        };
        word_bytes[3] = 1;
        assert_value_rejected(&bad_reserved_word);

        let mut unknown_field = snapshot_value(&words, &roots);
        let Value::Map(fields) = &mut unknown_field else {
            unreachable!()
        };
        fields.insert("extra".to_owned(), Value::Null);
        assert_value_rejected(&unknown_field);
    }

    #[test]
    fn zero_roots_and_invalid_drisl_are_rejected() {
        let zero_root = Value::Map(BTreeMap::from([
            field("premise", Value::Bytes(vec![0; 4])),
            field("conclusion", Value::Bytes(vec![0; 4])),
        ]));
        let (words, roots) = empty().snapshot();
        let mut value = snapshot_value(&words, &roots);
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
        assert_eq!(canonical[0], 0xa3);
        let mut noncanonical = vec![0xb8, 0x03];
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
