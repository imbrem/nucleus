//! Semantic wire codec for checked classical syntax.
//!
//! The wire records formulas and sequents. Allocator metadata remains private.

use std::collections::BTreeMap;

use covalence_data_cbor::drisl::{self, Policy, Value};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_classical::{
    Checked, Formula, FormulaKind, FormulaView, RuntimeError, Sequent,
};

/// Discriminator for the semantic classical-arena object.
pub const TYPE_NAME: &str = "io.github.imbrem.nucleus.classicalArenaV3";

const MAX_SEQUENTS: usize = 500_000;
const MAX_TOKENS: usize = 1_000_000;

/// Failure to decode semantic classical syntax.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DecodeError {
    /// The bytes are not one canonical DRISL item.
    #[snafu(context(suffix(DecodeSnafu)))]
    #[snafu(display("could not decode classical DRISL: {source}"))]
    Drisl { source: drisl::DecodeError },
    /// The item does not have the closed semantic schema.
    #[snafu(display("invalid classical CBOR schema: {reason}"))]
    Schema { reason: &'static str },
    /// The decoded syntax cannot be represented by the runtime.
    #[snafu(context(suffix(DecodeSnafu)))]
    #[snafu(display("invalid classical CBOR arena: {source}"))]
    Runtime { source: RuntimeError },
}

/// Failure to encode checked classical syntax.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum EncodeError {
    /// The checked value could not be read.
    #[snafu(context(suffix(EncodeSnafu)))]
    #[snafu(display("could not read checked classical syntax: {source}"))]
    Runtime { source: RuntimeError },
    /// The semantic object exceeds the codec policy.
    #[snafu(display("classical semantic encoding exceeds its resource bound"))]
    ResourceBound,
    /// DRISL rejected the semantic value.
    #[snafu(context(suffix(EncodeSnafu)))]
    #[snafu(display("could not encode classical CBOR: {source}"))]
    Drisl { source: drisl::EncodeError },
}

/// Decodes canonical semantic DRISL and packs its syntax.
///
/// # Errors
///
/// Returns an error for invalid DRISL, schema, resource use, or syntax.
pub fn decode_checked(bytes: &[u8]) -> Result<Checked, DecodeError> {
    let value =
        drisl::decode(Policy::ATPROTO, bytes).map_err(|source| DecodeError::Drisl { source })?;
    Checked::from_sequents(&decode_arena(&value)?).map_err(|source| DecodeError::Runtime { source })
}

/// Encodes checked syntax as canonical semantic DRISL.
///
/// # Errors
///
/// Returns an error if syntax cannot be read, is too large, or encoding fails.
pub fn encode_checked(checked: &Checked) -> Result<Vec<u8>, EncodeError> {
    drisl::encode(Policy::ATPROTO, &encode_checked_value(checked)?)
        .map_err(|source| EncodeError::Drisl { source })
}

fn encode_checked_value(checked: &Checked) -> Result<Value, EncodeError> {
    if checked.len() > MAX_SEQUENTS {
        return Err(EncodeError::ResourceBound);
    }
    let mut budget = MAX_TOKENS;
    let mut sequents = Vec::with_capacity(checked.len());
    for index in 0..checked.len() {
        let view = checked.view(index).ok_or(EncodeError::Runtime {
            source: RuntimeError::InvalidArena,
        })?;
        sequents.push(Value::Map(BTreeMap::from([
            entry("premise", encode_view(view.premise, &mut budget)?),
            entry("conclusion", encode_view(view.conclusion, &mut budget)?),
        ])));
    }
    Ok(Value::Map(BTreeMap::from([
        entry("$type", Value::Text(TYPE_NAME.to_owned())),
        entry("sequents", Value::Array(sequents)),
    ])))
}

fn encode_view(view: FormulaView<'_>, budget: &mut usize) -> Result<Value, EncodeError> {
    let mut pending = vec![view];
    let mut tokens = Vec::new();
    while let Some(view) = pending.pop() {
        *budget = budget.checked_sub(1).ok_or(EncodeError::ResourceBound)?;
        let kind = match view.kind() {
            FormulaKind::And => "and",
            FormulaKind::Or => "or",
            FormulaKind::Sat => "sat",
            FormulaKind::Literal => "literal",
        };
        let extra = if let Some(atom) = view.atom() {
            entry("atom", Value::Integer(i64::from(atom)))
        } else {
            for index in (0..view.len()).rev() {
                pending.push(view.child(index).ok_or(EncodeError::Runtime {
                    source: RuntimeError::InvalidArena,
                })?);
            }
            let arity = i64::try_from(view.len()).map_err(|_| EncodeError::ResourceBound)?;
            entry("arity", Value::Integer(arity))
        };
        tokens.push(Value::Map(BTreeMap::from([
            entry("kind", Value::Text(kind.to_owned())),
            entry("negative", Value::Bool(view.is_negative())),
            extra,
        ])));
    }
    Ok(Value::Array(tokens))
}

fn entry(name: &str, value: Value) -> (String, Value) {
    (name.to_owned(), value)
}

#[cfg(test)]
fn encode_arena(sequents: &[Sequent]) -> Result<Value, EncodeError> {
    if sequents.len() > MAX_SEQUENTS {
        return Err(EncodeError::ResourceBound);
    }
    let mut budget = MAX_TOKENS;
    let mut values = Vec::with_capacity(sequents.len());
    for sequent in sequents {
        values.push(Value::Map(BTreeMap::from([
            entry("premise", encode_formula(&sequent.premise, &mut budget)?),
            entry(
                "conclusion",
                encode_formula(&sequent.conclusion, &mut budget)?,
            ),
        ])));
    }
    Ok(Value::Map(BTreeMap::from([
        entry("$type", Value::Text(TYPE_NAME.to_owned())),
        entry("sequents", Value::Array(values)),
    ])))
}

#[cfg(test)]
fn encode_formula(formula: &Formula, budget: &mut usize) -> Result<Value, EncodeError> {
    let mut pending = vec![formula];
    let mut tokens = Vec::new();
    while let Some(formula) = pending.pop() {
        *budget = budget.checked_sub(1).ok_or(EncodeError::ResourceBound)?;
        let (kind, negative, extra) = match formula {
            Formula::Literal { atom, negative } => (
                "literal",
                *negative,
                entry("atom", Value::Integer(i64::from(*atom))),
            ),
            Formula::And { negative, children }
            | Formula::Or { negative, children }
            | Formula::Sat { negative, children } => {
                let kind = match formula {
                    Formula::And { .. } => "and",
                    Formula::Or { .. } => "or",
                    Formula::Sat { .. } => "sat",
                    Formula::Literal { .. } => unreachable!(),
                };
                pending.extend(children.iter().rev());
                let arity =
                    i64::try_from(children.len()).map_err(|_| EncodeError::ResourceBound)?;
                (kind, *negative, entry("arity", Value::Integer(arity)))
            }
        };
        tokens.push(Value::Map(BTreeMap::from([
            entry("kind", Value::Text(kind.to_owned())),
            entry("negative", Value::Bool(negative)),
            extra,
        ])));
    }
    Ok(Value::Array(tokens))
}

fn decode_arena(value: &Value) -> Result<Vec<Sequent>, DecodeError> {
    let fields = exact_map(value, 2, "top-level item must be a two-field map")?;
    if fields.get("$type") != Some(&Value::Text(TYPE_NAME.to_owned())) {
        return schema("wrong classical-arena discriminator");
    }
    let Some(Value::Array(values)) = fields.get("sequents") else {
        return schema("sequents must be an array");
    };
    if values.len() > MAX_SEQUENTS {
        return schema("too many sequents");
    }
    let mut budget = MAX_TOKENS;
    let mut sequents = Vec::with_capacity(values.len());
    for value in values {
        let fields = exact_map(value, 2, "each sequent must be a two-field map")?;
        sequents.push(Sequent {
            premise: decode_formula(required(fields, "premise")?, &mut budget)?,
            conclusion: decode_formula(required(fields, "conclusion")?, &mut budget)?,
        });
    }
    Ok(sequents)
}

#[derive(Clone, Copy)]
enum Kind {
    And,
    Or,
    Sat,
}

struct Frame {
    kind: Kind,
    negative: bool,
    remaining: usize,
    children: Vec<Formula>,
}

fn decode_formula(value: &Value, budget: &mut usize) -> Result<Formula, DecodeError> {
    let Value::Array(tokens) = value else {
        return schema("formula must be an array of preorder tokens");
    };
    *budget = budget
        .checked_sub(tokens.len())
        .ok_or(DecodeError::Schema {
            reason: "formula token bound exceeded",
        })?;
    let mut stack: Vec<Frame> = Vec::new();
    let mut root = None;
    for token in tokens {
        if root.is_some() {
            return schema("formula has trailing tokens");
        }
        let fields = exact_map(token, 3, "formula token must be a three-field map")?;
        let Some(Value::Text(kind)) = fields.get("kind") else {
            return schema("formula kind must be text");
        };
        let Some(Value::Bool(negative)) = fields.get("negative") else {
            return schema("formula polarity must be boolean");
        };
        let mut formula = if kind == "literal" {
            let Some(Value::Integer(atom)) = fields.get("atom") else {
                return schema("literal atom must be an integer");
            };
            Formula::Literal {
                atom: u32::try_from(*atom).map_err(|_| DecodeError::Schema {
                    reason: "literal atom must fit u32",
                })?,
                negative: *negative,
            }
        } else {
            let kind = match kind.as_str() {
                "and" => Kind::And,
                "or" => Kind::Or,
                "sat" => Kind::Sat,
                _ => return schema("unknown formula constructor"),
            };
            let Some(Value::Integer(arity)) = fields.get("arity") else {
                return schema("formula arity must be an integer");
            };
            let arity = usize::try_from(*arity).map_err(|_| DecodeError::Schema {
                reason: "formula arity must be nonnegative",
            })?;
            if arity > tokens.len() {
                return schema("formula arity exceeds its token array");
            }
            if arity != 0 {
                stack.push(Frame {
                    kind,
                    negative: *negative,
                    remaining: arity,
                    children: Vec::with_capacity(arity),
                });
                continue;
            }
            node(kind, *negative, Vec::new())
        };
        loop {
            let Some(frame) = stack.last_mut() else {
                root = Some(formula);
                break;
            };
            frame.children.push(formula);
            frame.remaining -= 1;
            if frame.remaining != 0 {
                break;
            }
            let frame = stack.pop().ok_or(DecodeError::Schema {
                reason: "invalid formula stack",
            })?;
            formula = node(frame.kind, frame.negative, frame.children);
        }
    }
    if !stack.is_empty() {
        return schema("formula is missing children");
    }
    root.ok_or(DecodeError::Schema {
        reason: "formula is empty",
    })
}

fn node(kind: Kind, negative: bool, children: Vec<Formula>) -> Formula {
    match kind {
        Kind::And => Formula::And { negative, children },
        Kind::Or => Formula::Or { negative, children },
        Kind::Sat => Formula::Sat { negative, children },
    }
}

fn exact_map<'a>(
    value: &'a Value,
    len: usize,
    reason: &'static str,
) -> Result<&'a BTreeMap<String, Value>, DecodeError> {
    let Value::Map(fields) = value else {
        return schema(reason);
    };
    if fields.len() != len {
        return schema(reason);
    }
    Ok(fields)
}

fn required<'a>(
    fields: &'a BTreeMap<String, Value>,
    name: &'static str,
) -> Result<&'a Value, DecodeError> {
    fields.get(name).ok_or(DecodeError::Schema {
        reason: "required field is missing",
    })
}

fn schema<T>(reason: &'static str) -> Result<T, DecodeError> {
    Err(DecodeError::Schema { reason })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(atom: u32) -> Formula {
        Formula::Literal {
            atom,
            negative: false,
        }
    }
    fn empty() -> Checked {
        Checked::from_sequents(&[]).unwrap()
    }
    fn sample() -> Checked {
        Checked::from_sequents(&[Sequent {
            premise: lit(1),
            conclusion: Formula::Or {
                negative: true,
                children: vec![lit(2)],
            },
        }])
        .unwrap()
    }

    #[test]
    fn semantic_round_trip_is_stable() {
        let checked = sample();
        let encoded = encode_checked(&checked).unwrap();
        assert!(String::from_utf8_lossy(&encoded).contains("classicalArenaV3"));
        let decoded = decode_checked(&encoded).unwrap();
        assert_eq!(
            decoded.decode_sequents().unwrap(),
            checked.decode_sequents().unwrap()
        );
        assert_eq!(encode_checked(&decoded).unwrap(), encoded);
    }

    #[test]
    fn constructors_polarities_and_empty_nodes_round_trip() {
        let leaves = vec![
            lit(0),
            Formula::Literal {
                atom: (1 << 29) - 1,
                negative: true,
            },
        ];
        let mut formulas = leaves.clone();
        for negative in [false, true] {
            formulas.push(Formula::And {
                negative,
                children: Vec::new(),
            });
            formulas.push(Formula::Or {
                negative,
                children: leaves.clone(),
            });
            formulas.push(Formula::Sat {
                negative,
                children: leaves.clone(),
            });
        }
        let sequents = formulas
            .iter()
            .zip(formulas.iter().rev())
            .map(|(a, b)| Sequent {
                premise: a.clone(),
                conclusion: b.clone(),
            })
            .collect::<Vec<_>>();
        let decoded =
            decode_checked(&encode_checked(&Checked::from_sequents(&sequents).unwrap()).unwrap())
                .unwrap();
        assert_eq!(decoded.decode_sequents().unwrap(), sequents);
    }

    #[test]
    fn closed_schema_and_incomplete_formula_are_rejected() {
        let mut value = encode_arena(&[]).unwrap();
        let Value::Map(fields) = &mut value else {
            unreachable!()
        };
        fields.insert("words".to_owned(), Value::Bytes(vec![0; 16]));
        reject(&value);

        let bad = Value::Array(vec![Value::Map(BTreeMap::from([
            entry("kind", Value::Text("and".to_owned())),
            entry("negative", Value::Bool(false)),
            entry("arity", Value::Integer(1)),
        ]))]);
        let value = Value::Map(BTreeMap::from([
            entry("$type", Value::Text(TYPE_NAME.to_owned())),
            entry(
                "sequents",
                Value::Array(vec![Value::Map(BTreeMap::from([
                    entry("premise", bad),
                    entry("conclusion", encode_formula(&lit(1), &mut 2).unwrap()),
                ]))]),
            ),
        ]));
        reject(&value);
    }

    #[test]
    fn deep_formula_has_flat_wire_shape() {
        let mut formula = lit(1);
        for _ in 0..10_000 {
            formula = Formula::And {
                negative: false,
                children: vec![formula],
            };
        }
        let checked = Checked::from_sequents(&[Sequent {
            premise: formula,
            conclusion: lit(2),
        }])
        .unwrap();
        let decoded = decode_checked(&encode_checked(&checked).unwrap()).unwrap();
        assert_eq!(decoded, checked);
    }

    #[test]
    fn invalid_and_noncanonical_drisl_are_rejected() {
        let mut trailing = encode_checked(&empty()).unwrap();
        trailing.push(0);
        assert!(matches!(
            decode_checked(&trailing),
            Err(DecodeError::Drisl { .. })
        ));
        let canonical = encode_checked(&empty()).unwrap();
        assert_eq!(canonical[0], 0xa2);
        let mut noncanonical = vec![0xb8, 0x02];
        noncanonical.extend_from_slice(&canonical[1..]);
        assert!(matches!(
            decode_checked(&noncanonical),
            Err(DecodeError::Drisl { .. })
        ));
    }

    fn reject(value: &Value) {
        let bytes = drisl::encode(Policy::ATPROTO, value).unwrap();
        assert!(decode_checked(&bytes).is_err());
    }
}
