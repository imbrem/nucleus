use std::{error::Error as StdError, fmt};

use serde::{Deserialize, Serialize};

use crate::{
    ContextId, ExportId, ImportId, MetadataTarget, MetadataValue, NamespaceId, TermId,
    TrustedImportId,
};

const MAX_JSON_BYTES: usize = 1 << 20;
const MAX_COLUMNS: usize = 128;
const MAX_RESPONSE_BYTES: usize = 1 << 20;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MetadataReadSpec {
    target: MetadataTargetSpec,
    columns: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MetadataWriteSpec {
    target: MetadataTargetSpec,
    assignments: Vec<MetadataEntrySpec>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
enum MetadataTargetSpec {
    Node { id: i64 },
    Context { id: i64 },
    ContextMember { context: i64, term: i64 },
    Judgement { context: i64, term: i64 },
    ContextImplication { antecedent: i64, consequent: i64 },
    ContextUnion { left: i64, right: i64 },
    Namespace { id: i64 },
    NamespaceExport { namespace: i64, export: i64 },
    Import { id: i64 },
    TrustedImport { id: i64 },
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MetadataEntrySpec {
    column: String,
    value: MetadataValueSpec,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum MetadataValueSpec {
    Null,
    Integer { value: String },
    Real { value: String },
    Text { value: String },
    Blob { hex: String },
}

pub(crate) struct MetadataReadRequest {
    pub(crate) target: MetadataTarget,
    pub(crate) columns: Vec<String>,
}

pub(crate) struct MetadataWriteRequest {
    pub(crate) target: MetadataTarget,
    pub(crate) metadata: Vec<(String, MetadataValue)>,
}

pub(crate) fn parse_metadata_read_json(
    json: &str,
) -> Result<MetadataReadRequest, MetadataSpecError> {
    check_length(json)?;
    let spec: MetadataReadSpec = serde_json::from_str(json)?;
    check_count(spec.columns.len())?;
    Ok(MetadataReadRequest {
        target: spec.target.try_into()?,
        columns: spec.columns,
    })
}

pub(crate) fn parse_metadata_write_json(
    json: &str,
) -> Result<MetadataWriteRequest, MetadataSpecError> {
    check_length(json)?;
    let spec: MetadataWriteSpec = serde_json::from_str(json)?;
    check_count(spec.assignments.len())?;
    let metadata = spec
        .assignments
        .into_iter()
        .map(|entry| Ok((entry.column, entry.value.try_into()?)))
        .collect::<Result<_, MetadataSpecError>>()?;
    Ok(MetadataWriteRequest {
        target: spec.target.try_into()?,
        metadata,
    })
}

pub(crate) fn encode_metadata_values_json(
    values: Vec<MetadataValue>,
) -> Result<String, MetadataSpecError> {
    check_encoded_response_size(&values)?;
    let values = values
        .into_iter()
        .map(MetadataValueSpec::try_from)
        .collect::<Result<Vec<_>, _>>()?;
    let json = serde_json::to_string(&values)?;
    if json.len() > MAX_RESPONSE_BYTES {
        return Err(MetadataSpecError::ResponseTooLarge {
            length: json.len(),
            maximum: MAX_RESPONSE_BYTES,
        });
    }
    Ok(json)
}

fn check_encoded_response_size(values: &[MetadataValue]) -> Result<(), MetadataSpecError> {
    let mut length = 2usize;
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            length = length.saturating_add(1);
        }
        let value_length = match value {
            MetadataValue::Null => 15,
            MetadataValue::Integer(value) => 43usize.saturating_add(value.to_string().len()),
            MetadataValue::Real(value) if value.is_finite() => {
                40usize.saturating_add(value.to_string().len())
            }
            MetadataValue::Real(value) => {
                return Err(MetadataSpecError::InvalidReal(value.to_string()));
            }
            MetadataValue::Text(value) => 35usize.saturating_add(json_string_length(value)),
            MetadataValue::Blob(value) => 24usize.saturating_add(value.len().saturating_mul(2)),
        };
        length = length.saturating_add(value_length);
        if length > MAX_RESPONSE_BYTES {
            return Err(MetadataSpecError::ResponseTooLarge {
                length,
                maximum: MAX_RESPONSE_BYTES,
            });
        }
    }
    Ok(())
}

fn json_string_length(value: &str) -> usize {
    value.chars().fold(2usize, |length, character| {
        length.saturating_add(match character {
            '\u{0000}'..='\u{001f}' => 6,
            '"' | '\\' => 2,
            _ => character.len_utf8(),
        })
    })
}

fn check_length(json: &str) -> Result<(), MetadataSpecError> {
    if json.len() > MAX_JSON_BYTES {
        return Err(MetadataSpecError::TooLarge {
            length: json.len(),
            maximum: MAX_JSON_BYTES,
        });
    }
    Ok(())
}

fn check_count(count: usize) -> Result<(), MetadataSpecError> {
    if count > MAX_COLUMNS {
        return Err(MetadataSpecError::TooManyColumns {
            count,
            maximum: MAX_COLUMNS,
        });
    }
    Ok(())
}

impl TryFrom<MetadataTargetSpec> for MetadataTarget {
    type Error = MetadataSpecError;

    fn try_from(target: MetadataTargetSpec) -> Result<Self, Self::Error> {
        Ok(match target {
            MetadataTargetSpec::Node { id } => Self::Node(nonnegative(id)?),
            MetadataTargetSpec::Context { id } => {
                Self::Context(ContextId::from_i64(nonnegative(id)?))
            }
            MetadataTargetSpec::ContextMember { context, term } => Self::context_member(
                ContextId::from_i64(nonnegative(context)?),
                TermId::from_i64(nonnegative(term)?),
            ),
            MetadataTargetSpec::Judgement { context, term } => Self::judgement(
                ContextId::from_i64(nonnegative(context)?),
                TermId::from_i64(nonnegative(term)?),
            ),
            MetadataTargetSpec::ContextImplication {
                antecedent,
                consequent,
            } => Self::context_implication(
                ContextId::from_i64(nonnegative(antecedent)?),
                ContextId::from_i64(nonnegative(consequent)?),
            ),
            MetadataTargetSpec::ContextUnion { left, right } => Self::context_union(
                ContextId::from_i64(nonnegative(left)?),
                ContextId::from_i64(nonnegative(right)?),
            ),
            MetadataTargetSpec::Namespace { id } => {
                Self::namespace(NamespaceId::from_i64(nonnegative(id)?))
            }
            MetadataTargetSpec::NamespaceExport { namespace, export } => Self::namespace_export(
                NamespaceId::from_i64(nonnegative(namespace)?),
                ExportId::from_i64(nonnegative(export)?),
            ),
            MetadataTargetSpec::Import { id } => Self::import(ImportId::from_i64(nonnegative(id)?)),
            MetadataTargetSpec::TrustedImport { id } => {
                Self::trusted_import(TrustedImportId::from_i64(nonnegative(id)?))
            }
        })
    }
}

fn nonnegative(value: i64) -> Result<i64, MetadataSpecError> {
    if value < 0 {
        Err(MetadataSpecError::NegativeId(value))
    } else {
        Ok(value)
    }
}

impl TryFrom<MetadataValueSpec> for MetadataValue {
    type Error = MetadataSpecError;

    fn try_from(value: MetadataValueSpec) -> Result<Self, Self::Error> {
        match value {
            MetadataValueSpec::Null => Ok(Self::Null),
            MetadataValueSpec::Integer { value } => value
                .parse()
                .map(Self::Integer)
                .map_err(|_| MetadataSpecError::InvalidInteger(value)),
            MetadataValueSpec::Real { value } => value
                .parse()
                .map_err(|_| MetadataSpecError::InvalidReal(value.clone()))
                .and_then(|parsed: f64| {
                    if parsed.is_finite() {
                        Ok(Self::Real(parsed))
                    } else {
                        Err(MetadataSpecError::InvalidReal(value))
                    }
                }),
            MetadataValueSpec::Text { value } => Ok(Self::Text(value)),
            MetadataValueSpec::Blob { hex } => decode_hex(&hex).map(Self::Blob),
        }
    }
}

impl TryFrom<MetadataValue> for MetadataValueSpec {
    type Error = MetadataSpecError;

    fn try_from(value: MetadataValue) -> Result<Self, Self::Error> {
        Ok(match value {
            MetadataValue::Null => Self::Null,
            MetadataValue::Integer(value) => Self::Integer {
                value: value.to_string(),
            },
            MetadataValue::Real(value) if value.is_finite() => Self::Real {
                value: value.to_string(),
            },
            MetadataValue::Real(value) => {
                return Err(MetadataSpecError::InvalidReal(value.to_string()));
            }
            MetadataValue::Text(value) => Self::Text { value },
            MetadataValue::Blob(value) => Self::Blob {
                hex: encode_hex(&value),
            },
        })
    }
}

fn decode_hex(value: &str) -> Result<Vec<u8>, MetadataSpecError> {
    if !value.len().is_multiple_of(2) || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(MetadataSpecError::InvalidHex);
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let pair = std::str::from_utf8(pair).expect("ASCII hex");
            u8::from_str_radix(pair, 16).map_err(|_| MetadataSpecError::InvalidHex)
        })
        .collect()
}

fn encode_hex(value: &[u8]) -> String {
    use fmt::Write as _;

    value.iter().fold(
        String::with_capacity(value.len().saturating_mul(2)),
        |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to String cannot fail");
            output
        },
    )
}

#[derive(Debug)]
pub enum MetadataSpecError {
    Json(serde_json::Error),
    TooLarge { length: usize, maximum: usize },
    TooManyColumns { count: usize, maximum: usize },
    ResponseTooLarge { length: usize, maximum: usize },
    InvalidInteger(String),
    InvalidReal(String),
    InvalidHex,
    NegativeId(i64),
}

impl fmt::Display for MetadataSpecError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Json(error) => write!(formatter, "invalid metadata JSON: {error}"),
            Self::TooLarge { length, maximum } => {
                write!(
                    formatter,
                    "metadata JSON is {length} bytes; maximum is {maximum}"
                )
            }
            Self::TooManyColumns { count, maximum } => {
                write!(
                    formatter,
                    "metadata request has {count} columns; maximum is {maximum}"
                )
            }
            Self::ResponseTooLarge { length, maximum } => {
                write!(
                    formatter,
                    "metadata response is {length} bytes; maximum is {maximum}"
                )
            }
            Self::InvalidInteger(value) => {
                write!(formatter, "invalid i64 metadata value {value:?}")
            }
            Self::InvalidReal(value) => write!(formatter, "invalid f64 metadata value {value:?}"),
            Self::InvalidHex => formatter.write_str("metadata blob must be even-length ASCII hex"),
            Self::NegativeId(value) => {
                write!(
                    formatter,
                    "metadata target ID must be non-negative, got {value}"
                )
            }
        }
    }
}

impl StdError for MetadataSpecError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Json(error) => Some(error),
            _ => None,
        }
    }
}

impl From<serde_json::Error> for MetadataSpecError {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_json_maps_every_metadata_target_without_losing_coordinates() {
        let cases = [
            (r#"{"kind":"node","id":1}"#, MetadataTarget::Node(1)),
            (
                r#"{"kind":"context","id":2}"#,
                MetadataTarget::Context(ContextId::from_i64(2)),
            ),
            (
                r#"{"kind":"contextMember","context":3,"term":4}"#,
                MetadataTarget::context_member(ContextId::from_i64(3), TermId::from_i64(4)),
            ),
            (
                r#"{"kind":"judgement","context":5,"term":6}"#,
                MetadataTarget::judgement(ContextId::from_i64(5), TermId::from_i64(6)),
            ),
            (
                r#"{"kind":"contextImplication","antecedent":7,"consequent":8}"#,
                MetadataTarget::context_implication(ContextId::from_i64(7), ContextId::from_i64(8)),
            ),
            (
                r#"{"kind":"contextUnion","left":9,"right":10}"#,
                MetadataTarget::context_union(ContextId::from_i64(9), ContextId::from_i64(10)),
            ),
            (
                r#"{"kind":"namespace","id":11}"#,
                MetadataTarget::namespace(NamespaceId::from_i64(11)),
            ),
            (
                r#"{"kind":"namespaceExport","namespace":12,"export":13}"#,
                MetadataTarget::namespace_export(NamespaceId::from_i64(12), ExportId::from_i64(13)),
            ),
            (
                r#"{"kind":"import","id":14}"#,
                MetadataTarget::import(ImportId::from_i64(14)),
            ),
            (
                r#"{"kind":"trustedImport","id":15}"#,
                MetadataTarget::trusted_import(TrustedImportId::from_i64(15)),
            ),
        ];
        for (target, expected) in cases {
            let request = format!(r#"{{"target":{target},"columns":[]}}"#);
            assert_eq!(parse_metadata_read_json(&request).unwrap().target, expected);
        }
    }

    #[test]
    fn metadata_values_use_lossless_strings_and_explicit_blob_hex() {
        let request = parse_metadata_write_json(
            r#"{"target":{"kind":"node","id":1},"assignments":[
                {"column":"n","value":{"kind":"null"}},
                {"column":"i","value":{"kind":"integer","value":"-9223372036854775808"}},
                {"column":"r","value":{"kind":"real","value":"1.25"}},
                {"column":"t","value":{"kind":"text","value":"hello"}},
                {"column":"b","value":{"kind":"blob","hex":"00Ff"}}
            ]}"#,
        )
        .unwrap();
        assert!(matches!(request.metadata[0].1, MetadataValue::Null));
        assert_eq!(request.metadata[1].1, MetadataValue::Integer(i64::MIN));
        assert_eq!(request.metadata[2].1, MetadataValue::Real(1.25));
        assert_eq!(
            request.metadata[3].1,
            MetadataValue::Text("hello".to_owned())
        );
        assert_eq!(request.metadata[4].1, MetadataValue::Blob(vec![0, 255]));
        assert!(matches!(
            parse_metadata_write_json(
                r#"{"target":{"kind":"node","id":1},"assignments":[{"column":"r","value":{"kind":"real","value":"NaN"}}]}"#,
            ),
            Err(MetadataSpecError::InvalidReal(_))
        ));
        assert!(matches!(
            parse_metadata_read_json(r#"{"target":{"kind":"node","id":-1},"columns":[]}"#),
            Err(MetadataSpecError::NegativeId(-1))
        ));
        assert!(matches!(
            encode_metadata_values_json(vec![MetadataValue::Blob(vec![0; MAX_RESPONSE_BYTES])]),
            Err(MetadataSpecError::ResponseTooLarge { .. })
        ));
    }
}
