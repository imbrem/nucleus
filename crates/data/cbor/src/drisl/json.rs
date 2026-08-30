//! `ATProto` JSON conventions for inspecting DRISL values.
//!
//! JSON is a debugging and transport representation, not a content-addressed
//! normal form. Byte strings use `{"$bytes":"..."}` and links use
//! `{"$link":"..."}`. DRISL bytes remain the only canonical representation.

use std::{collections::BTreeMap, str::FromStr};

use covalence_lib_cbor::ipld_core::cid::Cid as IpldCid;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_json::{
    Map as JsonMap, Number as JsonNumber, Value as JsonValue,
    base64::{
        DecodeError as Base64DecodeError, Engine as _,
        engine::general_purpose::{STANDARD, STANDARD_NO_PAD},
    },
};

use super::{Cid, CidError, Policy, Value};

const BYTES_KEY: &str = "$bytes";
const LINK_KEY: &str = "$link";

/// Failure to translate the non-canonical `ATProto` JSON representation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// Input was not valid JSON.
    #[snafu(display("could not parse ATProto JSON: {source}"))]
    Parse {
        /// Underlying JSON parser failure.
        source: covalence_lib_json::Error,
    },
    /// Debug JSON could not be emitted.
    #[snafu(display("could not write ATProto JSON: {source}"))]
    Write {
        /// Underlying JSON writer failure.
        source: covalence_lib_json::Error,
    },
    /// A JSON number was not a signed 64-bit integer.
    #[snafu(display("ATProto JSON numbers must be signed 64-bit integers"))]
    Integer,
    /// A `$bytes` wrapper did not contain valid standard Base64.
    #[snafu(display("invalid ATProto $bytes value: {source}"))]
    Base64 {
        /// Base64 decoding failure.
        source: Base64DecodeError,
    },
    /// A reserved wrapper did not have its required string value.
    #[snafu(display("ATProto {key} wrapper must contain exactly one string field"))]
    Wrapper {
        /// Reserved wrapper key.
        key: &'static str,
    },
    /// A textual link was not a syntactically valid CID.
    #[snafu(display("invalid ATProto $link CID: {source}"))]
    LinkText {
        /// General CID parser failure.
        source: covalence_lib_cbor::ipld_core::cid::Error,
    },
    /// A textual link was outside the fixed-width Nucleus CID family.
    #[snafu(display("invalid fixed-width ATProto $link CID: {source}"))]
    LinkFraming {
        /// Exact framing failure.
        source: CidError,
    },
    /// A link was outside the selected hash policy.
    #[snafu(display("ATProto $link hash is not accepted by this policy"))]
    RejectedLink,
    /// A fixed CID could not be represented by the IPLD CID library.
    #[snafu(display("fixed-width CID could not be rendered as an ATProto $link"))]
    LinkRepresentation,
    /// An ordinary map was indistinguishable from a JSON scalar wrapper.
    #[snafu(display("ordinary map is ambiguous with the reserved {key} JSON wrapper"))]
    AmbiguousMap {
        /// Colliding wrapper key.
        key: &'static str,
    },
}

/// Parses one `ATProto` JSON value under `policy`.
///
/// # Errors
///
/// Rejects malformed JSON, non-integer numbers, malformed byte/link wrappers,
/// and links outside the selected CID policy.
pub fn decode(policy: Policy, bytes: &[u8]) -> Result<Value, Error> {
    let value = covalence_lib_json::from_slice(bytes).map_err(|source| Error::Parse { source })?;
    from_value(policy, value)
}

/// Writes a human-readable `ATProto` JSON representation.
///
/// # Errors
///
/// Returns an error for the two ordinary singleton-map shapes that are
/// inherently ambiguous with the `$bytes` and `$link` scalar wrappers, or if
/// the JSON writer fails.
pub fn encode(value: &Value) -> Result<Vec<u8>, Error> {
    let value = to_value(value)?;
    covalence_lib_json::to_vec_pretty(&value).map_err(|source| Error::Write { source })
}

/// Converts a parsed JSON tree to the extensional DRISL value model.
///
/// # Errors
///
/// Rejects values outside the `ATProto` JSON conventions or selected link
/// policy.
pub fn from_value(policy: Policy, value: JsonValue) -> Result<Value, Error> {
    match value {
        JsonValue::Null => Ok(Value::Null),
        JsonValue::Bool(value) => Ok(Value::Bool(value)),
        JsonValue::Number(value) => signed_integer(&value).map(Value::Integer),
        JsonValue::String(value) => Ok(Value::Text(value)),
        JsonValue::Array(values) => values
            .into_iter()
            .map(|value| from_value(policy, value))
            .collect::<Result<Vec<_>, _>>()
            .map(Value::Array),
        JsonValue::Object(mut fields) if fields.len() == 1 && fields.contains_key(BYTES_KEY) => {
            let Some(JsonValue::String(encoded)) = fields.remove(BYTES_KEY) else {
                return Err(Error::Wrapper { key: BYTES_KEY });
            };
            decode_base64(&encoded).map(Value::Bytes)
        }
        JsonValue::Object(mut fields) if fields.len() == 1 && fields.contains_key(LINK_KEY) => {
            let Some(JsonValue::String(encoded)) = fields.remove(LINK_KEY) else {
                return Err(Error::Wrapper { key: LINK_KEY });
            };
            let parsed =
                IpldCid::from_str(&encoded).map_err(|source| Error::LinkText { source })?;
            let cid = Cid::parse_binary(&parsed.to_bytes())
                .map_err(|source| Error::LinkFraming { source })?;
            if policy.accepts(cid) {
                Ok(Value::Link(cid))
            } else {
                Err(Error::RejectedLink)
            }
        }
        JsonValue::Object(fields) => fields
            .into_iter()
            .map(|(key, value)| Ok((key, from_value(policy, value)?)))
            .collect::<Result<BTreeMap<_, _>, Error>>()
            .map(Value::Map),
    }
}

/// Converts a DRISL value to `ATProto`'s JSON tree representation.
///
/// # Errors
///
/// Rejects ordinary singleton maps that collide with the reserved byte/link
/// wrapper shapes.
pub fn to_value(value: &Value) -> Result<JsonValue, Error> {
    match value {
        Value::Null => Ok(JsonValue::Null),
        Value::Bool(value) => Ok(JsonValue::Bool(*value)),
        Value::Integer(value) => Ok(JsonValue::Number(JsonNumber::from(*value))),
        Value::Text(value) => Ok(JsonValue::String(value.clone())),
        Value::Bytes(value) => Ok(wrapper(BYTES_KEY, STANDARD_NO_PAD.encode(value))),
        Value::Link(cid) => {
            let cid = IpldCid::try_from(cid.binary().as_slice())
                .map_err(|_| Error::LinkRepresentation)?;
            Ok(wrapper(LINK_KEY, cid.to_string()))
        }
        Value::Array(values) => values
            .iter()
            .map(to_value)
            .collect::<Result<Vec<_>, _>>()
            .map(JsonValue::Array),
        Value::Map(fields) => {
            if fields.len() == 1 {
                if fields.contains_key(BYTES_KEY) {
                    return Err(Error::AmbiguousMap { key: BYTES_KEY });
                }
                if fields.contains_key(LINK_KEY) {
                    return Err(Error::AmbiguousMap { key: LINK_KEY });
                }
            }
            fields
                .iter()
                .map(|(key, value)| Ok((key.clone(), to_value(value)?)))
                .collect::<Result<JsonMap<_, _>, Error>>()
                .map(JsonValue::Object)
        }
    }
}

fn signed_integer(value: &JsonNumber) -> Result<i64, Error> {
    value.as_i64().ok_or(Error::Integer)
}

fn decode_base64(value: &str) -> Result<Vec<u8>, Error> {
    STANDARD
        .decode(value)
        .or_else(|_| STANDARD_NO_PAD.decode(value))
        .map_err(|source| Error::Base64 { source })
}

fn wrapper(key: &'static str, value: String) -> JsonValue {
    JsonValue::Object(JsonMap::from_iter([(
        key.to_owned(),
        JsonValue::String(value),
    )]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::drisl::{CidCodec, CidHash};

    #[test]
    fn byte_and_link_wrappers_round_trip() {
        let cid = Cid::new(CidCodec::Drisl, CidHash::Sha256, [0xa5; 32]);
        for value in [Value::Bytes(vec![0, 1, 2, 0xff]), Value::Link(cid)] {
            let encoded = encode(&value).unwrap();
            assert_eq!(decode(Policy::ATPROTO, &encoded).unwrap(), value);
        }
    }

    #[test]
    fn padded_and_unpadded_base64_are_accepted() {
        assert_eq!(
            decode(Policy::ATPROTO, br#"{"$bytes":"AQI="}"#).unwrap(),
            Value::Bytes(vec![1, 2])
        );
        assert_eq!(
            decode(Policy::ATPROTO, br#"{"$bytes":"AQI"}"#).unwrap(),
            Value::Bytes(vec![1, 2])
        );
    }

    #[test]
    fn floats_and_ambiguous_maps_are_rejected() {
        assert!(matches!(
            decode(Policy::ATPROTO, b"1.5"),
            Err(Error::Integer)
        ));
        let ambiguous = Value::Map(BTreeMap::from([(
            BYTES_KEY.to_owned(),
            Value::Text("AA".to_owned()),
        )]));
        assert!(matches!(
            encode(&ambiguous),
            Err(Error::AmbiguousMap { key: BYTES_KEY })
        ));
    }
}
