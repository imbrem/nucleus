//! Serde across the [`Json`] tree, and conversions to the ecosystem `Value`.
//!
//! Serialization walks the tree as it stands: [`Map`] keeps entries in key
//! order, so compact output is already in the sorted, whitespace-free shape
//! the rest of the project treats as "almost canonical". Deserialization is
//! where strictness that `serde_json` leaves to the caller lives: a repeated
//! object key is an error here, not a silent last-wins.

use std::{fmt, marker::PhantomData};

use covalence_lib_json::Number;
use covalence_lib_serde::de::{self, MapAccess, SeqAccess, Visitor};
use covalence_lib_serde::ser::{Serialize, SerializeMap, Serializer};

use crate::{Build, Entry, Index, Json, Map};

/// A parse failure: malformed JSON, or JSON this crate's strictness rejects.
pub use covalence_lib_json::Error as ParseError;

impl<I: Index> Serialize for Json<I> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Json::Null => serializer.serialize_unit(),
            Json::Bool(value) => serializer.serialize_bool(*value),
            Json::Number(value) => value.serialize(serializer),
            Json::String(value) => serializer.serialize_str(value),
            Json::Array(values) => serializer.collect_seq(values.iter()),
            Json::Object(map) => {
                let mut output = serializer.serialize_map(Some(map.len()))?;
                for entry in map {
                    output.serialize_entry(&*entry.key, &entry.value)?;
                }
                output.end()
            }
        }
    }
}

struct JsonVisitor<I>(PhantomData<I>);

impl<'de, I: Build> Visitor<'de> for JsonVisitor<I> {
    type Value = Json<I>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_unit<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(Json::Null)
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<Self::Value, E> {
        Ok(Json::Bool(value))
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<Self::Value, E> {
        Ok(Json::Number(value.into()))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
        Ok(Json::Number(value.into()))
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<Self::Value, E> {
        Number::from_f64(value)
            .map(Json::Number)
            .ok_or_else(|| E::custom("non-finite numbers are not JSON"))
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
        Ok(Json::String(I::str(value)))
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut values = Vec::with_capacity(access.size_hint().unwrap_or(0));
        while let Some(value) = access.next_element()? {
            values.push(value);
        }
        Ok(Json::Array(I::array(values)))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut entries = Vec::with_capacity(access.size_hint().unwrap_or(0));
        while let Some((key, value)) = access.next_entry::<String, Json<I>>()? {
            entries.push(Entry {
                key: I::str(&key),
                value,
            });
        }
        Map::from_entries(entries)
            .map(Json::Object)
            .map_err(de::Error::custom)
    }
}

impl<'de, I: Build> de::Deserialize<'de> for Json<I> {
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(JsonVisitor(PhantomData))
    }
}

/// Parses JSON text, strictly.
///
/// Strict RFC 8259 by way of `serde_json`, plus what this crate adds on top:
/// a duplicate object key is an error rather than a last-wins overwrite.
///
/// # Errors
///
/// Malformed JSON, trailing input, non-finite numbers, or a duplicate key.
pub fn from_str<I: Build>(text: &str) -> Result<Json<I>, ParseError> {
    covalence_lib_json::from_str(text)
}

/// Parses JSON from bytes, strictly; see [`from_str`].
///
/// # Errors
///
/// As [`from_str`], and the bytes must be UTF-8.
pub fn from_slice<I: Build>(bytes: &[u8]) -> Result<Json<I>, ParseError> {
    covalence_lib_json::from_slice(bytes)
}

impl<I: Index> Json<I> {
    /// Compact serialization: no whitespace, keys already sorted, the
    /// "almost canonical" form.
    ///
    /// # Panics
    ///
    /// Does not: serializing a well-formed tree to a string cannot fail.
    #[must_use]
    pub fn to_json_string(&self) -> String {
        covalence_lib_json::to_string(self).expect("a Json tree serializes infallibly")
    }

    /// Human-readable serialization, indented two spaces.
    ///
    /// # Panics
    ///
    /// Does not: serializing a well-formed tree to a string cannot fail.
    #[must_use]
    pub fn to_json_string_pretty(&self) -> String {
        covalence_lib_json::to_string_pretty(self).expect("a Json tree serializes infallibly")
    }
}

impl<I: Build> From<&covalence_lib_json::Value> for Json<I> {
    fn from(value: &covalence_lib_json::Value) -> Self {
        use covalence_lib_json::Value;
        match value {
            Value::Null => Json::Null,
            Value::Bool(value) => Json::Bool(*value),
            Value::Number(value) => Json::Number(value.clone()),
            Value::String(value) => Json::String(I::str(value)),
            Value::Array(values) => Json::Array(I::array(values.iter().map(Json::from).collect())),
            Value::Object(map) => Json::Object(Map::from_unique(
                map.iter()
                    .map(|(key, value)| Entry {
                        key: I::str(key),
                        value: Json::from(value),
                    })
                    .collect(),
            )),
        }
    }
}

impl<I: Index> From<&Json<I>> for covalence_lib_json::Value {
    fn from(value: &Json<I>) -> Self {
        use covalence_lib_json::Value;
        match value {
            Json::Null => Value::Null,
            Json::Bool(value) => Value::Bool(*value),
            Json::Number(value) => Value::Number(value.clone()),
            Json::String(value) => Value::String(value.to_string()),
            Json::Array(values) => Value::Array(values.iter().map(Value::from).collect()),
            Json::Object(map) => Value::Object(
                map.iter()
                    .map(|entry| (entry.key.to_string(), Value::from(&entry.value)))
                    .collect(),
            ),
        }
    }
}
