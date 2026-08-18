//! Serde-backed exact CBOR codecs for v0 `HolE` objects.

#![allow(clippy::missing_errors_doc)]

use std::error::Error;
use std::fmt::{self, Display, Formatter};

use covalence_lib_cbor::Value;
use serde::{Deserialize, Serialize};

use covalence_lib_hash::O256;

use crate::{Arena, Ctx, Seq};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodeError(String);

impl EncodeError {
    pub(crate) fn serialize(error: impl Display) -> Self {
        Self(error.to_string())
    }
}
impl Display for EncodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "cannot encode HolE CBOR: {}", self.0)
    }
}
impl Error for EncodeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecodeError(String);
impl Display for DecodeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "cannot decode HolE CBOR: {}", self.0)
    }
}
impl Error for DecodeError {}

pub fn serialize_cbor<T: Serialize>(value: &T) -> Result<Vec<u8>, EncodeError> {
    let mut bytes = Vec::new();
    covalence_lib_cbor::into_writer(value, &mut bytes).map_err(EncodeError::serialize)?;
    Ok(bytes)
}

pub fn deserialize_cbor<T: for<'de> Deserialize<'de>>(bytes: &[u8]) -> Result<T, DecodeError> {
    covalence_lib_cbor::from_reader(bytes).map_err(|error| DecodeError(error.to_string()))
}

pub fn to_value<T: Serialize>(value: &T) -> Result<Value, EncodeError> {
    Value::serialized(value).map_err(EncodeError::serialize)
}

pub fn from_value<T: for<'de> Deserialize<'de>>(value: &Value) -> Result<T, DecodeError> {
    value
        .deserialized()
        .map_err(|error| DecodeError(error.to_string()))
}

pub fn arena_to_value(arena: &Arena) -> Result<Value, EncodeError> {
    to_value(arena)
}
pub fn arena_from_value(value: &Value) -> Result<Arena, DecodeError> {
    from_value(value)
}
pub fn seq_to_value(seq: &Seq) -> Result<Value, EncodeError> {
    to_value(seq)
}
pub fn seq_from_value(value: &Value) -> Result<Seq, DecodeError> {
    from_value(value)
}
pub fn ctx_to_value(ctx: &Ctx) -> Result<Value, EncodeError> {
    to_value(ctx)
}
pub fn ctx_from_value(value: &Value) -> Result<Ctx, DecodeError> {
    from_value(value)
}
pub fn import_table_to_value(table: &crate::ImportTable) -> Result<Value, EncodeError> {
    to_value(table)
}
pub fn import_table_from_value(value: &Value) -> Result<crate::ImportTable, DecodeError> {
    from_value(value)
}
pub fn import_table_address_from_value(value: &Value) -> Result<O256, DecodeError> {
    from_value(value)
}
