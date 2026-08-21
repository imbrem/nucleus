//! Serde-backed wire representation for untrusted dense arenas.

use std::io::{Read, Write};

use serde::{Deserialize, Serialize};

use crate::{dense, row::RowSerde};

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DenseWire {
    tag: DenseTag,
    parent: (),
    offset: i64,
    defs: Vec<RowSerde>,
}

#[derive(Deserialize, Serialize)]
enum DenseTag {
    #[serde(rename = "arena.dense")]
    Dense,
}

/// Deserialize an untrusted dense arena. Integer narrowing to Rust `i64`
/// happens here; larger CBOR integers are rejected by Serde.
///
/// # Errors
///
/// Returns an error for malformed CBOR, schema violations, integer overflow,
/// or a row with the wrong arity.
pub fn deserialize(reader: impl Read) -> Result<dense::Arena, DecodeError> {
    let wire: DenseWire = covalence_lib_cbor::from_reader(reader)
        .map_err(|error| DecodeError::Deserialize(error.to_string()))?;
    let rows = wire
        .defs
        .into_iter()
        .enumerate()
        .map(|(index, row)| {
            row.try_into().map_err(|reason| DecodeError::InvalidRow {
                index,
                reason: format!("{reason:?}"),
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(dense::Arena::from_untrusted(wire.offset, rows))
}

/// Serialize the untrusted representation without admitting it as a kernel.
///
/// # Errors
///
/// Returns an error if the writer rejects the encoded bytes.
pub fn serialize(arena: &dense::Arena, writer: impl Write) -> Result<(), EncodeError> {
    let wire = DenseWire {
        tag: DenseTag::Dense,
        parent: (),
        offset: arena.offset(),
        defs: arena.rows().iter().copied().map(RowSerde::from).collect(),
    };
    covalence_lib_cbor::into_writer(&wire, writer).map_err(|error| EncodeError(error.to_string()))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError {
    Deserialize(String),
    InvalidRow { index: usize, reason: String },
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "invalid Ethane dense arena: {self:?}")
    }
}

impl std::error::Error for DecodeError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EncodeError(String);

impl std::fmt::Display for EncodeError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "could not encode Ethane dense arena: {}", self.0)
    }
}

impl std::error::Error for EncodeError {}
