//! Strict, reusable `ATProto` DRISL values and wire encoding.
//!
//! The wire implementation delegates generic deterministic DAG-CBOR parsing
//! to `serde_ipld_dagcbor`, then applies the smaller `ATProto` data profile:
//! signed 64-bit integers, no floats, and a selected fixed-width CID policy.
//! This crate owns those policy checks so schema crates do not each invent a
//! subtly different canonical codec.

pub mod json;

use std::{collections::BTreeMap, convert::Infallible};

use covalence_lib_cbor::{
    ipld_core::{cid::Cid as IpldCid, ipld::Ipld},
    serde_ipld_dagcbor,
};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::{Blake3, HashNamespace, Sha256};

/// Maximum nesting accepted while translating the extensional data model.
///
/// The underlying strict decoder also has a nesting bound. Keeping an
/// explicit bound here protects encoding of caller-constructed values and
/// makes the resource policy independent of an upstream implementation detail.
pub const MAX_NESTING_DEPTH: usize = 128;

const CID_VERSION: u8 = 0x01;
const CID_DIGEST_LENGTH: u8 = 0x20;
const CID_BINARY_LENGTH: usize = 36;
const CID_TAG_PAYLOAD_LENGTH: usize = 37;

/// Content kind carried by the CID codec code.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CidCodec {
    /// Arbitrary byte content (`0x55`).
    Raw,
    /// DRISL content, using the registered DAG-CBOR code (`0x71`).
    Drisl,
}

impl CidCodec {
    /// Returns the registered multicodec code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            Self::Raw => 0x55,
            Self::Drisl => 0x71,
        }
    }

    const fn from_code(code: u8) -> Option<Self> {
        match code {
            0x55 => Some(Self::Raw),
            0x71 => Some(Self::Drisl),
            _ => None,
        }
    }
}

/// Hash algorithms understood by the Nucleus migration format.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CidHash {
    /// `ATProto`'s blessed SHA-256 multihash (`0x12`).
    Sha256,
    /// Nucleus's explicit BLAKE3 migration extension (`0x1e`).
    Blake3,
}

impl CidHash {
    /// Returns the registered multihash code.
    #[must_use]
    pub const fn code(self) -> u8 {
        match self {
            Self::Sha256 => 0x12,
            Self::Blake3 => 0x1e,
        }
    }

    const fn from_code(code: u8) -> Option<Self> {
        match code {
            0x12 => Some(Self::Sha256),
            0x1e => Some(Self::Blake3),
            _ => None,
        }
    }
}

/// A `CIDv1` in the fixed-width `ATProto`/Nucleus migration family.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Cid {
    codec: CidCodec,
    hash: CidHash,
    digest: [u8; 32],
}

impl Cid {
    /// Constructs a fixed-width CID.
    #[must_use]
    pub const fn new(codec: CidCodec, hash: CidHash, digest: [u8; 32]) -> Self {
        Self {
            codec,
            hash,
            digest,
        }
    }

    /// Returns the content codec.
    #[must_use]
    pub const fn codec(self) -> CidCodec {
        self.codec
    }

    /// Returns the digest algorithm.
    #[must_use]
    pub const fn hash(self) -> CidHash {
        self.hash
    }

    /// Returns the exact 256-bit digest.
    #[must_use]
    pub const fn digest(self) -> [u8; 32] {
        self.digest
    }

    /// Returns the exact binary `CIDv1` framing.
    #[must_use]
    pub fn binary(self) -> [u8; CID_BINARY_LENGTH] {
        let mut bytes = [0; CID_BINARY_LENGTH];
        bytes[0] = CID_VERSION;
        bytes[1] = self.codec.code();
        bytes[2] = self.hash.code();
        bytes[3] = CID_DIGEST_LENGTH;
        bytes[4..].copy_from_slice(&self.digest);
        bytes
    }

    /// Returns the tag-42 byte-string payload with its historical zero prefix.
    #[must_use]
    pub fn tag42_payload(self) -> [u8; CID_TAG_PAYLOAD_LENGTH] {
        let mut bytes = [0; CID_TAG_PAYLOAD_LENGTH];
        bytes[1..].copy_from_slice(&self.binary());
        bytes
    }

    /// Parses the exact fixed-width binary CID subset.
    ///
    /// # Errors
    ///
    /// Returns an error for any width, version, codec, hash, or digest-length
    /// field outside the selected ATProto/Nucleus family.
    pub fn parse_binary(bytes: &[u8]) -> Result<Self, CidError> {
        if bytes.len() != CID_BINARY_LENGTH {
            return Err(CidError::BinaryLength {
                actual: bytes.len(),
            });
        }
        if bytes[0] != CID_VERSION {
            return Err(CidError::Version { actual: bytes[0] });
        }
        let codec = CidCodec::from_code(bytes[1]).ok_or(CidError::Codec { actual: bytes[1] })?;
        let hash = CidHash::from_code(bytes[2]).ok_or(CidError::Hash { actual: bytes[2] })?;
        if bytes[3] != CID_DIGEST_LENGTH {
            return Err(CidError::DigestLength { actual: bytes[3] });
        }
        let mut digest = [0; 32];
        digest.copy_from_slice(&bytes[4..]);
        Ok(Self::new(codec, hash, digest))
    }

    /// Parses an exact tag-42 byte-string payload.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing zero prefix or any invalid binary CID
    /// field.
    pub fn parse_tag42_payload(bytes: &[u8]) -> Result<Self, CidError> {
        if bytes.len() != CID_TAG_PAYLOAD_LENGTH {
            return Err(CidError::TagPayloadLength {
                actual: bytes.len(),
            });
        }
        if bytes[0] != 0 {
            return Err(CidError::TagPrefix { actual: bytes[0] });
        }
        Self::parse_binary(&bytes[1..])
    }
}

/// Invalid framing for the fixed-width CID family.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CidError {
    /// The binary CID had the wrong total width.
    #[snafu(display("binary CID is {actual} bytes; expected 36"))]
    BinaryLength {
        /// Actual byte width.
        actual: usize,
    },
    /// The tag-42 payload had the wrong total width.
    #[snafu(display("tag-42 CID payload is {actual} bytes; expected 37"))]
    TagPayloadLength {
        /// Actual byte width.
        actual: usize,
    },
    /// The CID version was not version one.
    #[snafu(display("unsupported CID version 0x{actual:02x}"))]
    Version {
        /// Rejected version byte.
        actual: u8,
    },
    /// The content codec was not raw or DRISL.
    #[snafu(display("unsupported CID codec 0x{actual:02x}"))]
    Codec {
        /// Rejected codec byte.
        actual: u8,
    },
    /// The multihash was not SHA-256 or BLAKE3.
    #[snafu(display("unsupported CID hash 0x{actual:02x}"))]
    Hash {
        /// Rejected hash byte.
        actual: u8,
    },
    /// The digest length was not 32 bytes.
    #[snafu(display("unsupported CID digest length 0x{actual:02x}"))]
    DigestLength {
        /// Rejected digest-length byte.
        actual: u8,
    },
    /// The tag-42 payload did not begin with zero.
    #[snafu(display("invalid tag-42 CID prefix 0x{actual:02x}"))]
    TagPrefix {
        /// Rejected prefix byte.
        actual: u8,
    },
}

/// Hash and codec policy for links accepted at a data-model boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Policy {
    accept_blake3: bool,
}

impl Policy {
    /// Exact `ATProto` policy: raw or DRISL content, using SHA-256 only.
    pub const ATPROTO: Self = Self {
        accept_blake3: false,
    };

    /// Nucleus migration policy: `ATProto` plus 32-byte BLAKE3 multihashes.
    pub const NUCLEUS: Self = Self {
        accept_blake3: true,
    };

    /// Returns whether the CID is admitted by this policy.
    #[must_use]
    pub const fn accepts(self, cid: Cid) -> bool {
        match cid.hash {
            CidHash::Sha256 => true,
            CidHash::Blake3 => self.accept_blake3,
        }
    }
}

/// Extensional float-free `ATProto` data value.
///
/// Maps use ordinary `BTreeMap` order only as an in-memory extensional
/// representation. The DRISL encoder applies the required historical
/// length-first order to the complete encoded text keys.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    /// Null.
    Null,
    /// Boolean.
    Bool(bool),
    /// Signed 64-bit integer.
    Integer(i64),
    /// UTF-8 text.
    Text(String),
    /// Byte string.
    Bytes(Vec<u8>),
    /// Policy-checked CID link.
    Link(Cid),
    /// Ordered sequence.
    Array(Vec<Self>),
    /// Extensional string-keyed map.
    Map(BTreeMap<String, Self>),
}

/// Value outside the selected DRISL profile or implementation resource bound.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ProfileError {
    /// Generic DAG-CBOR admitted a float, which `ATProto` forbids.
    #[snafu(display("floating-point values are not in the ATProto DRISL profile"))]
    Float,
    /// Generic DAG-CBOR admitted an integer outside signed 64-bit range.
    #[snafu(display("integer is outside signed 64-bit range"))]
    Integer,
    /// A CID did not use the fixed-width Nucleus framing family.
    #[snafu(display("invalid DRISL CID: {source}"))]
    Cid {
        /// Exact framing failure.
        source: CidError,
    },
    /// A well-typed fixed CID could not be represented by the IPLD library.
    #[snafu(display("fixed-width CID could not be represented by the DAG-CBOR codec"))]
    CidRepresentation,
    /// A link was outside the selected hash policy.
    #[snafu(display("CID hash is not accepted by this DRISL policy"))]
    RejectedLink,
    /// Nesting exceeded the explicit translation bound.
    #[snafu(display("DRISL nesting exceeds {MAX_NESTING_DEPTH} levels"))]
    Depth,
}

/// Failure to encode a DRISL value.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum EncodeError {
    /// The value was outside the selected profile.
    #[snafu(display("value is outside the selected DRISL profile: {source}"))]
    EncodeProfile {
        /// Profile failure.
        source: ProfileError,
    },
    /// The deterministic DAG-CBOR serializer failed.
    #[snafu(display("could not encode deterministic DRISL: {source}"))]
    EncodeDagCbor {
        /// Underlying deterministic codec failure.
        source: serde_ipld_dagcbor::EncodeError<std::collections::TryReserveError>,
    },
}

/// Failure to decode one exact deterministic DRISL item.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DecodeError {
    /// Generic deterministic DAG-CBOR parsing failed.
    #[snafu(display("could not decode deterministic DRISL: {source}"))]
    DecodeDagCbor {
        /// Underlying strict codec failure.
        source: serde_ipld_dagcbor::DecodeError<Infallible>,
    },
    /// The parsed DAG-CBOR value was outside the selected profile.
    #[snafu(display("decoded value is outside the selected DRISL profile: {source}"))]
    DecodeProfile {
        /// Profile failure.
        source: ProfileError,
    },
    /// Re-encoding did not reproduce the input bytes exactly.
    #[snafu(display("DRISL encoding is not canonical"))]
    Noncanonical,
    /// Re-encoding a checked value unexpectedly failed.
    #[snafu(display("could not verify decoded DRISL canonicality: {source}"))]
    Reencode {
        /// Deterministic re-encoding failure.
        source: EncodeError,
    },
}

/// Encodes a value in its unique deterministic representation.
///
/// # Errors
///
/// Returns an error when a link is outside `policy`, nesting exceeds the
/// explicit bound, or the in-memory serializer cannot allocate its output.
pub fn encode(policy: Policy, value: &Value) -> Result<Vec<u8>, EncodeError> {
    let ipld = to_ipld(policy, value, 0).map_err(|source| EncodeError::EncodeProfile { source })?;
    serde_ipld_dagcbor::to_vec(&ipld).map_err(|source| EncodeError::EncodeDagCbor { source })
}

/// Decodes one complete canonical DRISL item under `policy`.
///
/// # Errors
///
/// Rejects malformed, trailing, non-minimal, indefinite, deeply nested, or
/// incorrectly ordered CBOR; floats; integers outside signed 64-bit range;
/// duplicate or non-text map keys; and links outside `policy`.
pub fn decode(policy: Policy, bytes: &[u8]) -> Result<Value, DecodeError> {
    let ipld: Ipld = serde_ipld_dagcbor::from_slice(bytes)
        .map_err(|source| DecodeError::DecodeDagCbor { source })?;
    let value =
        from_ipld(policy, ipld, 0).map_err(|source| DecodeError::DecodeProfile { source })?;
    let canonical = encode(policy, &value).map_err(|source| DecodeError::Reencode { source })?;
    if canonical == bytes {
        Ok(value)
    } else {
        Err(DecodeError::Noncanonical)
    }
}

/// Computes the selected fixed-width content address.
#[must_use]
pub fn address(codec: CidCodec, hash: CidHash, content: &[u8]) -> Cid {
    let digest = match hash {
        CidHash::Sha256 => Sha256::hash(content).into_bytes(),
        CidHash::Blake3 => Blake3::hash(content).into_bytes(),
    };
    Cid::new(codec, hash, digest)
}

/// Computes the blessed SHA-256 address of a DRISL block.
#[must_use]
pub fn address_drisl(content: &[u8]) -> Cid {
    address(CidCodec::Drisl, CidHash::Sha256, content)
}

/// Computes the explicit BLAKE3 migration address of a DRISL block.
#[must_use]
pub fn address_drisl_blake3(content: &[u8]) -> Cid {
    address(CidCodec::Drisl, CidHash::Blake3, content)
}

/// Checks the semantic content-address claim made by a CID.
#[must_use]
pub fn addresses(cid: Cid, content: &[u8]) -> bool {
    address(cid.codec, cid.hash, content).digest == cid.digest
}

fn to_ipld(policy: Policy, value: &Value, depth: usize) -> Result<Ipld, ProfileError> {
    if depth > MAX_NESTING_DEPTH {
        return Err(ProfileError::Depth);
    }
    match value {
        Value::Null => Ok(Ipld::Null),
        Value::Bool(value) => Ok(Ipld::Bool(*value)),
        Value::Integer(value) => Ok(Ipld::Integer(i128::from(*value))),
        Value::Text(value) => Ok(Ipld::String(value.clone())),
        Value::Bytes(value) => Ok(Ipld::Bytes(value.clone())),
        Value::Link(cid) => {
            if !policy.accepts(*cid) {
                return Err(ProfileError::RejectedLink);
            }
            let cid = IpldCid::try_from(cid.binary().as_slice())
                .map_err(|_| ProfileError::CidRepresentation)?;
            Ok(Ipld::Link(cid))
        }
        Value::Array(values) => values
            .iter()
            .map(|value| to_ipld(policy, value, depth + 1))
            .collect::<Result<Vec<_>, _>>()
            .map(Ipld::List),
        Value::Map(fields) => fields
            .iter()
            .map(|(key, value)| Ok((key.clone(), to_ipld(policy, value, depth + 1)?)))
            .collect::<Result<BTreeMap<_, _>, ProfileError>>()
            .map(Ipld::Map),
    }
}

fn from_ipld(policy: Policy, value: Ipld, depth: usize) -> Result<Value, ProfileError> {
    if depth > MAX_NESTING_DEPTH {
        return Err(ProfileError::Depth);
    }
    match value {
        Ipld::Null => Ok(Value::Null),
        Ipld::Bool(value) => Ok(Value::Bool(value)),
        Ipld::Integer(value) => i64::try_from(value)
            .map(Value::Integer)
            .map_err(|_| ProfileError::Integer),
        Ipld::Float(_) => Err(ProfileError::Float),
        Ipld::String(value) => Ok(Value::Text(value)),
        Ipld::Bytes(value) => Ok(Value::Bytes(value)),
        Ipld::Link(value) => {
            let cid = Cid::parse_binary(&value.to_bytes())
                .map_err(|source| ProfileError::Cid { source })?;
            if policy.accepts(cid) {
                Ok(Value::Link(cid))
            } else {
                Err(ProfileError::RejectedLink)
            }
        }
        Ipld::List(values) => values
            .into_iter()
            .map(|value| from_ipld(policy, value, depth + 1))
            .collect::<Result<Vec<_>, _>>()
            .map(Value::Array),
        Ipld::Map(fields) => fields
            .into_iter()
            .map(|(key, value)| Ok((key, from_ipld(policy, value, depth + 1)?)))
            .collect::<Result<BTreeMap<_, _>, ProfileError>>()
            .map(Value::Map),
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{DefaultHasher, Hash as _, Hasher as _};

    use super::*;

    fn sha_link(codec: CidCodec) -> Cid {
        Cid::new(codec, CidHash::Sha256, [0xa5; 32])
    }

    fn hash(value: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn scalar_encodings_are_exact() {
        let fixtures = [
            (Value::Null, vec![0xf6]),
            (Value::Bool(false), vec![0xf4]),
            (Value::Bool(true), vec![0xf5]),
            (Value::Integer(0), vec![0x00]),
            (Value::Integer(23), vec![0x17]),
            (Value::Integer(24), vec![0x18, 0x18]),
            (Value::Integer(-1), vec![0x20]),
            (Value::Bytes(Vec::new()), vec![0x40]),
            (Value::Text("hi".to_owned()), vec![0x62, b'h', b'i']),
        ];
        for (value, expected) in fixtures {
            assert_eq!(encode(Policy::ATPROTO, &value).unwrap(), expected);
            assert_eq!(decode(Policy::ATPROTO, &expected).unwrap(), value);
        }

        let mut maximum = vec![0x1b];
        maximum.extend_from_slice(&i64::MAX.to_be_bytes());
        assert_eq!(
            encode(Policy::ATPROTO, &Value::Integer(i64::MAX)).unwrap(),
            maximum
        );
        let mut minimum = vec![0x3b];
        minimum.extend_from_slice(&i64::MAX.to_be_bytes());
        assert_eq!(
            encode(Policy::ATPROTO, &Value::Integer(i64::MIN)).unwrap(),
            minimum
        );
    }

    #[test]
    fn maps_use_historical_length_first_order() {
        let value = Value::Map(BTreeMap::from([
            ("aa".to_owned(), Value::Null),
            ("b".to_owned(), Value::Bool(true)),
        ]));
        let expected = [0xa2, 0x61, b'b', 0xf5, 0x62, b'a', b'a', 0xf6];
        assert_eq!(encode(Policy::ATPROTO, &value).unwrap(), expected);
        assert_eq!(decode(Policy::ATPROTO, &expected).unwrap(), value);
    }

    #[test]
    fn link_encoding_and_policy_are_exact() {
        let cid = sha_link(CidCodec::Drisl);
        let mut expected = vec![0xd8, 0x2a, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20];
        expected.extend_from_slice(&[0xa5; 32]);
        let value = Value::Link(cid);
        assert_eq!(encode(Policy::ATPROTO, &value).unwrap(), expected);
        assert_eq!(decode(Policy::ATPROTO, &expected).unwrap(), value);

        let blake = Value::Link(Cid::new(CidCodec::Drisl, CidHash::Blake3, [0x5a; 32]));
        assert!(matches!(
            encode(Policy::ATPROTO, &blake),
            Err(EncodeError::EncodeProfile {
                source: ProfileError::RejectedLink
            })
        ));
        let encoded = encode(Policy::NUCLEUS, &blake).unwrap();
        assert_eq!(decode(Policy::NUCLEUS, &encoded).unwrap(), blake);
        assert!(decode(Policy::ATPROTO, &encoded).is_err());
    }

    #[test]
    fn cid_binary_and_tag_payload_round_trip() {
        for codec in [CidCodec::Raw, CidCodec::Drisl] {
            for hash in [CidHash::Sha256, CidHash::Blake3] {
                let cid = Cid::new(codec, hash, [codec.code() ^ hash.code(); 32]);
                assert_eq!(Cid::parse_binary(&cid.binary()).unwrap(), cid);
                assert_eq!(Cid::parse_tag42_payload(&cid.tag42_payload()).unwrap(), cid);
            }
        }

        let cid = sha_link(CidCodec::Raw);
        for (index, replacement) in [(0, 2), (1, 0x70), (2, 0x13), (3, 0x1f)] {
            let mut bytes = cid.binary();
            bytes[index] = replacement;
            assert!(Cid::parse_binary(&bytes).is_err());
        }
        let mut payload = cid.tag42_payload();
        payload[0] = 1;
        assert!(matches!(
            Cid::parse_tag42_payload(&payload),
            Err(CidError::TagPrefix { actual: 1 })
        ));
    }

    #[test]
    fn bounded_recursive_corpus_round_trips_stably() {
        let mut values = vec![
            Value::Null,
            Value::Bool(false),
            Value::Bool(true),
            Value::Integer(i64::MIN),
            Value::Integer(-24),
            Value::Integer(-1),
            Value::Integer(0),
            Value::Integer(24),
            Value::Integer(i64::MAX),
            Value::Text(String::new()),
            Value::Text("λ nucleus 🧠".to_owned()),
            Value::Bytes(Vec::new()),
            Value::Bytes(vec![0, 1, 2, 0xff]),
            Value::Link(sha_link(CidCodec::Raw)),
            Value::Link(sha_link(CidCodec::Drisl)),
        ];
        for depth in 0_i64..8 {
            let previous = values.clone();
            values.push(Value::Array(previous.clone()));
            values.push(Value::Map(BTreeMap::from([
                (format!("d{depth}"), Value::Integer(depth)),
                (format!("nested-{depth}"), Value::Array(previous)),
            ])));
        }

        for value in values {
            let encoded = encode(Policy::ATPROTO, &value).unwrap();
            let decoded = decode(Policy::ATPROTO, &encoded).unwrap();
            assert_eq!(decoded, value);
            assert_eq!(encode(Policy::ATPROTO, &decoded).unwrap(), encoded);
        }
    }

    #[test]
    fn malformed_and_noncanonical_inputs_are_rejected() {
        let malformed: &[&[u8]] = &[
            &[0x18, 0x00],                                     // non-minimal integer
            &[0x1b, 0x80, 0, 0, 0, 0, 0, 0, 0],                // above i64::MAX
            &[0x3b, 0x80, 0, 0, 0, 0, 0, 0, 0],                // below i64::MIN
            &[0xf9, 0, 0],                                     // float
            &[0xf7],                                           // undefined
            &[0x9f, 0xff],                                     // indefinite array
            &[0xa1, 0x00, 0xf6],                               // non-text map key
            &[0xa2, 0x62, b'a', b'a', 0xf6, 0x61, b'b', 0xf5], // wrong map order
            &[0xa2, 0x61, b'a', 0xf6, 0x61, b'a', 0xf5],       // duplicate key
            &[0xd8, 0x18, 0x40],                               // unsupported tag
            &[0xf6, 0x00],                                     // trailing item
        ];
        for bytes in malformed {
            assert!(
                decode(Policy::ATPROTO, bytes).is_err(),
                "accepted {bytes:x?}"
            );
        }
    }

    #[test]
    fn malformed_link_framing_is_rejected() {
        let cid = sha_link(CidCodec::Drisl);
        for index in 0..4 {
            let mut payload = cid.tag42_payload();
            payload[index] ^= 0xff;
            let mut bytes = vec![0xd8, 0x2a, 0x58, 0x25];
            bytes.extend_from_slice(&payload);
            assert!(decode(Policy::NUCLEUS, &bytes).is_err());
        }
    }

    #[test]
    fn nesting_resource_bound_is_checked_in_both_directions() {
        let mut value = Value::Null;
        let mut bytes = vec![0xf6];
        for _ in 0..=MAX_NESTING_DEPTH {
            value = Value::Array(vec![value]);
            bytes.insert(0, 0x81);
        }
        assert!(matches!(
            encode(Policy::ATPROTO, &value),
            Err(EncodeError::EncodeProfile {
                source: ProfileError::Depth
            })
        ));
        assert!(decode(Policy::ATPROTO, &bytes).is_err());
    }

    #[test]
    fn extensional_map_equality_and_hash_ignore_insertion_order() {
        let mut left = BTreeMap::new();
        left.insert("aa".to_owned(), Value::Null);
        left.insert("b".to_owned(), Value::Bool(true));
        let mut right = BTreeMap::new();
        right.insert("b".to_owned(), Value::Bool(true));
        right.insert("aa".to_owned(), Value::Null);
        let left = Value::Map(left);
        let right = Value::Map(right);
        assert_eq!(left, right);
        assert_eq!(hash(&left), hash(&right));
    }

    #[test]
    fn content_addresses_use_the_selected_algorithm() {
        let sha = address_drisl(b"abc");
        let blake = address_drisl_blake3(b"abc");
        assert_eq!(sha.hash(), CidHash::Sha256);
        assert_eq!(blake.hash(), CidHash::Blake3);
        assert!(Policy::ATPROTO.accepts(sha));
        assert!(!Policy::ATPROTO.accepts(blake));
        assert!(Policy::NUCLEUS.accepts(blake));
        assert!(addresses(sha, b"abc"));
        assert!(addresses(blake, b"abc"));
        assert!(!addresses(sha, b"abd"));
    }
}
