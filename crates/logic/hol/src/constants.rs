//! Encapsulated, typed constant storage. References are local to one arena.
//!
//! Naturals and integers of any size may be stored here. Inline rows are a
//! construction optimization, not a restriction on constant-table values.

use bytes::Bytes;
use covalence_data_cbor::drisl::{Cid, CidCodec, CidHash};
use covalence_data_num::{Int, Num};
use covalence_lib_cbor::Value;
use serde::{Deserialize, Serialize, de, ser::SerializeStruct};

use crate::{
    Arena, Ref,
    literals::{Builtin, LiteralType, LiteralValue, WordWidth},
    row::{Expr, Row},
};

/// Maximum resident literal payload accepted by construction and decoding.
pub const MAX_LITERAL_BYTES: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ConstantId(pub(crate) u32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Constant {
    Nat(Num),
    Int(Int),
    Bytes(Bytes),
    LinkToBytes(Cid),
}

impl Constant {
    pub(crate) const fn literal_type(&self) -> LiteralType {
        match self {
            Self::Nat(_) => LiteralType::Nat,
            Self::Int(_) => LiteralType::Int,
            Self::Bytes(_) | Self::LinkToBytes(_) => LiteralType::Bytes,
        }
    }

    pub(crate) fn value(&self) -> Option<LiteralValue> {
        Some(match self {
            Self::Nat(value) => LiteralValue::Nat(value.clone()),
            Self::Int(value) => LiteralValue::Int(value.clone()),
            Self::Bytes(value) => LiteralValue::Bytes(value.clone()),
            Self::LinkToBytes(_) => return None,
        })
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct ConstantTable(Vec<Constant>);

impl ConstantTable {
    pub(crate) const fn empty() -> Self {
        Self(Vec::new())
    }

    pub(crate) fn get(&self, id: ConstantId) -> Option<&Constant> {
        self.0.get(id.0 as usize)
    }

    pub(crate) fn push(&mut self, constant: Constant) -> Option<ConstantId> {
        let id = ConstantId(u32::try_from(self.0.len()).ok()?);
        self.0.push(constant);
        Some(id)
    }

    fn can_push(&self) -> bool {
        u32::try_from(self.0.len()).is_ok()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn starts_with(&self, prefix: &Self) -> bool {
        self.0.starts_with(&prefix.0)
    }
}

impl Arena {
    pub(crate) fn can_push_literal(&self, value: &LiteralValue) -> bool {
        if crate::next_ref(self.dense.defs.len()).is_none() {
            return false;
        }
        let (size, out_of_line) = match value {
            LiteralValue::Nat(value) => (value.to_canonical_bytes().len(), value.bits() > 63),
            LiteralValue::Int(value) => {
                let size = value.to_canonical_bytes().len();
                (size, size > 8)
            }
            LiteralValue::Bytes(value) => (value.len(), true),
            _ => (0, false),
        };
        size <= MAX_LITERAL_BYTES && (!out_of_line || self.constants.can_push())
    }

    /// Appends a raw literal type without creating checked typing evidence.
    pub fn push_literal_ty(&mut self, ty: LiteralType) -> Option<Ref> {
        if ty == LiteralType::Bool {
            return self.push_bool_ty();
        }
        self.push_row(Row::new(Expr::LiteralTy(ty)), None)
    }

    /// Appends a raw literal, choosing its storage representation privately.
    ///
    /// Returns `None` on arena exhaustion or an oversized resident payload.
    /// Small naturals and integers are normally inline; constant-table storage
    /// remains valid for these values as well.
    pub fn push_literal(&mut self, value: LiteralValue) -> Option<Ref> {
        crate::next_ref(self.dense.defs.len())?;
        let expr = match value {
            LiteralValue::Bool(value) => Expr::Bool(value),
            LiteralValue::I8(value) => Expr::Word(
                WordWidth::W8,
                i64::from(i8::from_ne_bytes(value.to_ne_bytes())),
            ),
            LiteralValue::I16(value) => Expr::Word(
                WordWidth::W16,
                i64::from(i16::from_ne_bytes(value.to_ne_bytes())),
            ),
            LiteralValue::I32(value) => Expr::Word(
                WordWidth::W32,
                i64::from(i32::from_ne_bytes(value.to_ne_bytes())),
            ),
            LiteralValue::I64(value) => {
                Expr::Word(WordWidth::W64, i64::from_ne_bytes(value.to_ne_bytes()))
            }
            LiteralValue::Nat(value) => {
                if let Some(small) = u64::try_from(&value)
                    .ok()
                    .filter(|n| i64::try_from(*n).is_ok())
                {
                    Expr::Nat(small)
                } else {
                    if value.to_canonical_bytes().len() > MAX_LITERAL_BYTES {
                        return None;
                    }
                    Expr::ConstRef(self.constants.push(Constant::Nat(value))?)
                }
            }
            LiteralValue::Int(value) => {
                if let Ok(small) = i64::try_from(&value) {
                    Expr::Int(small)
                } else {
                    if value.to_canonical_bytes().len() > MAX_LITERAL_BYTES {
                        return None;
                    }
                    Expr::ConstRef(self.constants.push(Constant::Int(value))?)
                }
            }
            LiteralValue::Bytes(value) => {
                if value.len() > MAX_LITERAL_BYTES {
                    return None;
                }
                Expr::ConstRef(self.constants.push(Constant::Bytes(value))?)
            }
        };
        self.push_row(Row::new(expr), None)
    }

    /// Reads a resident literal independently of its storage representation.
    ///
    /// Linked bytes have no resident value: an address is not evidence of its
    /// contents. This accessor does not create checked typing evidence.
    #[must_use]
    pub fn literal_value(&self, reference: Ref) -> Option<LiteralValue> {
        Some(match *self.dense.row(reference)?.expr() {
            Expr::Bool(value) => LiteralValue::Bool(value),
            Expr::Word(width, value) => {
                LiteralValue::wrapping_word(width, u64::from_ne_bytes(value.to_ne_bytes()))
            }
            Expr::Nat(value) => LiteralValue::Nat(Num::from(value)),
            Expr::Int(value) => LiteralValue::Int(Int::from(value)),
            Expr::ConstRef(id) => return self.constants.get(id)?.value(),
            _ => return None,
        })
    }

    pub(crate) fn literal_type_of_ref(&self, reference: Ref) -> Option<LiteralType> {
        match *self.dense.row(reference)?.expr() {
            Expr::Bool(_) => Some(LiteralType::Bool),
            Expr::Word(width, _) => Some(width.ty()),
            Expr::Nat(_) => Some(LiteralType::Nat),
            Expr::Int(_) => Some(LiteralType::Int),
            Expr::ConstRef(id) => Some(self.constants.get(id)?.literal_type()),
            _ => None,
        }
    }

    /// Reads a raw literal-type row without asserting a classifier for it.
    #[must_use]
    pub fn literal_type(&self, reference: Ref) -> Option<LiteralType> {
        match *self.dense.row(reference)?.expr() {
            Expr::BoolTy => Some(LiteralType::Bool),
            Expr::LiteralTy(ty) => Some(ty),
            _ => None,
        }
    }

    /// Appends a raw builtin constant without creating checked typing evidence.
    ///
    /// Arguments use ordinary application rows, including partial applications.
    pub fn push_builtin_const(&mut self, builtin: Builtin) -> Option<Ref> {
        builtin.signature().ok()?;
        self.push_row(Row::new(Expr::Builtin(builtin)), None)
    }

    pub(crate) fn clone_constant_from(
        &mut self,
        source: &Self,
        id: ConstantId,
    ) -> Option<ConstantId> {
        self.constants.push(source.constants.get(id)?.clone())
    }
}

impl Serialize for ConstantTable {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(self.0.iter())
    }
}

impl<'de> Deserialize<'de> for ConstantTable {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let values = Vec::<Constant>::deserialize(deserializer)?;
        if values
            .len()
            .checked_sub(1)
            .is_some_and(|last| u32::try_from(last).is_err())
        {
            return Err(de::Error::custom(
                "constant table exceeds local index range",
            ));
        }
        Ok(Self(values))
    }
}

impl Serialize for Constant {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let (tag, value) = match self {
            Self::Nat(value) => ("nat", Value::Bytes(value.to_canonical_bytes())),
            Self::Int(value) => ("int", Value::Bytes(value.to_canonical_bytes())),
            Self::Bytes(value) => ("bytes", Value::Bytes(value.to_vec())),
            Self::LinkToBytes(cid) => (
                "link",
                Value::Tag(42, Box::new(Value::Bytes(cid.tag42_payload().to_vec()))),
            ),
        };
        let mut record = serializer.serialize_struct("Constant", 2)?;
        record.serialize_field("tag", tag)?;
        record.serialize_field("val", &value)?;
        record.end()
    }
}

impl<'de> Deserialize<'de> for Constant {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Record {
            tag: String,
            val: Value,
        }
        let record = Record::deserialize(deserializer)?;
        if record.tag == "link" {
            let Value::Tag(42, payload) = record.val else {
                return Err(de::Error::custom("byte link must use CID tag 42"));
            };
            let Value::Bytes(payload) = *payload else {
                return Err(de::Error::custom("CID payload must be bytes"));
            };
            let cid = Cid::parse_tag42_payload(&payload).map_err(de::Error::custom)?;
            if cid.codec() != CidCodec::Raw {
                return Err(de::Error::custom("byte link must address raw bytes"));
            }
            if cid.hash() != CidHash::Blake3 {
                return Err(de::Error::custom("byte link must use BLAKE3"));
            }
            return Ok(Self::LinkToBytes(cid));
        }
        let Value::Bytes(bytes) = record.val else {
            return Err(de::Error::custom("resident constant payload must be bytes"));
        };
        if bytes.len() > MAX_LITERAL_BYTES {
            return Err(de::Error::custom("constant payload exceeds literal limit"));
        }
        match record.tag.as_str() {
            "nat" => {
                let value = Num::from_canonical_bytes(&bytes).map_err(de::Error::custom)?;
                Ok(Self::Nat(value))
            }
            "int" => {
                let value = Int::from_canonical_bytes(&bytes).map_err(de::Error::custom)?;
                Ok(Self::Int(value))
            }
            "bytes" => Ok(Self::Bytes(bytes.into())),
            _ => Err(de::Error::custom("unknown constant type")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_lean_numeric_payload_fixtures() {
        let cases: Vec<(String, Vec<u8>, Option<String>)> =
            covalence_lib_json::from_str(include_str!("../literal-wire.json")).unwrap();
        for (tag, payload, expected) in cases {
            let value = Value::Map(vec![
                (Value::Text("tag".into()), Value::Text(tag.clone())),
                (Value::Text("val".into()), Value::Bytes(payload.clone())),
            ]);
            let mut encoded = Vec::new();
            covalence_lib_cbor::into_writer(&value, &mut encoded).unwrap();
            let decoded = covalence_lib_cbor::from_reader::<Constant, _>(encoded.as_slice());
            let actual = decoded.ok().map(|constant| match constant {
                Constant::Nat(value) => value.to_string(),
                Constant::Int(value) => value.to_string(),
                _ => panic!("numeric fixture decoded as another carrier"),
            });
            assert_eq!(actual, expected, "{tag} {payload:?}");
        }
    }

    fn roundtrip(value: &Constant) {
        let mut encoded = Vec::new();
        covalence_lib_cbor::into_writer(value, &mut encoded).unwrap();
        let decoded: Constant = covalence_lib_cbor::from_reader(encoded.as_slice()).unwrap();
        assert_eq!(&decoded, value);
    }

    #[test]
    fn small_numbers_are_valid_constants() {
        for value in [0_u64, 1, i64::MAX.unsigned_abs()] {
            roundtrip(&Constant::Nat(Num::from(value)));
        }
        for value in [i64::MIN, -1, 0, 1, i64::MAX] {
            roundtrip(&Constant::Int(Int::from(value)));
        }
    }

    #[test]
    fn table_and_inline_values_have_the_same_literal_api() {
        let mut arena = Arena::default();
        for value in [
            LiteralValue::Nat(Num::from(7_u8)),
            LiteralValue::Int(Int::from(-7_i8)),
        ] {
            let inline = arena.push_literal(value.clone()).unwrap();
            let constant = match &value {
                LiteralValue::Nat(value) => Constant::Nat(value.clone()),
                LiteralValue::Int(value) => Constant::Int(value.clone()),
                _ => unreachable!(),
            };
            let id = arena.constants.push(constant).unwrap();
            let outline = arena.push_row(Row::new(Expr::ConstRef(id)), None).unwrap();
            assert_eq!(arena.literal_value(inline), Some(value.clone()));
            assert_eq!(arena.literal_value(outline), Some(value));
            assert_eq!(
                arena.literal_type_of_ref(inline),
                arena.literal_type_of_ref(outline)
            );
            let mut encoded = Vec::new();
            crate::wire::serialize(&arena, &mut encoded).unwrap();
            let decoded = crate::wire::deserialize(encoded.as_slice()).unwrap();
            assert_eq!(
                decoded.literal_value(inline),
                decoded.literal_value(outline)
            );
            assert_eq!(decoded, arena);
        }
    }

    #[test]
    fn malformed_numeric_constants_are_rejected() {
        for (tag, payload) in [
            ("nat", vec![]),
            ("nat", vec![0, 1]),
            ("int", vec![]),
            ("int", vec![0, 1]),
            ("int", vec![255, 255]),
        ] {
            let value = Value::Map(vec![
                (Value::Text("tag".into()), Value::Text(tag.into())),
                (Value::Text("val".into()), Value::Bytes(payload)),
            ]);
            let mut encoded = Vec::new();
            covalence_lib_cbor::into_writer(&value, &mut encoded).unwrap();
            assert!(covalence_lib_cbor::from_reader::<Constant, _>(encoded.as_slice()).is_err());
        }
    }

    #[test]
    fn byte_links_are_typed_addresses_not_resident_values() {
        let cid = Cid::new(CidCodec::Raw, CidHash::Blake3, [7; 32]);
        roundtrip(&Constant::LinkToBytes(cid));
        let mut arena = Arena::empty();
        let id = arena.constants.push(Constant::LinkToBytes(cid)).unwrap();
        let reference = arena.push_row(Row::new(Expr::ConstRef(id)), None).unwrap();
        assert_eq!(
            arena.literal_type_of_ref(reference),
            Some(LiteralType::Bytes)
        );
        assert_eq!(arena.literal_value(reference), None);
        for cid in [
            Cid::new(CidCodec::Drisl, CidHash::Blake3, [7; 32]),
            Cid::new(CidCodec::Raw, CidHash::Sha256, [7; 32]),
        ] {
            let mut encoded = Vec::new();
            covalence_lib_cbor::into_writer(&Constant::LinkToBytes(cid), &mut encoded).unwrap();
            assert!(covalence_lib_cbor::from_reader::<Constant, _>(encoded.as_slice()).is_err());
        }
    }

    #[test]
    fn missing_constants_and_oversized_payloads_are_rejected() {
        let mut arena = Arena::empty();
        let before = arena.clone();
        assert!(
            arena
                .push_literal(LiteralValue::Bytes(vec![0; MAX_LITERAL_BYTES + 1].into()))
                .is_none()
        );
        assert_eq!(arena, before);
        arena
            .push_row(Row::new(Expr::ConstRef(ConstantId(0))), None)
            .unwrap();
        let mut encoded = Vec::new();
        crate::wire::serialize(&arena, &mut encoded).unwrap();
        assert!(crate::wire::deserialize(encoded.as_slice()).is_err());
    }

    #[test]
    fn constant_identity_is_part_of_the_definition_prefix() {
        let mut original = Arena::default();
        let id = original
            .constants
            .push(Constant::Nat(Num::from(1_u8)))
            .unwrap();
        original
            .push_row(Row::new(Expr::ConstRef(id)), None)
            .unwrap();
        let mut changed = original.clone();
        changed.constants.0[0] = Constant::Nat(Num::from(2_u8));
        assert!(!changed.has_definition_prefix(&original));
        let mut extended = original.clone();
        extended
            .constants
            .push(Constant::Nat(Num::from(3_u8)))
            .unwrap();
        assert!(extended.has_definition_prefix(&original));
    }
}
