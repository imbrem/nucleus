//! Immutable, shared CBOR values.

pub mod drisl;

use std::sync::Arc;

use covalence_data_num::Num;
pub use covalence_data_num::{DecodeLimit, Int};

/// A cheap-to-clone handle to an immutable CBOR value.
#[derive(Clone, Debug, PartialEq)]
pub struct Value(Arc<ValueKind>);

/// The data stored by a [`Value`].
///
/// Map entries retain insertion order because CBOR maps are sequences on the
/// wire and may use any CBOR value as a key. Float widths and bit patterns are
/// retained exactly; Boolean, null, and undefined values use their standard
/// [`ValueKind::Simple`] encodings.
#[derive(Debug, PartialEq)]
pub enum ValueKind {
    /// A mathematical integer. Encoders use major type 0 or 1 when possible
    /// and standard bignum tag 2 or 3 outside the native CBOR integer range.
    Integer(Int),
    Bytes(Arc<[u8]>),
    Text(Arc<str>),
    Simple(u8),
    Float16(u16),
    Float32(u32),
    Float64(u64),
    Tag(u64, Value),
    Array(Arc<[Value]>),
    Map(Arc<[(Value, Value)]>),
}

impl Value {
    #[must_use]
    pub fn new(kind: ValueKind) -> Self {
        Self(Arc::new(kind))
    }

    #[must_use]
    pub fn kind(&self) -> &ValueKind {
        &self.0
    }

    #[must_use]
    pub fn integer(value: Int) -> Self {
        Self::new(ValueKind::Integer(value))
    }

    #[must_use]
    pub fn bytes(value: impl Into<Arc<[u8]>>) -> Self {
        Self::new(ValueKind::Bytes(value.into()))
    }

    #[must_use]
    pub fn simple(value: u8) -> Self {
        Self::new(ValueKind::Simple(value))
    }

    #[must_use]
    pub fn text(value: impl Into<Arc<str>>) -> Self {
        Self::new(ValueKind::Text(value.into()))
    }

    #[must_use]
    pub fn bool(value: bool) -> Self {
        Self::simple(if value { 21 } else { 20 })
    }

    #[must_use]
    pub fn null() -> Self {
        Self::simple(22)
    }

    #[must_use]
    pub fn undefined() -> Self {
        Self::simple(23)
    }

    #[must_use]
    pub fn float16(bits: u16) -> Self {
        Self::new(ValueKind::Float16(bits))
    }

    #[must_use]
    pub fn float32(bits: u32) -> Self {
        Self::new(ValueKind::Float32(bits))
    }

    #[must_use]
    pub fn float64(bits: u64) -> Self {
        Self::new(ValueKind::Float64(bits))
    }

    #[must_use]
    pub fn tag(tag: u64, value: Self) -> Self {
        Self::new(ValueKind::Tag(tag, value))
    }

    #[must_use]
    pub fn array(values: impl Into<Arc<[Self]>>) -> Self {
        Self::new(ValueKind::Array(values.into()))
    }

    #[must_use]
    pub fn map(entries: impl Into<Arc<[(Self, Self)]>>) -> Self {
        Self::new(ValueKind::Map(entries.into()))
    }

    #[must_use]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Self::integer(Int::from(Num::from(value)))
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Self::integer(Int::from(value))
    }
}

impl From<Int> for Value {
    fn from(value: Int) -> Self {
        Self::integer(value)
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::bool(value)
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::text(value)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::text(value)
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{Int, Value, ValueKind};

    #[test]
    fn handles_are_shared_and_pointer_sized() {
        let value = Value::from(42_u64);
        let clone = value.clone();

        assert!(value.ptr_eq(&clone));
        assert_eq!(size_of::<Value>(), size_of::<usize>());
        assert_eq!(value.kind(), &ValueKind::Integer(Int::from(42_i64)));
    }

    #[test]
    fn compound_values_are_immutable_shared_slices() {
        let key = Value::from("answer");
        let value = Value::from(42_u64);
        let map = Value::map([(key.clone(), value.clone())]);
        let array = Value::array([map.clone(), Value::tag(24, value)]);

        let ValueKind::Array(values) = array.kind() else {
            panic!("expected an array");
        };
        assert_eq!(values.len(), 2);
        assert!(map.ptr_eq(&values[0]));
    }

    #[test]
    fn scalar_syntax_is_preserved_exactly() {
        assert_eq!(
            Value::from(-1_i64).kind(),
            &ValueKind::Integer(Int::from(-1_i64))
        );
        assert_eq!(
            Value::from(i64::MIN).kind(),
            &ValueKind::Integer(Int::from(i64::MIN))
        );
        let positive_bignum = Int::from_canonical_bytes(&[1; 33]).unwrap();
        let negative_bignum = Int::from_canonical_bytes(&[0xfe; 33]).unwrap();
        assert_eq!(
            Value::from(positive_bignum.clone()).kind(),
            &ValueKind::Integer(positive_bignum)
        );
        assert_eq!(
            Value::from(negative_bignum.clone()).kind(),
            &ValueKind::Integer(negative_bignum)
        );
        assert_eq!(Value::bool(false).kind(), &ValueKind::Simple(20));
        assert_eq!(Value::bool(true).kind(), &ValueKind::Simple(21));
        assert_eq!(Value::null().kind(), &ValueKind::Simple(22));
        assert_eq!(Value::undefined().kind(), &ValueKind::Simple(23));
        assert_eq!(
            Value::float64(f64::NAN.to_bits()).kind(),
            &ValueKind::Float64(f64::NAN.to_bits())
        );
    }
}
