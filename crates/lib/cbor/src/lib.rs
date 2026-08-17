//! CBOR serialization used by Nucleus.
//!
//! The default `serde` feature exposes Ciborium's Serde codec. Disable default
//! features when only a dependency-level marker for CBOR is needed.

#[cfg(feature = "serde")]
pub use ciborium;
#[cfg(feature = "serde")]
pub use ciborium::*;

#[cfg(all(test, feature = "serde"))]
mod tests {
    #[test]
    fn values_round_trip() {
        let value = crate::Value::Array(vec![1_u64.into(), "answer".into()]);
        let mut encoded = Vec::new();
        crate::into_writer(&value, &mut encoded).unwrap();

        assert_eq!(
            crate::from_reader::<crate::Value, _>(&encoded[..]).unwrap(),
            value
        );
    }
}
