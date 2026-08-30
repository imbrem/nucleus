//! CBOR serialization used by Nucleus.
//!
//! The default `serde` feature exposes Ciborium's Serde codec. Disable default
//! features when only a dependency-level marker for CBOR is needed.

#[cfg(feature = "serde")]
pub use ciborium;
#[cfg(feature = "serde")]
pub use ciborium::*;

/// IPLD's extensional data model used by the strict DAG-CBOR codec.
#[cfg(feature = "drisl")]
pub use ipld_core;
/// Strict deterministic DAG-CBOR serialization used as the DRISL substrate.
#[cfg(feature = "drisl")]
pub use serde_ipld_dagcbor;

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
