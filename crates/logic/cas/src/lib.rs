//! LCF-style checked facts about whole content-addressed blobs.
//!
//! [`CasAssertion`] is ordinary, unchecked data. [`CasFact`] is an opaque
//! wrapper introduced only after hashing every byte or by hashing bytes to
//! choose the address. The wrapper, rather than a map, cache, database, or
//! transport, is the trusted object. This keeps concrete storage policy out of
//! the logic layer.
//!
//! This first slice intentionally includes only whole objects. Range and
//! length assertions require their own derivation or proof-checking rules and
//! are not represented here.
//!
//! The corresponding Lean theory names the unchecked proposition
//! `Nucleus.CasAssertion.Valid` and the checked atom `Nucleus.CasPair`; see
//! issue #875. This crate erases the Lean proof while preserving the same LCF
//! constructor boundary in safe Rust.

mod assertion;
mod fact;
mod trusted;

pub use bytes::Bytes;
pub use covalence_lib_hash::O256;

pub use assertion::CasAssertion;
pub use fact::{CasFact, InvalidCasAssertion};
pub use trusted::{GetError, TrustedCas, get_exact};

#[cfg(test)]
mod tests {
    use std::{convert::Infallible, io};

    use super::*;

    #[test]
    fn whole_assertion_checks_every_byte() {
        let blob = Bytes::from(vec![0x5a; 64 * 1024 + 1]);
        let hash = O256::from_bytes(&blob);
        let fact = CasFact::try_from(CasAssertion {
            hash,
            blob: blob.clone(),
        })
        .unwrap();

        assert_eq!(fact.hash(), hash);
        assert_eq!(fact.bytes(), &blob);

        let mut changed = blob.to_vec();
        *changed.last_mut().unwrap() ^= 1;
        let error = CasFact::try_from(CasAssertion {
            hash,
            blob: Bytes::from(changed),
        })
        .unwrap_err();
        assert_eq!(error.claimed, hash);
        assert_ne!(error.computed, hash);
    }

    #[test]
    fn wrong_claimed_hash_is_rejected() {
        let assertion = CasAssertion {
            hash: O256::from_bytes(b"other"),
            blob: Bytes::from_static(b"blob"),
        };
        let error = CasFact::try_from(assertion).unwrap_err();

        assert_eq!(error.claimed, O256::from_bytes(b"other"));
        assert_eq!(error.computed, O256::from_bytes(b"blob"));
    }

    #[test]
    fn hashing_constructor_accepts_empty_blob() {
        let fact = CasFact::from_bytes(Bytes::new());

        assert_eq!(fact.hash(), O256::from_bytes([]));
        assert!(fact.bytes().is_empty());
    }

    #[test]
    fn checked_fact_round_trips_to_unchecked_assertion() {
        let fact = CasFact::from_bytes(Bytes::from_static(b"round trip"));
        let expected = CasAssertion {
            hash: fact.hash(),
            blob: fact.bytes().clone(),
        };

        assert_eq!(CasAssertion::from(&fact), expected);
        assert_eq!(fact.into_assertion(), expected);
    }

    struct LyingCas {
        fact: CasFact,
    }

    impl TrustedCas for LyingCas {
        type Error = Infallible;

        fn get(&self, _address: O256) -> Result<CasFact, Self::Error> {
            Ok(self.fact.clone())
        }
    }

    #[test]
    fn exact_get_rejects_fact_for_another_address() {
        let returned = CasFact::from_bytes(Bytes::from_static(b"returned"));
        let requested = O256::from_bytes(b"requested");
        let cas = LyingCas {
            fact: returned.clone(),
        };

        let error = get_exact(&cas, requested).unwrap_err();
        assert_eq!(error.requested(), requested);
        assert!(matches!(
            error,
            GetError::WrongAddress {
                requested: wrong_request,
                returned: wrong_return,
            } if wrong_request == requested && wrong_return == returned.hash()
        ));
    }

    struct FailingCas;

    impl TrustedCas for FailingCas {
        type Error = io::Error;

        fn get(&self, _address: O256) -> Result<CasFact, Self::Error> {
            Err(io::Error::other("offline"))
        }
    }

    #[test]
    fn exact_get_preserves_provider_failure() {
        let requested = O256::from_bytes(b"requested");
        let error = get_exact(&FailingCas, requested).unwrap_err();

        assert_eq!(error.requested(), requested);
        assert!(
            matches!(error, GetError::Provider { source, .. } if source.kind() == io::ErrorKind::Other)
        );
    }

    #[test]
    fn fact_keeps_complete_bytes_after_provider_is_dropped() {
        let expected = Bytes::from_static(b"independent");
        let requested = O256::from_bytes(&expected);
        let fact = {
            let cas = LyingCas {
                fact: CasFact::from_bytes(expected.clone()),
            };
            get_exact(&cas, requested).unwrap()
        };

        assert_eq!(fact.bytes(), &expected);
    }
}
