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

mod fact;

pub use bytes::Bytes;
pub use covalence_lib_hash::O256;

pub use fact::{CasAssertion, CasCheckError, CasFact};

use std::ops::Range;

use covalence_lib_error::snafu::Snafu;

/// A read-only source of content-addressed bytes.
///
/// Implementations are untrusted. The raw operations are useful when a caller
/// does not need an LCF fact. [`Self::get_fact`] may avoid hashing when a
/// provider already holds checked facts, while [`CasExt::get_checked`] still
/// verifies that the returned fact answers the requested address.
pub trait Cas {
    /// Implementation-specific lookup or I/O failure.
    type Error: std::error::Error + 'static;

    /// An immutable object pinned independently of the CAS.
    type Object: CasObject<Error = Self::Error>;

    /// Opens and pins `address`, or returns `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup or I/O failure.
    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error>;

    /// Gets all bytes at `address`, or `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup, I/O, or read failure.
    fn get(&self, address: O256) -> Result<Option<Bytes>, Self::Error> {
        self.open(address)?
            .map(|object| object.read(0..object.len()))
            .transpose()
    }

    /// Gets the length at `address`, or `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup or I/O failure.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
        Ok(self.open(address)?.map(|object| object.len()))
    }

    /// Gets exactly `range`, or `None` when `address` is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup, I/O, or range failure.
    fn get_range(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        self.open(address)?
            .map(|object| object.read(range))
            .transpose()
    }

    /// Gets a checked whole-object fact, if present.
    ///
    /// The default obtains the raw bytes and checks them against `address`.
    /// Implementations holding checked facts may override this to avoid
    /// rehashing. Such an override can accidentally answer the wrong request;
    /// callers requiring the exact relation use [`CasExt::get_checked`].
    ///
    /// # Errors
    ///
    /// Returns [`CasLookupError::Provider`] for provider failures or
    /// [`CasLookupError::Check`] when raw bytes do not match `address`.
    fn get_fact(&self, address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
        self.get(address)
            .map_err(|source| CasLookupError::Provider {
                requested: address,
                source,
            })?
            .map(|blob| {
                CasFact::new(address, blob).map_err(|source| CasLookupError::Check {
                    requested: address,
                    source,
                })
            })
            .transpose()
    }
}

/// An immutable object pinned by [`Cas::open`].
pub trait CasObject {
    /// Implementation-specific read failure.
    type Error: std::error::Error + 'static;

    /// Returns the object's length.
    fn len(&self) -> u64;

    /// Returns whether the object is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Reads exactly `range`.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific I/O or range failure.
    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error>;
}

/// Failure to resolve a checked fact for a requested address.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasLookupError<E>
where
    E: std::error::Error + 'static,
{
    /// The underlying CAS failed to answer the lookup.
    #[snafu(display("could not get CAS object {requested}: {source}"))]
    Provider {
        /// Requested address.
        requested: O256,
        /// Provider-specific failure.
        source: E,
    },
    /// Raw bytes returned for the request did not hash to that address.
    #[snafu(display("CAS bytes for {requested} failed validation: {source}"))]
    Check {
        /// Requested address.
        requested: O256,
        /// Failed whole-object check.
        source: CasCheckError,
    },
    /// An optimized fact lookup returned a fact for another address.
    #[snafu(display("CAS returned address {returned} for request {requested}"))]
    WrongAddress {
        /// Requested address.
        requested: O256,
        /// Address carried by the returned checked fact.
        returned: O256,
    },
}

impl<E> CasLookupError<E>
where
    E: std::error::Error + 'static,
{
    /// Returns the address whose lookup failed.
    #[must_use]
    pub const fn requested(&self) -> O256 {
        match self {
            Self::Provider { requested, .. }
            | Self::Check { requested, .. }
            | Self::WrongAddress { requested, .. } => *requested,
        }
    }
}

mod sealed {
    pub trait CasExt {}

    impl<C: super::Cas + ?Sized> CasExt for C {}
}

/// Checked lookup operations available on every [`Cas`].
///
/// This trait is sealed and blanket-implemented. A successful result from
/// [`Self::get_checked`] is both a valid hash/blob fact and an answer to the
/// exact requested address, regardless of the CAS implementation.
pub trait CasExt: Cas + sealed::CasExt {
    /// Gets a checked fact for exactly `address`, or `None` when absent.
    ///
    /// # Errors
    ///
    /// Propagates failures from [`Cas::get_fact`] and returns
    /// [`CasLookupError::WrongAddress`] if an optimized implementation answers
    /// with a valid fact for a different address.
    fn get_checked(&self, address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
        let Some(fact) = self.get_fact(address)? else {
            return Ok(None);
        };
        let returned = fact.hash();
        if returned == address {
            Ok(Some(fact))
        } else {
            Err(CasLookupError::WrongAddress {
                requested: address,
                returned,
            })
        }
    }
}

impl<C: Cas + ?Sized> CasExt for C {}

/// A CAS supporting fallible insertion through exclusive access.
pub trait CasMut: Cas {
    /// Value returned after a successful insertion.
    type InsertSuccess;
    /// Implementation-specific insertion failure.
    type InsertError: std::error::Error + 'static;

    /// Inserts complete bytes.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific admission or storage failure.
    fn insert(&mut self, bytes: Bytes) -> Result<Self::InsertSuccess, Self::InsertError>;
}

/// A CAS supporting fallible insertion through shared access.
///
/// This intentionally does not extend [`CasMut`]: synchronized and persistent
/// stores often support one access pattern without the other.
pub trait CasShared: Cas {
    /// Value returned after a successful insertion.
    type InsertSuccess;
    /// Implementation-specific insertion failure.
    type InsertError: std::error::Error + 'static;

    /// Inserts complete bytes through shared access.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific admission or storage failure.
    fn insert(&self, bytes: Bytes) -> Result<Self::InsertSuccess, Self::InsertError>;
}

#[cfg(test)]
mod tests {
    use std::{convert::Infallible, io, ops::Range};

    use super::*;

    #[test]
    fn whole_assertion_checks_every_byte() {
        let blob = Bytes::from(vec![0x5a; 64 * 1024 + 1]);
        let hash = O256::from_bytes(&blob);
        let fact = CasAssertion {
            hash,
            blob: blob.clone(),
        }
        .check()
        .unwrap();

        assert_eq!(fact.hash(), hash);
        assert_eq!(fact.bytes(), &blob);

        let mut changed = blob.to_vec();
        *changed.last_mut().unwrap() ^= 1;
        let error = CasAssertion {
            hash,
            blob: Bytes::from(changed),
        }
        .check()
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
        let error = assertion.check().unwrap_err();

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

    #[derive(Clone)]
    struct TestObject(Bytes);

    impl CasObject for TestObject {
        type Error = Infallible;

        fn len(&self) -> u64 {
            self.0.len() as u64
        }

        fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
            let start = usize::try_from(range.start).expect("test range fits usize");
            let end = usize::try_from(range.end).expect("test range fits usize");
            Ok(self.0.slice(start..end))
        }
    }

    struct LyingCas(CasFact);

    impl Cas for LyingCas {
        type Error = Infallible;
        type Object = TestObject;

        fn open(&self, _address: O256) -> Result<Option<Self::Object>, Self::Error> {
            Ok(Some(TestObject(self.0.bytes().clone())))
        }

        fn get_fact(&self, _address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
            Ok(Some(self.0.clone()))
        }
    }

    #[test]
    fn exact_get_rejects_fact_for_another_address() {
        let returned = CasFact::from_bytes(Bytes::from_static(b"returned"));
        let requested = O256::from_bytes(b"requested");
        let cas = LyingCas(returned.clone());

        let error = cas.get_checked(requested).unwrap_err();
        assert_eq!(error.requested(), requested);
        assert!(matches!(
            error,
            CasLookupError::WrongAddress {
                requested: wrong_request,
                returned: wrong_return,
            } if wrong_request == requested && wrong_return == returned.hash()
        ));
    }

    struct FailingCas;

    impl Cas for FailingCas {
        type Error = io::Error;
        type Object = FailingObject;

        fn open(&self, _address: O256) -> Result<Option<Self::Object>, Self::Error> {
            Err(io::Error::other("offline"))
        }
    }

    struct FailingObject;

    impl CasObject for FailingObject {
        type Error = io::Error;

        fn len(&self) -> u64 {
            0
        }

        fn read(&self, _range: Range<u64>) -> Result<Bytes, Self::Error> {
            Err(io::Error::other("offline"))
        }
    }

    #[test]
    fn exact_get_preserves_provider_failure() {
        let requested = O256::from_bytes(b"requested");
        let error = FailingCas.get_checked(requested).unwrap_err();

        assert_eq!(error.requested(), requested);
        assert!(
            matches!(error, CasLookupError::Provider { source, .. } if source.kind() == io::ErrorKind::Other)
        );
    }

    #[test]
    fn fact_keeps_complete_bytes_after_provider_is_dropped() {
        let expected = Bytes::from_static(b"independent");
        let requested = O256::from_bytes(&expected);
        let fact = {
            let cas = LyingCas(CasFact::from_bytes(expected.clone()));
            cas.get_checked(requested).unwrap().unwrap()
        };

        assert_eq!(fact.bytes(), &expected);
    }
}
