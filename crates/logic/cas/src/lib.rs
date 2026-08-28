//! LCF-style checked facts about content-addressed blobs.
//!
//! [`CasRangeAssertion`] is ordinary, unchecked data. [`CasRangeFact`] is an
//! opaque wrapper introduced only by this crate's checking rules. The wrapper,
//! rather than a map, cache, database, or transport, is the trusted object.
//! This keeps concrete storage policy out of the logic layer.
//!
//! A fact is parameterized by the byte range it covers, and a whole-blob fact
//! is the `RangeFull` case: [`CasFact`] is `CasRangeFact<RangeFull>` and
//! [`CasAssertion`] is `CasRangeAssertion<RangeFull>`. See [`range`] for what
//! the four range shapes claim.
//!
//! The rules that introduce a fact are
//!
//! - [`CasFact::from_bytes`] and [`CasAssertion::check`], which hash every
//!   byte of a complete blob;
//! - [`CasRangeFact::slice`], which cuts a fact down to a sub-range, so that a
//!   whole-blob fact yields range facts and a `0..` fact yields a whole-blob
//!   one;
//! - [`CasRangeFact::fuse`], which joins two overlapping or touching facts
//!   about the same blob, so that a prefix and a suffix yield a whole-blob
//!   fact;
//! - [`RangeProof::check`], which validates a byte range against the BLAKE3
//!   chaining values around it without holding the rest of the blob.
//!
//! There is no separate length fact. A length claim is the empty case of an
//! open-ended range: a fact about `n..` whose bytes are empty says only that
//! the blob is `n` bytes long, which is what a `CasLengthFact` would carry.
//! [`CasRangeFact::blob_len`] reads it back, and answers `None` for a bounded
//! range, so a range's end is never mistaken for the blob's.
//!
//! The corresponding Lean theory names the unchecked whole-blob proposition
//! `Nucleus.CasAssertion.Valid` and the checked atom `Nucleus.CasPair`; see
//! issue #875. This crate erases the Lean proof while preserving the same LCF
//! constructor boundary in safe Rust. The range rules have no Lean counterpart
//! yet.

mod fact;
pub mod proof;
#[cfg(feature = "prove")]
pub mod prove;
pub mod range;

pub use bytes::Bytes;
pub use covalence_lib_hash::{O256, blake3::Blake3Cv};

pub use fact::{
    CasAssertion, CasCheckError, CasFact, CasRangeAssertion, CasRangeFact, FuseError, SliceError,
};
pub use proof::{BLOCK_LEN, MAX_LEVEL, RangeProof, RangeProofError, block_len};
pub use range::{BlobRange, BlobSpan, FuseRange};

use std::ops::{Deref, DerefMut, Range};

use covalence_lib_error::snafu::Snafu;

impl<R: BlobRange> Deref for CasRangeFact<R> {
    type Target = CasRangeAssertion<R>;

    fn deref(&self) -> &Self::Target {
        self.as_assertion()
    }
}

impl<R: BlobRange> Deref for CasRangeAssertion<R> {
    type Target = Bytes;

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

// An assertion is unchecked data. Mutating its `Bytes` view deliberately does
// not recompute the claimed hash; a later check validates the new claim.
impl<R: BlobRange> DerefMut for CasRangeAssertion<R> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}

impl<R: BlobRange> AsRef<[u8]> for CasRangeAssertion<R> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<R: BlobRange> AsRef<[u8]> for CasRangeFact<R> {
    fn as_ref(&self) -> &[u8] {
        self.bytes().as_ref()
    }
}

impl<R: BlobRange> From<CasRangeFact<R>> for CasRangeAssertion<R> {
    fn from(fact: CasRangeFact<R>) -> Self {
        fact.into_assertion()
    }
}

impl<R: BlobRange> From<&CasRangeFact<R>> for CasRangeAssertion<R> {
    fn from(fact: &CasRangeFact<R>) -> Self {
        fact.as_assertion().clone()
    }
}

/// A read-only source of content-addressed bytes.
///
/// Implementations are untrusted. The raw operations are useful when a caller
/// does not need an LCF fact. Returned [`Bytes`] values own or share the
/// storage needed to remain valid independently of the CAS.
/// [`Self::get_fact`] may avoid hashing when a provider already holds checked
/// facts, while [`CasExt::get_checked`] still verifies that the returned fact
/// answers the requested address.
pub trait Cas {
    /// Implementation-specific lookup or I/O failure.
    type Error: std::error::Error + 'static;

    /// Gets all bytes at `address`, or returns `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup or read failure.
    fn get_bytes(&self, address: O256) -> Result<Option<Bytes>, Self::Error>;

    /// Gets the length at `address`, or `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup or read failure.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
        self.get_bytes(address).map(|bytes| {
            bytes.map(|bytes| {
                u64::try_from(bytes.len()).unwrap_or_else(|_| panic!("CAS object exceeds u64"))
            })
        })
    }

    /// Gets exactly `range`, or `None` when `address` is absent.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific lookup, read, or range failure.
    fn get_range(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error>;

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
        self.get_bytes(address)
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
    use std::{collections::BTreeSet, io, ops::Range};

    use super::*;

    #[test]
    fn whole_assertion_checks_every_byte() {
        let blob = Bytes::from(vec![0x5a; 64 * 1024 + 1]);
        let hash = O256::from_bytes(&blob);
        let fact = CasAssertion {
            hash,
            range: ..,
            bytes: blob.clone(),
        }
        .check()
        .unwrap();

        assert_eq!(fact.hash(), hash);
        assert_eq!(fact.bytes(), &blob);

        let mut changed = blob.to_vec();
        *changed.last_mut().unwrap() ^= 1;
        let error = CasAssertion {
            hash,
            range: ..,
            bytes: Bytes::from(changed),
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
            range: ..,
            bytes: Bytes::from_static(b"blob"),
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
            range: ..,
            bytes: fact.bytes().clone(),
        };

        assert_eq!(CasAssertion::from(&fact), expected);
        assert_eq!(fact.into_assertion(), expected);
    }

    #[test]
    fn assertions_and_facts_borrow_their_blob_bytes() {
        let mut assertion = CasAssertion::new(
            O256::from_bytes(b"claimed"),
            ..,
            Bytes::from_static(b"blob"),
        );
        assert_eq!(AsRef::<[u8]>::as_ref(&assertion), b"blob");

        assertion.clear();
        assert!(assertion.bytes.is_empty());
        assert!(assertion.check().is_err());

        let fact = CasFact::from_bytes(Bytes::from_static(b"checked"));
        assert_eq!(AsRef::<[u8]>::as_ref(&fact), b"checked");
    }

    #[test]
    fn assertions_and_facts_have_lexicographic_value_order() {
        let facts = [
            CasFact::from_bytes(Bytes::from_static(b"c")),
            CasFact::from_bytes(Bytes::from_static(b"a")),
            CasFact::from_bytes(Bytes::from_static(b"b")),
        ];
        let fact_set = facts.clone().into_iter().collect::<BTreeSet<_>>();
        let assertion_set = facts
            .iter()
            .map(CasAssertion::from)
            .collect::<BTreeSet<_>>();

        assert_eq!(fact_set.len(), facts.len());
        assert_eq!(assertion_set.len(), facts.len());
        assert_eq!(
            fact_set
                .iter()
                .map(|fact| (fact.hash(), fact.bytes().clone()))
                .collect::<Vec<_>>(),
            assertion_set
                .iter()
                .map(|assertion| (assertion.hash, assertion.bytes.clone()))
                .collect::<Vec<_>>()
        );
    }

    struct LyingCas(CasFact);

    impl Cas for LyingCas {
        type Error = io::Error;

        fn get_bytes(&self, _address: O256) -> Result<Option<Bytes>, Self::Error> {
            Ok(Some(self.0.bytes().clone()))
        }

        fn get_range(
            &self,
            _address: O256,
            range: Range<u64>,
        ) -> Result<Option<Bytes>, Self::Error> {
            let start = usize::try_from(range.start)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range start"))?;
            let end = usize::try_from(range.end)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range end"))?;
            let bytes = self.0.bytes();
            if start > end || end > bytes.len() {
                return Err(io::Error::new(io::ErrorKind::InvalidInput, "range"));
            }
            Ok(Some(bytes.slice(start..end)))
        }

        fn get_fact(&self, _address: O256) -> Result<Option<CasFact>, CasLookupError<Self::Error>> {
            Ok(Some(self.0.clone()))
        }
    }

    #[test]
    fn checked_lookup_rejects_fact_for_another_address() {
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

        fn get_bytes(&self, _address: O256) -> Result<Option<Bytes>, Self::Error> {
            Err(io::Error::other("offline"))
        }

        fn get_range(
            &self,
            _address: O256,
            _range: Range<u64>,
        ) -> Result<Option<Bytes>, Self::Error> {
            Err(io::Error::other("offline"))
        }
    }

    #[test]
    fn checked_lookup_preserves_provider_failure() {
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
