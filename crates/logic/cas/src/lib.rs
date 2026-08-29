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
//!
//! [`CasRangeFact::blob_len`] reads that length back. It answers `None` for a
//! bounded range, so a range's end is never mistaken for the blob's.
//!
//! The corresponding Lean theory names the unchecked whole-blob proposition
//! `Nucleus.CasAssertion.Valid` and the checked atom `Nucleus.CasPair`; see
//! issue #875. This crate erases the Lean proof while preserving the same LCF
//! constructor boundary in safe Rust. The range rules have no Lean counterpart
//! yet.
//!
//! # Blob expressions
//!
//! [`BlobExpr`] is a second, more general layer: a little algebra of
//! expressions — a content address, literal bytes, a run of zeros, a
//! concatenation, a sub-range — together with [`BlobEq`], the proposition that
//! two of them denote the same byte string.
//!
//! ## Models
//!
//! An expression is *syntax* and means nothing on its own. It is interpreted
//! in a **model**: a map
//!
//! ```text
//! σ : O256 -> Bytes
//! ```
//!
//! with three properties.
//!
//! - **Total**: defined at every hash.
//! - **Injective**: different hashes go to different byte strings.
//! - **Extends the CAS**: `σ h = b` for every checked pair `(h, b)`, and, for a
//!   [`CasRangeFact`] covering only part of a blob, `σ h` agrees with that
//!   fact's bytes on just that range.
//!
//! The checked facts of this crate *are* the CAS as far as this definition is
//! concerned; nothing else pins `σ`.
//!
//! Interpretation is then the partial function
//!
//! | Expression | `denote σ` |
//! | ---------- | ---------- |
//! | `Blake3(h)` | `Some(σ h)` — always defined |
//! | `Bytes(v)` | `Some(v)` |
//! | `Zero(n)` | `Some` of `n` zero bytes |
//! | `Cat(x, y)` | the two denotations concatenated, when both are defined |
//! | `Slice(e, s)` | the `s` sub-range of `denote σ e`, when `s` is in range |
//!
//! **Totality** is why a digest is never undefined. `σ` reads some byte string
//! at every hash, pinned or not; what varies from model to model is *which*
//! bytes, never *whether* there are any.
//!
//! Undefinedness has exactly two sources: a slice whose span runs past its
//! subject, and a concatenation with an undefined side.
//!
//! **Injectivity** is what licenses [`BlobProp::decide`] to refute an equality
//! between two different digests. It is the right condition because `σ h` is
//! *the* blob that `h` names, and two different hashes cannot name one blob:
//! naming is a function, so `name b` determines `h` uniquely.
//!
//! *Considered, not adopted:* the stronger *section* property, `name (σ h) = h`
//! for every `h`. It implies injectivity, so it would license the digest
//! refutation too, and it would buy one branch this calculus does not have:
//! `Blake3(h)` against literal `Bytes(v)` could be refuted whenever
//! `name v != h`, since `name (σ h) = h != name v` forces `σ h != v` in every
//! model.
//!
//! Two things argue against it:
//!
//! - the digest refutation is already two lines from injectivity alone;
//! - a section exists only if `name` is *surjective* onto the hashes anyone
//!   writes down, a strictly stronger existence assumption than the one below,
//!   for a completeness gain nothing yet needs.
//!
//! ## Standing assumption: the CAS is collision-free
//!
//! Everything in this layer is sound relative to the existence of at least one
//! model, and that existence is exactly collision-freedom.
//!
//! A `σ` extending the CAS exists if and only if no hash is pinned to two
//! different blobs.
//!
//! The pinned part is finite, and it is automatically injective: `name` is a
//! function, so no blob is pinned to two hashes. There are infinitely many byte
//! strings, so a finite injective partial map always extends to a total
//! injection. The sole obstruction is therefore a single hash pinned to two
//! different blobs — precisely a collision.
//!
//! Under a collision there are no models, every proposition is vacuously valid,
//! and the calculus is unsound.
//!
//! That is the standing hypothesis of the whole calculus, stated here once: no
//! rule repeats it, no rule's name carries it, and no rule has a side condition
//! standing in for it.
//!
//! ## Validity
//!
//! [`BlobEq`] `l r` is *valid* when `denote σ l = denote σ r` for every model
//! `σ`. The comparison is of two `Option`s, so two expressions undefined in
//! every model count as equal: this is the weak, Kleene reading.
//!
//! The weak reading is what keeps [`BlobFact::refl`] unconditional: an
//! out-of-range slice is equal to itself. Nothing leaks out of it either, since
//! undefinedness propagates outward through `Cat` and `Slice` rather than
//! turning into a byte string.
//!
//! *Considered, not adopted:* the strong reading, requiring both sides to be
//! defined as well as equal. It would cost a total `refl`: reflexivity would
//! carry a definedness side condition that [`BlobExpr::len`] can only sometimes
//! discharge, and never for a `Cat` measuring past `u64`. The strong claim
//! remains expressible as a `BlobEq` alongside a definedness certificate.
//!
//! ## Observations
//!
//! [`BlobExpr::len`] answers `Option<u64>`. `Some(n)` certifies that the
//! expression is defined in every model and is `n` bytes long in every one of
//! them. That certificate is what makes length disagreement a sound refutation.
//!
//! `Blake3(h)` is `None`: always defined, but `σ h` varies with the model, so
//! no single `n` answers.
//!
//! Unknown lengths compare like SQL `NULL` — none agrees with anything, not
//! even itself — so they are compared only through [`cmp_length`], never with
//! `==`.
//!
//! [`BlobExpr::eval`] is the stronger certificate: `Some(v)` says the
//! expression denotes exactly `v` in every model.
//!
//! [`BlobLike::size`] is the third observation, and the only one that is not
//! about denotation at all. It counts the expression as a tree. `Cat` shares
//! its children through an [`Arc`](std::sync::Arc), so a DAG of `n + 1` nodes
//! can denote a tree of `2^n` leaves, and the observations that read an
//! expression walk the tree.
//!
//! Every constructor here is nonetheless total, so such a DAG can be built. It
//! is a degenerate input, and dying on one is acceptable where a wrong answer
//! is not.
//!
//! So the measurements are made not to lie: the size saturates and the length
//! is summed with `checked_add`. The observations that would have to walk the
//! tree — [`BlobExpr::len`], [`BlobExpr::eval`] and [`BlobProp::decide`] among
//! them — decline past [`MAX_TREE_NODES`]. Declining proves nothing false:
//! `None` means "the rules do not settle it", which costs completeness only.
//!
//! `==` and `Drop` are deliberately left unlimited, the first because a limit
//! would change what equality means and the second because it cannot decline
//! at all.
//!
//! [`BlobFact`] is the LCF wrapper over that layer, the counterpart of
//! [`CasRangeFact`] one level up. Its rules are
//!
//! - evaluation, [`BlobFact::check`], which turns a decided proposition into a
//!   fact;
//! - [`BlobFact::refl`], [`BlobFact::symm`] and [`BlobFact::trans`];
//! - congruence for the two operators, [`BlobFact::cat`] and
//!   [`BlobFact::slice`].
//!
//! Congruence yields equality and never disequality, so the sound partial
//! converse — cancelling a `Cat` operand that is defined in every model — is a
//! separate rule. It is deferred, marked by a `DEFERRED:` comment in `eq.rs`,
//! as is n-ary distinctness.
//!
//! Every rule but [`BlobFact::check`] and [`BlobFact::trans`] is total,
//! including the two congruence rules: they build a bigger expression, and what
//! happens past [`MAX_TREE_NODES`] is that [`BlobProp::decide`] stops answering
//! about it, not that the rule stops applying.
//!
//! ## `CasFact` is not a blob-expression fact
//!
//! The two layers are still not unified, but the reason is now shape rather
//! than strength. A [`CasRangeFact`] is a checked pair carrying its bytes; a
//! [`BlobEq`] is a claim about two expressions, and only some equalities have
//! a range fact's shape.
//!
//! Their *content* agrees. A model extends the CAS by definition, so a checked
//! pair makes its equality valid. Conversely, an equality `Blake3(h) = Bytes(v)`
//! can only be valid if the CAS pins `h`, since an unpinned `h` is free and
//! some model reads other bytes there.
//!
//! Both directions of the bridge are therefore ordinary rules with no
//! hypothesis of their own beyond the standing one.
//! [`CasRangeFact::to_blob_fact`] goes up and [`BlobFact::to_range_fact`]
//! comes back down; the latter is partial only in the shapes it can express,
//! never in what it believes.
//!
//! Neither is decidable from within the calculus, because
//! [`BlobProp::decide`] cannot read a store. That is what makes going up a
//! genuine introduction rule.

mod blob;
mod eq;
mod fact;
pub mod proof;
#[cfg(feature = "prove")]
pub mod prove;
pub mod range;

pub use bytes::Bytes;
pub use covalence_lib_hash::{O256, blake3::Blake3Cv};

pub use blob::{
    BlobCat, BlobExpr, BlobLike, BlobSlice, MAX_EVAL_BYTES, MAX_TREE_NODES, cmp_length,
};
pub use eq::{BlobEq, BlobFact, BlobProp};
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
///
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
