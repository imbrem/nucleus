//! Synchronous content-addressed byte sources.
//!
//! [`Cas`] is the trusted interface. Its primitive is *opening* an address,
//! not reading one: [`Cas::open`] resolves an address once and returns a
//! [`CasObject`] which serves ranges thereafter. [`Verified`] upgrades an
//! untrusted [`RangeSource`] by checking every response with a
//! [`RangeVerifier`] before exposing it through [`Cas`].
//!
//! [`MemoryCas`] is the concrete starting point: whole objects, resident in
//! memory, admitted by hashing complete bytes.
//!
//! # Why opening is the primitive
//!
//! An address-keyed `read` cannot promise anything about an object it is not
//! holding. If the object is dropped from the store between two reads, the
//! second fails — so a database opened over a content-addressed file would
//! start failing mid-query. Handing out an object instead makes the guarantee
//! structural: *while you hold it, it reads*. Removal affects only future
//! opens.
//!
//! This also gives composition somewhere to attach. A copy-on-write layer, an
//! overlay, or a cache is naturally an object built from other objects, and it
//! can hold its bases open for exactly as long as it needs them. That is not
//! expressible when the only operation is "read this address, now".
//!
//! # Why the contract is only open, len, and read
//!
//! Because that is what a directory of files can do. Name each file by its own
//! address and a plain file server implements this interface exactly:
//! `GET /cas/<address>` with ranges, and 404 for an address it does not hold.
//! So does an S3 bucket, and so does static hosting. Nothing about a store
//! that small should need writing.
//!
//! Nothing else belongs in the contract for the same reason. Listing is the
//! obvious candidate and the clearest mistake: a bucket cannot cheaply
//! enumerate, an overlay has no single list to give, and putting it here would
//! mean every implementation either lies or refuses. `MemoryCas::addresses`
//! exists because that store happens to keep a map, and callers must treat it
//! as a property of that store rather than of stores.
//!
//! The direction this points is worth being explicit about: **a more capable
//! store is a front end over a simpler one, not a bigger interface.** A store
//! wanting an index, a manifest, or a packing scheme for ten thousand small
//! objects should keep that state *in* a simple store -- an `SQLite` database
//! is itself one object, at one address -- and serve this same interface over
//! the result. That way the sophisticated thing composes onto the dumb thing,
//! and the dumb thing stays something you can host anywhere.

mod memory;

pub use memory::{
    AdmissionError, CasStats, InvalidRange, MAX_OBJECT_BYTES, MemoryCas, ResidentObject,
};

use std::ops::Range;

use bytes::Bytes;
use covalence_lib_hash::O256;

/// A trusted, immutable content-addressed byte source.
pub trait Cas: Send + Sync {
    /// Implementation-specific failure.
    type Error;

    /// An object opened from this source.
    type Object: CasObject<Error = Self::Error>;

    /// Opens `address`, or returns `None` when it does not resolve.
    ///
    /// The returned object stays readable for as long as it is held, whatever
    /// happens to the store afterwards. Resolving an address is therefore a
    /// one-time act, and implementations may do their length lookup,
    /// authentication, or handle acquisition here rather than per read.
    ///
    /// `None` is an unauthenticated, fail-closed absence signal. It means this
    /// source did not produce the object, not that no such object exists.
    ///
    /// # Errors
    ///
    /// Returns an error when the source fails to answer at all, as distinct
    /// from answering that the address does not resolve.
    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error>;

    /// Returns the length of `address`, or `None` when it does not resolve.
    ///
    /// # Errors
    ///
    /// Returns an error when the source cannot determine the length.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
        Ok(self.open(address)?.map(|object| object.len()))
    }

    /// Returns exactly `range` from `address`, or `None` when it does not
    /// resolve.
    ///
    /// This is a convenience for a single read. A caller making several reads
    /// of one address should [`open`](Self::open) it instead, both to resolve
    /// once and to hold the object still.
    ///
    /// # Errors
    ///
    /// Returns an error when the range cannot be served or authenticated.
    fn read(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        self.open(address)?
            .map(|object| object.read(range))
            .transpose()
    }
}

/// An object opened from a [`Cas`].
///
/// Holding one keeps its bytes readable. An implementation must not depend on
/// the address still resolving in the store it came from.
pub trait CasObject: Send + Sync {
    /// Implementation-specific failure.
    type Error;

    /// Returns the object's total length in bytes.
    ///
    /// This is fixed for the object's lifetime: content-addressed objects are
    /// immutable, so length cannot change under a holder.
    fn len(&self) -> u64;

    /// Returns whether the object is empty.
    ///
    /// An empty object is a legitimate object, distinct from an address which
    /// does not resolve.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns exactly `range`.
    ///
    /// Implementations must reject a reversed range or one extending past
    /// [`len`](Self::len) rather than truncating it. A short read is an error,
    /// not a silent partial answer.
    ///
    /// # Errors
    ///
    /// Returns an error when the range is invalid, cannot be served, or cannot
    /// be authenticated.
    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error>;
}

/// Data and opaque authentication evidence returned by an untrusted source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UntrustedRange {
    /// Total length claimed for the complete object.
    pub total_len: u64,
    /// Bytes returned for the requested range.
    pub data: Bytes,
    /// Verifier-specific proof encoding.
    pub proof: Bytes,
}

/// An untrusted source of ranged data and authentication evidence.
pub trait RangeSource: Send + Sync {
    /// Source failure.
    type Error;

    /// Fetches data and evidence for `range`.
    ///
    /// Returning a value makes no authenticity claim. Returning `None` is an
    /// unauthenticated, fail-closed absence signal: it is safe for integrity
    /// but may reduce availability and is not proof of non-membership.
    /// Authenticated non-membership requires verifier-specific evidence and
    /// may be added by a future protocol.
    ///
    /// # Errors
    ///
    /// Returns an error when the source cannot answer the request.
    fn fetch(
        &self,
        address: O256,
        range: Range<u64>,
    ) -> Result<Option<UntrustedRange>, Self::Error>;
}

/// Checks an untrusted range against its expected content address.
pub trait RangeVerifier: Send + Sync {
    /// Verification failure.
    type Error;

    /// Verifies one source response.
    ///
    /// # Errors
    ///
    /// Returns an error if the response is malformed or unauthenticated.
    fn verify(
        &self,
        address: O256,
        range: Range<u64>,
        response: &UntrustedRange,
    ) -> Result<(), Self::Error>;
}

/// Error returned by [`Verified`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerifiedError<S, V> {
    /// The untrusted source failed.
    Source(S),
    /// Authentication failed.
    Verify(V),
    /// The requested range was reversed or exceeded the claimed object.
    InvalidRange {
        start: u64,
        end: u64,
        total_len: Option<u64>,
    },
    /// The source returned the wrong number of bytes.
    WrongLength { expected: u64, actual: usize },
    /// The source stopped serving an object which had already been opened.
    Withdrawn,
    /// The source restated a total length contradicting the opened one.
    LengthChanged {
        /// Length authenticated when the object was opened.
        opened: u64,
        /// Length the source has now returned.
        returned: u64,
    },
}

impl<S: std::fmt::Display, V: std::fmt::Display> std::fmt::Display for VerifiedError<S, V> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(error) => write!(formatter, "range source failed: {error}"),
            Self::Verify(error) => write!(formatter, "range verification failed: {error}"),
            Self::InvalidRange {
                start,
                end,
                total_len,
            } => match total_len {
                Some(total_len) => {
                    write!(
                        formatter,
                        "invalid range {start}..{end} for length {total_len}"
                    )
                }
                None => write!(formatter, "invalid reversed range {start}..{end}"),
            },
            Self::WrongLength { expected, actual } => {
                write!(formatter, "expected {expected} bytes, received {actual}")
            }
            Self::Withdrawn => formatter.write_str("the source withdrew an opened object"),
            Self::LengthChanged { opened, returned } => write!(
                formatter,
                "object opened at {opened} bytes is now claimed to be {returned}"
            ),
        }
    }
}

impl<S, V> std::error::Error for VerifiedError<S, V>
where
    S: std::error::Error + 'static,
    V: std::error::Error + 'static,
{
}

/// A trusted CAS view over an untrusted source and a verifier.
///
/// The source and verifier are held behind [`Arc`](std::sync::Arc) so that an
/// opened object can keep them alive independently of this view. An object
/// must stay readable once handed out, and for a remote source that means
/// still being able to fetch and authenticate.
pub struct Verified<S, V> {
    source: std::sync::Arc<S>,
    verifier: std::sync::Arc<V>,
}

impl<S, V> Verified<S, V> {
    /// Constructs a verified view.
    #[must_use]
    pub fn new(source: S, verifier: V) -> Self {
        Self {
            source: std::sync::Arc::new(source),
            verifier: std::sync::Arc::new(verifier),
        }
    }

    /// Borrows the underlying source.
    #[must_use]
    pub fn source(&self) -> &S {
        &self.source
    }

    /// Borrows the verifier.
    #[must_use]
    pub fn verifier(&self) -> &V {
        &self.verifier
    }
}

/// An object opened from a [`Verified`] view.
///
/// Every read is fetched from the untrusted source and authenticated before
/// being returned, exactly as it would be through the view. The object exists
/// so that the length claim is established once, at open, and so that holding
/// it keeps the source and verifier alive.
pub struct VerifiedObject<S, V> {
    source: std::sync::Arc<S>,
    verifier: std::sync::Arc<V>,
    address: O256,
    len: u64,
}

impl<S, V> CasObject for VerifiedObject<S, V>
where
    S: RangeSource,
    V: RangeVerifier,
{
    type Error = VerifiedError<S::Error, V::Error>;

    fn len(&self) -> u64 {
        self.len
    }

    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
        let expected = range
            .end
            .checked_sub(range.start)
            .ok_or(VerifiedError::InvalidRange {
                start: range.start,
                end: range.end,
                total_len: Some(self.len),
            })?;
        if range.end > self.len {
            return Err(VerifiedError::InvalidRange {
                start: range.start,
                end: range.end,
                total_len: Some(self.len),
            });
        }
        let response = self
            .source
            .fetch(self.address, range.clone())
            .map_err(VerifiedError::Source)?
            // The object was resolvable at open. A source which now denies it
            // is a source failure, not an absence: the object is still an
            // object, and the holder was promised it would read.
            .ok_or(VerifiedError::Withdrawn)?;
        // The source restates the total length on every response. It is
        // untrusted, so a restatement which contradicts the one authenticated
        // at open is rejected rather than believed.
        if response.total_len != self.len {
            return Err(VerifiedError::LengthChanged {
                opened: self.len,
                returned: response.total_len,
            });
        }
        if response.data.len() as u64 != expected {
            return Err(VerifiedError::WrongLength {
                expected,
                actual: response.data.len(),
            });
        }
        self.verifier
            .verify(self.address, range, &response)
            .map_err(VerifiedError::Verify)?;
        Ok(response.data)
    }
}

impl<S, V> Cas for Verified<S, V>
where
    S: RangeSource,
    V: RangeVerifier,
{
    type Error = VerifiedError<S::Error, V::Error>;
    type Object = VerifiedObject<S, V>;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        // An empty range is the length probe: it carries no data, so a
        // well-behaved source answers it with evidence and nothing else.
        let response = self
            .source
            .fetch(address, 0..0)
            .map_err(VerifiedError::Source)?;
        let Some(response) = response else {
            return Ok(None);
        };
        if !response.data.is_empty() {
            return Err(VerifiedError::WrongLength {
                expected: 0,
                actual: response.data.len(),
            });
        }
        self.verifier
            .verify(address, 0..0, &response)
            .map_err(VerifiedError::Verify)?;
        Ok(Some(VerifiedObject {
            source: std::sync::Arc::clone(&self.source),
            verifier: std::sync::Arc::clone(&self.verifier),
            address,
            len: response.total_len,
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use covalence_lib_hash::Obj;

    use super::*;

    const ADDRESS: O256 = Obj::from_array([7; 32]);

    struct Source {
        response: Option<UntrustedRange>,
        requests: Mutex<Vec<Range<u64>>>,
    }

    impl RangeSource for Source {
        type Error = ();

        fn fetch(
            &self,
            address: O256,
            range: Range<u64>,
        ) -> Result<Option<UntrustedRange>, Self::Error> {
            assert_eq!(address, ADDRESS);
            self.requests.lock().unwrap().push(range.clone());
            // The empty range is the length probe `open` issues. A source
            // answers it with evidence and no data.
            if range == (0..0) {
                return Ok(self.response.as_ref().map(|response| UntrustedRange {
                    data: Bytes::new(),
                    ..response.clone()
                }));
            }
            Ok(self.response.clone())
        }
    }

    struct Verifier {
        accepted: bool,
    }

    impl RangeVerifier for Verifier {
        type Error = &'static str;

        fn verify(
            &self,
            address: O256,
            range: Range<u64>,
            response: &UntrustedRange,
        ) -> Result<(), Self::Error> {
            assert_eq!(address, ADDRESS);
            assert_eq!(response.proof, Bytes::from_static(b"proof"));
            // The probe must authenticate too, or nothing could ever be
            // opened. Only the data range is gated by `accepted`.
            if range == (0..0) {
                return Ok(());
            }
            if self.accepted && range == (2..5) {
                Ok(())
            } else {
                Err("bad proof")
            }
        }
    }

    fn response(data: &'static [u8]) -> UntrustedRange {
        UntrustedRange {
            total_len: 9,
            data: Bytes::from_static(data),
            proof: Bytes::from_static(b"proof"),
        }
    }

    #[test]
    fn authenticated_range_is_exposed() {
        let source = Source {
            response: Some(response(b"cde")),
            requests: Mutex::new(Vec::new()),
        };
        let cas = Verified::new(source, Verifier { accepted: true });

        assert_eq!(
            cas.read(ADDRESS, 2..5).unwrap(),
            Some(Bytes::from_static(b"cde"))
        );
        // One probe at open, one fetch for the data.
        let requests = cas.source().requests.lock().unwrap();
        assert_eq!(requests.len(), 2);
        assert_eq!(requests[0], 0..0);
        assert_eq!(requests[1], 2..5);
    }

    #[test]
    fn rejected_proof_never_exposes_data() {
        let cas = Verified::new(
            Source {
                response: Some(response(b"cde")),
                requests: Mutex::new(Vec::new()),
            },
            Verifier { accepted: false },
        );

        assert_eq!(
            cas.read(ADDRESS, 2..5),
            Err(VerifiedError::Verify("bad proof"))
        );
    }

    #[test]
    fn wrong_data_length_is_rejected_before_verification() {
        let cas = Verified::new(
            Source {
                response: Some(response(b"cd")),
                requests: Mutex::new(Vec::new()),
            },
            Verifier { accepted: true },
        );

        assert_eq!(
            cas.read(ADDRESS, 2..5),
            Err(VerifiedError::WrongLength {
                expected: 3,
                actual: 2
            })
        );
    }

    #[test]
    fn absence_is_preserved() {
        let cas = Verified::new(
            Source {
                response: None,
                requests: Mutex::new(Vec::new()),
            },
            Verifier { accepted: true },
        );

        assert_eq!(cas.read(ADDRESS, 2..5).unwrap(), None);
    }

    #[test]
    fn invalid_ranges_are_rejected() {
        let cas = Verified::new(
            Source {
                response: Some(response(b"")),
                requests: Mutex::new(Vec::new()),
            },
            Verifier { accepted: true },
        );

        // After `open`, the length is known, so both a reversed range and one
        // past the end are reported against it.
        let start = 5;
        let end = 2;
        assert_eq!(
            cas.read(ADDRESS, start..end),
            Err(VerifiedError::InvalidRange {
                start: 5,
                end: 2,
                total_len: Some(9),
            })
        );
        assert_eq!(
            cas.read(ADDRESS, 9..10),
            Err(VerifiedError::InvalidRange {
                start: 9,
                end: 10,
                total_len: Some(9),
            })
        );
    }
}
