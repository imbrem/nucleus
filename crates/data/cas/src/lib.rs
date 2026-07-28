//! Synchronous content-addressed byte sources.
//!
//! [`Cas`] is the trusted interface: implementations may serve any requested
//! byte range, but the bytes must belong to the object named by the address.
//! [`Verified`] upgrades an untrusted [`RangeSource`] by checking every
//! response with a [`RangeVerifier`] before exposing it through [`Cas`].

use std::ops::Range;

use bytes::Bytes;
use covalence_lib_hash::O256;

/// A trusted, immutable content-addressed byte source.
pub trait Cas: Send + Sync {
    /// Implementation-specific failure.
    type Error;

    /// Returns the length of `address`, or `None` when it is absent.
    ///
    /// # Errors
    ///
    /// Returns an error when the source cannot determine the length.
    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error>;

    /// Returns exactly `range` from `address`, or `None` when it is absent.
    ///
    /// Implementations must reject ranges outside the object.
    ///
    /// # Errors
    ///
    /// Returns an error when the range cannot be served or authenticated.
    fn read(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error>;
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
pub struct Verified<S, V> {
    source: S,
    verifier: V,
}

impl<S, V> Verified<S, V> {
    /// Constructs a verified view.
    #[must_use]
    pub const fn new(source: S, verifier: V) -> Self {
        Self { source, verifier }
    }

    /// Borrows the underlying source.
    #[must_use]
    pub const fn source(&self) -> &S {
        &self.source
    }

    /// Borrows the verifier.
    #[must_use]
    pub const fn verifier(&self) -> &V {
        &self.verifier
    }
}

impl<S, V> Cas for Verified<S, V>
where
    S: RangeSource,
    V: RangeVerifier,
{
    type Error = VerifiedError<S::Error, V::Error>;

    fn len(&self, address: O256) -> Result<Option<u64>, Self::Error> {
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
        Ok(Some(response.total_len))
    }

    fn read(&self, address: O256, range: Range<u64>) -> Result<Option<Bytes>, Self::Error> {
        let expected = range
            .end
            .checked_sub(range.start)
            .ok_or(VerifiedError::InvalidRange {
                start: range.start,
                end: range.end,
                total_len: None,
            })?;
        let response = self
            .source
            .fetch(address, range.clone())
            .map_err(VerifiedError::Source)?;
        let Some(response) = response else {
            return Ok(None);
        };
        if range.end > response.total_len {
            return Err(VerifiedError::InvalidRange {
                start: range.start,
                end: range.end,
                total_len: Some(response.total_len),
            });
        }
        if response.data.len() as u64 != expected {
            return Err(VerifiedError::WrongLength {
                expected,
                actual: response.data.len(),
            });
        }
        self.verifier
            .verify(address, range, &response)
            .map_err(VerifiedError::Verify)?;
        Ok(Some(response.data))
    }
}
