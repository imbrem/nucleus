//! Verification of BLAKE3 ranges through an untrusted source.

use std::{convert::Infallible, fmt, ops::Range};

use blake3::hazmat;

use super::{Blake3, Blake3Cv, Cov, CtxKey, range::Blake3ProofMode};
use crate::{O256, Obj};

/// Synchronous, untrusted storage used while verifying BLAKE3 ranges.
///
/// The verifier chooses every requested range. Implementations may read from a
/// file, a remote object, or an existing proof encoding; returned bytes and CVs
/// are authenticated only when verification reaches the expected root.
pub trait Blake3ProofSource {
    /// Storage or transport failure.
    type Error;

    /// Fetches the exact bytes in `range`.
    ///
    /// # Errors
    ///
    /// Returns a source-specific storage or transport failure.
    fn fragment(&mut self, range: Range<u64>) -> Result<Vec<u8>, Self::Error>;

    /// Fetches the chaining value for the exact canonical subtree in `range`.
    ///
    /// # Errors
    ///
    /// Returns a source-specific storage or transport failure.
    fn cv(&mut self, range: Range<u64>) -> Result<Blake3Cv, Self::Error>;
}

/// A source operation requested by the verifier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Blake3SourceRequest {
    /// Raw bytes for this range.
    Fragment(Range<u64>),
    /// A chaining value for this canonical subtree.
    Cv(Range<u64>),
}

/// Failure to verify ranges through an untrusted source.
#[derive(Debug, Eq, PartialEq)]
pub enum Blake3SourceProofError<E> {
    /// The complete input is empty.
    EmptyInput,
    /// A desired range was empty, out of bounds, overlapping, or non-monotonic.
    InvalidRange {
        range: Range<u64>,
        total_length: u64,
    },
    /// Offset or length arithmetic overflowed.
    Overflow,
    /// A source operation failed.
    Source {
        request: Blake3SourceRequest,
        source: E,
    },
    /// A byte fragment did not have the requested length.
    InvalidFragmentLength { range: Range<u64>, actual: usize },
    /// Reconstructed root did not match the expected root.
    RootMismatch,
}

impl<E: fmt::Display> fmt::Display for Blake3SourceProofError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("range proofs require a non-empty input"),
            Self::InvalidRange {
                range,
                total_length,
            } => write!(
                formatter,
                "invalid or unordered range {}..{} for input length {total_length}",
                range.start, range.end
            ),
            Self::Overflow => formatter.write_str("range-proof offset or length overflowed"),
            Self::Source { request, source } => {
                write!(
                    formatter,
                    "source failed while fetching {request:?}: {source}"
                )
            }
            Self::InvalidFragmentLength { range, actual } => write!(
                formatter,
                "fragment {}..{} contained {actual} bytes",
                range.start, range.end
            ),
            Self::RootMismatch => formatter.write_str("range proof reconstructed the wrong root"),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Blake3SourceProofError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Source { source, .. } => Some(source),
            _ => None,
        }
    }
}

struct RequestedRanges {
    requested: Vec<Range<u64>>,
    covered: Vec<Range<u64>>,
}

fn covered_ranges(
    total_length: u64,
    ranges: impl IntoIterator<Item = Range<u64>>,
) -> Result<RequestedRanges, Blake3SourceProofError<Infallible>> {
    if total_length == 0 {
        return Err(Blake3SourceProofError::EmptyInput);
    }
    let chunk = blake3::CHUNK_LEN as u64;
    let mut requested = Vec::new();
    let mut covered: Vec<Range<u64>> = Vec::new();
    let mut previous_end = 0;
    for range in ranges {
        if range.start >= range.end
            || range.end > total_length
            || (!requested.is_empty() && range.start < previous_end)
        {
            return Err(Blake3SourceProofError::InvalidRange {
                range,
                total_length,
            });
        }
        previous_end = range.end;
        let start = range.start / chunk * chunk;
        let end = range
            .end
            .checked_add(chunk - 1)
            .ok_or(Blake3SourceProofError::Overflow)?
            / chunk
            * chunk;
        let rounded = start..end.min(total_length);
        if let Some(last) = covered.last_mut()
            && rounded.start <= last.end
        {
            last.end = last.end.max(rounded.end);
        } else {
            covered.push(rounded);
        }
        requested.push(range);
    }
    if requested.is_empty() {
        return Err(Blake3SourceProofError::InvalidRange {
            range: 0..0,
            total_length,
        });
    }
    Ok(RequestedRanges { requested, covered })
}

struct SourceVerification<'a, S> {
    covered: &'a [Range<u64>],
    source: &'a mut S,
    mode: Blake3ProofMode<'a>,
}

impl<S: Blake3ProofSource> SourceVerification<'_, S> {
    fn subtree(
        &mut self,
        offset: u64,
        length: u64,
    ) -> Result<Blake3Cv, Blake3SourceProofError<S::Error>> {
        let end = offset
            .checked_add(length)
            .ok_or(Blake3SourceProofError::Overflow)?;
        let range = offset..end;
        if self
            .covered
            .iter()
            .any(|covered| range.start >= covered.start && range.end <= covered.end)
        {
            let bytes = self.source.fragment(range.clone()).map_err(|source| {
                Blake3SourceProofError::Source {
                    request: Blake3SourceRequest::Fragment(range.clone()),
                    source,
                }
            })?;
            let expected = usize::try_from(length).map_err(|_| Blake3SourceProofError::Overflow)?;
            if bytes.len() != expected {
                return Err(Blake3SourceProofError::InvalidFragmentLength {
                    range,
                    actual: bytes.len(),
                });
            }
            return Ok(self.mode.subtree(offset, &bytes));
        }
        if self
            .covered
            .iter()
            .all(|covered| range.end <= covered.start || range.start >= covered.end)
        {
            return self.source.cv(range.clone()).map_err(|source| {
                Blake3SourceProofError::Source {
                    request: Blake3SourceRequest::Cv(range),
                    source,
                }
            });
        }
        if length <= blake3::CHUNK_LEN as u64 {
            return Err(Blake3SourceProofError::InvalidRange {
                range,
                total_length: end,
            });
        }
        let left_length = hazmat::left_subtree_len(length);
        let right_offset = offset
            .checked_add(left_length)
            .ok_or(Blake3SourceProofError::Overflow)?;
        let left = self.subtree(offset, left_length)?;
        let right = self.subtree(right_offset, length - left_length)?;
        Ok(self.mode.merge(left, right))
    }
}

fn verify_from_source<S: Blake3ProofSource>(
    expected: &[u8; 32],
    total_length: u64,
    ranges: impl IntoIterator<Item = Range<u64>>,
    source: &mut S,
    mode: Blake3ProofMode<'_>,
) -> Result<Vec<Range<u64>>, Blake3SourceProofError<S::Error>> {
    let ranges = covered_ranges(total_length, ranges).map_err(|error| match error {
        Blake3SourceProofError::EmptyInput => Blake3SourceProofError::EmptyInput,
        Blake3SourceProofError::InvalidRange {
            range,
            total_length,
        } => Blake3SourceProofError::InvalidRange {
            range,
            total_length,
        },
        Blake3SourceProofError::Overflow => Blake3SourceProofError::Overflow,
        _ => unreachable!(),
    })?;
    let actual = if total_length <= blake3::CHUNK_LEN as u64 {
        let range = 0..total_length;
        let bytes =
            source
                .fragment(range.clone())
                .map_err(|source| Blake3SourceProofError::Source {
                    request: Blake3SourceRequest::Fragment(range.clone()),
                    source,
                })?;
        let expected_length =
            usize::try_from(total_length).map_err(|_| Blake3SourceProofError::Overflow)?;
        if bytes.len() != expected_length {
            return Err(Blake3SourceProofError::InvalidFragmentLength {
                range,
                actual: bytes.len(),
            });
        }
        mode.hash(&bytes)
    } else {
        let left_length = hazmat::left_subtree_len(total_length);
        let mut verification = SourceVerification {
            covered: &ranges.covered,
            source,
            mode,
        };
        let left = verification.subtree(0, left_length)?;
        let right = verification.subtree(left_length, total_length - left_length)?;
        mode.root(left, right)
    };
    if &actual != expected {
        return Err(Blake3SourceProofError::RootMismatch);
    }
    Ok(ranges.requested)
}

macro_rules! impl_source_verification {
    ($namespace:ty) => {
        impl Obj<$namespace> {
            /// Verifies ordered, non-overlapping ranges through an untrusted source.
            ///
            /// # Errors
            ///
            /// Returns an error for invalid ranges, source failures, malformed
            /// fragments, arithmetic overflow, or a root mismatch.
            pub fn verify_blake3_ranges_from<S: Blake3ProofSource>(
                &self,
                total_length: u64,
                ranges: impl IntoIterator<Item = Range<u64>>,
                source: &mut S,
            ) -> Result<Vec<Range<u64>>, Blake3SourceProofError<S::Error>> {
                verify_from_source(
                    self.as_bytes(),
                    total_length,
                    ranges,
                    source,
                    Blake3ProofMode::Unkeyed,
                )
            }

            /// Verifies keyed-BLAKE3 ranges through an untrusted source.
            ///
            /// # Errors
            ///
            /// Returns an error for invalid ranges, source failures, malformed
            /// fragments, arithmetic overflow, or a root mismatch.
            pub fn verify_blake3_keyed_ranges_from<S: Blake3ProofSource>(
                &self,
                key: &O256,
                total_length: u64,
                ranges: impl IntoIterator<Item = Range<u64>>,
                source: &mut S,
            ) -> Result<Vec<Range<u64>>, Blake3SourceProofError<S::Error>> {
                verify_from_source(
                    self.as_bytes(),
                    total_length,
                    ranges,
                    source,
                    Blake3ProofMode::Keyed(key),
                )
            }

            /// Verifies context-keyed BLAKE3 ranges through an untrusted source.
            ///
            /// # Errors
            ///
            /// Returns an error for invalid ranges, source failures, malformed
            /// fragments, arithmetic overflow, or a root mismatch.
            pub fn verify_blake3_context_ranges_from<S: Blake3ProofSource>(
                &self,
                key: &CtxKey,
                total_length: u64,
                ranges: impl IntoIterator<Item = Range<u64>>,
                source: &mut S,
            ) -> Result<Vec<Range<u64>>, Blake3SourceProofError<S::Error>> {
                verify_from_source(
                    self.as_bytes(),
                    total_length,
                    ranges,
                    source,
                    Blake3ProofMode::Context(key),
                )
            }
        }
    };
}

impl_source_verification!(Blake3);
impl_source_verification!(Cov);

#[cfg(test)]
mod tests {
    use super::*;

    struct TestSource<'a> {
        input: &'a [u8],
        mode: Blake3ProofMode<'a>,
        requests: Vec<Blake3SourceRequest>,
        corrupt_cv: bool,
    }

    impl Blake3ProofSource for TestSource<'_> {
        type Error = &'static str;

        fn fragment(&mut self, range: Range<u64>) -> Result<Vec<u8>, Self::Error> {
            self.requests
                .push(Blake3SourceRequest::Fragment(range.clone()));
            let start = usize::try_from(range.start).map_err(|_| "offset")?;
            let end = usize::try_from(range.end).map_err(|_| "offset")?;
            self.input
                .get(start..end)
                .map(<[u8]>::to_vec)
                .ok_or("range")
        }

        fn cv(&mut self, range: Range<u64>) -> Result<Blake3Cv, Self::Error> {
            self.requests.push(Blake3SourceRequest::Cv(range.clone()));
            if self.corrupt_cv {
                self.corrupt_cv = false;
                return Ok(Blake3Cv::default());
            }
            let start = usize::try_from(range.start).map_err(|_| "offset")?;
            let end = usize::try_from(range.end).map_err(|_| "offset")?;
            let bytes = self.input.get(start..end).ok_or("range")?;
            Ok(self.mode.subtree(range.start, bytes))
        }
    }

    #[test]
    fn source_verifier_drives_arbitrary_ordered_ranges() {
        let input = (0u8..=250).cycle().take(8_193).collect::<Vec<_>>();
        let mode = Blake3ProofMode::Unkeyed;
        let root = Obj::<Blake3>::from_array(mode.hash(&input));
        let ranges = vec![100..300, 2_200..2_400, 7_000..8_000];
        let mut source = TestSource {
            input: &input,
            mode,
            requests: Vec::new(),
            corrupt_cv: false,
        };

        assert_eq!(
            root.verify_blake3_ranges_from(input.len() as u64, ranges.clone(), &mut source),
            Ok(ranges)
        );
        assert!(
            source
                .requests
                .iter()
                .any(|request| matches!(request, Blake3SourceRequest::Fragment(_)))
        );
        assert!(
            source
                .requests
                .iter()
                .any(|request| matches!(request, Blake3SourceRequest::Cv(_)))
        );
    }

    #[test]
    fn source_verifier_rejects_ordering_and_untrusted_values() {
        let input = vec![9; 4_097];
        let key = O256::from_array([7; 32]);
        let mode = Blake3ProofMode::Keyed(&key);
        let root = O256::from_array(mode.hash(&input));
        let mut source = TestSource {
            input: &input,
            mode,
            requests: Vec::new(),
            corrupt_cv: false,
        };
        assert!(matches!(
            root.verify_blake3_keyed_ranges_from(
                &key,
                input.len() as u64,
                [2_000..2_100, 1_000..1_100],
                &mut source,
            ),
            Err(Blake3SourceProofError::InvalidRange { .. })
        ));
        assert!(source.requests.is_empty());

        source.corrupt_cv = true;
        assert!(matches!(
            root.verify_blake3_keyed_ranges_from(
                &key,
                input.len() as u64,
                std::iter::once(1_100..1_200),
                &mut source,
            ),
            Err(Blake3SourceProofError::RootMismatch)
        ));
    }

    #[test]
    fn source_verifier_supports_context_mode_and_single_chunks() {
        let input = b"a small authenticated object";
        let key = CtxKey::derive("source verifier test");
        let mode = Blake3ProofMode::Context(&key);
        let root = O256::from_array(mode.hash(input));
        let mut source = TestSource {
            input,
            mode,
            requests: Vec::new(),
            corrupt_cv: false,
        };

        let verified = root
            .verify_blake3_context_ranges_from(
                &key,
                input.len() as u64,
                std::iter::once(2..9),
                &mut source,
            )
            .unwrap();
        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0], 2..9);
        assert_eq!(
            source.requests,
            vec![Blake3SourceRequest::Fragment(0..input.len() as u64)]
        );
    }
}
