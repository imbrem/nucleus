//! BLAKE3 byte-range proof verification.

use std::{convert::Infallible, fmt, ops::Range};

use blake3::hazmat::{self, HasherExt, Mode};
use covalence_lib_error::snafu;
use snafu::Snafu;

use super::{Blake3, Blake3Cv, Cov, CtxKey};
use crate::{O256, Obj, RangeProofNamespace};

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

/// A positioned BLAKE3 subtree supplied as range-proof evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Blake3ProofNode {
    /// Byte offset of the subtree in the complete input.
    pub offset: u64,
    /// Number of bytes covered by the subtree.
    pub length: u64,
    /// Non-root chaining value of the subtree.
    pub cv: Blake3Cv,
}

/// Mode-neutral evidence for a contiguous BLAKE3 byte range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3RangeProof {
    /// Length of the complete input.
    pub total_length: u64,
    /// Requested byte range.
    pub range: Range<u64>,
    /// Canonical outside subtrees, ordered by byte offset.
    pub nodes: Vec<Blake3ProofNode>,
}

/// Unkeyed BLAKE3 range evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3UnkeyedEvidence(pub Blake3RangeProof);

/// Regular keyed-BLAKE3 range evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3KeyedEvidence {
    /// Mode-neutral proof structure.
    pub proof: Blake3RangeProof,
    /// BLAKE3 key. Protocol encodings should generally keep this separate.
    pub key: O256,
}

/// Context-keyed BLAKE3 range evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3ContextEvidence {
    /// Mode-neutral proof structure.
    pub proof: Blake3RangeProof,
    /// Precomputed BLAKE3 context key.
    pub key: CtxKey,
}

/// Failure to verify a BLAKE3 byte-range proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum Blake3RangeProofError {
    /// Empty inputs do not have non-root chaining values.
    #[snafu(display("range proofs require a non-empty input"))]
    EmptyInput,
    /// The requested range was empty or outside the input.
    #[snafu(display("invalid requested range {start}..{end} for input length {total_length}"))]
    InvalidRange {
        start: u64,
        end: u64,
        total_length: u64,
    },
    /// The disclosed data had the wrong chunk-rounded length.
    #[snafu(display("expected {expected} disclosed bytes, found {actual}"))]
    InvalidDataLength { expected: usize, actual: usize },
    /// Proof nodes were not the exact canonical outside frontier.
    #[snafu(display("invalid proof frontier near byte offset {offset}"))]
    InvalidFrontier { offset: u64 },
    /// Offset or length arithmetic overflowed the supported representation.
    #[snafu(display("range-proof offset or length overflowed"))]
    Overflow,
    /// The reconstructed root did not match the expected root.
    #[snafu(display("range proof reconstructed the wrong root"))]
    RootMismatch,
}

#[derive(Clone, Copy)]
enum Blake3ProofMode<'a> {
    Unkeyed,
    Keyed(&'a O256),
    Context(&'a CtxKey),
}

impl<'a> Blake3ProofMode<'a> {
    fn hasher(self) -> blake3::Hasher {
        match self {
            Self::Unkeyed => blake3::Hasher::new(),
            Self::Keyed(key) => blake3::Hasher::new_keyed(key.as_bytes()),
            Self::Context(key) => blake3::Hasher::new_from_context_key(key.as_bytes()),
        }
    }

    fn hazmat(self) -> Mode<'a> {
        match self {
            Self::Unkeyed => Mode::Hash,
            Self::Keyed(key) => Mode::KeyedHash(key.as_bytes()),
            Self::Context(key) => Mode::DeriveKeyMaterial(key.as_bytes()),
        }
    }

    fn subtree(self, offset: u64, bytes: &[u8]) -> Blake3Cv {
        let mut hasher = self.hasher();
        hasher.set_input_offset(offset);
        hasher.update(bytes);
        Blake3Cv::from_array(hasher.finalize_non_root())
    }

    fn merge(self, left: Blake3Cv, right: Blake3Cv) -> Blake3Cv {
        Blake3Cv::from_array(hazmat::merge_subtrees_non_root(
            left.as_bytes(),
            right.as_bytes(),
            self.hazmat(),
        ))
    }

    fn root(self, left: Blake3Cv, right: Blake3Cv) -> [u8; 32] {
        *hazmat::merge_subtrees_root(left.as_bytes(), right.as_bytes(), self.hazmat()).as_bytes()
    }

    fn hash(self, bytes: &[u8]) -> [u8; 32] {
        let mut hasher = self.hasher();
        hasher.update(bytes);
        *hasher.finalize().as_bytes()
    }
}

struct Verification<'a> {
    proof: &'a Blake3RangeProof,
    covered: Range<u64>,
    data: &'a [u8],
    node_index: usize,
    mode: Blake3ProofMode<'a>,
}

impl Verification<'_> {
    fn subtree(&mut self, offset: u64, length: u64) -> Result<Blake3Cv, Blake3RangeProofError> {
        let end = offset
            .checked_add(length)
            .ok_or(Blake3RangeProofError::Overflow)?;
        if offset >= self.covered.start && end <= self.covered.end {
            let start = usize::try_from(offset - self.covered.start)
                .map_err(|_| Blake3RangeProofError::Overflow)?;
            let length = usize::try_from(length).map_err(|_| Blake3RangeProofError::Overflow)?;
            let bytes = self
                .data
                .get(start..start + length)
                .ok_or(Blake3RangeProofError::Overflow)?;
            return Ok(self.mode.subtree(offset, bytes));
        }

        if end <= self.covered.start || offset >= self.covered.end {
            let node = self
                .proof
                .nodes
                .get(self.node_index)
                .ok_or(Blake3RangeProofError::InvalidFrontier { offset })?;
            if node.offset != offset || node.length != length {
                return Err(Blake3RangeProofError::InvalidFrontier { offset });
            }
            self.node_index += 1;
            return Ok(node.cv);
        }

        if length <= blake3::CHUNK_LEN as u64 {
            return Err(Blake3RangeProofError::InvalidFrontier { offset });
        }
        let left_length = hazmat::left_subtree_len(length);
        let right_offset = offset
            .checked_add(left_length)
            .ok_or(Blake3RangeProofError::Overflow)?;
        let left = self.subtree(offset, left_length)?;
        let right = self.subtree(right_offset, length - left_length)?;
        Ok(self.mode.merge(left, right))
    }
}

fn chunk_covered_range(proof: &Blake3RangeProof) -> Result<Range<u64>, Blake3RangeProofError> {
    if proof.total_length == 0 {
        return Err(Blake3RangeProofError::EmptyInput);
    }
    if proof.range.start >= proof.range.end || proof.range.end > proof.total_length {
        return Err(Blake3RangeProofError::InvalidRange {
            start: proof.range.start,
            end: proof.range.end,
            total_length: proof.total_length,
        });
    }
    let chunk = blake3::CHUNK_LEN as u64;
    let start = proof.range.start / chunk * chunk;
    let end = proof
        .range
        .end
        .checked_add(chunk - 1)
        .ok_or(Blake3RangeProofError::Overflow)?
        / chunk
        * chunk;
    Ok(start..end.min(proof.total_length))
}

fn verify(
    expected: &[u8; 32],
    proof: &Blake3RangeProof,
    data: &[u8],
    mode: Blake3ProofMode<'_>,
) -> Result<Range<u64>, Blake3RangeProofError> {
    let covered = chunk_covered_range(proof)?;
    let expected_length = usize::try_from(covered.end - covered.start)
        .map_err(|_| Blake3RangeProofError::Overflow)?;
    if data.len() != expected_length {
        return Err(Blake3RangeProofError::InvalidDataLength {
            expected: expected_length,
            actual: data.len(),
        });
    }

    let actual = if proof.total_length <= blake3::CHUNK_LEN as u64 {
        if !proof.nodes.is_empty() || covered != (0..proof.total_length) {
            return Err(Blake3RangeProofError::InvalidFrontier { offset: 0 });
        }
        mode.hash(data)
    } else {
        let left_length = hazmat::left_subtree_len(proof.total_length);
        let mut verification = Verification {
            proof,
            covered,
            data,
            node_index: 0,
            mode,
        };
        let left = verification.subtree(0, left_length)?;
        let right = verification.subtree(left_length, proof.total_length - left_length)?;
        if verification.node_index != proof.nodes.len() {
            return Err(Blake3RangeProofError::InvalidFrontier {
                offset: proof.total_length,
            });
        }
        mode.root(left, right)
    };

    if &actual != expected {
        return Err(Blake3RangeProofError::RootMismatch);
    }
    Ok(proof.range.clone())
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

macro_rules! impl_unkeyed {
    ($namespace:ty) => {
        impl RangeProofNamespace<Blake3UnkeyedEvidence> for $namespace {
            type Error = Blake3RangeProofError;

            fn verify_range(
                root: &Obj<Self>,
                evidence: Blake3UnkeyedEvidence,
                data: &[u8],
            ) -> Result<Range<u64>, Self::Error> {
                verify(root.as_bytes(), &evidence.0, data, Blake3ProofMode::Unkeyed)
            }
        }
    };
}

macro_rules! impl_keyed {
    ($namespace:ty) => {
        impl RangeProofNamespace<Blake3KeyedEvidence> for $namespace {
            type Error = Blake3RangeProofError;

            fn verify_range(
                root: &Obj<Self>,
                evidence: Blake3KeyedEvidence,
                data: &[u8],
            ) -> Result<Range<u64>, Self::Error> {
                verify(
                    root.as_bytes(),
                    &evidence.proof,
                    data,
                    Blake3ProofMode::Keyed(&evidence.key),
                )
            }
        }
    };
}

macro_rules! impl_context {
    ($namespace:ty) => {
        impl RangeProofNamespace<Blake3ContextEvidence> for $namespace {
            type Error = Blake3RangeProofError;

            fn verify_range(
                root: &Obj<Self>,
                evidence: Blake3ContextEvidence,
                data: &[u8],
            ) -> Result<Range<u64>, Self::Error> {
                verify(
                    root.as_bytes(),
                    &evidence.proof,
                    data,
                    Blake3ProofMode::Context(&evidence.key),
                )
            }
        }
    };
}

impl_unkeyed!(Blake3);
impl_unkeyed!(Cov);
impl_keyed!(Blake3);
impl_keyed!(Cov);
impl_context!(Blake3);
impl_context!(Cov);

#[cfg(test)]
mod tests {
    use super::*;

    fn collect_nodes(
        input: &[u8],
        covered: &Range<u64>,
        offset: u64,
        length: u64,
        mode: Blake3ProofMode<'_>,
        nodes: &mut Vec<Blake3ProofNode>,
    ) {
        let end = offset + length;
        if end <= covered.start || offset >= covered.end {
            let start = usize::try_from(offset).unwrap();
            let end = usize::try_from(end).unwrap();
            nodes.push(Blake3ProofNode {
                offset,
                length,
                cv: mode.subtree(offset, &input[start..end]),
            });
        } else if offset < covered.start || end > covered.end {
            let left_length = hazmat::left_subtree_len(length);
            collect_nodes(input, covered, offset, left_length, mode, nodes);
            collect_nodes(
                input,
                covered,
                offset + left_length,
                length - left_length,
                mode,
                nodes,
            );
        }
    }

    fn proof_for(input: &[u8], range: Range<u64>, mode: Blake3ProofMode<'_>) -> Blake3RangeProof {
        let mut proof = Blake3RangeProof {
            total_length: input.len() as u64,
            range,
            nodes: Vec::new(),
        };
        let covered = chunk_covered_range(&proof).unwrap();
        if input.len() > blake3::CHUNK_LEN {
            let left_length = hazmat::left_subtree_len(input.len() as u64);
            collect_nodes(input, &covered, 0, left_length, mode, &mut proof.nodes);
            collect_nodes(
                input,
                &covered,
                left_length,
                input.len() as u64 - left_length,
                mode,
                &mut proof.nodes,
            );
        }
        proof
    }

    fn disclosed<'a>(input: &'a [u8], proof: &Blake3RangeProof) -> &'a [u8] {
        let covered = chunk_covered_range(proof).unwrap();
        &input[usize::try_from(covered.start).unwrap()..usize::try_from(covered.end).unwrap()]
    }

    #[test]
    fn all_modes_verify_for_blake3_and_covalence_namespaces() {
        let input: Vec<u8> = (0u8..=250).cycle().take(5_123).collect();
        let range = 1_300..2_500;
        let key = O256::from_array([7; 32]);
        let context = CtxKey::derive("range proof test");

        let unkeyed = proof_for(&input, range.clone(), Blake3ProofMode::Unkeyed);
        let unkeyed_root = Blake3ProofMode::Unkeyed.hash(&input);
        let blake3_root = Obj::<Blake3>::from_array(unkeyed_root);
        let covalence_root = O256::from_array(unkeyed_root);
        assert_eq!(
            blake3_root
                .verify_range(
                    Blake3UnkeyedEvidence(unkeyed.clone()),
                    disclosed(&input, &unkeyed)
                )
                .unwrap(),
            range
        );
        assert_eq!(
            covalence_root
                .verify_range(
                    Blake3UnkeyedEvidence(unkeyed.clone()),
                    disclosed(&input, &unkeyed)
                )
                .unwrap(),
            range
        );

        let keyed_mode = Blake3ProofMode::Keyed(&key);
        let keyed = proof_for(&input, range.clone(), keyed_mode);
        let keyed_root = keyed_mode.hash(&input);
        assert_eq!(
            Obj::<Blake3>::from_array(keyed_root)
                .verify_range(
                    Blake3KeyedEvidence {
                        proof: keyed.clone(),
                        key
                    },
                    disclosed(&input, &keyed)
                )
                .unwrap(),
            range
        );
        assert_eq!(
            O256::from_array(keyed_root)
                .verify_range(
                    Blake3KeyedEvidence {
                        proof: keyed.clone(),
                        key
                    },
                    disclosed(&input, &keyed)
                )
                .unwrap(),
            range
        );

        let context_mode = Blake3ProofMode::Context(&context);
        let context_proof = proof_for(&input, range.clone(), context_mode);
        let context_root = context_mode.hash(&input);
        assert_eq!(
            Obj::<Blake3>::from_array(context_root)
                .verify_range(
                    Blake3ContextEvidence {
                        proof: context_proof.clone(),
                        key: context
                    },
                    disclosed(&input, &context_proof)
                )
                .unwrap(),
            range
        );
        assert_eq!(
            O256::from_array(context_root)
                .verify_range(
                    Blake3ContextEvidence {
                        proof: context_proof.clone(),
                        key: context
                    },
                    disclosed(&input, &context_proof)
                )
                .unwrap(),
            range
        );
    }

    #[test]
    fn rejects_tampering_and_noncanonical_frontiers() {
        let input = vec![42; 4_097];
        let range = 1_100..2_100;
        let proof = proof_for(&input, range, Blake3ProofMode::Unkeyed);
        let root = Obj::<Blake3>::from_array(Blake3ProofMode::Unkeyed.hash(&input));
        let mut data = disclosed(&input, &proof).to_vec();
        data[0] ^= 1;
        assert_eq!(
            root.verify_range(Blake3UnkeyedEvidence(proof.clone()), &data),
            Err(Blake3RangeProofError::RootMismatch)
        );

        let mut extra = proof.clone();
        extra.nodes.push(Blake3ProofNode {
            offset: 0,
            length: blake3::CHUNK_LEN as u64,
            cv: Blake3Cv::default(),
        });
        assert!(matches!(
            root.verify_range(Blake3UnkeyedEvidence(extra), disclosed(&input, &proof)),
            Err(Blake3RangeProofError::InvalidFrontier { .. })
        ));
    }

    #[test]
    fn verifies_ranges_within_single_chunk_inputs() {
        let input = b"small input";
        let proof = proof_for(input, 2..7, Blake3ProofMode::Unkeyed);
        let root = Obj::<Blake3>::from_array(Blake3ProofMode::Unkeyed.hash(input));
        assert_eq!(
            root.verify_range(
                Blake3UnkeyedEvidence(proof.clone()),
                disclosed(input, &proof)
            ),
            Ok(2..7)
        );
    }

    #[test]
    fn wrong_keys_and_invalid_ranges_are_rejected() {
        let input = vec![17; 3_000];
        let key = O256::from_array([3; 32]);
        let mode = Blake3ProofMode::Keyed(&key);
        let proof = proof_for(&input, 1_100..1_200, mode);
        let root = Obj::<Blake3>::from_array(mode.hash(&input));
        assert_eq!(
            root.verify_range(
                Blake3KeyedEvidence {
                    proof: proof.clone(),
                    key: O256::from_array([4; 32]),
                },
                disclosed(&input, &proof),
            ),
            Err(Blake3RangeProofError::RootMismatch)
        );

        let invalid_start = 2_000;
        let invalid_end = 1_000;
        let invalid = Blake3RangeProof {
            total_length: input.len() as u64,
            range: invalid_start..invalid_end,
            nodes: Vec::new(),
        };
        assert!(matches!(
            root.verify_range(Blake3UnkeyedEvidence(invalid), &[]),
            Err(Blake3RangeProofError::InvalidRange { .. })
        ));
    }

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
