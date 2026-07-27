//! Streaming verification of segmented BLAKE3 range proofs.

use std::{collections::VecDeque, ops::Range};

use super::range::{
    Blake3ContextEvidence, Blake3KeyedEvidence, Blake3RangeProof, Blake3RangeProofError,
    Blake3UnkeyedEvidence, chunk_covered_range,
};
use crate::{
    Namespace, Obj, RangeProofNamespace, RangeValidationProgress, StreamingRangeProofNamespace,
    StreamingRangeVerifier,
};

/// Evidence that can participate in segmented BLAKE3 streaming verification.
pub trait Blake3Evidence {
    /// Returns the mode-neutral proof structure.
    fn proof(&self) -> &Blake3RangeProof;
}

impl Blake3Evidence for Blake3UnkeyedEvidence {
    fn proof(&self) -> &Blake3RangeProof {
        &self.0
    }
}

impl Blake3Evidence for Blake3KeyedEvidence {
    fn proof(&self) -> &Blake3RangeProof {
        &self.proof
    }
}

impl Blake3Evidence for Blake3ContextEvidence {
    fn proof(&self) -> &Blake3RangeProof {
        &self.proof
    }
}

/// Independently root-verifiable range-proof segments in stream order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3StreamingEvidence<E> {
    /// Evidence segments whose requested ranges form one contiguous range.
    pub segments: Vec<E>,
}

/// Streaming verifier for segmented BLAKE3 range evidence.
pub struct Blake3RangeVerifier<N: Namespace, E> {
    root: Obj<N>,
    segments: VecDeque<E>,
    buffer: Vec<u8>,
    next_length: usize,
    validated: Range<u64>,
    complete_end: u64,
}

impl<N, E> Blake3RangeVerifier<N, E>
where
    N: Namespace + RangeProofNamespace<E, Error = Blake3RangeProofError>,
    E: Blake3Evidence,
{
    fn new(
        root: Obj<N>,
        evidence: Blake3StreamingEvidence<E>,
    ) -> Result<Self, Blake3RangeProofError> {
        let segments = VecDeque::from(evidence.segments);
        let first = segments
            .front()
            .ok_or(Blake3RangeProofError::EmptyEvidence)?;
        let total_length = first.proof().total_length;
        let start = first.proof().range.start;
        let mut end = start;
        for segment in &segments {
            let proof = segment.proof();
            if proof.total_length != total_length || proof.range.start != end {
                return Err(Blake3RangeProofError::DiscontinuousSegments { offset: end });
            }
            chunk_covered_range(proof)?;
            end = proof.range.end;
        }
        let next_length = covered_length(first.proof())?;
        Ok(Self {
            root,
            segments,
            buffer: Vec::new(),
            next_length,
            validated: start..start,
            complete_end: end,
        })
    }
}

fn covered_length(proof: &Blake3RangeProof) -> Result<usize, Blake3RangeProofError> {
    let covered = chunk_covered_range(proof)?;
    usize::try_from(covered.end - covered.start).map_err(|_| Blake3RangeProofError::Overflow)
}

impl<N, E> StreamingRangeVerifier for Blake3RangeVerifier<N, E>
where
    N: Namespace + RangeProofNamespace<E, Error = Blake3RangeProofError>,
    E: Blake3Evidence,
{
    type Error = Blake3RangeProofError;

    fn update(&mut self, data: &[u8]) -> Result<RangeValidationProgress, Self::Error> {
        let mut consumed = 0;
        while consumed < data.len() {
            if self.segments.is_empty() {
                return Err(Blake3RangeProofError::TrailingData);
            }
            let needed = self.next_length - self.buffer.len();
            let take = needed.min(data.len() - consumed);
            self.buffer
                .extend_from_slice(&data[consumed..consumed + take]);
            consumed += take;

            if self.buffer.len() == self.next_length {
                let evidence = self
                    .segments
                    .pop_front()
                    .ok_or(Blake3RangeProofError::IncompleteData)?;
                let range = evidence.proof().range.clone();
                N::verify_range(&self.root, evidence, &self.buffer)?;
                self.buffer.clear();
                self.validated.end = range.end;
                self.next_length = match self.segments.front() {
                    Some(next) => covered_length(next.proof())?,
                    None => 0,
                };
            }
        }

        Ok(RangeValidationProgress {
            consumed,
            validated: self.validated.clone(),
        })
    }

    fn finish(self) -> Result<Range<u64>, Self::Error> {
        if !self.segments.is_empty() || !self.buffer.is_empty() {
            return Err(Blake3RangeProofError::IncompleteData);
        }
        debug_assert_eq!(self.validated.end, self.complete_end);
        Ok(self.validated)
    }
}

impl<N, E> StreamingRangeProofNamespace<Blake3StreamingEvidence<E>> for N
where
    N: Namespace + RangeProofNamespace<E, Error = Blake3RangeProofError>,
    E: Blake3Evidence,
{
    type Error = Blake3RangeProofError;
    type Verifier = Blake3RangeVerifier<N, E>;

    fn range_verifier(
        root: Obj<Self>,
        evidence: Blake3StreamingEvidence<E>,
    ) -> Result<Self::Verifier, Self::Error> {
        Blake3RangeVerifier::new(root, evidence)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        O256,
        blake3::{
            Blake3, Blake3KeyedEvidence, Blake3UnkeyedEvidence,
            range::{
                Blake3ProofMode, Blake3RangeProofError,
                tests::{disclosed, proof_for},
            },
        },
    };

    #[test]
    fn segmented_streaming_proofs_advance_only_after_root_checks() {
        let input: Vec<u8> = (0u8..=250).cycle().take(5_123).collect();
        let first = proof_for(&input, 1_024..2_048, Blake3ProofMode::Unkeyed);
        let second = proof_for(&input, 2_048..3_072, Blake3ProofMode::Unkeyed);
        let mut stream = Vec::new();
        stream.extend_from_slice(disclosed(&input, &first));
        stream.extend_from_slice(disclosed(&input, &second));

        let root = O256::from_array(Blake3ProofMode::Unkeyed.hash(&input));
        let evidence = Blake3StreamingEvidence {
            segments: vec![Blake3UnkeyedEvidence(first), Blake3UnkeyedEvidence(second)],
        };
        let mut verifier = root.range_verifier(evidence).unwrap();

        let progress = verifier.update(&stream[..500]).unwrap();
        assert_eq!(progress.consumed, 500);
        assert_eq!(progress.validated, 1_024..1_024);

        let progress = verifier.update(&stream[500..1_124]).unwrap();
        assert_eq!(progress.consumed, 624);
        assert_eq!(progress.validated, 1_024..2_048);

        let progress = verifier.update(&stream[1_124..]).unwrap();
        assert_eq!(progress.validated, 1_024..3_072);
        assert_eq!(verifier.finish(), Ok(1_024..3_072));
    }

    #[test]
    fn streaming_proofs_support_keyed_modes_and_reject_incomplete_data() {
        let input = vec![23; 4_096];
        let key = O256::from_array([9; 32]);
        let mode = Blake3ProofMode::Keyed(&key);
        let proof = proof_for(&input, 1_024..2_048, mode);
        let root = Obj::<Blake3>::from_array(mode.hash(&input));
        let evidence = Blake3StreamingEvidence {
            segments: vec![Blake3KeyedEvidence {
                proof: proof.clone(),
                key,
            }],
        };
        let mut verifier = root.range_verifier(evidence).unwrap();
        verifier.update(&disclosed(&input, &proof)[..100]).unwrap();
        assert_eq!(
            verifier.finish(),
            Err(Blake3RangeProofError::IncompleteData)
        );
    }

    #[test]
    fn streaming_setup_rejects_discontinuous_segments() {
        let input = vec![31; 4_096];
        let first = proof_for(&input, 0..1_024, Blake3ProofMode::Unkeyed);
        let third = proof_for(&input, 2_048..3_072, Blake3ProofMode::Unkeyed);
        let root = Obj::<Blake3>::from_array(Blake3ProofMode::Unkeyed.hash(&input));
        let result = root.range_verifier(Blake3StreamingEvidence {
            segments: vec![Blake3UnkeyedEvidence(first), Blake3UnkeyedEvidence(third)],
        });
        assert!(matches!(
            result,
            Err(Blake3RangeProofError::DiscontinuousSegments { offset: 1_024 })
        ));
    }
}
