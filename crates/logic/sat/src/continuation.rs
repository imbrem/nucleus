//! One-shot continuation for completely untrusted SAT providers.
//!
//! This module defines no transport and mutates no logical authority. It keeps
//! the canonical [`Cnf`] on the trusted side, correlates one provider response,
//! and delegates checking back to that value.

use std::num::NonZeroU64;

use crate::{Cnf, Limits, LratError, ModelError, ProblemId, VerifiedModel, VerifiedUnsat};

/// Opaque identity of one continuation invocation.
///
/// A job id is a local, single-use correlation capability. It is deliberately
/// distinct from [`ProblemId`], which identifies only canonical matrix bytes
/// and can therefore recur in many jobs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct JobId(NonZeroU64);

impl JobId {
    /// Returns the process-local correlation number.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

/// Provider response bounds repeated at the untrusted boundary.
///
/// These help hosts reject oversized responses early. The checker independently
/// enforces the retained authoritative bounds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResponseLimits {
    /// Maximum literals in a claimed satisfying assignment.
    pub max_model_literals: usize,
    /// Maximum bytes in a claimed LRAT proof.
    pub max_proof_bytes: usize,
    /// Maximum bytes in optional provider diagnostics.
    pub max_diagnostic_bytes: usize,
}

/// Requested proof representation.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ProofRequest {
    /// Whether the provider may attach ASCII LRAT for diagnostics.
    ///
    /// Binary LRAT remains the checked artifact. Diagnostic ASCII is untrusted,
    /// optional, and never substitutes for the binary proof.
    pub diagnostic_ascii_lrat: bool,
}

/// Transport-neutral request passed to an untrusted provider.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SolveRequest {
    job: JobId,
    problem: ProblemId,
    dimacs: Box<[u8]>,
    limits: ResponseLimits,
    proof: ProofRequest,
}

impl SolveRequest {
    /// Returns the opaque single-use correlation capability.
    #[must_use]
    pub const fn job(&self) -> JobId {
        self.job
    }

    /// Returns the canonical matrix identity.
    #[must_use]
    pub const fn problem(&self) -> ProblemId {
        self.problem
    }

    /// Returns canonical DIMACS bytes.
    #[must_use]
    pub fn dimacs(&self) -> &[u8] {
        &self.dimacs
    }

    /// Returns host-facing response bounds.
    #[must_use]
    pub const fn limits(&self) -> ResponseLimits {
        self.limits
    }

    /// Returns the proof representation request.
    #[must_use]
    pub const fn proof(&self) -> ProofRequest {
        self.proof
    }
}

/// Raw data claimed by an untrusted provider.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SolveResult {
    /// Claimed satisfying assignment.
    Sat {
        /// Matrix identity echoed by the provider.
        problem: ProblemId,
        /// Signed DIMACS assignment.
        model: Box<[i64]>,
    },
    /// Claimed refutation.
    Unsat {
        /// Matrix identity echoed by the provider.
        problem: ProblemId,
        /// Binary LRAT proof bytes.
        proof: Box<[u8]>,
        /// Optional untrusted ASCII rendering requested for diagnostics.
        diagnostic_ascii_lrat: Option<Box<[u8]>>,
    },
    /// Provider could not decide the problem.
    Unknown {
        /// Matrix identity echoed by the provider.
        problem: ProblemId,
        /// Optional untrusted diagnostic.
        reason: Option<String>,
    },
}

impl SolveResult {
    /// Returns the canonical problem identity echoed by the provider.
    #[must_use]
    pub const fn problem(&self) -> ProblemId {
        match self {
            Self::Sat { problem, .. }
            | Self::Unsat { problem, .. }
            | Self::Unknown { problem, .. } => *problem,
        }
    }
}

/// Locally checked, non-authoritative completion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CheckedResult {
    /// The retained matrix accepted the model.
    Sat(VerifiedModel),
    /// The retained matrix accepted the binary LRAT refutation.
    Unsat(VerifiedUnsat),
    /// The provider returned no mathematical claim to check.
    Unknown {
        /// Optional untrusted provider diagnostic.
        reason: Option<String>,
    },
}

/// Failure at the continuation boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// Another single-flight job is still pending.
    Pending,
    /// Every representable local job id has been issued.
    JobIdExhausted,
    /// The capability does not name the current pending job.
    StaleJob,
    /// The provider echoed a different canonical matrix identity.
    WrongProblem,
    /// ASCII LRAT was returned without the explicit diagnostic opt-in.
    UnexpectedAsciiDiagnostic,
    /// Diagnostic ASCII exceeded the proof-byte response bound.
    AsciiDiagnosticTooLarge,
    /// An untrusted provider diagnostic exceeded its display bound.
    DiagnosticTooLarge,
    /// The SAT claim failed local checking.
    Model(ModelError),
    /// The binary LRAT claim failed local checking.
    Lrat(LratError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pending => f.write_str("a SAT job is already pending"),
            Self::JobIdExhausted => f.write_str("SAT job ids are exhausted"),
            Self::StaleJob => f.write_str("SAT job is stale or unknown"),
            Self::WrongProblem => f.write_str("SAT result names the wrong problem"),
            Self::UnexpectedAsciiDiagnostic => {
                f.write_str("provider returned unrequested ASCII LRAT diagnostics")
            }
            Self::AsciiDiagnosticTooLarge => {
                f.write_str("ASCII LRAT diagnostics exceed the response bound")
            }
            Self::DiagnosticTooLarge => f.write_str("SAT provider diagnostic exceeds its bound"),
            Self::Model(error) => write!(f, "SAT model rejected: {error}"),
            Self::Lrat(error) => write!(f, "LRAT proof rejected: {error}"),
        }
    }
}

impl std::error::Error for Error {}

struct Pending {
    job: JobId,
    cnf: Cnf,
    limits: ResponseLimits,
    lrat_limits: Limits,
    proof: ProofRequest,
}

/// Single-flight owner of one retained canonical problem.
#[derive(Default)]
pub struct Continuation {
    last_job: u64,
    pending: Option<Pending>,
}

impl Continuation {
    /// Creates an empty continuation.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            last_job: 0,
            pending: None,
        }
    }

    /// Retains `cnf` and returns the transport-neutral provider request.
    ///
    /// # Errors
    ///
    /// Rejects a second concurrent job or exhausted local job identity space.
    pub fn begin(
        &mut self,
        cnf: Cnf,
        max_model_literals: usize,
        lrat_limits: Limits,
        proof: ProofRequest,
    ) -> Result<SolveRequest, Error> {
        if self.pending.is_some() {
            return Err(Error::Pending);
        }
        let raw = self.last_job.checked_add(1).ok_or(Error::JobIdExhausted)?;
        let job = JobId(NonZeroU64::new(raw).ok_or(Error::JobIdExhausted)?);
        let limits = ResponseLimits {
            max_model_literals,
            max_proof_bytes: lrat_limits.proof_bytes,
            max_diagnostic_bytes: 64 * 1024,
        };
        let request = SolveRequest {
            job,
            problem: cnf.id(),
            dimacs: cnf.dimacs().into(),
            limits,
            proof,
        };
        self.last_job = raw;
        self.pending = Some(Pending {
            job,
            cnf,
            limits,
            lrat_limits,
            proof,
        });
        Ok(request)
    }

    /// Consumes a matching result and checks any mathematical claim locally.
    ///
    /// A wrong job or problem does not consume the real pending continuation.
    /// A matching provider response is consumed before checking, so malformed
    /// data, unknown, and checker rejection cannot be replayed as another try.
    ///
    /// # Errors
    ///
    /// Rejects stale capabilities, mismatched problems, or invalid claims.
    pub fn complete(&mut self, job: JobId, result: SolveResult) -> Result<CheckedResult, Error> {
        let Some(pending) = self.pending.as_ref() else {
            return Err(Error::StaleJob);
        };
        if pending.job != job {
            return Err(Error::StaleJob);
        }
        if pending.cnf.id() != result.problem() {
            return Err(Error::WrongProblem);
        }
        let pending = self.pending.take().ok_or(Error::StaleJob)?;
        match result {
            SolveResult::Sat { model, .. } => pending
                .cnf
                .verify_model(&model, pending.limits.max_model_literals)
                .map(CheckedResult::Sat)
                .map_err(Error::Model),
            SolveResult::Unsat {
                proof,
                diagnostic_ascii_lrat,
                ..
            } => {
                if diagnostic_ascii_lrat.is_some() && !pending.proof.diagnostic_ascii_lrat {
                    return Err(Error::UnexpectedAsciiDiagnostic);
                }
                if diagnostic_ascii_lrat
                    .as_ref()
                    .is_some_and(|text| text.len() > pending.limits.max_proof_bytes)
                {
                    return Err(Error::AsciiDiagnosticTooLarge);
                }
                pending
                    .cnf
                    .verify_binary(&proof, pending.lrat_limits)
                    .map(CheckedResult::Unsat)
                    .map_err(Error::Lrat)
            }
            SolveResult::Unknown { reason, .. } => {
                if reason
                    .as_ref()
                    .is_some_and(|text| text.len() > pending.limits.max_diagnostic_bytes)
                {
                    return Err(Error::DiagnosticTooLarge);
                }
                Ok(CheckedResult::Unknown { reason })
            }
        }
    }

    /// Cancels and consumes the matching pending job.
    ///
    /// Cancellation cannot stop an uncooperative provider; it only guarantees
    /// that any later completion is stale and cannot be checked or admitted.
    ///
    /// # Errors
    ///
    /// Rejects a capability other than the current pending job.
    pub fn cancel(&mut self, job: JobId) -> Result<(), Error> {
        match self.pending.as_ref() {
            Some(pending) if pending.job == job => {
                self.pending = None;
                Ok(())
            }
            _ => Err(Error::StaleJob),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfLimits, CnfPolicy};

    fn contradiction() -> Cnf {
        Cnf::new(
            [vec![1], vec![-1]],
            CnfLimits::default(),
            CnfPolicy::default(),
        )
        .expect("CNF")
    }

    fn satisfiable() -> Cnf {
        Cnf::new([vec![1]], CnfLimits::default(), CnfPolicy::default()).expect("CNF")
    }

    #[test]
    fn request_carries_exact_identity_and_binary_default() {
        let cnf = contradiction();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf.clone(), 8, Limits::default(), ProofRequest::default())
            .expect("begin");
        assert_eq!(request.problem(), cnf.id());
        assert_eq!(request.dimacs(), cnf.dimacs());
        assert_eq!(
            request.limits().max_proof_bytes,
            Limits::default().proof_bytes
        );
        assert!(!request.proof().diagnostic_ascii_lrat);
        assert!(matches!(
            continuation.begin(cnf, 8, Limits::default(), ProofRequest::default()),
            Err(Error::Pending)
        ));
    }

    #[test]
    fn completion_is_exactly_once_even_when_checking_fails() {
        let cnf = satisfiable();
        let problem = cnf.id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf, 1, Limits::default(), ProofRequest::default())
            .expect("begin");
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Sat {
                    problem,
                    model: Box::new([]),
                }
            ),
            Err(Error::Model(ModelError::Incomplete))
        ));
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Sat {
                    problem,
                    model: Box::new([1]),
                }
            ),
            Err(Error::StaleJob)
        ));
    }

    #[test]
    fn wrong_problem_does_not_consume_pending_job() {
        let cnf = satisfiable();
        let problem = cnf.id();
        let wrong = contradiction().id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf, 1, Limits::default(), ProofRequest::default())
            .expect("begin");
        assert_eq!(
            continuation.complete(
                request.job(),
                SolveResult::Unknown {
                    problem: wrong,
                    reason: None,
                }
            ),
            Err(Error::WrongProblem)
        );
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Sat {
                    problem,
                    model: Box::new([1]),
                }
            ),
            Ok(CheckedResult::Sat(_))
        ));
    }

    #[test]
    fn wrong_job_does_not_consume_pending_job() {
        let cnf = satisfiable();
        let problem = cnf.id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf, 1, Limits::default(), ProofRequest::default())
            .expect("begin");
        let wrong = JobId(NonZeroU64::new(request.job().0.get() + 1).expect("nonzero"));
        assert!(matches!(
            continuation.complete(
                wrong,
                SolveResult::Unknown {
                    problem,
                    reason: None,
                }
            ),
            Err(Error::StaleJob)
        ));
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Sat {
                    problem,
                    model: Box::new([1]),
                }
            ),
            Ok(CheckedResult::Sat(_))
        ));
    }

    #[test]
    fn cancellation_makes_late_completion_stale() {
        let cnf = satisfiable();
        let problem = cnf.id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf, 1, Limits::default(), ProofRequest::default())
            .expect("begin");
        continuation.cancel(request.job()).expect("cancel");
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Sat {
                    problem,
                    model: Box::new([1]),
                }
            ),
            Err(Error::StaleJob)
        ));
        assert_eq!(continuation.cancel(request.job()), Err(Error::StaleJob));
    }

    #[test]
    fn unknown_and_diagnostics_are_consumed_and_bounded() {
        let cnf = satisfiable();
        let problem = cnf.id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf.clone(), 1, Limits::default(), ProofRequest::default())
            .expect("begin");
        let oversized = "x".repeat(request.limits().max_diagnostic_bytes + 1);
        assert_eq!(
            continuation.complete(
                request.job(),
                SolveResult::Unknown {
                    problem,
                    reason: Some(oversized),
                }
            ),
            Err(Error::DiagnosticTooLarge)
        );
        assert_eq!(continuation.cancel(request.job()), Err(Error::StaleJob));

        let request = continuation
            .begin(cnf, 1, Limits::default(), ProofRequest::default())
            .expect("begin again");
        assert_eq!(
            continuation.complete(
                request.job(),
                SolveResult::Unknown {
                    problem,
                    reason: Some("interrupted".to_owned()),
                }
            ),
            Ok(CheckedResult::Unknown {
                reason: Some("interrupted".to_owned()),
            })
        );
    }

    #[test]
    fn ascii_lrat_is_an_explicit_bounded_diagnostic_only() {
        let cnf = contradiction();
        let problem = cnf.id();
        let proof: Box<[u8]> = Box::new([b'a', 6, 0, 2, 4, 0]);
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf.clone(), 0, Limits::default(), ProofRequest::default())
            .expect("begin");
        assert_eq!(
            continuation.complete(
                request.job(),
                SolveResult::Unsat {
                    problem,
                    proof: proof.clone(),
                    diagnostic_ascii_lrat: Some(b"3 0 1 2 0\n".as_slice().into()),
                }
            ),
            Err(Error::UnexpectedAsciiDiagnostic)
        );

        let request = continuation
            .begin(
                cnf,
                0,
                Limits::default(),
                ProofRequest {
                    diagnostic_ascii_lrat: true,
                },
            )
            .expect("diagnostic begin");
        assert!(matches!(
            continuation.complete(
                request.job(),
                SolveResult::Unsat {
                    problem,
                    proof,
                    diagnostic_ascii_lrat: Some(b"not checked as proof".as_slice().into()),
                }
            ),
            Ok(CheckedResult::Unsat(_))
        ));
    }

    #[test]
    fn valid_binary_lrat_is_checked_without_authority_mutation() {
        let cnf = contradiction();
        let problem = cnf.id();
        let mut continuation = Continuation::new();
        let request = continuation
            .begin(cnf, 0, Limits::default(), ProofRequest::default())
            .expect("begin");
        let proof: Box<[u8]> = Box::new([b'a', 6, 0, 2, 4, 0]);
        let result = continuation
            .complete(
                request.job(),
                SolveResult::Unsat {
                    problem,
                    proof,
                    diagnostic_ascii_lrat: None,
                },
            )
            .expect("checked");
        assert!(matches!(result, CheckedResult::Unsat(verdict) if verdict.problem() == problem));
    }
}
