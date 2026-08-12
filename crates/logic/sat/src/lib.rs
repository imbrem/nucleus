//! Bounded checking of results from untrusted SAT solvers.
//!
//! Binary LRAT is the production proof format. The ASCII parser is exposed
//! only to make diagnostics and fixtures readable. This crate has no storage
//! or Nucleus dependency: callers decide what authority, if any, a successful
//! check may confer.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

/// Stable identity of one canonical CNF matrix.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProblemId([u8; 32]);

impl ProblemId {
    /// Returns the digest bytes.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

/// Resource bounds applied while canonicalizing an untrusted CNF.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CnfLimits {
    /// Largest variable number.
    pub max_variable: u64,
    /// Maximum clauses before or after canonicalization.
    pub clauses: usize,
    /// Maximum literals in one input clause.
    pub literals_per_clause: usize,
    /// Maximum literals across the input matrix.
    pub total_literals: usize,
    /// Maximum bytes in the rendered canonical DIMACS problem.
    pub dimacs_bytes: usize,
}

impl Default for CnfLimits {
    fn default() -> Self {
        Self {
            max_variable: i64::MAX as u64,
            clauses: 1_000_000,
            literals_per_clause: 1_000_000,
            total_literals: 16_000_000,
            dimacs_bytes: 256 * 1024 * 1024,
        }
    }
}

/// Policy for structurally redundant CNF input.
#[non_exhaustive]
#[expect(
    clippy::struct_excessive_bools,
    reason = "independent canonicalization choices are the explicit policy"
)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CnfPolicy {
    /// Whether a matrix with no effective clauses is accepted.
    pub allow_empty_cnf: bool,
    /// Whether an empty clause is a valid immediate contradiction.
    pub allow_empty_clause: bool,
    /// Whether tautological clauses are dropped instead of rejected.
    pub drop_tautologies: bool,
    /// Whether duplicate literals are canonicalized instead of rejected.
    pub canonicalize_duplicate_literals: bool,
    /// Whether duplicate clauses are canonicalized instead of rejected.
    pub canonicalize_duplicate_clauses: bool,
}

impl Default for CnfPolicy {
    fn default() -> Self {
        Self {
            allow_empty_cnf: true,
            allow_empty_clause: true,
            drop_tautologies: true,
            canonicalize_duplicate_literals: true,
            canonicalize_duplicate_clauses: true,
        }
    }
}

/// Failure to validate and canonicalize a CNF matrix.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CnfError {
    /// A configured bound was exceeded.
    Limit {
        /// Name of the exhausted resource.
        resource: &'static str,
        /// Configured maximum.
        limit: usize,
    },
    /// Zero and the minimum signed integer cannot encode literals.
    InvalidLiteral,
    /// A variable exceeded the configured range.
    VariableOutOfRange,
    /// Policy rejected an empty clause.
    EmptyClause,
    /// Policy rejected a matrix with no effective clauses.
    EmptyCnf,
    /// Policy rejected a tautological clause.
    TautologicalClause,
    /// Policy rejected a repeated literal.
    DuplicateLiteral,
    /// Policy rejected a repeated clause.
    DuplicateClause,
}

impl std::fmt::Display for CnfError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Limit { resource, limit } => write!(f, "CNF {resource} exceeds limit {limit}"),
            Self::InvalidLiteral => f.write_str("CNF contains an invalid literal"),
            Self::VariableOutOfRange => f.write_str("CNF variable is outside the allowed range"),
            Self::EmptyClause => f.write_str("CNF policy rejects empty clauses"),
            Self::EmptyCnf => f.write_str("CNF policy rejects an empty matrix"),
            Self::TautologicalClause => f.write_str("CNF policy rejects tautological clauses"),
            Self::DuplicateLiteral => f.write_str("CNF policy rejects duplicate literals"),
            Self::DuplicateClause => f.write_str("CNF policy rejects duplicate clauses"),
        }
    }
}

impl std::error::Error for CnfError {}

/// An owned, validated canonical CNF problem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cnf {
    clauses: Box<[Vec<i64>]>,
    id: ProblemId,
    dimacs: Box<[u8]>,
}

impl Cnf {
    /// Validates, canonicalizes, identifies, and renders a CNF matrix.
    ///
    /// # Errors
    ///
    /// Rejects invalid, policy-forbidden, or oversized matrices.
    pub fn new(
        clauses: impl IntoIterator<Item = Vec<i64>>,
        limits: CnfLimits,
        policy: CnfPolicy,
    ) -> Result<Self, CnfError> {
        let mut canonical = Vec::new();
        let mut total = 0usize;
        let mut input_clauses = 0usize;
        for mut clause in clauses {
            input_clauses = input_clauses.checked_add(1).ok_or(CnfError::Limit {
                resource: "clauses",
                limit: limits.clauses,
            })?;
            if input_clauses > limits.clauses {
                return Err(CnfError::Limit {
                    resource: "clauses",
                    limit: limits.clauses,
                });
            }
            if clause.len() > limits.literals_per_clause {
                return Err(CnfError::Limit {
                    resource: "literals per clause",
                    limit: limits.literals_per_clause,
                });
            }
            total = total.checked_add(clause.len()).ok_or(CnfError::Limit {
                resource: "total literals",
                limit: limits.total_literals,
            })?;
            if total > limits.total_literals {
                return Err(CnfError::Limit {
                    resource: "total literals",
                    limit: limits.total_literals,
                });
            }
            if clause.is_empty() && !policy.allow_empty_clause {
                return Err(CnfError::EmptyClause);
            }
            for &literal in &clause {
                if literal == 0 || literal == i64::MIN {
                    return Err(CnfError::InvalidLiteral);
                }
                if literal.unsigned_abs() > limits.max_variable {
                    return Err(CnfError::VariableOutOfRange);
                }
            }
            clause.sort_unstable();
            let duplicate = clause.windows(2).any(|pair| pair[0] == pair[1]);
            if duplicate && !policy.canonicalize_duplicate_literals {
                return Err(CnfError::DuplicateLiteral);
            }
            clause.dedup();
            let literals: BTreeSet<i64> = clause.iter().copied().collect();
            let tautological = clause.iter().any(|literal| literals.contains(&-*literal));
            if tautological {
                if policy.drop_tautologies {
                    continue;
                }
                return Err(CnfError::TautologicalClause);
            }
            canonical.push(clause);
        }
        canonical.sort();
        let duplicate = canonical.windows(2).any(|pair| pair[0] == pair[1]);
        if duplicate && !policy.canonicalize_duplicate_clauses {
            return Err(CnfError::DuplicateClause);
        }
        canonical.dedup();
        if canonical.is_empty() && !policy.allow_empty_cnf {
            return Err(CnfError::EmptyCnf);
        }

        let mut identity = b"covalence.logic.sat.cnf/v1\0".to_vec();
        identity.extend_from_slice(&(canonical.len() as u64).to_le_bytes());
        for clause in &canonical {
            identity.extend_from_slice(&(clause.len() as u64).to_le_bytes());
            for literal in clause {
                identity.extend_from_slice(&literal.to_le_bytes());
            }
        }
        let id = ProblemId(*blake3::hash(&identity).as_bytes());
        let dimacs = render_dimacs(&canonical, limits.dimacs_bytes)?;
        Ok(Self {
            clauses: canonical.into_boxed_slice(),
            id,
            dimacs,
        })
    }

    /// Returns this exact canonical problem's identity.
    #[must_use]
    pub const fn id(&self) -> ProblemId {
        self.id
    }

    /// Returns canonical DIMACS bytes.
    #[must_use]
    pub fn dimacs(&self) -> &[u8] {
        &self.dimacs
    }

    /// Returns the canonical clause matrix in DIMACS clause order.
    #[must_use]
    pub fn clauses(&self) -> &[Vec<i64>] {
        &self.clauses
    }

    /// Checks a complete satisfying assignment for this problem.
    ///
    /// # Errors
    ///
    /// Rejects malformed, partial, unrelated, contradictory, or false models.
    pub fn verify_model(
        &self,
        model: &[i64],
        max_literals: usize,
    ) -> Result<VerifiedModel, ModelError> {
        verify_model_for(self, model, max_literals)
    }

    /// Checks a binary LRAT refutation of this exact problem.
    ///
    /// # Errors
    ///
    /// Rejects malformed, oversized, or invalid proofs.
    pub fn verify_binary(&self, proof: &[u8], limits: Limits) -> Result<VerifiedUnsat, LratError> {
        let instructions = parse_binary_bounded(proof, limits)?;
        check_clauses_bounded(&self.clauses, &instructions, limits)?;
        Ok(VerifiedUnsat { problem: self.id })
    }

    /// Checks parser-independent typed LRAT calls against this exact problem.
    ///
    /// # Errors
    ///
    /// Returns the first semantic call rejection or a missing-refutation error.
    pub fn verify_typed(
        &self,
        calls: &[covalence_logic_lrat::Call],
    ) -> Result<VerifiedUnsat, covalence_logic_lrat::Error> {
        covalence_logic_lrat::check(&self.clauses, calls)?;
        Ok(VerifiedUnsat { problem: self.id })
    }
}

fn render_dimacs(canonical: &[Vec<i64>], limit: usize) -> Result<Box<[u8]>, CnfError> {
    let max_variable = canonical
        .iter()
        .flatten()
        .map(|literal| literal.unsigned_abs())
        .max()
        .unwrap_or(0);
    let header = format!("p cnf {max_variable} {}\n", canonical.len());
    let dimacs_len = canonical.iter().try_fold(header.len(), |total, clause| {
        clause
            .iter()
            .try_fold(total, |total, literal| {
                total
                    .checked_add(decimal_len(*literal))
                    .and_then(|value| value.checked_add(1))
                    .ok_or(CnfError::Limit {
                        resource: "DIMACS bytes",
                        limit,
                    })
            })
            .and_then(|value| {
                value.checked_add(2).ok_or(CnfError::Limit {
                    resource: "DIMACS bytes",
                    limit,
                })
            })
    })?;
    if dimacs_len > limit {
        return Err(CnfError::Limit {
            resource: "DIMACS bytes",
            limit,
        });
    }
    let mut dimacs = String::with_capacity(dimacs_len);
    dimacs.push_str(&header);
    for clause in canonical {
        for literal in clause {
            write!(dimacs, "{literal} ").expect("writing to String cannot fail");
        }
        dimacs.push_str("0\n");
    }
    Ok(dimacs.into_bytes().into_boxed_slice())
}

fn decimal_len(value: i64) -> usize {
    let digits = value.unsigned_abs().ilog10() as usize + 1;
    digits + usize::from(value < 0)
}

/// One LRAT instruction.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LratInstr {
    /// Learn `clause` under `id`, justified by unit propagation over the
    /// clauses named in `hints` (in order, ending in a conflict).
    Learn {
        /// The new clause's identifier.
        id: u64,
        /// The clause's literals; empty is the refutation.
        clause: Vec<i64>,
        /// Propagation hints, in order; a negative hint opens a RAT
        /// group for the named clause.
        hints: Vec<i64>,
    },
    /// Forget the named clauses.
    Forget {
        /// The forgotten clause identifiers.
        ids: Vec<u64>,
    },
}

/// A failure while parsing a proof or applying an instruction.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LratError {
    /// A configured resource bound was exceeded.
    Limit {
        /// Name of the exhausted budget.
        resource: &'static str,
        /// Configured maximum.
        limit: usize,
    },
    /// The proof bytes are not well-formed LRAT.
    Parse {
        /// The offending line (ASCII) or byte offset (binary).
        at: usize,
    },
    /// A hint names a clause that is not live.
    UnknownClause {
        /// The instruction being applied.
        step: u64,
        /// The missing clause id.
        clause: u64,
    },
    /// A hint clause neither propagates nor conflicts.
    UselessHint {
        /// The instruction being applied.
        step: u64,
        /// The offending hint.
        clause: u64,
    },
    /// The hint list ended without reaching a conflict.
    NoConflict {
        /// The instruction being applied.
        step: u64,
    },
    /// A RAT step does not cover every clause containing the negated
    /// pivot.
    IncompleteRat {
        /// The instruction being applied.
        step: u64,
        /// A clause containing the negated pivot with no group.
        clause: u64,
    },
    /// A RAT instruction repeated a clause group.
    DuplicateRatGroup {
        /// The instruction being applied.
        step: u64,
        /// The repeated clause id.
        clause: u64,
    },
    /// A RAT step was encountered where only RUP is permitted.
    RatUnsupported {
        /// The instruction being applied.
        step: u64,
    },
    /// The instruction stream ended without deriving the empty clause.
    NoRefutation,
    /// A learned clause id was not strictly newer than every prior id.
    NonFreshClauseId {
        /// The rejected instruction id.
        step: u64,
    },
}

impl std::fmt::Display for LratError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Limit { resource, limit } => write!(f, "LRAT {resource} exceeds limit {limit}"),
            Self::Parse { at } => write!(f, "malformed LRAT at {at}"),
            Self::UnknownClause { step, clause } => {
                write!(f, "LRAT step {step} references unknown clause {clause}")
            }
            Self::UselessHint { step, clause } => {
                write!(f, "LRAT hint {clause} does not advance step {step}")
            }
            Self::NoConflict { step } => write!(f, "LRAT step {step} reaches no conflict"),
            Self::IncompleteRat { step, clause } => {
                write!(f, "LRAT step {step} omits RAT clause {clause}")
            }
            Self::DuplicateRatGroup { step, clause } => {
                write!(f, "LRAT step {step} repeats RAT clause {clause}")
            }
            Self::RatUnsupported { step } => write!(f, "LRAT step {step} uses unsupported RAT"),
            Self::NoRefutation => f.write_str("LRAT proof derives no refutation"),
            Self::NonFreshClauseId { step } => {
                write!(f, "LRAT learned clause id {step} is not fresh")
            }
        }
    }
}

impl std::error::Error for LratError {}

/// Resource bounds for untrusted certificates.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    pub proof_bytes: usize,
    pub instructions: usize,
    pub live_clauses: usize,
    pub terms_per_instruction: usize,
    pub total_terms: usize,
    pub work_units: usize,
}

/// Successful bounded verification of an LRAT refutation.
///
/// Fields are private so callers cannot manufacture a verifier verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VerifiedUnsat {
    problem: ProblemId,
}

impl VerifiedUnsat {
    /// Returns the exact canonical problem which was refuted.
    #[must_use]
    pub const fn problem(&self) -> ProblemId {
        self.problem
    }
}

/// Successful bounded verification of a satisfying assignment.
///
/// This is evidence returned by a checker, not logical authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedModel {
    problem: ProblemId,
    literals: Box<[i64]>,
}

impl VerifiedModel {
    /// Returns the exact canonical problem satisfied by the assignment.
    #[must_use]
    pub const fn problem(&self) -> ProblemId {
        self.problem
    }

    /// Returns the checked assignment.
    #[must_use]
    pub fn literals(&self) -> &[i64] {
        &self.literals
    }
}

/// Why an untrusted model was rejected.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModelError {
    /// The response exceeded its literal budget.
    TooLarge,
    /// A zero or minimum signed literal cannot name a variable.
    InvalidLiteral,
    /// The response mentioned a variable absent from the problem.
    UnrelatedVariable,
    /// Both polarities of one variable were supplied.
    ContradictoryLiterals,
    /// A literal appeared more than once.
    DuplicateLiteral,
    /// The response did not assign every problem variable.
    Incomplete,
    /// At least one clause was not satisfied.
    UnsatisfiedClause,
}

impl std::fmt::Display for ModelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooLarge => f.write_str("SAT model exceeds its literal limit"),
            Self::InvalidLiteral => f.write_str("SAT model contains an invalid literal"),
            Self::UnrelatedVariable => f.write_str("SAT model mentions an unrelated variable"),
            Self::ContradictoryLiterals => f.write_str("SAT model assigns both polarities"),
            Self::DuplicateLiteral => f.write_str("SAT model repeats a literal"),
            Self::Incomplete => f.write_str("SAT model does not assign every variable"),
            Self::UnsatisfiedClause => f.write_str("SAT model leaves a clause unsatisfied"),
        }
    }
}

impl std::error::Error for ModelError {}

/// Checks a complete model for a CNF under an explicit response bound.
///
/// # Errors
///
/// Rejects malformed, partial, unrelated, contradictory, or non-satisfying
/// assignments.
fn verify_model_for(
    cnf: &Cnf,
    model: &[i64],
    max_literals: usize,
) -> Result<VerifiedModel, ModelError> {
    if model.len() > max_literals {
        return Err(ModelError::TooLarge);
    }
    let mut variables = BTreeSet::new();
    for &literal in cnf.clauses.iter().flatten() {
        if literal == 0 || literal == i64::MIN {
            return Err(ModelError::InvalidLiteral);
        }
        variables.insert(literal.unsigned_abs());
    }
    let mut assignment = BTreeSet::new();
    for &literal in model {
        if literal == 0 || literal == i64::MIN {
            return Err(ModelError::InvalidLiteral);
        }
        if !variables.contains(&literal.unsigned_abs()) {
            return Err(ModelError::UnrelatedVariable);
        }
        if assignment.contains(&-literal) {
            return Err(ModelError::ContradictoryLiterals);
        }
        if !assignment.insert(literal) {
            return Err(ModelError::DuplicateLiteral);
        }
    }
    if assignment.len() != variables.len() {
        return Err(ModelError::Incomplete);
    }
    if cnf
        .clauses
        .iter()
        .any(|clause| !clause.iter().any(|literal| assignment.contains(literal)))
    {
        return Err(ModelError::UnsatisfiedClause);
    }
    let mut literals = model.to_vec();
    literals.sort_unstable_by_key(|literal| literal.unsigned_abs());
    Ok(VerifiedModel {
        problem: cnf.id,
        literals: literals.into_boxed_slice(),
    })
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            proof_bytes: 64 * 1024 * 1024,
            instructions: 2_000_000,
            live_clauses: 1_000_000,
            terms_per_instruction: 1_000_000,
            total_terms: 16_000_000,
            work_units: 100_000_000,
        }
    }
}

/// The mini-LCF clause kernel.
///
/// Clauses enter only through [`Self::new`] (the caller-vouched initial
/// clauses) and the checked [`Self::learn`]; [`Self::refuted`] reports
/// whether the empty clause has been established.
pub(crate) struct LratKernel {
    live: BTreeMap<u64, Vec<i64>>,
    refuted: bool,
    last_id: u64,
}

impl LratKernel {
    /// Opens a kernel over the initial clauses, numbered `1..=n` in order.
    #[must_use]
    pub(crate) fn new(initial: &[Vec<i64>]) -> Self {
        Self {
            live: initial
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as u64 + 1, clause.clone()))
                .collect(),
            refuted: false,
            last_id: initial.len() as u64,
        }
    }

    /// The `learn` rule: admits `clause` iff its negation propagates to
    /// a conflict through the hinted clauses (RUP), or — when the hints
    /// contain RAT groups — every resolvent on the pivot (the clause's
    /// first literal) does. RAT additions preserve satisfiability rather
    /// than equivalence, which suffices for the kernel's only judgement,
    /// unsatisfiability of the initial clauses.
    ///
    /// # Errors
    ///
    /// Fails without changing kernel state when the hints do not certify
    /// the clause.
    pub(crate) fn learn(
        &mut self,
        id: u64,
        clause: &[i64],
        hints: &[i64],
    ) -> Result<(), LratError> {
        if id <= self.last_id {
            return Err(LratError::NonFreshClauseId { step: id });
        }
        let split = hints
            .iter()
            .position(|hint| *hint < 0)
            .unwrap_or(hints.len());
        let (rup_hints, rat_hints) = hints.split_at(split);
        let mut assigned: BTreeSet<i64> = clause.iter().map(|literal| -literal).collect();
        if !self.propagate(id, &mut assigned, rup_hints)? {
            if clause.is_empty() {
                return Err(LratError::NoConflict { step: id });
            }
            self.rat(id, clause, &assigned, rat_hints)?;
        }
        if clause.is_empty() {
            self.refuted = true;
        }
        self.live.insert(id, clause.to_vec());
        self.last_id = id;
        Ok(())
    }

    /// Checks the RAT groups against the propagated assignment: every
    /// live clause containing the negated pivot (the clause's first
    /// literal) must resolve to a conflict, either tautologically or
    /// through its group's propagation hints.
    fn rat(
        &self,
        id: u64,
        clause: &[i64],
        assigned: &BTreeSet<i64>,
        rat_hints: &[i64],
    ) -> Result<(), LratError> {
        let pivot = *clause.first().ok_or(LratError::NoConflict { step: id })?;
        let mut groups: Vec<(u64, Vec<i64>)> = Vec::new();
        let mut seen = BTreeSet::new();
        for hint in rat_hints {
            if *hint < 0 {
                let key = hint.unsigned_abs();
                if !seen.insert(key) {
                    return Err(LratError::DuplicateRatGroup {
                        step: id,
                        clause: key,
                    });
                }
                groups.push((key, Vec::new()));
            } else if let Some(group) = groups.last_mut() {
                group.1.push(*hint);
            } else {
                return Err(LratError::NoConflict { step: id });
            }
        }
        let covered: BTreeSet<u64> = groups.iter().map(|(key, _)| *key).collect();
        for (other_id, other) in &self.live {
            if other.contains(&-pivot) && !covered.contains(other_id) {
                return Err(LratError::IncompleteRat {
                    step: id,
                    clause: *other_id,
                });
            }
        }
        for (key, group_hints) in &groups {
            let other = self.live.get(key).ok_or(LratError::UnknownClause {
                step: id,
                clause: *key,
            })?;
            if !other.contains(&-pivot) {
                continue;
            }
            // Resolvent assignment: extend the propagated assignment
            // with the negation of the other clause minus the resolved
            // literal. A contradictory extension is an immediate
            // (tautological) conflict.
            let mut assignment = assigned.clone();
            let mut contradictory = false;
            for literal in other {
                if *literal != -pivot {
                    if assignment.contains(literal) {
                        contradictory = true;
                        break;
                    }
                    assignment.insert(-literal);
                }
            }
            if contradictory {
                continue;
            }
            if !self.propagate(id, &mut assignment, group_hints)? {
                return Err(LratError::NoConflict { step: id });
            }
        }
        Ok(())
    }

    /// Unit-propagates through hinted clauses, extending `assigned`;
    /// returns whether a conflict was reached.
    fn propagate(
        &self,
        id: u64,
        assigned: &mut BTreeSet<i64>,
        hints: &[i64],
    ) -> Result<bool, LratError> {
        for hint in hints {
            let key = u64::try_from(*hint).map_err(|_| LratError::NoConflict { step: id })?;
            let hinted = self.live.get(&key).ok_or(LratError::UnknownClause {
                step: id,
                clause: key,
            })?;
            if hinted.iter().any(|literal| assigned.contains(literal)) {
                return Err(LratError::UselessHint {
                    step: id,
                    clause: key,
                });
            }
            let mut unassigned = hinted
                .iter()
                .filter(|literal| !assigned.contains(&-**literal));
            match (unassigned.next(), unassigned.next()) {
                (None, _) => return Ok(true),
                (Some(unit), None) => {
                    assigned.insert(*unit);
                }
                (Some(_), Some(_)) => {
                    return Err(LratError::UselessHint {
                        step: id,
                        clause: key,
                    });
                }
            }
        }
        Ok(false)
    }

    /// The `forget` rule: dropping clauses only ever weakens the kernel.
    pub(crate) fn forget(&mut self, ids: &[u64]) -> Result<(), LratError> {
        let mut seen = BTreeSet::new();
        for id in ids {
            if !seen.insert(*id) || !self.live.contains_key(id) {
                return Err(LratError::UnknownClause {
                    step: self.last_id,
                    clause: *id,
                });
            }
        }
        for id in ids {
            self.live.remove(id);
        }
        Ok(())
    }

    /// Whether the empty clause has been established.
    #[must_use]
    pub(crate) const fn refuted(&self) -> bool {
        self.refuted
    }

    /// Applies one instruction.
    ///
    /// # Errors
    ///
    /// Fails when a `Learn` instruction is not certified by its hints.
    pub(crate) fn apply(&mut self, instruction: &LratInstr) -> Result<(), LratError> {
        match instruction {
            LratInstr::Learn { id, clause, hints } => self.learn(*id, clause, hints),
            LratInstr::Forget { ids } => self.forget(ids),
        }
    }
}

/// Drives a fresh kernel through an instruction stream and demands a
/// refutation.
///
/// # Errors
///
/// Fails on the first uncertified instruction, or if the stream ends
/// without deriving the empty clause.
pub fn check(cnf: &Cnf, instructions: &[LratInstr]) -> Result<(), LratError> {
    check_bounded(cnf, instructions, Limits::default())
}

/// Checks a decoded proof under explicit work and live-state bounds.
///
/// # Errors
///
/// Returns the first failed bound or proof step.
pub fn check_bounded(
    cnf: &Cnf,
    instructions: &[LratInstr],
    limits: Limits,
) -> Result<(), LratError> {
    check_clauses_bounded(&cnf.clauses, instructions, limits)
}

#[expect(
    clippy::too_many_lines,
    reason = "validation and replay share one work budget"
)]
fn check_clauses_bounded(
    initial: &[Vec<i64>],
    instructions: &[LratInstr],
    limits: Limits,
) -> Result<(), LratError> {
    validate_decoded(instructions, limits)?;
    if instructions.len() > limits.instructions {
        return Err(LratError::Limit {
            resource: "instructions",
            limit: limits.instructions,
        });
    }
    if initial.len() > limits.live_clauses {
        return Err(LratError::Limit {
            resource: "live clauses",
            limit: limits.live_clauses,
        });
    }
    let mut decoded_terms = initial.iter().try_fold(0usize, |total, clause| {
        if clause.iter().any(|value| *value == 0 || *value == i64::MIN) {
            return Err(LratError::Parse { at: 0 });
        }
        if clause.len() > limits.terms_per_instruction {
            return Err(LratError::Limit {
                resource: "terms per instruction",
                limit: limits.terms_per_instruction,
            });
        }
        total.checked_add(clause.len()).ok_or(LratError::Limit {
            resource: "total terms",
            limit: limits.total_terms,
        })
    })?;
    if decoded_terms > limits.total_terms {
        return Err(LratError::Limit {
            resource: "total terms",
            limit: limits.total_terms,
        });
    }
    for instruction in instructions {
        let terms = match instruction {
            LratInstr::Learn { clause, hints, .. } => clause.len().saturating_add(hints.len()),
            LratInstr::Forget { ids } => ids.len(),
        };
        if terms > limits.terms_per_instruction {
            return Err(LratError::Limit {
                resource: "terms per instruction",
                limit: limits.terms_per_instruction,
            });
        }
        decoded_terms = decoded_terms.checked_add(terms).ok_or(LratError::Limit {
            resource: "total terms",
            limit: limits.total_terms,
        })?;
        if decoded_terms > limits.total_terms {
            return Err(LratError::Limit {
                resource: "total terms",
                limit: limits.total_terms,
            });
        }
    }
    let mut kernel = LratKernel::new(initial);
    let mut work = initial.iter().try_fold(0usize, |total, clause| {
        checked_work(total, clause.len(), limits.work_units)
    })?;
    for instruction in instructions {
        work = match instruction {
            LratInstr::Learn { clause, hints, .. } => {
                let split = hints
                    .iter()
                    .position(|hint| *hint < 0)
                    .unwrap_or(hints.len());
                let mut cost = checked_work(work, clause.len(), limits.work_units)?;
                let mut assignment = clause.len();
                for hint in &hints[..split] {
                    let length = kernel.live.get(&hint.unsigned_abs()).map_or(1, Vec::len);
                    cost = checked_work(cost, length, limits.work_units)?;
                    assignment = checked_work(assignment, length, limits.work_units)?;
                }
                if split < hints.len() {
                    for live in kernel.live.values() {
                        cost = checked_work(cost, live.len(), limits.work_units)?;
                    }
                    for hint in &hints[split..] {
                        let length = kernel.live.get(&hint.unsigned_abs()).map_or(1, Vec::len);
                        cost = checked_work(cost, length, limits.work_units)?;
                        if *hint < 0 {
                            cost = checked_work(cost, assignment, limits.work_units)?;
                        }
                    }
                }
                cost
            }
            LratInstr::Forget { ids } => checked_work(work, ids.len(), limits.work_units)?,
        };
        kernel.apply(instruction)?;
        if kernel.live.len() > limits.live_clauses {
            return Err(LratError::Limit {
                resource: "live clauses",
                limit: limits.live_clauses,
            });
        }
        if kernel.refuted() {
            return Ok(());
        }
    }
    Err(LratError::NoRefutation)
}

fn checked_work(total: usize, amount: usize, limit: usize) -> Result<usize, LratError> {
    let work = total.checked_add(amount).ok_or(LratError::Limit {
        resource: "checker work",
        limit,
    })?;
    if work > limit {
        return Err(LratError::Limit {
            resource: "checker work",
            limit,
        });
    }
    Ok(work)
}

pub(crate) fn validate_decoded(
    instructions: &[LratInstr],
    limits: Limits,
) -> Result<(), LratError> {
    if instructions.len() > limits.instructions {
        return Err(LratError::Limit {
            resource: "instructions",
            limit: limits.instructions,
        });
    }
    let mut total = 0usize;
    for (index, instruction) in instructions.iter().enumerate() {
        let terms = match instruction {
            LratInstr::Learn { id, clause, hints } => {
                if *id == 0
                    || clause.iter().any(|value| *value == 0 || *value == i64::MIN)
                    || hints.iter().any(|value| *value == 0 || *value == i64::MIN)
                {
                    return Err(LratError::Parse { at: index });
                }
                clause.len().saturating_add(hints.len())
            }
            LratInstr::Forget { ids } => {
                if ids.contains(&0) {
                    return Err(LratError::Parse { at: index });
                }
                ids.len()
            }
        };
        if terms > limits.terms_per_instruction {
            return Err(LratError::Limit {
                resource: "terms per instruction",
                limit: limits.terms_per_instruction,
            });
        }
        total = total.checked_add(terms).ok_or(LratError::Limit {
            resource: "total terms",
            limit: limits.total_terms,
        })?;
        if total > limits.total_terms {
            return Err(LratError::Limit {
                resource: "total terms",
                limit: limits.total_terms,
            });
        }
    }
    Ok(())
}

/// Parses a proof for diagnostics, auto-detecting its representation.
///
/// # Errors
///
/// Fails on malformed input; parsing is untrusted, so a parse bug can
/// only mis-drive the kernel into rejection.
pub fn parse(bytes: &[u8]) -> Result<Vec<LratInstr>, LratError> {
    parse_bounded(bytes, Limits::default())
}

/// Parses ASCII or binary LRAT for diagnostics under explicit bounds.
///
/// # Errors
///
/// Returns a parse or bound error.
pub fn parse_bounded(bytes: &[u8], limits: Limits) -> Result<Vec<LratInstr>, LratError> {
    if bytes.len() > limits.proof_bytes {
        return Err(LratError::Limit {
            resource: "proof bytes",
            limit: limits.proof_bytes,
        });
    }
    if bytes
        .first()
        .is_some_and(|byte| *byte == b'a' || *byte == b'd')
    {
        parse_binary_bounded(bytes, limits)
    } else {
        parse_text_bounded(
            std::str::from_utf8(bytes).map_err(|_| LratError::Parse { at: 0 })?,
            limits,
        )
    }
}

/// Parses the ASCII LRAT format.
///
/// # Errors
///
/// Fails on any line that is not an addition or deletion step.
pub fn parse_text(text: &str) -> Result<Vec<LratInstr>, LratError> {
    parse_text_bounded(text, Limits::default())
}

fn parse_text_bounded(text: &str, limits: Limits) -> Result<Vec<LratInstr>, LratError> {
    if text.len() > limits.proof_bytes {
        return Err(LratError::Limit {
            resource: "proof bytes",
            limit: limits.proof_bytes,
        });
    }
    let mut instructions = Vec::new();
    let mut total_terms = 0usize;
    for (index, raw_line) in text.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let parse_error = LratError::Parse { at: index + 1 };
        let mut tokens = line.split_ascii_whitespace();
        let id: u64 = tokens
            .next()
            .and_then(|token| token.parse().ok())
            .ok_or(parse_error.clone())?;
        if id == 0 {
            return Err(parse_error);
        }
        let first = tokens.next().ok_or(parse_error.clone())?;
        if first == "d" {
            let mut ids = Vec::new();
            let mut terminated = false;
            for token in tokens.by_ref() {
                let value: u64 = token.parse().map_err(|_| parse_error.clone())?;
                if value == 0 {
                    terminated = true;
                    break;
                }
                ids.push(value);
                charge(&mut total_terms, ids.len(), limits)?;
            }
            if !terminated {
                return Err(parse_error);
            }
            if tokens.next().is_some() {
                return Err(parse_error);
            }
            instructions.push(LratInstr::Forget { ids });
            charge_instructions(instructions.len(), limits)?;
            continue;
        }
        let mut clause = Vec::new();
        let mut hints = Vec::new();
        let mut in_hints = false;
        let mut terminated = false;
        let mut values = std::iter::once(first).chain(tokens.by_ref());
        for token in values.by_ref() {
            let value: i64 = token.parse().map_err(|_| parse_error.clone())?;
            if value == i64::MIN {
                return Err(parse_error.clone());
            }
            if value == 0 {
                if in_hints {
                    terminated = true;
                    break;
                }
                in_hints = true;
            } else if in_hints {
                hints.push(value);
                charge(
                    &mut total_terms,
                    clause.len().saturating_add(hints.len()),
                    limits,
                )?;
            } else {
                clause.push(value);
                charge(&mut total_terms, clause.len(), limits)?;
            }
        }
        if !terminated {
            return Err(parse_error);
        }
        if values.next().is_some() {
            return Err(parse_error);
        }
        instructions.push(LratInstr::Learn { id, clause, hints });
        charge_instructions(instructions.len(), limits)?;
    }
    Ok(instructions)
}

/// Parses the binary LRAT format (`CaDiCaL`'s default).
///
/// Steps are marked `a`/`d`; every number is a variable-length integer
/// (7 data bits per byte, high bit continues) carrying the signed mapping
/// `2|n| + sign`, with `0x00` terminating each section.
///
/// # Errors
///
/// Fails on truncated or malformed input.
pub fn parse_binary(bytes: &[u8]) -> Result<Vec<LratInstr>, LratError> {
    parse_binary_bounded(bytes, Limits::default())
}

/// Renders strict binary LRAT as canonical ASCII for diagnostics.
///
/// This function does not check a proof and confers no authority. Deletion
/// command numbers are synthetic because binary LRAT does not encode them.
///
/// # Errors
///
/// Rejects malformed or oversized binary input, or diagnostic output larger
/// than `limits.proof_bytes`.
pub fn binary_lrat_to_text(bytes: &[u8], limits: Limits) -> Result<String, LratError> {
    let instructions = parse_binary_bounded(bytes, limits)?;
    let mut output = String::new();
    for (index, instruction) in instructions.iter().enumerate() {
        match instruction {
            LratInstr::Learn { id, clause, hints } => {
                write!(output, "{id}").expect("writing to String cannot fail");
                for literal in clause {
                    write!(output, " {literal}").expect("writing to String cannot fail");
                }
                output.push_str(" 0");
                for hint in hints {
                    write!(output, " {hint}").expect("writing to String cannot fail");
                }
                output.push_str(" 0\n");
            }
            LratInstr::Forget { ids } => {
                write!(output, "{} d", index + 1).expect("writing to String cannot fail");
                for id in ids {
                    write!(output, " {id}").expect("writing to String cannot fail");
                }
                output.push_str(" 0\n");
            }
        }
        if output.len() > limits.proof_bytes {
            return Err(LratError::Limit {
                resource: "diagnostic bytes",
                limit: limits.proof_bytes,
            });
        }
    }
    Ok(output)
}

fn parse_binary_bounded(bytes: &[u8], limits: Limits) -> Result<Vec<LratInstr>, LratError> {
    if bytes.len() > limits.proof_bytes {
        return Err(LratError::Limit {
            resource: "proof bytes",
            limit: limits.proof_bytes,
        });
    }
    let mut instructions = Vec::new();
    let mut position = 0_usize;
    let mut total_terms = 0usize;
    while position < bytes.len() {
        let marker = bytes[position];
        position += 1;
        match marker {
            b'a' => {
                let id = read_unsigned(bytes, &mut position)?;
                if id == 0 {
                    return Err(LratError::Parse { at: position });
                }
                let mut clause = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    clause.push(value);
                    charge(&mut total_terms, clause.len(), limits)?;
                }
                let mut hints = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    hints.push(value);
                    charge(
                        &mut total_terms,
                        clause.len().saturating_add(hints.len()),
                        limits,
                    )?;
                }
                instructions.push(LratInstr::Learn { id, clause, hints });
                charge_instructions(instructions.len(), limits)?;
            }
            b'd' => {
                let mut ids = Vec::new();
                loop {
                    let value = read_signed(bytes, &mut position)?;
                    if value == 0 {
                        break;
                    }
                    let id = u64::try_from(value).map_err(|_| LratError::Parse { at: position })?;
                    ids.push(id);
                    charge(&mut total_terms, ids.len(), limits)?;
                }
                instructions.push(LratInstr::Forget { ids });
                charge_instructions(instructions.len(), limits)?;
            }
            _ => return Err(LratError::Parse { at: position - 1 }),
        }
    }
    Ok(instructions)
}

fn charge(total: &mut usize, current: usize, limits: Limits) -> Result<(), LratError> {
    if current > limits.terms_per_instruction {
        return Err(LratError::Limit {
            resource: "terms per instruction",
            limit: limits.terms_per_instruction,
        });
    }
    *total = total.checked_add(1).ok_or(LratError::Limit {
        resource: "total terms",
        limit: limits.total_terms,
    })?;
    if *total > limits.total_terms {
        return Err(LratError::Limit {
            resource: "total terms",
            limit: limits.total_terms,
        });
    }
    Ok(())
}

fn charge_instructions(current: usize, limits: Limits) -> Result<(), LratError> {
    if current > limits.instructions {
        Err(LratError::Limit {
            resource: "instructions",
            limit: limits.instructions,
        })
    } else {
        Ok(())
    }
}

/// Reads one canonical MSB-continuation `u64` varint.
fn read_varint(bytes: &[u8], position: &mut usize) -> Result<u64, LratError> {
    let mut value = 0_u64;
    let mut shift = 0_u32;
    let mut bytes_read = 0_u32;
    loop {
        let byte = *bytes
            .get(*position)
            .ok_or(LratError::Parse { at: *position })?;
        *position += 1;
        bytes_read += 1;
        let payload = byte & 0x7f;
        if shift == 63 && payload > 1 {
            return Err(LratError::Parse { at: *position });
        }
        value |= u64::from(payload) << shift;
        if byte & 0x80 == 0 {
            if bytes_read > 1 && payload == 0 {
                return Err(LratError::Parse { at: *position });
            }
            return Ok(value);
        }
        if bytes_read == 10 {
            return Err(LratError::Parse { at: *position });
        }
        shift += 7;
    }
}

/// Reads a number in the signed mapping and demands it be non-negative.
fn read_unsigned(bytes: &[u8], position: &mut usize) -> Result<u64, LratError> {
    let value = read_signed(bytes, position)?;
    u64::try_from(value).map_err(|_| LratError::Parse { at: *position })
}

/// Reads a number in the signed mapping `2|n| + sign`.
fn read_signed(bytes: &[u8], position: &mut usize) -> Result<i64, LratError> {
    let raw = read_varint(bytes, position)?;
    if raw == 1 {
        return Err(LratError::Parse { at: *position });
    }
    let magnitude = i64::try_from(raw >> 1).map_err(|_| LratError::Parse { at: *position })?;
    Ok(if raw & 1 == 1 { -magnitude } else { magnitude })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cnf(clauses: Vec<Vec<i64>>) -> Cnf {
        Cnf::new(clauses, CnfLimits::default(), CnfPolicy::default()).expect("CNF")
    }

    #[test]
    fn canonical_cnf_has_stable_identity_and_dimacs() {
        let first = cnf(vec![vec![2, 1, 1], vec![-3, 2], vec![4, -4]]);
        let second = cnf(vec![vec![2, -3], vec![1, 2]]);
        assert_eq!(first, second);
        assert_eq!(first.dimacs(), b"p cnf 3 2\n-3 2 0\n1 2 0\n");
        assert_eq!(
            first.id().as_bytes(),
            &[
                45, 138, 29, 167, 97, 0, 86, 101, 238, 111, 17, 157, 34, 60, 14, 180, 93, 84, 239,
                104, 156, 95, 40, 111, 235, 243, 14, 127, 207, 155, 88, 142,
            ]
        );
    }

    #[test]
    fn cnf_policy_rejects_each_noncanonical_input_when_requested() {
        let strict = CnfPolicy {
            allow_empty_cnf: false,
            allow_empty_clause: false,
            drop_tautologies: false,
            canonicalize_duplicate_literals: false,
            canonicalize_duplicate_clauses: false,
        };
        let limits = CnfLimits {
            max_variable: 3,
            clauses: 2,
            literals_per_clause: 2,
            total_literals: 3,
            dimacs_bytes: 128,
        };
        assert_eq!(
            Cnf::new(Vec::<Vec<i64>>::new(), limits, strict),
            Err(CnfError::EmptyCnf)
        );
        assert_eq!(
            Cnf::new(vec![vec![]], limits, strict),
            Err(CnfError::EmptyClause)
        );
        assert_eq!(
            Cnf::new(vec![vec![1, -1]], limits, strict),
            Err(CnfError::TautologicalClause)
        );
        assert_eq!(
            Cnf::new(vec![vec![1, 1]], limits, strict),
            Err(CnfError::DuplicateLiteral)
        );
        assert_eq!(
            Cnf::new(vec![vec![1], vec![1]], limits, strict),
            Err(CnfError::DuplicateClause)
        );
        assert_eq!(
            Cnf::new(vec![vec![4]], limits, strict),
            Err(CnfError::VariableOutOfRange)
        );
        assert_eq!(
            Cnf::new(vec![vec![0]], limits, strict),
            Err(CnfError::InvalidLiteral)
        );
    }

    #[test]
    fn model_verdict_is_complete_and_non_contradictory() {
        let cnf = Cnf::new(
            vec![vec![1, 2], vec![-1, 2]],
            CnfLimits::default(),
            CnfPolicy::default(),
        )
        .expect("CNF");
        assert_eq!(
            cnf.verify_model(&[1, 2], 2).expect("model").literals(),
            &[1, 2]
        );
        assert_eq!(cnf.verify_model(&[2], 2), Err(ModelError::Incomplete));
        assert_eq!(
            cnf.verify_model(&[1, -1, 2], 3),
            Err(ModelError::ContradictoryLiterals)
        );
        assert_eq!(
            cnf.verify_model(&[2, 1], 2)
                .expect("canonical model")
                .literals(),
            &[1, 2]
        );
    }

    #[test]
    fn dimacs_size_is_bounded_before_rendering() {
        let limits = CnfLimits {
            dimacs_bytes: 12,
            ..CnfLimits::default()
        };
        assert_eq!(
            Cnf::new(vec![vec![i64::MAX]], limits, CnfPolicy::default()),
            Err(CnfError::Limit {
                resource: "DIMACS bytes",
                limit: 12,
            })
        );
    }

    #[test]
    fn verdicts_are_bound_to_the_exact_problem() {
        let contradiction = cnf(vec![vec![1], vec![-1]]);
        let other = cnf(vec![vec![1]]);
        let proof = [b'a', 6, 0, 2, 4, 0];
        let verdict = contradiction
            .verify_binary(&proof, Limits::default())
            .expect("refutation");
        assert_eq!(verdict.problem(), contradiction.id());
        assert_ne!(verdict.problem(), other.id());
        assert!(other.verify_binary(&proof, Limits::default()).is_err());

        let model = other.verify_model(&[1], 1).expect("model");
        assert_eq!(model.problem(), other.id());
        assert_ne!(model.problem(), contradiction.id());
    }

    #[test]
    fn typed_lrat_verdict_is_bound_to_the_exact_problem() {
        let contradiction = cnf(vec![vec![1], vec![-1]]);
        let calls = [covalence_logic_lrat::Call::LearnRup {
            id: 3,
            clause: vec![],
            ordered_hints: vec![1, 2],
        }];
        let verdict = contradiction.verify_typed(&calls).expect("refutation");
        assert_eq!(verdict.problem(), contradiction.id());
        assert!(cnf(vec![vec![1]]).verify_typed(&calls).is_err());
    }

    #[test]
    fn learned_clause_ids_are_strictly_monotone_even_after_deletion() {
        let initial = vec![vec![1], vec![-1]];
        assert_eq!(
            check(
                &cnf(initial.clone()),
                &[LratInstr::Learn {
                    id: 2,
                    clause: vec![],
                    hints: vec![1, 2],
                }]
            ),
            Err(LratError::NonFreshClauseId { step: 2 })
        );
        assert_eq!(
            check(
                &cnf(initial.clone()),
                &[
                    LratInstr::Learn {
                        id: 3,
                        clause: vec![1],
                        hints: vec![2],
                    },
                    LratInstr::Forget { ids: vec![3] },
                    LratInstr::Learn {
                        id: 3,
                        clause: vec![1],
                        hints: vec![1],
                    },
                ]
            ),
            Err(LratError::NonFreshClauseId { step: 3 })
        );
    }

    #[test]
    fn deletions_reject_unknown_and_repeated_ids_without_mutation() {
        let mut kernel = LratKernel::new(&[vec![1], vec![-1]]);
        assert_eq!(
            kernel.forget(&[1, 99]),
            Err(LratError::UnknownClause {
                step: 2,
                clause: 99,
            })
        );
        assert!(kernel.live.contains_key(&1));
        assert!(kernel.live.contains_key(&2));
        assert_eq!(
            kernel.forget(&[1, 1]),
            Err(LratError::UnknownClause { step: 2, clause: 1 })
        );
        assert!(kernel.live.contains_key(&1));
        kernel.forget(&[1]).expect("first deletion");
        assert_eq!(
            kernel.forget(&[1]),
            Err(LratError::UnknownClause { step: 2, clause: 1 })
        );
    }

    #[test]
    fn binary_diagnostics_roundtrip_and_remain_bounded() {
        let binary = [b'a', 6, 0, 2, 4, 0, b'd', 6, 0];
        let text = binary_lrat_to_text(&binary, Limits::default()).expect("diagnostic text");
        assert_eq!(
            parse_binary(&binary).expect("binary"),
            parse_text(&text).expect("text")
        );
        let tight = Limits {
            proof_bytes: binary.len(),
            ..Limits::default()
        };
        assert_eq!(
            binary_lrat_to_text(&binary, tight),
            Err(LratError::Limit {
                resource: "diagnostic bytes",
                limit: binary.len(),
            })
        );
        let mut trailing = binary.to_vec();
        trailing.push(0xff);
        assert!(parse_binary(&trailing).is_err());
    }

    #[test]
    fn binary_numbers_cover_the_cnf_domain_and_reject_nonminimal_varints() {
        fn encode(mut value: u64) -> Vec<u8> {
            let mut bytes = Vec::new();
            loop {
                let payload = (value & 0x7f) as u8;
                value >>= 7;
                bytes.push(if value == 0 { payload } else { payload | 0x80 });
                if value == 0 {
                    return bytes;
                }
            }
        }

        let mut proof = vec![b'a', 2];
        proof.extend(encode((i64::MAX as u64) << 1));
        proof.extend([0, 0]);
        assert_eq!(
            parse_binary(&proof).expect("maximum signed literal"),
            vec![LratInstr::Learn {
                id: 1,
                clause: vec![i64::MAX],
                hints: vec![],
            }]
        );

        assert!(parse_binary(&[b'a', 2, 0x80, 0, 0]).is_err());
        assert!(parse_binary(&[b'a', 2, 0, 0x80, 0]).is_err());
        assert!(
            parse_binary(&[
                b'a', 2, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 2
            ])
            .is_err()
        );
    }

    #[test]
    fn parses_additions_and_deletions() {
        let instructions = parse_text("3 1 -2 0 1 2 0\n4 d 1 2 0\n5 0 3 4 0\n").expect("parse");
        assert_eq!(
            instructions,
            vec![
                LratInstr::Learn {
                    id: 3,
                    clause: vec![1, -2],
                    hints: vec![1, 2],
                },
                LratInstr::Forget { ids: vec![1, 2] },
                LratInstr::Learn {
                    id: 5,
                    clause: vec![],
                    hints: vec![3, 4],
                },
            ]
        );
        assert!(parse_text("nonsense").is_err());
    }

    #[test]
    fn binary_and_text_agree_on_a_real_proof() {
        // The pigeonhole proof emitted by CaDiCaL in both formats; the
        // binary bytes were captured from a live run.
        let text = "10 -2 0 7 8 2 3 6 0\n11 1 0 10 1 0\n12 -3 0 11 4 0\n\
                    13 -5 0 11 5 0\n14 4 0 12 2 0\n15 6 0 13 3 0\n16 0 14 15 9 0\n";
        let binary: &[u8] = &[
            0x61, 0x14, 0x05, 0x00, 0x0e, 0x10, 0x04, 0x06, 0x0c, 0x00, 0x61, 0x16, 0x02, 0x00,
            0x14, 0x02, 0x00, 0x61, 0x18, 0x07, 0x00, 0x16, 0x08, 0x00, 0x61, 0x1a, 0x0b, 0x00,
            0x16, 0x0a, 0x00, 0x61, 0x1c, 0x08, 0x00, 0x18, 0x04, 0x00, 0x61, 0x1e, 0x0c, 0x00,
            0x1a, 0x06, 0x00, 0x61, 0x20, 0x00, 0x1c, 0x1e, 0x12, 0x00,
        ];
        assert_eq!(
            parse(binary).expect("binary"),
            parse_text(text).expect("text")
        );
    }

    #[test]
    fn the_kernel_learns_only_certified_clauses() {
        let initial = vec![vec![1], vec![-1]];
        let mut kernel = LratKernel::new(&initial);
        assert_eq!(
            kernel.learn(3, &[], &[1, 1]),
            Err(LratError::UselessHint { step: 3, clause: 1 })
        );
        assert!(!kernel.refuted());
        kernel.learn(3, &[], &[1, 2]).expect("refutation");
        assert!(kernel.refuted());
    }

    #[test]
    fn checks_the_unit_contradiction() {
        let initial = vec![vec![1], vec![-1]];
        let instructions = parse_text("3 0 1 2 0\n").expect("parse");
        check(&cnf(initial), &instructions).expect("refutation");
    }

    #[test]
    fn rejects_bogus_hints_and_missing_refutations() {
        let initial = vec![vec![1], vec![-1]];
        assert_eq!(
            check(
                &cnf(initial.clone()),
                &parse_text("3 0 1 1 0\n").expect("parse")
            ),
            Err(LratError::UselessHint { step: 3, clause: 1 })
        );
        // A valid but non-refuting instruction stream is not a refutation.
        assert_eq!(
            check(
                &cnf(initial.clone()),
                &parse_text("3 -1 0 1 0\n").expect("parse")
            ),
            Err(LratError::NoRefutation)
        );
        assert_eq!(check(&cnf(initial), &[]), Err(LratError::NoRefutation));
    }

    #[test]
    fn accepts_rat_steps_with_fresh_variables() {
        // Mirrors the shape CaDiCaL's preprocessing emits: clauses over
        // fresh variable 3 introduced with vacuous/blocked RAT (empty
        // hints, no clause contains -3), then a full RAT step whose
        // resolvents are tautological.
        // The exact shape of CaDiCaL's php5 preprocessing steps
        // (46/47/48 there), relabeled: fresh variable 3 enters through
        // blocked clauses, then the definition's other direction is RAT
        // with tautological resolvents.
        let initial = vec![vec![1, 2], vec![-1, 2]];
        let mut kernel = LratKernel::new(&initial);
        // Blocked: no live clause contains -3.
        kernel.learn(3, &[3, -2], &[]).expect("blocked clause");
        kernel.learn(4, &[3, -1], &[]).expect("blocked clause");
        kernel
            .learn(5, &[-3, 2, 1], &[-3, -4])
            .expect("rat with tautological resolvents");
        // Incomplete coverage is rejected.
        assert_eq!(
            kernel.learn(6, &[-3, -2], &[-3]),
            Err(LratError::IncompleteRat { step: 6, clause: 4 })
        );
        assert_eq!(
            kernel.learn(7, &[-3, 2], &[-3, -3]),
            Err(LratError::DuplicateRatGroup { step: 7, clause: 3 })
        );
    }

    #[test]
    fn checks_a_three_variable_pigeonhole_style_proof() {
        let initial = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
        let instructions = parse_text("5 2 0 3 4 0\n6 -2 0 1 2 0\n7 0 5 6 0\n").expect("parse");
        check(&cnf(initial), &instructions).expect("refutation");
    }

    #[test]
    fn rejects_hostile_inputs_at_each_decode_bound() {
        let tiny = Limits {
            proof_bytes: 16,
            instructions: 1,
            live_clauses: 2,
            terms_per_instruction: 2,
            total_terms: 2,
            work_units: 2,
        };
        assert!(matches!(
            parse_bounded(b"12345678901234567", tiny),
            Err(LratError::Limit {
                resource: "proof bytes",
                ..
            })
        ));
        assert!(matches!(
            parse_bounded(b"3 1 2 3 0 1 0\n", tiny),
            Err(LratError::Limit {
                resource: "terms per instruction",
                ..
            })
        ));
        assert!(matches!(
            parse_bounded(&[b'a', 6, 2, 4, 6, 0, 2, 0], tiny),
            Err(LratError::Limit {
                resource: "terms per instruction",
                ..
            })
        ));
        assert!(parse_text("3 -9223372036854775808 0 1 0\n").is_err());
        assert!(parse_binary(&[b'a', 0]).is_err());
        let hostile = [LratInstr::Learn {
            id: 3,
            clause: vec![i64::MIN],
            hints: vec![1],
        }];
        assert!(matches!(
            check_bounded(&cnf(vec![vec![1]]), &hostile, Limits::default()),
            Err(LratError::Parse { .. })
        ));
        let initial_limit = Limits {
            total_terms: 2,
            ..Limits::default()
        };
        assert!(matches!(
            check_bounded(&cnf(vec![vec![1, 2], vec![3]]), &[], initial_limit),
            Err(LratError::Limit {
                resource: "total terms",
                ..
            })
        ));

        let long_tail = [LratInstr::Learn {
            id: 2,
            clause: Vec::new(),
            hints: vec![1; 100_000],
        }];
        let early_work_limit = Limits {
            terms_per_instruction: 100_000,
            total_terms: 100_001,
            work_units: 1,
            ..Limits::default()
        };
        assert!(matches!(
            check_bounded(&cnf(vec![vec![1]]), &long_tail, early_work_limit),
            Err(LratError::Limit {
                resource: "checker work",
                ..
            })
        ));
    }
}
