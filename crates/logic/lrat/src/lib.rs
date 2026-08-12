//! Parser-independent typed LRAT clause validation.
//!
//! This crate knows nothing about DIMACS, proof bytes, problem identities,
//! snapshots, solvers, or authority. Format and admission layers translate
//! into [`Call`] values and may act only on a successful [`Kernel`] result.

use std::collections::{BTreeMap, BTreeSet};

/// A signed, nonzero propositional literal.
pub type Literal = i64;
/// A disjunction of literals.
pub type Clause = Vec<Literal>;
/// A monotonically allocated clause identifier.
pub type ClauseId = u64;

/// One explicitly delimited RAT resolvent check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RatGroup {
    pub opposing_clause_id: ClauseId,
    pub resolvent_rup_hints: Vec<ClauseId>,
}

/// Parser-independent vocabulary corresponding to `Nucleus.Lrat.ValidatorCall`.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Call {
    /// Introduces both a fresh identifier and the clause justified by RUP.
    /// The clause is data, not metadata: it is not present in the kernel
    /// before this atomic operation.
    LearnRup {
        id: ClauseId,
        clause: Clause,
        ordered_hints: Vec<ClauseId>,
    },
    /// Introduces both a fresh identifier and the clause justified by RAT.
    LearnRat {
        id: ClauseId,
        clause: Clause,
        pivot: Literal,
        prefix_rup_hints: Vec<ClauseId>,
        groups: Vec<RatGroup>,
    },
    Forget {
        ids: Vec<ClauseId>,
    },
}

/// A semantic rejection category. Rejection never changes kernel state.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidLiteral,
    NonFreshId { id: ClauseId },
    UnknownClause { step: ClauseId, clause: ClauseId },
    UselessHint { step: ClauseId, clause: ClauseId },
    NoConflict { step: ClauseId },
    BadPivot { step: ClauseId },
    WrongOpposingClause { step: ClauseId, clause: ClauseId },
    DuplicateRatGroup { step: ClauseId, clause: ClauseId },
    IncompleteRat { step: ClauseId, clause: ClauseId },
    NoRefutation,
}

impl std::fmt::Display for Error {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "typed LRAT rejection: {self:?}")
    }
}

impl std::error::Error for Error {}

/// The standalone clause kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kernel {
    live: BTreeMap<ClauseId, Clause>,
    high_water: ClauseId,
    refuted: bool,
}

impl Kernel {
    /// Opens initial clauses numbered `1..=n`.
    ///
    /// # Errors
    ///
    /// Rejects zero and `i64::MIN`, whose negation is not representable.
    pub fn open(initial: &[Clause]) -> Result<Self, Error> {
        if initial
            .iter()
            .flatten()
            .any(|literal| *literal == 0 || *literal == i64::MIN)
        {
            return Err(Error::InvalidLiteral);
        }
        Ok(Self {
            live: initial
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as ClauseId + 1, clause.clone()))
                .collect(),
            high_water: initial.len() as ClauseId,
            refuted: initial.iter().any(Vec::is_empty),
        })
    }

    #[must_use]
    pub const fn refuted(&self) -> bool {
        self.refuted
    }

    #[must_use]
    pub const fn high_water(&self) -> ClauseId {
        self.high_water
    }

    #[must_use]
    pub fn clause(&self, id: ClauseId) -> Option<&[Literal]> {
        self.live.get(&id).map(Vec::as_slice)
    }

    /// Applies one typed call transactionally.
    ///
    /// # Errors
    ///
    /// Returns a semantic rejection and leaves `self` byte-for-byte equal to
    /// its prior value.
    pub fn apply(&mut self, call: &Call) -> Result<(), Error> {
        match call {
            Call::LearnRup {
                id,
                clause,
                ordered_hints,
            } => self.learn_rup(*id, clause, ordered_hints),
            Call::LearnRat {
                id,
                clause,
                pivot,
                prefix_rup_hints,
                groups,
            } => self.learn_rat(*id, clause, *pivot, prefix_rup_hints, groups),
            Call::Forget { ids } => self.forget(ids),
        }
    }

    /// Learns `clause` under a fresh `id` by ordered reverse unit propagation.
    ///
    /// The clause is required because `id` names no live clause before this
    /// operation. Keeping declaration and validation together makes admission
    /// atomic and prevents an unchecked external clause table from entering
    /// the semantic boundary.
    ///
    /// # Errors
    ///
    /// Returns a semantic rejection and leaves `self` unchanged.
    pub fn learn_rup(
        &mut self,
        id: ClauseId,
        clause: &[Literal],
        ordered_hints: &[ClauseId],
    ) -> Result<(), Error> {
        self.transaction(|candidate| {
            candidate.check_learn(id, clause)?;
            let mut trail = falsifying_trail(clause)?;
            if !candidate.propagate(id, &mut trail, ordered_hints)? {
                return Err(Error::NoConflict { step: id });
            }
            candidate.commit(id, clause);
            Ok(())
        })
    }

    /// Learns `clause` under a fresh `id` by explicit RAT groups.
    ///
    /// # Errors
    ///
    /// Returns a semantic rejection and leaves `self` unchanged.
    pub fn learn_rat(
        &mut self,
        id: ClauseId,
        clause: &[Literal],
        pivot: Literal,
        prefix_rup_hints: &[ClauseId],
        groups: &[RatGroup],
    ) -> Result<(), Error> {
        self.transaction(|candidate| {
            candidate.check_learn(id, clause)?;
            if clause.first() != Some(&pivot) {
                return Err(Error::BadPivot { step: id });
            }
            let mut trail = falsifying_trail(clause)?;
            if candidate.propagate(id, &mut trail, prefix_rup_hints)? {
                candidate.commit(id, clause);
                return Ok(());
            }
            candidate.check_rat(id, pivot, &trail, groups)?;
            candidate.commit(id, clause);
            Ok(())
        })
    }

    /// Deletes live clauses without lowering the identifier high-water mark.
    ///
    /// # Errors
    ///
    /// Unknown or duplicate identifiers reject the entire operation and leave
    /// `self` unchanged.
    pub fn forget(&mut self, ids: &[ClauseId]) -> Result<(), Error> {
        self.transaction(|candidate| {
            let mut seen = BTreeSet::new();
            for id in ids {
                if !seen.insert(*id) || !candidate.live.contains_key(id) {
                    return Err(Error::UnknownClause {
                        step: candidate.high_water,
                        clause: *id,
                    });
                }
            }
            for id in ids {
                candidate.live.remove(id);
            }
            Ok(())
        })
    }

    fn transaction(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let mut candidate = self.clone();
        operation(&mut candidate)?;
        *self = candidate;
        Ok(())
    }

    fn check_learn(&self, id: ClauseId, clause: &[Literal]) -> Result<(), Error> {
        if id <= self.high_water {
            return Err(Error::NonFreshId { id });
        }
        if clause
            .iter()
            .any(|literal| *literal == 0 || *literal == i64::MIN)
        {
            return Err(Error::InvalidLiteral);
        }
        Ok(())
    }

    fn commit(&mut self, id: ClauseId, clause: &[Literal]) {
        self.refuted |= clause.is_empty();
        self.live.insert(id, clause.to_vec());
        self.high_water = id;
    }

    fn propagate(
        &self,
        step: ClauseId,
        trail: &mut BTreeSet<Literal>,
        hints: &[ClauseId],
    ) -> Result<bool, Error> {
        for id in hints {
            let clause = self
                .live
                .get(id)
                .ok_or(Error::UnknownClause { step, clause: *id })?;
            if clause.iter().any(|literal| trail.contains(literal)) {
                return Err(Error::UselessHint { step, clause: *id });
            }
            let mut open = clause.iter().filter(|literal| !trail.contains(&-**literal));
            match (open.next(), open.next()) {
                (None, _) => return Ok(true),
                (Some(unit), None) => {
                    trail.insert(*unit);
                }
                _ => return Err(Error::UselessHint { step, clause: *id }),
            }
        }
        Ok(false)
    }

    fn check_rat(
        &self,
        step: ClauseId,
        pivot: Literal,
        prefix_trail: &BTreeSet<Literal>,
        groups: &[RatGroup],
    ) -> Result<(), Error> {
        let mut covered = BTreeSet::new();
        for group in groups {
            if !covered.insert(group.opposing_clause_id) {
                return Err(Error::DuplicateRatGroup {
                    step,
                    clause: group.opposing_clause_id,
                });
            }
            let opposing =
                self.live
                    .get(&group.opposing_clause_id)
                    .ok_or(Error::UnknownClause {
                        step,
                        clause: group.opposing_clause_id,
                    })?;
            if !opposing.contains(&-pivot) {
                return Err(Error::WrongOpposingClause {
                    step,
                    clause: group.opposing_clause_id,
                });
            }
            let mut trail = prefix_trail.clone();
            let mut tautological = false;
            for literal in opposing.iter().filter(|literal| **literal != -pivot) {
                if trail.contains(literal) {
                    tautological = true;
                    break;
                }
                trail.insert(-*literal);
            }
            if !tautological && !self.propagate(step, &mut trail, &group.resolvent_rup_hints)? {
                return Err(Error::NoConflict { step });
            }
        }
        for (id, clause) in &self.live {
            if clause.contains(&-pivot) && !covered.contains(id) {
                return Err(Error::IncompleteRat { step, clause: *id });
            }
        }
        Ok(())
    }
}

fn falsifying_trail(clause: &[Literal]) -> Result<BTreeSet<Literal>, Error> {
    let mut trail = BTreeSet::new();
    for literal in clause {
        if *literal == 0 || *literal == i64::MIN {
            return Err(Error::InvalidLiteral);
        }
        trail.insert(-*literal);
    }
    Ok(trail)
}

/// Replays a complete typed trace and requires an admitted empty clause.
///
/// # Errors
///
/// Returns the first transactional call rejection or [`Error::NoRefutation`].
pub fn check(initial: &[Clause], calls: &[Call]) -> Result<(), Error> {
    let mut kernel = Kernel::open(initial)?;
    if kernel.refuted() {
        return Ok(());
    }
    for call in calls {
        kernel.apply(call)?;
        if kernel.refuted() {
            return Ok(());
        }
    }
    Err(Error::NoRefutation)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rup_refutes_a_unit_contradiction() {
        let mut kernel = Kernel::open(&[vec![1], vec![-1]]).expect("initial clauses");
        kernel
            .apply(&Call::LearnRup {
                id: 3,
                clause: vec![],
                ordered_hints: vec![1, 2],
            })
            .expect("RUP");
        assert!(kernel.refuted());
    }

    #[test]
    fn every_rejection_is_transactional_and_deletion_keeps_high_water() {
        let mut kernel = Kernel::open(&[vec![1], vec![-1]]).expect("initial clauses");
        let before = kernel.clone();
        assert_eq!(
            kernel.apply(&Call::LearnRup {
                id: 3,
                clause: vec![],
                ordered_hints: vec![99],
            }),
            Err(Error::UnknownClause {
                step: 3,
                clause: 99
            })
        );
        assert_eq!(kernel, before);

        kernel
            .apply(&Call::LearnRup {
                id: 3,
                clause: vec![1],
                ordered_hints: vec![1],
            })
            .expect("learn");
        kernel
            .apply(&Call::Forget { ids: vec![3] })
            .expect("forget");
        assert_eq!(kernel.high_water(), 3);
        assert_eq!(
            kernel.apply(&Call::LearnRup {
                id: 3,
                clause: vec![1],
                ordered_hints: vec![1],
            }),
            Err(Error::NonFreshId { id: 3 })
        );
    }

    #[test]
    fn rat_requires_exact_opposing_coverage() {
        let mut kernel = Kernel::open(&[vec![1, 2], vec![-1, 2]]).expect("initial clauses");
        kernel
            .apply(&Call::LearnRat {
                id: 3,
                clause: vec![3, -2],
                pivot: 3,
                prefix_rup_hints: vec![],
                groups: vec![],
            })
            .expect("blocked clause");
        let before = kernel.clone();
        assert_eq!(
            kernel.apply(&Call::LearnRat {
                id: 4,
                clause: vec![-3, 2],
                pivot: -3,
                prefix_rup_hints: vec![],
                groups: vec![],
            }),
            Err(Error::IncompleteRat { step: 4, clause: 3 })
        );
        assert_eq!(kernel, before);
    }

    #[test]
    fn an_initial_empty_clause_is_already_a_refutation() {
        check(&[vec![]], &[]).expect("initial empty clause");
    }
}
