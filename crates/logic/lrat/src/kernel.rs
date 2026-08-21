//! Parser-independent typed LRAT clause validation.
//!
//! This crate knows nothing about DIMACS, proof bytes, problem identities,
//! snapshots, solvers, or authority. Format and admission layers call the
//! narrow [`Kernel`] operations and may act only on successful results.

use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{self, Snafu};
use covalence_logic_sat::cnf::{Clause, Formula, Literal};

/// A monotonically allocated clause identifier.
pub type ClauseId = u64;

/// One explicitly delimited RAT resolvent check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RatGroup {
    pub opposing_clause_id: ClauseId,
    pub resolvent_rup_hints: Vec<ClauseId>,
}

/// A semantic rejection category. Rejection never changes kernel state.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum Error {
    /// The identifier is not above the high-water mark, so it names a clause
    /// the kernel has already allocated.
    #[snafu(display("clause identifier {id} is not fresh"))]
    NonFreshId { id: ClauseId },
    /// A hint or RAT group named an identifier with no live clause.
    #[snafu(display("step {step} names clause {clause}, which is not live"))]
    UnknownClause { step: ClauseId, clause: ClauseId },
    /// A hint neither closed the trail nor extended it by exactly one unit.
    #[snafu(display("hint {clause} in step {step} is not unit under the trail"))]
    UselessHint { step: ClauseId, clause: ClauseId },
    /// Reverse unit propagation ran out of hints without reaching a conflict.
    #[snafu(display("step {step} does not propagate to a conflict"))]
    NoConflict { step: ClauseId },
    /// The declared pivot is not the clause's first literal.
    #[snafu(display("step {step} does not begin with its declared pivot"))]
    BadPivot { step: ClauseId },
    /// A RAT group named a clause not containing the negated pivot.
    #[snafu(display("clause {clause} in step {step} does not contain the negated pivot"))]
    WrongOpposingClause { step: ClauseId, clause: ClauseId },
    /// Two RAT groups in one step named the same opposing clause.
    #[snafu(display("step {step} gives more than one RAT group for clause {clause}"))]
    DuplicateRatGroup { step: ClauseId, clause: ClauseId },
    /// A live clause containing the negated pivot has no RAT group.
    #[snafu(display("step {step} gives no RAT group for clause {clause}"))]
    IncompleteRat { step: ClauseId, clause: ClauseId },
    /// The proof ended without deriving the empty clause.
    #[snafu(display("the proof does not derive the empty clause"))]
    NoRefutation,
}

/// The standalone clause kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kernel {
    live: BTreeMap<ClauseId, Clause>,
    high_water: ClauseId,
    refuted: bool,
}

impl Kernel {
    /// Opens a CNF formula with initial clauses numbered `1..=n`.
    #[must_use]
    pub fn open(initial: &Formula) -> Self {
        Self {
            live: initial
                .clauses()
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as ClauseId + 1, clause.clone()))
                .collect(),
            high_water: initial.len() as ClauseId,
            refuted: initial.clauses().iter().any(Clause::is_empty),
        }
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
    pub fn clause(&self, id: ClauseId) -> Option<&Clause> {
        self.live.get(&id)
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
        clause: &Clause,
        ordered_hints: &[ClauseId],
    ) -> Result<(), Error> {
        self.transaction(|candidate| {
            candidate.check_learn(id, clause)?;
            let mut trail = falsifying_trail(clause);
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
        clause: &Clause,
        pivot: Literal,
        prefix_rup_hints: &[ClauseId],
        groups: &[RatGroup],
    ) -> Result<(), Error> {
        self.transaction(|candidate| {
            candidate.check_learn(id, clause)?;
            if clause.first() != Some(pivot) {
                return Err(Error::BadPivot { step: id });
            }
            let mut trail = falsifying_trail(clause);
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

    fn check_learn(&self, id: ClauseId, _clause: &Clause) -> Result<(), Error> {
        if id <= self.high_water {
            return Err(Error::NonFreshId { id });
        }
        Ok(())
    }

    fn commit(&mut self, id: ClauseId, clause: &Clause) {
        self.refuted |= clause.is_empty();
        self.live.insert(id, clause.clone());
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
            if clause.iter().any(|literal| trail.contains(&literal)) {
                return Err(Error::UselessHint { step, clause: *id });
            }
            let mut open = clause.iter().filter(|literal| !trail.contains(&-*literal));
            match (open.next(), open.next()) {
                (None, _) => return Ok(true),
                (Some(unit), None) => {
                    trail.insert(unit);
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
            if !opposing.contains(-pivot) {
                return Err(Error::WrongOpposingClause {
                    step,
                    clause: group.opposing_clause_id,
                });
            }
            let mut trail = prefix_trail.clone();
            let mut tautological = false;
            for literal in opposing.iter().filter(|literal| *literal != -pivot) {
                if trail.contains(&literal) {
                    tautological = true;
                    break;
                }
                trail.insert(-literal);
            }
            if !tautological && !self.propagate(step, &mut trail, &group.resolvent_rup_hints)? {
                return Err(Error::NoConflict { step });
            }
        }
        for (id, clause) in &self.live {
            if clause.contains(-pivot) && !covered.contains(id) {
                return Err(Error::IncompleteRat { step, clause: *id });
            }
        }
        Ok(())
    }
}

fn falsifying_trail(clause: &Clause) -> BTreeSet<Literal> {
    clause.iter().map(std::ops::Neg::neg).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(literals: impl IntoIterator<Item = i64>) -> Clause {
        Clause::from_signed(literals).unwrap()
    }

    fn kernel(clauses: impl IntoIterator<Item = Vec<i64>>) -> Kernel {
        Kernel::open(&Formula::from_signed(clauses).unwrap())
    }

    #[test]
    fn rup_refutes_a_unit_contradiction() {
        let mut kernel = kernel([vec![1], vec![-1]]);
        kernel.learn_rup(3, &clause([]), &[1, 2]).expect("RUP");
        assert!(kernel.refuted());
    }

    #[test]
    fn every_rejection_is_transactional_and_deletion_keeps_high_water() {
        let mut kernel = kernel([vec![1], vec![-1]]);
        let before = kernel.clone();
        assert_eq!(
            kernel.learn_rup(3, &clause([]), &[99]),
            Err(Error::UnknownClause {
                step: 3,
                clause: 99
            })
        );
        assert_eq!(kernel, before);

        kernel.learn_rup(3, &clause([1]), &[1]).expect("learn");
        kernel.forget(&[3]).expect("forget");
        assert_eq!(kernel.high_water(), 3);
        assert_eq!(
            kernel.learn_rup(3, &clause([1]), &[1]),
            Err(Error::NonFreshId { id: 3 })
        );
    }

    #[test]
    fn rat_requires_exact_opposing_coverage() {
        let mut kernel = kernel([vec![1, 2], vec![-1, 2]]);
        kernel
            .learn_rat(3, &clause([3, -2]), Literal::new(3).unwrap(), &[], &[])
            .expect("blocked clause");
        let before = kernel.clone();
        assert_eq!(
            kernel.learn_rat(4, &clause([-3, 2]), Literal::new(-3).unwrap(), &[], &[],),
            Err(Error::IncompleteRat { step: 4, clause: 3 })
        );
        assert_eq!(kernel, before);
    }
}
