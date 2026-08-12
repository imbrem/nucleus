//! Snapshot-bound adapter from the reusable SAT checker to local facts.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use covalence_logic_sat::{Limits, LratError, ModelError, VerifiedModel, VerifiedUnsat};

use super::{
    CheckerVersion, Error, Fact, Judgement, Literal, LocalPropTable, SnapshotId, has_cycle,
};

/// A canonical SAT problem for the negation of one local implication.
///
/// The problem is bound to the table snapshot from which its definitional
/// clauses were built. It carries no authority.
#[derive(Clone, Debug)]
pub struct SatProblem {
    snapshot: SnapshotId,
    premise: Literal,
    conclusion: Literal,
    clauses: Box<[Vec<i64>]>,
    dimacs: Box<[u8]>,
}

impl SatProblem {
    /// Returns the snapshot from which the problem was derived.
    #[must_use]
    pub const fn snapshot(&self) -> SnapshotId {
        self.snapshot
    }

    /// Returns canonical DIMACS for an untrusted solver.
    #[must_use]
    pub fn dimacs(&self) -> &[u8] {
        &self.dimacs
    }

    /// Checks the solver's binary LRAT response.
    ///
    /// # Errors
    ///
    /// Rejects malformed, oversized, or invalid proofs.
    pub fn check_binary_lrat(
        self,
        proof: &[u8],
        limits: Limits,
    ) -> Result<CheckedRefutation, LratError> {
        let verdict = covalence_logic_sat::verify_binary(&self.clauses, proof, limits)?;
        Ok(CheckedRefutation {
            snapshot: self.snapshot,
            premise: self.premise,
            conclusion: self.conclusion,
            verdict,
        })
    }

    /// Checks a solver model without admitting anything to the table.
    ///
    /// # Errors
    ///
    /// Rejects malformed, partial, unrelated, or non-satisfying assignments.
    pub fn check_model(
        self,
        model: &[i64],
        max_literals: usize,
    ) -> Result<ModelWitness, ModelError> {
        let model = covalence_logic_sat::verify_model(&self.clauses, model, max_literals)?;
        Ok(ModelWitness {
            snapshot: self.snapshot,
            premise: self.premise,
            conclusion: self.conclusion,
            model,
        })
    }
}

/// A checked refutation awaiting snapshot validation and atomic admission.
pub struct CheckedRefutation {
    snapshot: SnapshotId,
    premise: Literal,
    conclusion: Literal,
    verdict: VerifiedUnsat,
}

fn consume_verdict(_verdict: VerifiedUnsat) {}

/// A checked satisfying assignment for one snapshot-bound problem.
///
/// This is deliberately not a [`Fact`] and is never stored as authority.
#[derive(Clone, Debug)]
pub struct ModelWitness {
    snapshot: SnapshotId,
    premise: Literal,
    conclusion: Literal,
    model: VerifiedModel,
}

impl ModelWitness {
    /// Returns the snapshot whose problem was satisfied.
    #[must_use]
    pub const fn snapshot(&self) -> SnapshotId {
        self.snapshot
    }

    /// Returns the implication premise whose negation was satisfied.
    #[must_use]
    pub const fn premise(&self) -> Literal {
        self.premise
    }

    /// Returns the implication conclusion whose negation was satisfied.
    #[must_use]
    pub const fn conclusion(&self) -> Literal {
        self.conclusion
    }

    /// Returns the checked DIMACS assignment.
    #[must_use]
    pub fn literals(&self) -> &[i64] {
        self.model.literals()
    }
}

impl LocalPropTable {
    /// Builds the canonical negation of `premise => conclusion` at the
    /// current snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error when stored definitions are invalid or unreadable.
    pub fn prepare_sat_refutation(
        &self,
        premise: Literal,
        conclusion: Literal,
    ) -> Result<SatProblem, Error> {
        if has_cycle(&self.connection)? {
            return Err(Error::InvalidState);
        }
        let rows = self.connection.query_all(
            "SELECT premise, conclusion FROM prop_row WHERE source=0 AND reason=0 ORDER BY premise, conclusion",
            &[],
            |row| Ok((row.integer(0)?, row.integer(1)?)),
        )?;
        let mut definitions: BTreeMap<i64, Vec<i64>> = BTreeMap::new();
        for (atom, conjunct) in rows {
            if atom <= 0 || conjunct == 0 || conjunct == i64::MIN {
                return Err(Error::InvalidState);
            }
            definitions.entry(atom).or_default().push(conjunct);
        }
        let mut clauses = vec![vec![premise.encoded()], vec![-conclusion.encoded()]];
        for (atom, conjuncts) in definitions {
            for &conjunct in &conjuncts {
                clauses.push(vec![-atom, conjunct]);
            }
            let mut introduction = Vec::with_capacity(conjuncts.len() + 1);
            introduction.push(atom);
            introduction.extend(conjuncts.into_iter().map(|conjunct| -conjunct));
            clauses.push(introduction);
        }
        let max_variable = clauses
            .iter()
            .flatten()
            .map(|literal| literal.unsigned_abs())
            .max()
            .unwrap_or(0);
        let mut dimacs = String::new();
        writeln!(dimacs, "p cnf {max_variable} {}", clauses.len())
            .expect("writing to a String cannot fail");
        for clause in &clauses {
            for literal in clause {
                write!(dimacs, "{literal} ").expect("writing to a String cannot fail");
            }
            dimacs.push_str("0\n");
        }
        Ok(SatProblem {
            snapshot: self.snapshot(),
            premise,
            conclusion,
            clauses: clauses.into_boxed_slice(),
            dimacs: dimacs.into_bytes().into_boxed_slice(),
        })
    }

    /// Atomically admits one snapshot-current checked refutation as a fact.
    ///
    /// Proof bytes and solver claims cannot enter through this method: only a
    /// private-field verdict minted by [`SatProblem::check_binary_lrat`] can.
    ///
    /// # Errors
    ///
    /// Rejects stale snapshots or conflicting/unstoreable theorem rows.
    #[expect(
        clippy::needless_pass_by_value,
        reason = "consumption makes each checked admission attempt explicit"
    )]
    pub fn admit_sat_refutation(&mut self, checked: CheckedRefutation) -> Result<Fact, Error> {
        let CheckedRefutation {
            snapshot,
            premise,
            conclusion,
            verdict,
        } = checked;
        consume_verdict(verdict);
        if !self.is_current(snapshot) {
            return Err(Error::StaleSnapshot);
        }
        self.insert_proved(premise, conclusion)?;
        Ok(Fact {
            premise,
            conclusion,
            kernel: self.kernel,
            generation: self.generation,
            source: super::SourceId::LOCAL,
            context: super::ContextId::EMPTY,
            judgement: Judgement::SatRefutation,
            checker: CheckerVersion::BinaryLratV1,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::local_prop::{AtomId, Definition};

    fn literal(value: u32) -> Literal {
        Literal::positive(AtomId::new(value).expect("atom"))
    }

    #[test]
    fn binary_refutation_mints_a_snapshot_bound_fact() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let proposition = literal(1);
        let problem = table
            .prepare_sat_refutation(proposition, proposition)
            .expect("problem");
        assert!(
            std::str::from_utf8(problem.dimacs())
                .expect("DIMACS")
                .starts_with("p cnf 1 2\n")
        );
        // Step 3 derives the empty clause from initial unit clauses 1 and 2.
        let proof = [b'a', 6, 0, 2, 4, 0];
        let checked = problem
            .check_binary_lrat(&proof, Limits::default())
            .expect("checked refutation");
        let fact = table.admit_sat_refutation(checked).expect("admitted fact");
        assert_eq!(fact.premise(), proposition);
        assert_eq!(fact.conclusion(), proposition);
        assert_eq!(fact.judgement(), Judgement::SatRefutation);
        assert_eq!(fact.checker(), CheckerVersion::BinaryLratV1);
    }

    #[test]
    fn models_remain_non_authoritative_and_snapshot_bound() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let premise = literal(1);
        let conclusion = literal(2);
        let problem = table
            .prepare_sat_refutation(premise, conclusion)
            .expect("problem");
        let witness = problem.check_model(&[1, -2], 2).expect("model");
        assert_eq!(witness.literals(), &[1, -2]);
        assert!(table.is_current(witness.snapshot()));

        table
            .define(Definition::new(AtomId::new(3).expect("atom"), vec![premise]).expect("def"))
            .expect("define");
        // New definitions change the lowering and must obsolete old witnesses.
        assert!(!table.is_current(witness.snapshot()));
    }
}
