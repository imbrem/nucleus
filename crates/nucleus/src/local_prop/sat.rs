//! Snapshot-bound adapter from the reusable SAT checker to local facts.

use std::collections::BTreeMap;

use covalence_logic_sat::{
    Cnf, CnfError, CnfLimits, CnfPolicy, Limits, LratError, ModelError, ProblemId, VerifiedModel,
    VerifiedUnsat,
};

use super::{
    CheckerVersion, Error, Fact, Judgement, Literal, LocalPropTable, SnapshotId, has_cycle,
};

/// Versioned lowering from a local implication query to canonical CNF.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LoweringVersion {
    /// Negate the implication and include both directions of every current
    /// local grouped definition.
    LocalDefinitionsImplicationV1,
}

/// Failure while deriving a canonical SAT problem from a local table.
#[derive(Debug)]
pub enum PrepareError {
    /// The local table could not be read or was invalid.
    Table(Error),
    /// The derived matrix violated the requested CNF bounds or policy.
    Cnf(CnfError),
}

impl std::fmt::Display for PrepareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Table(error) => write!(f, "cannot derive SAT problem: {error}"),
            Self::Cnf(error) => write!(f, "derived CNF rejected: {error}"),
        }
    }
}

impl std::error::Error for PrepareError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Table(error) => Some(error),
            Self::Cnf(_) => None,
        }
    }
}

/// A canonical SAT problem for the negation of one local implication.
///
/// The problem is bound to the table snapshot from which its definitional
/// clauses were built. It carries no authority.
#[derive(Clone, Debug)]
pub struct SatProblem {
    snapshot: SnapshotId,
    premise: Literal,
    conclusion: Literal,
    lowering: LoweringVersion,
    cnf: Cnf,
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
        self.cnf.dimacs()
    }

    /// Returns the exact canonical SAT problem identity.
    #[must_use]
    pub const fn id(&self) -> ProblemId {
        self.cnf.id()
    }

    /// Returns the exact proposition-to-CNF lowering profile.
    #[must_use]
    pub const fn lowering(&self) -> LoweringVersion {
        self.lowering
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
        let verdict = self.cnf.verify_binary(proof, limits)?;
        Ok(CheckedRefutation {
            snapshot: self.snapshot,
            premise: self.premise,
            conclusion: self.conclusion,
            lowering: self.lowering,
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
        let model = self.cnf.verify_model(model, max_literals)?;
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
    lowering: LoweringVersion,
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
    /// Returns the exact canonical problem satisfied by this witness.
    #[must_use]
    pub const fn problem(&self) -> ProblemId {
        self.model.problem()
    }

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
        limits: CnfLimits,
        policy: CnfPolicy,
    ) -> Result<SatProblem, PrepareError> {
        if has_cycle(&self.connection).map_err(PrepareError::Table)? {
            return Err(PrepareError::Table(Error::InvalidState));
        }
        let rows = self.connection.query_all(
            "SELECT premise, conclusion FROM prop_row WHERE source=0 AND reason=0 ORDER BY premise, conclusion",
            &[],
            |row| Ok((row.integer(0)?, row.integer(1)?)),
        )
        .map_err(Error::from)
        .map_err(PrepareError::Table)?;
        let mut definitions: BTreeMap<i64, Vec<i64>> = BTreeMap::new();
        for (atom, conjunct) in rows {
            if atom <= 0 || conjunct == 0 || conjunct == i64::MIN {
                return Err(PrepareError::Table(Error::InvalidState));
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
        let cnf = Cnf::new(clauses, limits, policy).map_err(PrepareError::Cnf)?;
        Ok(SatProblem {
            snapshot: self.snapshot(),
            premise,
            conclusion,
            lowering: LoweringVersion::LocalDefinitionsImplicationV1,
            cnf,
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
            lowering,
            verdict,
        } = checked;
        consume_verdict(verdict);
        if snapshot.kernel != self.kernel {
            return Err(Error::ForeignSnapshot);
        }
        if snapshot.generation != self.generation {
            return Err(Error::StaleSnapshot);
        }
        if lowering != LoweringVersion::LocalDefinitionsImplicationV1 {
            return Err(Error::InvalidState);
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
            checker: CheckerVersion::LocalImplicationBinaryLratV1,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::local_prop::{AtomId, Definition};
    use std::collections::BTreeMap;
    use std::fmt::Write;

    fn literal(value: u32) -> Literal {
        Literal::positive(AtomId::new(value).expect("atom"))
    }

    fn fixture_lines() -> impl Iterator<Item = &'static str> {
        include_str!("../../fixtures/local_prop_sat_v1.tsv")
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
    }

    fn signed_literal(value: i64) -> Literal {
        let atom = AtomId::new(u32::try_from(value.unsigned_abs()).expect("fixture atom"))
            .expect("nonzero fixture atom");
        if value < 0 {
            Literal::negative(atom)
        } else {
            Literal::positive(atom)
        }
    }

    fn problem_id_hex(id: ProblemId) -> String {
        id.as_bytes().iter().fold(String::new(), |mut text, byte| {
            write!(text, "{byte:02x}").expect("writing to a string cannot fail");
            text
        })
    }

    fn check_rejection_fixture(rejection: &str) {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let proposition = literal(1);
        let problem = table
            .prepare_sat_refutation(
                proposition,
                proposition,
                CnfLimits::default(),
                CnfPolicy::default(),
            )
            .expect("problem");
        let proof = [b'a', 6, 0, 2, 4, 0];
        match rejection {
            "invalid-lrat" => assert!(
                problem.check_binary_lrat(&[], Limits::default()).is_err(),
                "SAT fixture {rejection}"
            ),
            "foreign-snapshot" => {
                let checked = problem
                    .check_binary_lrat(&proof, Limits::default())
                    .expect("checked proof");
                let mut foreign = LocalPropTable::open_in_memory().expect("foreign table");
                assert!(matches!(
                    foreign.admit_sat_refutation(checked),
                    Err(Error::ForeignSnapshot)
                ));
            }
            "stale-snapshot" => {
                let checked = problem
                    .check_binary_lrat(&proof, Limits::default())
                    .expect("checked proof");
                table
                    .define(
                        Definition::new(AtomId::new(2).expect("atom"), vec![proposition])
                            .expect("definition"),
                    )
                    .expect("define");
                assert!(matches!(
                    table.admit_sat_refutation(checked),
                    Err(Error::StaleSnapshot)
                ));
            }
            other => panic!("unknown SAT rejection fixture: {other}"),
        }
    }

    #[test]
    fn sat_lowering_matches_the_shared_conformance_corpus() {
        let mut definitions = BTreeMap::<String, (u32, Vec<Literal>)>::new();
        let mut problems = BTreeMap::<String, (Literal, Literal, Option<&str>)>::new();
        let mut clauses = BTreeMap::<String, Vec<Vec<i64>>>::new();
        let mut rejections = Vec::new();
        for line in fixture_lines() {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 5, "invalid SAT fixture record: {line}");
            match fields[1] {
                "definition" => {
                    let atom = fields[2].parse().expect("definition atom");
                    let conjuncts = fields[3]
                        .split(',')
                        .map(|value| signed_literal(value.parse().expect("conjunct")))
                        .collect();
                    definitions.insert(fields[0].to_owned(), (atom, conjuncts));
                }
                "problem" => {
                    problems.insert(
                        fields[0].to_owned(),
                        (
                            signed_literal(fields[2].parse().expect("premise")),
                            signed_literal(fields[3].parse().expect("conclusion")),
                            (fields[4] != ".").then_some(fields[4]),
                        ),
                    );
                }
                "clause" => {
                    let clause = if fields[2] == "." {
                        Vec::new()
                    } else {
                        fields[2]
                            .split(',')
                            .map(|value| value.parse().expect("clause literal"))
                            .collect()
                    };
                    clauses
                        .entry(fields[0].to_owned())
                        .or_default()
                        .push(clause);
                }
                "reject" => rejections.push(fields[2]),
                other => panic!("unknown SAT fixture record: {other}"),
            }
        }
        for (name, (premise, conclusion, expected_id)) in problems {
            let mut table = LocalPropTable::open_in_memory().expect("table");
            if let Some((atom, conjuncts)) = definitions.remove(&name) {
                table
                    .define(
                        Definition::new(AtomId::new(atom).expect("atom"), conjuncts)
                            .expect("definition"),
                    )
                    .expect("admit definition");
            }
            let problem = table
                .prepare_sat_refutation(
                    premise,
                    conclusion,
                    CnfLimits::default(),
                    CnfPolicy::default(),
                )
                .expect("prepare problem");
            assert_eq!(problem.cnf.clauses(), clauses[&name], "SAT fixture {name}");
            if let Some(expected_id) = expected_id {
                assert_eq!(
                    problem_id_hex(problem.id()),
                    expected_id,
                    "SAT fixture {name}"
                );
            }
        }
        for rejection in rejections {
            check_rejection_fixture(rejection);
        }
    }

    #[test]
    fn binary_refutation_mints_a_snapshot_bound_fact() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let proposition = literal(1);
        let problem = table
            .prepare_sat_refutation(
                proposition,
                proposition,
                CnfLimits::default(),
                CnfPolicy::default(),
            )
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
        assert_eq!(fact.checker(), CheckerVersion::LocalImplicationBinaryLratV1);
    }

    #[test]
    fn models_remain_non_authoritative_and_snapshot_bound() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let premise = literal(1);
        let conclusion = literal(2);
        let problem = table
            .prepare_sat_refutation(
                premise,
                conclusion,
                CnfLimits::default(),
                CnfPolicy::default(),
            )
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

    #[test]
    fn admission_distinguishes_foreign_and_stale_snapshots() {
        let mut table = LocalPropTable::open_in_memory().expect("table");
        let proposition = literal(1);
        let proof = [b'a', 6, 0, 2, 4, 0];
        let checked = table
            .prepare_sat_refutation(
                proposition,
                proposition,
                CnfLimits::default(),
                CnfPolicy::default(),
            )
            .expect("problem")
            .check_binary_lrat(&proof, Limits::default())
            .expect("checked");
        let mut foreign = LocalPropTable::open_in_memory().expect("foreign table");
        assert!(matches!(
            foreign.admit_sat_refutation(checked),
            Err(Error::ForeignSnapshot)
        ));

        let checked = table
            .prepare_sat_refutation(
                proposition,
                proposition,
                CnfLimits::default(),
                CnfPolicy::default(),
            )
            .expect("problem")
            .check_binary_lrat(&proof, Limits::default())
            .expect("checked");
        table
            .define(Definition::new(AtomId::new(2).expect("atom"), vec![proposition]).expect("def"))
            .expect("define");
        assert!(matches!(
            table.admit_sat_refutation(checked),
            Err(Error::StaleSnapshot)
        ));
    }
}
