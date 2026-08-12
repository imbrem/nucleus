//! Small named SAT problems and checked solver continuation state.

use std::fmt::Write as _;

use covalence_logic_sat::continuation::{
    CheckedResult, Continuation, Error as ContinuationError, JobId, ProofRequest, SolveRequest,
    SolveResult,
};
use covalence_logic_sat::{
    Cnf, CnfError, CnfLimits, CnfPolicy, Limits, ProblemId, binary_lrat_to_text,
};
use covalence_nucleus::local_prop::sat::{PrepareError, SatProblem};
use covalence_nucleus::local_prop::{
    AtomId, Definition, Error as PropError, Fact, Literal, LocalPropTable,
};

/// One reusable, human-sized circuit problem.
pub(crate) struct Demo {
    pub(crate) name: &'static str,
    pub(crate) description: &'static str,
    build: fn() -> Vec<Vec<i64>>,
}

pub(crate) const DEMOS: &[Demo] = &[
    Demo {
        name: "and-sat",
        description: "AND gate: a=b=out=true",
        build: and_sat,
    },
    Demo {
        name: "and-unsat",
        description: "AND gate: a=b=true, out=false",
        build: and_unsat,
    },
    Demo {
        name: "half-adder-sat",
        description: "half adder: 1+1 gives sum=0, carry=1",
        build: half_adder_sat,
    },
    Demo {
        name: "half-adder-unsat",
        description: "half adder: 1+1 cannot give sum=1",
        build: half_adder_unsat,
    },
    Demo {
        name: "full-adder-sat",
        description: "full adder: 1+1+0 gives sum=0, carry=1",
        build: full_adder_sat,
    },
    Demo {
        name: "full-adder-unsat",
        description: "full adder: 1+1+0 cannot give sum=1",
        build: full_adder_unsat,
    },
];

#[derive(Debug)]
pub enum Error {
    UnknownDemo(String),
    NoActive,
    NoPending,
    NoResult,
    NoProof,
    Dimacs(&'static str),
    Cnf(CnfError),
    Prepare(PrepareError),
    Prop(PropError),
    Continuation(ContinuationError),
    VerdictMismatch,
    Image(covalence_neutron::ImageError),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownDemo(name) => write!(f, "no SAT demo {name:?}"),
            Self::NoActive => f.write_str("no SAT problem is selected"),
            Self::NoPending => f.write_str("no SAT solve is pending"),
            Self::NoResult => f.write_str("no checked SAT result is available"),
            Self::NoProof => f.write_str("the checked result has no LRAT certificate"),
            Self::Dimacs(reason) => write!(f, "invalid DIMACS: {reason}"),
            Self::Cnf(error) => error.fmt(f),
            Self::Prepare(error) => error.fmt(f),
            Self::Prop(error) => error.fmt(f),
            Self::Continuation(error) => error.fmt(f),
            Self::VerdictMismatch => {
                f.write_str("checked verdict does not match the active problem")
            }
            Self::Image(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Error {}
impl From<CnfError> for Error {
    fn from(value: CnfError) -> Self {
        Self::Cnf(value)
    }
}
impl From<PrepareError> for Error {
    fn from(value: PrepareError) -> Self {
        Self::Prepare(value)
    }
}
impl From<PropError> for Error {
    fn from(value: PropError) -> Self {
        Self::Prop(value)
    }
}
impl From<ContinuationError> for Error {
    fn from(value: ContinuationError) -> Self {
        Self::Continuation(value)
    }
}
impl From<covalence_neutron::ImageError> for Error {
    fn from(value: covalence_neutron::ImageError) -> Self {
        Self::Image(value)
    }
}

enum Status {
    Empty,
    Operational,
    Pending,
    Rejected(String),
    Checked,
}

struct Active {
    name: String,
    description: String,
    table: LocalPropTable,
    problem: SatProblem,
}

enum Outcome {
    Sat {
        problem: ProblemId,
        model: Box<[i64]>,
    },
    Unsat {
        problem: ProblemId,
        proof: Box<[u8]>,
        fact: Fact,
    },
    Unknown {
        problem: ProblemId,
        reason: Option<String>,
    },
}

pub(crate) struct State {
    active: Option<Active>,
    continuation: Continuation,
    pending: Option<(JobId, SatProblem)>,
    result: Option<Outcome>,
    status: Status,
}

impl State {
    pub(crate) const fn new() -> Self {
        Self {
            active: None,
            continuation: Continuation::new(),
            pending: None,
            result: None,
            status: Status::Empty,
        }
    }

    pub(crate) fn select_demo(&mut self, name: &str) -> Result<(), Error> {
        let demo = DEMOS
            .iter()
            .find(|demo| demo.name == name)
            .ok_or_else(|| Error::UnknownDemo(name.to_owned()))?;
        let cnf = Cnf::new((demo.build)(), limits(), policy())?;
        self.select(name, demo.description, &cnf)
    }

    pub(crate) fn set_dimacs(&mut self, text: &str) -> Result<(), Error> {
        let cnf = parse_dimacs(text)?;
        self.select("custom", "custom canonical DIMACS", &cnf)
    }

    fn select(&mut self, name: &str, description: &str, cnf: &Cnf) -> Result<(), Error> {
        if self.pending.is_some() {
            return Err(Error::Continuation(ContinuationError::Pending));
        }
        let (table, problem) = lower(cnf)?;
        self.active = Some(Active {
            name: name.to_owned(),
            description: description.to_owned(),
            table,
            problem,
        });
        self.result = None;
        self.status = Status::Operational;
        Ok(())
    }

    pub(crate) fn demo_cnf(name: &str) -> Result<Cnf, Error> {
        let demo = DEMOS
            .iter()
            .find(|demo| demo.name == name)
            .ok_or_else(|| Error::UnknownDemo(name.to_owned()))?;
        Ok(Cnf::new((demo.build)(), limits(), policy())?)
    }

    pub(crate) fn active_summary(&self) -> Result<String, Error> {
        let active = self.active.as_ref().ok_or(Error::NoActive)?;
        Ok(format!(
            "{} — {}; problem={}",
            active.name,
            active.description,
            hex(active.problem.id())
        ))
    }

    pub(crate) fn dimacs(&self) -> Result<String, Error> {
        let bytes = self
            .active
            .as_ref()
            .ok_or(Error::NoActive)?
            .problem
            .dimacs();
        String::from_utf8(bytes.to_vec()).map_err(|_| Error::Dimacs("renderer emitted non-UTF-8"))
    }

    pub(crate) fn problem_id(&self) -> Result<String, Error> {
        Ok(hex(self
            .active
            .as_ref()
            .ok_or(Error::NoActive)?
            .problem
            .id()))
    }

    pub(crate) fn begin(&mut self) -> Result<SolveRequest, Error> {
        let active = self.active.as_ref().ok_or(Error::NoActive)?;
        let retained = active.problem.clone();
        let request = self.continuation.begin(
            retained.canonical_cnf(),
            1024,
            Limits::default(),
            ProofRequest::default(),
        )?;
        self.pending = Some((request.job(), retained));
        self.result = None;
        self.status = Status::Pending;
        Ok(request)
    }

    pub(crate) fn complete(&mut self, job: JobId, raw: SolveResult) -> Result<(), Error> {
        let (expected_job, pending) = self.pending.as_ref().ok_or(Error::NoPending)?;
        if *expected_job != job || pending.id() != raw.problem() {
            self.continuation.complete(job, raw)?;
            unreachable!("mismatched SAT completion was accepted")
        }
        let raw_proof = match &raw {
            SolveResult::Unsat { proof, .. } => Some(proof.clone()),
            _ => None,
        };
        let checked = self.continuation.complete(job, raw);
        let (_, pending) = self.pending.take().ok_or(Error::NoPending)?;
        let checked = match checked {
            Ok(checked) => checked,
            Err(error) => {
                self.status = Status::Rejected(error.to_string());
                return Err(error.into());
            }
        };
        self.result = Some(match checked {
            CheckedResult::Sat(model) => Outcome::Sat {
                problem: model.problem(),
                model: model.literals().into(),
            },
            CheckedResult::Unsat(verdict) => {
                let problem = verdict.problem();
                let checked = pending
                    .bind_verified_unsat(verdict)
                    .map_err(|_| Error::VerdictMismatch)?;
                let active = self.active.as_mut().ok_or(Error::NoActive)?;
                let fact = active.table.admit_sat_refutation(checked)?;
                Outcome::Unsat {
                    problem,
                    proof: raw_proof.ok_or(Error::NoProof)?,
                    fact,
                }
            }
            CheckedResult::Unknown { reason } => Outcome::Unknown {
                problem: pending.id(),
                reason,
            },
        });
        self.status = Status::Checked;
        Ok(())
    }

    pub(crate) fn cancel(&mut self) -> Result<(), Error> {
        let (job, _) = self.pending.as_ref().ok_or(Error::NoPending)?;
        self.continuation.cancel(*job)?;
        self.pending = None;
        self.status = Status::Operational;
        Ok(())
    }

    pub(crate) fn reject_provider(&mut self, reason: &str) -> Result<(), Error> {
        let (job, _) = self.pending.as_ref().ok_or(Error::NoPending)?;
        self.continuation.cancel(*job)?;
        self.pending = None;
        self.status = Status::Rejected(reason.to_owned());
        Ok(())
    }

    pub(crate) fn status(&self) -> String {
        match &self.status {
            Status::Empty => "empty".to_owned(),
            Status::Operational => "operational".to_owned(),
            Status::Pending => "pending".to_owned(),
            Status::Rejected(reason) => format!("rejected; reason={reason}"),
            Status::Checked => "checked".to_owned(),
        }
    }

    pub(crate) fn sqlite_image(&self) -> Result<Vec<u8>, Error> {
        Ok(self
            .active
            .as_ref()
            .ok_or(Error::NoActive)?
            .table
            .serialize()?
            .to_vec())
    }

    pub(crate) fn result_summary(&self) -> Result<String, Error> {
        Ok(match self.result.as_ref().ok_or(Error::NoResult)? {
            Outcome::Sat { problem, model } => format!(
                "sat; checked-model; problem={}; literals={}",
                hex(*problem),
                model.len()
            ),
            Outcome::Unsat {
                problem,
                proof,
                fact,
            } => format!(
                "unsat; admitted={:?}; checker={:?}; problem={}; binary-lrat-bytes={}",
                fact.judgement(),
                fact.checker(),
                hex(*problem),
                proof.len()
            ),
            Outcome::Unknown { problem, reason } => format!(
                "unknown; problem={}; reason={}",
                hex(*problem),
                reason.as_deref().unwrap_or("none")
            ),
        })
    }

    pub(crate) fn model(&self) -> Result<String, Error> {
        let Outcome::Sat { model, .. } = self.result.as_ref().ok_or(Error::NoResult)? else {
            return Err(Error::NoResult);
        };
        Ok(model
            .iter()
            .map(i64::to_string)
            .collect::<Vec<_>>()
            .join(" "))
    }

    pub(crate) fn proof_metadata(&self) -> Result<String, Error> {
        let Outcome::Unsat {
            problem,
            proof,
            fact,
        } = self.result.as_ref().ok_or(Error::NoResult)?
        else {
            return Err(Error::NoProof);
        };
        Ok(format!(
            "binary-lrat; bytes={}; problem={}; judgement={:?}; checker={:?}",
            proof.len(),
            hex(*problem),
            fact.judgement(),
            fact.checker()
        ))
    }

    pub(crate) fn proof_text(&self) -> Result<String, Error> {
        let Outcome::Unsat { proof, .. } = self.result.as_ref().ok_or(Error::NoResult)? else {
            return Err(Error::NoProof);
        };
        binary_lrat_to_text(proof, Limits::default())
            .map_err(|error| Error::Continuation(ContinuationError::Lrat(error)))
    }
}

fn lower(cnf: &Cnf) -> Result<(LocalPropTable, SatProblem), Error> {
    let mut table = LocalPropTable::open_in_memory()?;
    let max = cnf
        .clauses()
        .iter()
        .flatten()
        .map(|literal| literal.unsigned_abs())
        .max()
        .unwrap_or(0);
    let mut next = u32::try_from(max)
        .map_err(|_| Error::Dimacs("variable is too large"))?
        .checked_add(1)
        .ok_or(Error::Dimacs("atom space exhausted"))?;
    let mut clauses = Vec::with_capacity(cnf.clauses().len());
    for clause in cnf.clauses() {
        let atom = AtomId::new(next).ok_or(Error::Dimacs("atom space exhausted"))?;
        next = next
            .checked_add(1)
            .ok_or(Error::Dimacs("atom space exhausted"))?;
        let conjuncts = clause
            .iter()
            .map(|literal| decode_literal(*literal).map(Literal::complement))
            .collect::<Result<Vec<_>, _>>()?;
        table.define(Definition::new(atom, conjuncts)?)?;
        clauses.push(Literal::negative(atom));
    }
    let formula = AtomId::new(next).ok_or(Error::Dimacs("atom space exhausted"))?;
    table.define(Definition::new(formula, clauses)?)?;
    let literal = Literal::positive(formula);
    let problem =
        table.prepare_sat_refutation(literal, literal.complement(), limits(), policy())?;
    Ok((table, problem))
}

fn decode_literal(literal: i64) -> Result<Literal, Error> {
    let atom = u32::try_from(literal.unsigned_abs())
        .ok()
        .and_then(AtomId::new)
        .ok_or(Error::Dimacs("variable is too large"))?;
    Ok(if literal < 0 {
        Literal::negative(atom)
    } else {
        Literal::positive(atom)
    })
}

fn limits() -> CnfLimits {
    CnfLimits::default()
}

fn policy() -> CnfPolicy {
    CnfPolicy::default()
}

fn parse_dimacs(text: &str) -> Result<Cnf, Error> {
    if text.len() > 16 * 1024 * 1024 {
        return Err(Error::Dimacs("input is too large"));
    }
    let mut header = None;
    let mut values = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            if header.is_some() {
                return Err(Error::Dimacs("repeated header"));
            }
            let fields = line.split_ascii_whitespace().collect::<Vec<_>>();
            if fields.len() != 4 || fields[0] != "p" || fields[1] != "cnf" {
                return Err(Error::Dimacs("expected `p cnf VARIABLES CLAUSES`"));
            }
            header = Some((
                fields[2]
                    .parse::<u64>()
                    .map_err(|_| Error::Dimacs("bad variable count"))?,
                fields[3]
                    .parse::<usize>()
                    .map_err(|_| Error::Dimacs("bad clause count"))?,
            ));
        } else {
            if header.is_none() {
                return Err(Error::Dimacs("clauses precede header"));
            }
            for token in line.split_ascii_whitespace() {
                values.push(
                    token
                        .parse::<i64>()
                        .map_err(|_| Error::Dimacs("bad literal"))?,
                );
            }
        }
    }
    let (variables, expected) = header.ok_or(Error::Dimacs("missing header"))?;
    let mut clauses = Vec::new();
    let mut clause = Vec::new();
    for value in values {
        if value == 0 {
            clauses.push(std::mem::take(&mut clause));
        } else {
            if value == i64::MIN || value.unsigned_abs() > variables {
                return Err(Error::Dimacs("literal exceeds header"));
            }
            clause.push(value);
        }
    }
    if !clause.is_empty() {
        return Err(Error::Dimacs("unterminated clause"));
    }
    if clauses.len() != expected {
        return Err(Error::Dimacs("clause count differs from header"));
    }
    if clauses.is_empty() || clauses.iter().any(Vec::is_empty) {
        return Err(Error::Dimacs(
            "empty formulas and clauses are not supported by this demo",
        ));
    }
    let cnf = Cnf::new(clauses, limits(), policy())?;
    if cnf.clauses().is_empty() {
        return Err(Error::Dimacs("problem has no effective clauses"));
    }
    Ok(cnf)
}

fn and_gate() -> Vec<Vec<i64>> {
    vec![vec![-1, -2, 3], vec![1, -3], vec![2, -3]]
}
fn and_sat() -> Vec<Vec<i64>> {
    let mut c = and_gate();
    c.extend([vec![1], vec![2], vec![3]]);
    c
}
fn and_unsat() -> Vec<Vec<i64>> {
    let mut c = and_gate();
    c.extend([vec![1], vec![2], vec![-3]]);
    c
}

fn half_adder() -> Vec<Vec<i64>> {
    vec![
        vec![1, 2, -3],
        vec![-1, -2, -3],
        vec![-1, 2, 3],
        vec![1, -2, 3],
        vec![-1, -2, 4],
        vec![1, -4],
        vec![2, -4],
    ]
}
fn half_adder_sat() -> Vec<Vec<i64>> {
    let mut c = half_adder();
    c.extend([vec![1], vec![2], vec![-3], vec![4]]);
    c
}
fn half_adder_unsat() -> Vec<Vec<i64>> {
    let mut c = half_adder();
    c.extend([vec![1], vec![2], vec![3]]);
    c
}

fn full_adder() -> Vec<Vec<i64>> {
    let mut clauses = Vec::new();
    for bits in 0_u8..8 {
        let a = bits & 1 != 0;
        let b = bits & 2 != 0;
        let carry_in = bits & 4 != 0;
        let inputs = [(1, a), (2, b), (3, carry_in)];
        let mut prefix = inputs
            .map(|(variable, value)| if value { -variable } else { variable })
            .to_vec();
        let sum = a ^ b ^ carry_in;
        let carry = (u8::from(a) + u8::from(b) + u8::from(carry_in)) >= 2;
        let mut sum_clause = prefix.clone();
        sum_clause.push(if sum { 4 } else { -4 });
        clauses.push(sum_clause);
        prefix.push(if carry { 5 } else { -5 });
        clauses.push(prefix);
    }
    clauses
}
fn full_adder_sat() -> Vec<Vec<i64>> {
    let mut c = full_adder();
    c.extend([vec![1], vec![2], vec![-3], vec![-4], vec![5]]);
    c
}
fn full_adder_unsat() -> Vec<Vec<i64>> {
    let mut c = full_adder();
    c.extend([vec![1], vec![2], vec![-3], vec![4]]);
    c
}

pub(crate) fn hex(problem: ProblemId) -> String {
    problem
        .as_bytes()
        .iter()
        .fold(String::new(), |mut text, byte| {
            write!(text, "{byte:02x}").expect("writing to String cannot fail");
            text
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn satisfiable(clauses: &[Vec<i64>]) -> bool {
        let variables = clauses
            .iter()
            .flatten()
            .map(|literal| usize::try_from(literal.unsigned_abs()).expect("small fixture variable"))
            .max()
            .unwrap_or(0);
        (0_u64..(1_u64 << variables)).any(|assignment| {
            clauses.iter().all(|clause| {
                clause.iter().any(|literal| {
                    let bit = 1_u64 << (literal.unsigned_abs() - 1);
                    let value = assignment & bit != 0;
                    value == (*literal > 0)
                })
            })
        })
    }

    #[test]
    fn every_circuit_has_a_sat_and_unsat_sibling() {
        for (sat, unsat) in [
            ("and-sat", "and-unsat"),
            ("half-adder-sat", "half-adder-unsat"),
            ("full-adder-sat", "full-adder-unsat"),
        ] {
            let sat = State::demo_cnf(sat).expect("SAT sibling");
            let unsat = State::demo_cnf(unsat).expect("UNSAT sibling");
            assert!(satisfiable(sat.clauses()), "expected SAT: {sat:?}");
            assert!(!satisfiable(unsat.clauses()), "expected UNSAT: {unsat:?}");
        }
    }

    #[test]
    fn canonical_problem_identity_ignores_input_order() {
        let original = State::demo_cnf("and-sat").expect("demo");
        let mut reversed = and_sat();
        reversed.reverse();
        for clause in &mut reversed {
            clause.reverse();
        }
        let reversed = Cnf::new(reversed, limits(), policy()).expect("reordered");
        assert_eq!(original.id(), reversed.id());
        assert_eq!(original.dimacs(), reversed.dimacs());
    }
}
