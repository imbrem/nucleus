//! Bounded DIMACS problems for the REPL.

use std::collections::BTreeSet;
use std::sync::Arc;

use covalence_lib_hash::O256;
use covalence_nucleus::Connection;
use covalence_nucleus::prop::{AllowAll, CnfLimits, Lit, PreparedSat, Prop, PropId, lrat};

const MAX_BYTES: usize = 1024 * 1024;
const MAX_VARIABLES: usize = 100_000;
const MAX_CLAUSES: usize = 200_000;
const MAX_LITERALS: usize = 1_000_000;
const MAX_SOURCE_BYTES: usize = 4_096;

/// A built-in SAT problem.
pub struct SatDemo {
    pub name: &'static str,
    pub expected: &'static str,
    pub description: &'static str,
    pub dimacs: &'static str,
}

pub const SAT_DEMOS: &[SatDemo] = &[
    SatDemo {
        name: "and-sat",
        expected: "sat",
        description: "AND gate with its output true",
        dimacs: include_str!("../samples/sat/and-sat.cnf"),
    },
    SatDemo {
        name: "and-unsat",
        expected: "unsat",
        description: "AND output true with one input false",
        dimacs: include_str!("../samples/sat/and-unsat.cnf"),
    },
    SatDemo {
        name: "half-adder-sat",
        expected: "sat",
        description: "one plus one has sum zero and carry one",
        dimacs: include_str!("../samples/sat/half-adder-sat.cnf"),
    },
    SatDemo {
        name: "half-adder-unsat",
        expected: "unsat",
        description: "one plus one cannot have sum one",
        dimacs: include_str!("../samples/sat/half-adder-unsat.cnf"),
    },
];

/// One selected, canonical problem and its trusted encoding.
pub(crate) struct SatProblem {
    pub source: String,
    pub expected: Option<&'static str>,
    pub variables: usize,
    pub clauses: usize,
    pub dimacs: Vec<u8>,
    pub identity: O256,
    connection: Arc<Connection<Prop<AllowAll>>>,
    formula: PropId,
    clause_ids: Vec<PropId>,
    model_literals: usize,
}

impl SatProblem {
    pub fn parse(
        bytes: &[u8],
        source: String,
        expected: Option<&'static str>,
    ) -> Result<Self, String> {
        if source.len() > MAX_SOURCE_BYTES {
            return Err("SAT source exceeds 4096 UTF-8 bytes".to_owned());
        }
        let (variables, mut matrix) = parse_dimacs(bytes)?;
        let clauses = matrix.len();

        // The prop kernel has no empty conjunction. Encode DIMACS constants
        // with one fresh variable, which is hidden by the problem metadata.
        // Reserve an id outside the accepted DIMACS range so a constant's
        // canonical identity cannot collide with a caller-visible variable.
        let constant = MAX_VARIABLES + 1;
        if matrix.is_empty() {
            matrix.push(vec![i64::try_from(constant).map_err(|_| {
                "DIMACS encoding exceeds propositional identifiers".to_owned()
            })?]);
        } else if matrix.iter().any(Vec::is_empty) {
            let literal = i64::try_from(constant)
                .map_err(|_| "DIMACS encoding exceeds propositional identifiers".to_owned())?;
            matrix = vec![vec![literal], vec![-literal]];
        }
        let used: BTreeSet<_> = matrix
            .iter()
            .flatten()
            .map(|literal| literal.unsigned_abs())
            .collect();

        let connection = Arc::new(
            Connection::<Prop<AllowAll>>::open_prop_in_memory(AllowAll)
                .map_err(|error| error.to_string())?,
        );
        let view = connection.view();
        for &variable in &used {
            let variable =
                usize::try_from(variable).map_err(|_| "DIMACS literal is too large".to_owned())?;
            view.declare_free(prop_id(variable)?)
                .map_err(|error| error.to_string())?;
        }
        let variable_ceiling = used
            .last()
            .copied()
            .map(usize::try_from)
            .transpose()
            .map_err(|_| "DIMACS literal is too large".to_owned())?
            .unwrap_or(0);
        let mut clause_ids = Vec::with_capacity(matrix.len());
        for (index, row) in matrix.iter().enumerate() {
            let id = prop_id(variable_ceiling + index + 1)?;
            let negated = row
                .iter()
                .map(|literal| {
                    Lit::new(-literal).ok_or_else(|| "invalid DIMACS literal".to_owned())
                })
                .collect::<Result<Vec<_>, _>>()?;
            view.define(id, &negated)
                .map_err(|error| error.to_string())?;
            clause_ids.push(id);
        }
        let formula = prop_id(variable_ceiling + matrix.len() + 1)?;
        let conjuncts = clause_ids.iter().map(|id| id.negated()).collect::<Vec<_>>();
        view.define(formula, &conjuncts)
            .map_err(|error| error.to_string())?;
        let prepared = connection
            .prepare_sat(
                formula,
                &clause_ids,
                CnfLimits::default(),
                used.len(),
                lrat::Limits::default(),
            )
            .map_err(|error| error.to_string())?;
        let identity = prepared.id();
        let dimacs = prepared.dimacs().to_vec();

        Ok(Self {
            source,
            expected,
            variables,
            clauses,
            dimacs,
            identity,
            connection,
            formula,
            clause_ids,
            model_literals: used.len(),
        })
    }

    pub fn prepare(&self) -> Result<PreparedSat<AllowAll>, String> {
        self.connection
            .prepare_sat(
                self.formula,
                &self.clause_ids,
                CnfLimits::default(),
                self.model_literals,
                lrat::Limits::default(),
            )
            .map_err(|error| error.to_string())
    }

    pub fn sat_holds(&self, world: covalence_nucleus::prop::WorldId) -> Result<bool, String> {
        self.connection
            .view()
            .world_holds(world, self.formula.lit())
            .map_err(|error| error.to_string())
    }

    pub fn unsat_holds(&self) -> Result<bool, String> {
        self.connection
            .view()
            .unsat(self.formula.lit())
            .map_err(|error| error.to_string())
    }

    pub fn snapshot(&self) -> Result<Vec<u8>, String> {
        self.connection
            .snapshot()
            .map_err(|error| error.to_string())
    }
}

fn parse_dimacs(bytes: &[u8]) -> Result<(usize, Vec<Vec<i64>>), String> {
    if bytes.len() > MAX_BYTES {
        return Err("DIMACS exceeds 1 MiB".to_owned());
    }
    let text = std::str::from_utf8(bytes).map_err(|_| "DIMACS is not UTF-8")?;
    let mut header = None;
    let mut matrix = Vec::new();
    let mut clause = Vec::new();
    let mut literals = 0_usize;

    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            if header.is_some() || !matrix.is_empty() || !clause.is_empty() {
                return Err("DIMACS header is misplaced or repeated".to_owned());
            }
            header = Some(parse_header(line)?);
            continue;
        }
        let Some((variables, declared_clauses)) = header else {
            return Err("DIMACS clauses precede the header".to_owned());
        };
        for token in line.split_ascii_whitespace() {
            let value = token
                .parse::<i64>()
                .map_err(|_| format!("invalid DIMACS literal {token:?}"))?;
            if value == 0 {
                matrix.push(std::mem::take(&mut clause));
                if matrix.len() > declared_clauses {
                    return Err("DIMACS has more clauses than declared".to_owned());
                }
                continue;
            }
            let variable =
                usize::try_from(value.unsigned_abs()).map_err(|_| "DIMACS literal is too large")?;
            if variable == 0 || variable > variables {
                return Err(format!("DIMACS literal {value} exceeds the header"));
            }
            literals = literals
                .checked_add(1)
                .ok_or_else(|| "DIMACS literal count overflow".to_owned())?;
            if literals > MAX_LITERALS {
                return Err("DIMACS has too many literals".to_owned());
            }
            clause.push(value);
        }
    }
    let Some((variables, declared_clauses)) = header else {
        return Err("DIMACS has no header".to_owned());
    };
    if !clause.is_empty() {
        return Err("DIMACS final clause has no terminating zero".to_owned());
    }
    if matrix.len() != declared_clauses {
        return Err(format!(
            "DIMACS declares {declared_clauses} clauses but contains {}",
            matrix.len()
        ));
    }
    Ok((variables, matrix))
}

fn parse_header(line: &str) -> Result<(usize, usize), String> {
    let fields: Vec<_> = line.split_ascii_whitespace().collect();
    if fields.len() != 4 || fields[0] != "p" || fields[1] != "cnf" {
        return Err("expected `p cnf VARIABLES CLAUSES`".to_owned());
    }
    let variables = fields[2]
        .parse::<usize>()
        .map_err(|_| "invalid DIMACS variable count")?;
    let clauses = fields[3]
        .parse::<usize>()
        .map_err(|_| "invalid DIMACS clause count")?;
    if variables > MAX_VARIABLES || clauses > MAX_CLAUSES {
        return Err("DIMACS header exceeds its bounds".to_owned());
    }
    Ok((variables, clauses))
}

fn prop_id(value: usize) -> Result<PropId, String> {
    i64::try_from(value)
        .ok()
        .and_then(PropId::new)
        .ok_or_else(|| "DIMACS encoding exceeds propositional identifiers".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimacs_true_and_false_have_sound_internal_constants() {
        let truth = SatProblem::parse(b"p cnf 0 0\n", "true".to_owned(), None).expect("true");
        assert_eq!(truth.variables, 0);
        assert_eq!(truth.clauses, 0);
        assert_eq!(truth.dimacs, b"p cnf 100001 1\n100001 0\n");
        let prepared = truth.prepare().expect("prepare true");
        let world = prepared
            .certify_model(&[Lit::new(100_001).expect("literal")])
            .expect("true model");
        assert!(truth.sat_holds(world).expect("admitted model"));

        let falsehood =
            SatProblem::parse(b"p cnf 0 1\n0\n", "false".to_owned(), None).expect("false");
        assert_eq!(falsehood.variables, 0);
        assert_eq!(falsehood.clauses, 1);
        assert_eq!(falsehood.dimacs, b"p cnf 100001 2\n100001 0\n-100001 0\n");
        falsehood
            .prepare()
            .expect("prepare false")
            .certify_lrat(&[b'a', 6, 0, 2, 4, 0], -1)
            .expect("false proof");
        assert!(falsehood.unsat_holds().expect("admitted refutation"));
    }

    #[test]
    fn sparse_headers_do_not_create_unused_kernel_variables() {
        let problem = SatProblem::parse(b"p cnf 100000 1\n100000 0\n", "sparse".to_owned(), None)
            .expect("sparse problem");
        assert_eq!(problem.variables, 100_000);
        assert_eq!(problem.model_literals, 1);
        assert_eq!(problem.dimacs, b"p cnf 100000 1\n100000 0\n");
        assert_eq!(problem.prepare().expect("prepare").max_model_literals(), 1);
    }

    #[test]
    fn source_metadata_is_bounded() {
        let source = "x".repeat(MAX_SOURCE_BYTES + 1);
        assert!(SatProblem::parse(b"p cnf 1 1\n1 0\n", source, None).is_err());
    }
}
