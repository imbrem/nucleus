//! SAT-in-the-kernel demo: load a `DIMACS` problem, ask `CaDiCaL`, and
//! land the verdict as checked propositional kernel state.
//!
//! ```sh
//! cargo run -p covalence-nucleus --example sat_lrat -- problem.cnf
//! ```
//!
//! SAT answers are replayed as a kernel world (CHOOSE + CONTRA + TRANS +
//! FOLD), so the witness is verified by LCF rules alone. UNSAT answers
//! are certified two ways, chosen by `--paranoid`: the default drives
//! the big-step LRAT mini-kernel; paranoid mode replays the same
//! instruction stream through scratch-table rule applications only
//! (zero added TCB) and concludes by inter-table import. Binary and
//! ASCII LRAT are both accepted. The solver is never trusted; either
//! way the demo ends by querying the recorded judgement.

use std::io::Write as _;
use std::process::Command;

use covalence_nucleus::prop::{AllowAll, Ant, Lit, PropId, Target, lrat};
use covalence_nucleus::{Connection, Prop};

type Kernel = Connection<Prop<AllowAll>>;

fn main() {
    let mut paranoid = false;
    let mut positional = Vec::new();
    for argument in std::env::args().skip(1) {
        if argument == "--paranoid" {
            paranoid = true;
        } else {
            positional.push(argument);
        }
    }
    let mut arguments = positional.into_iter();
    let Some(path) = arguments.next() else {
        eprintln!("usage: sat_lrat [--paranoid] <problem.cnf> [cadical-binary]");
        std::process::exit(2);
    };
    let solver = arguments.next().unwrap_or_else(|| "cadical".to_owned());
    let text = std::fs::read_to_string(&path).expect("read DIMACS file");
    let (variables, clauses) = parse_dimacs(&text);
    println!(
        "loaded {path}: {variables} variables, {} clauses",
        clauses.len()
    );

    let connection = Kernel::open_prop_in_memory(AllowAll).expect("open kernel");
    let prop = connection.view();

    // Ids: variables 1..=v, clause negations v+1..=v+m, formula v+m+1.
    let clause_negation = |index: usize| {
        let offset = i64::try_from(index).expect("clause index");
        PropId::new(variables + 1 + offset).expect("clause id")
    };
    let clause_count = i64::try_from(clauses.len()).expect("clause count");
    let formula = PropId::new(variables + 1 + clause_count).expect("formula id");
    for variable in 1..=variables {
        prop.declare_free(PropId::new(variable).expect("variable"))
            .expect("declare variable");
    }
    for (index, clause) in clauses.iter().enumerate() {
        let negated: Vec<Lit> = clause
            .iter()
            .map(|literal| Lit::new(-literal).expect("literal"))
            .collect();
        prop.define(clause_negation(index), &negated)
            .expect("define clause negation");
    }
    let formula_conjuncts: Vec<Lit> = (0..clauses.len())
        .map(|index| clause_negation(index).negated())
        .collect();
    prop.define(formula, &formula_conjuncts)
        .expect("define formula");
    println!("kernel state: formula is id {}", formula.get());

    // Ask the solver for a verdict and an LRAT certificate.
    let proof_path = std::env::temp_dir().join(format!("sat-lrat-{}.lrat", std::process::id()));
    let output = Command::new(&solver)
        .arg("--lrat")
        .arg(&path)
        .arg(&proof_path)
        .output()
        .expect("run the SAT solver");
    let stdout = String::from_utf8_lossy(&output.stdout);
    match output.status.code() {
        Some(10) => replay_sat(&prop, &stdout, &clauses, clause_negation, formula),
        Some(20) => {
            let proof_bytes = std::fs::read(&proof_path).expect("read LRAT proof");
            check_unsat(
                &prop,
                &proof_bytes,
                clauses.len(),
                clause_negation,
                formula,
                paranoid,
            );
        }
        other => {
            let _ = std::io::stderr().write_all(&output.stderr);
            panic!("unexpected solver exit: {other:?}");
        }
    }
    let violations = prop.check_validity().expect("validity");
    assert!(violations.is_empty(), "validity violations: {violations:?}");
    println!("kernel: W1-W4 validity assertions clean");
    let _ = std::fs::remove_file(&proof_path);
}

/// Replays a satisfying assignment as a kernel world: CHOOSE the model
/// literals, then derive the formula by CONTRA + TRANS + FOLD.
fn replay_sat(
    prop: &covalence_nucleus::prop::PropView<'_, AllowAll>,
    stdout: &str,
    clauses: &[Vec<i64>],
    clause_negation: impl Fn(usize) -> PropId,
    formula: PropId,
) {
    println!("solver: SAT — replaying the witness as a kernel world");
    let model = parse_model(stdout);
    let world = prop.world(None).expect("scratch world");
    let target = Target::World(world);
    for literal in &model {
        prop.choose(world, *literal).expect("choose model literal");
    }
    for (index, clause) in clauses.iter().enumerate() {
        let satisfied = clause
            .iter()
            .find(|literal| model.contains(&Lit::new(**literal).expect("literal")))
            .copied()
            .expect("model satisfies every clause");
        let witness = Lit::new(satisfied).expect("literal");
        // clause-negation => -witness definitionally, so witness =>
        // -clause-negation, and truth chains through.
        prop.contra(target, clause_negation(index).lit(), witness.negated())
            .expect("contrapose the definitional row");
        prop.trans(target, Ant::TRUE, witness, clause_negation(index).negated())
            .expect("chain from the chosen literal");
    }
    prop.fold(target, Ant::TRUE, formula)
        .expect("fold the formula");
    assert!(
        prop.world_holds(world, formula.lit())
            .expect("query the witness world")
    );
    println!(
        "kernel: SAT verified — (0, {}) holds in world {}",
        formula.get(),
        world.get()
    );
}

/// Checks the solver's LRAT certificate through the policy-gated kernel
/// rule and confirms the recorded judgement.
fn check_unsat(
    prop: &covalence_nucleus::prop::PropView<'_, AllowAll>,
    proof_bytes: &[u8],
    clause_count: usize,
    clause_negation: impl Fn(usize) -> PropId,
    formula: PropId,
    paranoid: bool,
) {
    println!("solver: UNSAT — certifying in the kernel");
    let instructions = lrat::parse(proof_bytes).expect("parse LRAT proof");
    println!("proof: {} instructions", instructions.len());
    let clause_ids: Vec<PropId> = (0..clause_count).map(clause_negation).collect();
    if paranoid {
        covalence_nucleus::prop::scratch::lrat_replay_scratch(
            prop,
            formula,
            &clause_ids,
            &instructions,
            "sat_lrat --paranoid scratch replay",
        )
        .expect("rule-level scratch replay");
        println!("kernel: replayed through scratch-table rules (zero added TCB)");
    } else {
        prop.lrat_refutation(formula, &clause_ids, &instructions, -1)
            .expect("mini-kernel refutation");
        println!("kernel: certified by the big-step LRAT mini-kernel");
    }
    assert!(prop.unsat(formula.lit()).expect("query the judgement"));
    println!(
        "kernel: UNSAT verified — ({0}, {1}) recorded universally",
        formula.get(),
        -formula.get()
    );
}

/// Parses a `DIMACS` CNF file into (variable count, clauses).
fn parse_dimacs(text: &str) -> (i64, Vec<Vec<i64>>) {
    let mut variables = 0_i64;
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(header) = line.strip_prefix("p cnf") {
            let mut fields = header.split_ascii_whitespace();
            variables = fields
                .next()
                .and_then(|field| field.parse().ok())
                .expect("variable count");
            continue;
        }
        for token in line.split_ascii_whitespace() {
            let literal: i64 = token.parse().expect("literal");
            if literal == 0 {
                clauses.push(std::mem::take(&mut current));
            } else {
                current.push(literal);
            }
        }
    }
    (variables, clauses)
}

/// Parses the `v` lines of a SAT solver's model output.
fn parse_model(stdout: &str) -> Vec<Lit> {
    let mut model = Vec::new();
    for line in stdout.lines() {
        if let Some(values) = line.strip_prefix("v ") {
            for token in values.split_ascii_whitespace() {
                let literal: i64 = token.parse().expect("model literal");
                if literal != 0 {
                    model.push(Lit::new(literal).expect("literal"));
                }
            }
        }
    }
    model
}
