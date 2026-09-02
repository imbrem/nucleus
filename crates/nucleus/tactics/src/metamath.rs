//! Ground-instance Metamath replay into impredicative HOL derivability.
//!
//! The Metamath verifier remains untrusted. Its passive replay observer records
//! only rule applications that have already passed every substitution, scope,
//! ordering, and distinct-variable check. This module then independently
//! reconstructs those ground rule instances through the public HOL kernel.
//! No parser result or verifier success can mint a theorem directly.
//!
//! A theorem is imported into a proof-scoped logic `L'`: its closure contains
//! exactly the ground logical rule instances used by that proof. This avoids a
//! grammar parser in the first running bridge and is intentionally explicit in
//! [`GroundImport::rule_instances`]. Relating `L'` to the full schematic
//! database logic is a separate transport theorem.

use std::collections::{HashMap, HashSet};

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, ThmId, builtin::Op2};
use covalence_logic_hol_derived::{ForallError, forall_elim};
use covalence_logic_metamath::{Assertion, Database, Expr, MmError, ReplayObserver, Subst, replay};

const TYPE_NAME: u64 = 0;
const CONCAT_NAME: u64 = 1;
const PREDICATE_NAME: u64 = 2;
const FIRST_SYMBOL_NAME: u64 = 3;

/// A checked theorem obtained by replaying one Metamath proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GroundImport {
    /// HOL encoding of the Metamath conclusion.
    pub expression: Ref,
    /// The impredicative proposition `Derivable_L' expression`.
    pub proposition: Ref,
    /// Checked theorem concluding [`proposition`](Self::proposition).
    pub theorem: ThmId,
    /// Number of distinct ground logical rule instances in `L'`.
    pub rule_instances: usize,
}

/// Failure while replaying verified Metamath events through HOL.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum GroundReplayError {
    /// The Metamath proof did not verify.
    #[snafu(display("Metamath proof replay failed: {source}"))]
    Metamath { source: Box<MmError> },
    /// A checked HOL operation rejected the proposed reconstruction.
    #[snafu(transparent)]
    Kernel { source: KernelError },
    /// Derived universal elimination rejected an internal theorem shape.
    #[snafu(display("could not specialize an impredicative derivation: {source}"))]
    Forall { source: ForallError },
    /// The passive event stream was internally inconsistent.
    #[snafu(display("Metamath replay event stream is inconsistent: {detail}"))]
    Trace { detail: String },
}

impl From<ForallError> for GroundReplayError {
    fn from(source: ForallError) -> Self {
        Self::Forall { source }
    }
}

impl From<MmError> for GroundReplayError {
    fn from(source: MmError) -> Self {
        Self::Metamath {
            source: Box::new(source),
        }
    }
}

#[derive(Clone, Debug)]
enum Event {
    Float(Expr),
    Essential(Expr),
    Apply {
        pop: usize,
        floats: usize,
        logical: bool,
        premises: Vec<Expr>,
        conclusion: Expr,
    },
    Save,
    Heap(usize),
}

#[derive(Default)]
struct Trace {
    events: Vec<Event>,
}

impl ReplayObserver for Trace {
    fn float_hyp(&mut self, _label: &str, pushed: &Expr, _depth: usize) {
        self.events.push(Event::Float(pushed.clone()));
    }

    fn essential_hyp(&mut self, _label: &str, pushed: &Expr, _depth: usize) {
        self.events.push(Event::Essential(pushed.clone()));
    }

    fn assertion(
        &mut self,
        _label: &str,
        target: &Assertion,
        args: &[Expr],
        _subst: &Subst,
        pushed: &Expr,
        _depth: usize,
    ) {
        let floats = target.frame.floats.len();
        self.events.push(Event::Apply {
            pop: args.len(),
            floats,
            logical: target.conclusion.typecode() == "|-",
            premises: args[floats..].to_vec(),
            conclusion: pushed.clone(),
        });
    }

    fn save(&mut self, _saved: &Expr, _depth: usize) {
        self.events.push(Event::Save);
    }

    fn heap(&mut self, idx: usize, _pushed: &Expr, _depth: usize) {
        self.events.push(Event::Heap(idx));
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RuleInstance {
    premises: Vec<Expr>,
    conclusion: Expr,
}

#[derive(Clone, Copy)]
struct RuleLayout {
    formula: Ref,
}

#[derive(Clone, Copy)]
enum Slot {
    Syntax,
    Proved(ThmId),
}

/// Stateful importer sharing one checked syntax arena across many theorems.
pub struct GroundSession<'db> {
    db: &'db Database,
    kernel: Kernel,
    phi: Ref,
    bool_ty: Ref,
    concat: Ref,
    predicate: Ref,
    next_symbol_name: u64,
    symbols: HashMap<String, Ref>,
    expressions: HashMap<Expr, Ref>,
}

impl<'db> GroundSession<'db> {
    /// Starts a ground replay session for `db` in a fresh HOL kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the checked kernel rejects the fixed carrier,
    /// predicate, or concatenation-function declarations.
    pub fn new(db: &'db Database) -> Result<Self, GroundReplayError> {
        let mut kernel = Kernel::new();
        let star = kernel.star()?;
        let phi = kernel.ty_fv(TYPE_NAME, star)?;
        let bool_ty = kernel.bool_ty(star)?;
        let phi_to_phi = kernel.ty_arr(phi, phi)?;
        let concat_ty = kernel.ty_arr(phi, phi_to_phi)?;
        let concat = kernel.tm_fv(CONCAT_NAME, concat_ty)?;
        let pred_ty = kernel.ty_arr(phi, bool_ty)?;
        let predicate = kernel.tm_fv(PREDICATE_NAME, pred_ty)?;
        Ok(Self {
            db,
            kernel,
            phi,
            bool_ty,
            concat,
            predicate,
            next_symbol_name: FIRST_SYMBOL_NAME,
            symbols: HashMap::new(),
            expressions: HashMap::new(),
        })
    }

    /// The checked kernel containing every successfully imported theorem.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Imports one `$p` assertion transactionally.
    ///
    /// The returned theorem concludes impredicative derivability in the exact
    /// ground rule-instance logic reported by `rule_instances`. Essential
    /// hypotheses remain theorem premises; ordinary closed corpus theorems are
    /// premise-free.
    ///
    /// # Errors
    ///
    /// Returns an error if Metamath verification fails, the assertion has no
    /// proof, the event stream is inconsistent, or any checked HOL operation
    /// rejects the reconstruction. Failure leaves this session unchanged.
    pub fn import(&mut self, assertion: &Assertion) -> Result<GroundImport, GroundReplayError> {
        if assertion.proof.is_none() {
            return Err(GroundReplayError::Trace {
                detail: format!("assertion {} has no proof", assertion.label),
            });
        }
        let mut trace = Trace::default();
        replay(self.db, assertion, &mut trace)?;

        let mut staged = self.kernel.fork();
        let mut symbols = self.symbols.clone();
        let mut expressions = self.expressions.clone();
        let mut next_symbol_name = self.next_symbol_name;
        let result = import_trace(
            &mut staged,
            self.phi,
            self.bool_ty,
            self.concat,
            self.predicate,
            &mut next_symbol_name,
            &mut symbols,
            &mut expressions,
            assertion,
            &trace.events,
        )?;
        self.kernel = staged;
        self.symbols = symbols;
        self.expressions = expressions;
        self.next_symbol_name = next_symbol_name;
        Ok(result)
    }
}

#[allow(clippy::too_many_arguments)]
fn import_trace(
    kernel: &mut Kernel,
    phi: Ref,
    bool_ty: Ref,
    concat: Ref,
    predicate: Ref,
    next_symbol_name: &mut u64,
    symbols: &mut HashMap<String, Ref>,
    expressions: &mut HashMap<Expr, Ref>,
    assertion: &Assertion,
    events: &[Event],
) -> Result<GroundImport, GroundReplayError> {
    let rules = collect_rules(events);
    let (layouts, mut predicate_apps) = encode_rules(
        kernel,
        phi,
        concat,
        predicate,
        next_symbol_name,
        symbols,
        expressions,
        &rules,
    )?;
    let (closed, suffixes) = closed_formula(kernel, bool_ty, &layouts)?;
    let rule_index: HashMap<RuleInstance, usize> = rules
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, rule)| (rule, index))
        .collect();
    let theorem = replay_events(
        kernel,
        phi,
        bool_ty,
        concat,
        predicate,
        next_symbol_name,
        symbols,
        expressions,
        events,
        &layouts,
        &suffixes,
        &rule_index,
        closed,
        &mut predicate_apps,
    )?;
    finish_import(
        kernel,
        phi,
        bool_ty,
        concat,
        predicate,
        next_symbol_name,
        symbols,
        expressions,
        assertion,
        closed,
        theorem,
        rules.len(),
        &mut predicate_apps,
    )
}

fn collect_rules(events: &[Event]) -> Vec<RuleInstance> {
    let mut seen = HashSet::new();
    let mut rules = Vec::new();
    for event in events {
        let Event::Apply {
            logical: true,
            premises,
            conclusion,
            ..
        } = event
        else {
            continue;
        };
        let rule = RuleInstance {
            premises: premises.clone(),
            conclusion: conclusion.clone(),
        };
        if seen.insert(rule.clone()) {
            rules.push(rule);
        }
    }
    rules
}

#[allow(clippy::too_many_arguments)]
fn encode_rules(
    kernel: &mut Kernel,
    phi: Ref,
    concat: Ref,
    predicate: Ref,
    next_symbol_name: &mut u64,
    symbols: &mut HashMap<String, Ref>,
    expressions: &mut HashMap<Expr, Ref>,
    rules: &[RuleInstance],
) -> Result<(Vec<RuleLayout>, HashMap<Expr, Ref>), GroundReplayError> {
    let mut layouts = Vec::with_capacity(rules.len());
    let mut predicate_apps = HashMap::<Expr, Ref>::new();
    for rule in rules {
        let conclusion = encode_expr(
            kernel,
            phi,
            concat,
            next_symbol_name,
            symbols,
            expressions,
            &rule.conclusion,
        )?;
        let mut formula = predicate_app(
            kernel,
            predicate,
            &rule.conclusion,
            conclusion,
            &mut predicate_apps,
        )?;
        for premise in rule.premises.iter().rev() {
            let encoded = encode_expr(
                kernel,
                phi,
                concat,
                next_symbol_name,
                symbols,
                expressions,
                premise,
            )?;
            let antecedent =
                predicate_app(kernel, predicate, premise, encoded, &mut predicate_apps)?;
            formula = kernel.op2(Op2::Imp, antecedent, formula)?;
        }
        layouts.push(RuleLayout { formula });
    }
    Ok((layouts, predicate_apps))
}

#[allow(clippy::too_many_arguments)]
fn replay_events(
    kernel: &mut Kernel,
    phi: Ref,
    bool_ty: Ref,
    concat: Ref,
    predicate: Ref,
    next_symbol_name: &mut u64,
    symbols: &mut HashMap<String, Ref>,
    expressions: &mut HashMap<Expr, Ref>,
    events: &[Event],
    layouts: &[RuleLayout],
    suffixes: &[Ref],
    rule_index: &HashMap<RuleInstance, usize>,
    closed: Ref,
    predicate_apps: &mut HashMap<Expr, Ref>,
) -> Result<ThmId, GroundReplayError> {
    let mut stack = Vec::<Slot>::new();
    let mut heap = Vec::<Slot>::new();
    for event in events {
        match event {
            Event::Float(expression) => {
                let _ = encode_expr(
                    kernel,
                    phi,
                    concat,
                    next_symbol_name,
                    symbols,
                    expressions,
                    expression,
                )?;
                stack.push(Slot::Syntax);
            }
            Event::Essential(expression) => {
                let encoded = encode_expr(
                    kernel,
                    phi,
                    concat,
                    next_symbol_name,
                    symbols,
                    expressions,
                    expression,
                )?;
                let applied =
                    predicate_app(kernel, predicate, expression, encoded, predicate_apps)?;
                let derivable = derivable_formula(kernel, bool_ty, predicate, closed, applied)?;
                let assumed_derivable = kernel.identity(positive(derivable))?;
                let specialized = forall_elim(kernel, assumed_derivable, predicate)?;
                let assumed_closed = kernel.identity(positive(closed))?;
                let theorem = modus_ponens(kernel, specialized.theorem, assumed_closed)?;
                stack.push(Slot::Proved(theorem));
            }
            Event::Apply {
                pop,
                floats,
                logical,
                premises,
                conclusion,
            } => {
                if stack.len() < *pop || *floats > *pop {
                    return Err(trace_error("assertion stack underflow"));
                }
                let args = stack.split_off(stack.len() - pop);
                if !logical {
                    stack.push(Slot::Syntax);
                    continue;
                }
                let rule = RuleInstance {
                    premises: premises.clone(),
                    conclusion: conclusion.clone(),
                };
                let index = *rule_index
                    .get(&rule)
                    .ok_or_else(|| trace_error("logical rule instance is absent"))?;
                let mut theorem = extract_clause(kernel, layouts, suffixes, index)?;
                let proof_args = &args[*floats..];
                if proof_args.len() != premises.len() {
                    return Err(trace_error("essential argument count changed"));
                }
                for slot in proof_args {
                    let Slot::Proved(premise) = slot else {
                        return Err(trace_error("logical premise is only syntax"));
                    };
                    theorem = modus_ponens(kernel, theorem, *premise)?;
                }
                stack.push(Slot::Proved(theorem));
            }
            Event::Save => {
                heap.push(
                    *stack
                        .last()
                        .ok_or_else(|| trace_error("empty save stack"))?,
                );
            }
            Event::Heap(index) => {
                stack.push(
                    *heap
                        .get(*index)
                        .ok_or_else(|| trace_error("heap reference is absent"))?,
                );
            }
        }
    }

    let [Slot::Proved(theorem)] = stack.as_slice() else {
        return Err(trace_error("proof did not finish with one logical theorem"));
    };
    Ok(*theorem)
}

#[allow(clippy::too_many_arguments)]
fn finish_import(
    kernel: &mut Kernel,
    phi: Ref,
    bool_ty: Ref,
    concat: Ref,
    predicate: Ref,
    next_symbol_name: &mut u64,
    symbols: &mut HashMap<String, Ref>,
    expressions: &mut HashMap<Expr, Ref>,
    assertion: &Assertion,
    closed: Ref,
    theorem: ThmId,
    rule_instances: usize,
    predicate_apps: &mut HashMap<Expr, Ref>,
) -> Result<GroundImport, GroundReplayError> {
    let expression = encode_expr(
        kernel,
        phi,
        concat,
        next_symbol_name,
        symbols,
        expressions,
        &assertion.conclusion,
    )?;
    let conclusion = predicate_app(
        kernel,
        predicate,
        &assertion.conclusion,
        expression,
        predicate_apps,
    )?;
    let implication = kernel.op2(Op2::Imp, closed, conclusion)?;
    kernel.contract_theorem(theorem)?;
    let discharged = kernel.imp_right(theorem, positive(implication))?;
    let proposition = kernel.forall_tm(bool_ty, predicate, implication)?;
    let theorem = kernel.forall_intro_at(discharged, predicate, proposition)?;
    Ok(GroundImport {
        expression,
        proposition,
        theorem,
        rule_instances,
    })
}

#[allow(clippy::too_many_arguments)]
fn encode_expr(
    kernel: &mut Kernel,
    phi: Ref,
    concat: Ref,
    next_symbol_name: &mut u64,
    symbols: &mut HashMap<String, Ref>,
    expressions: &mut HashMap<Expr, Ref>,
    expression: &Expr,
) -> Result<Ref, GroundReplayError> {
    if let Some(encoded) = expressions.get(expression) {
        return Ok(*encoded);
    }
    let mut parts = Vec::new();
    for symbol in expression.symbols() {
        let encoded = if let Some(encoded) = symbols.get(symbol) {
            *encoded
        } else {
            let name = *next_symbol_name;
            *next_symbol_name = next_symbol_name
                .checked_add(1)
                .ok_or_else(|| trace_error("symbol-name space is exhausted"))?;
            let encoded = kernel.tm_fv(name, phi)?;
            symbols.insert(symbol.to_owned(), encoded);
            encoded
        };
        parts.push(encoded);
    }
    let mut iter = parts.into_iter().rev();
    let mut encoded = iter
        .next()
        .ok_or_else(|| trace_error("Metamath expression has no typecode"))?;
    for part in iter {
        let partial = kernel.app(concat, part)?;
        encoded = kernel.app(partial, encoded)?;
    }
    expressions.insert(expression.clone(), encoded);
    Ok(encoded)
}

fn closed_formula(
    kernel: &mut Kernel,
    bool_ty: Ref,
    layouts: &[RuleLayout],
) -> Result<(Ref, Vec<Ref>), GroundReplayError> {
    if layouts.is_empty() {
        return Ok((kernel.bool(bool_ty, true)?, Vec::new()));
    }
    let mut suffixes = vec![layouts.last().expect("nonempty").formula; layouts.len()];
    for index in (0..layouts.len() - 1).rev() {
        suffixes[index] = kernel.op2(Op2::And, layouts[index].formula, suffixes[index + 1])?;
    }
    Ok((suffixes[0], suffixes))
}

fn derivable_formula(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate: Ref,
    closed: Ref,
    applied: Ref,
) -> Result<Ref, GroundReplayError> {
    let body = kernel.op2(Op2::Imp, closed, applied)?;
    Ok(kernel.forall_tm(bool_ty, predicate, body)?)
}

fn predicate_app(
    kernel: &mut Kernel,
    predicate: Ref,
    expression: &Expr,
    encoded: Ref,
    applications: &mut HashMap<Expr, Ref>,
) -> Result<Ref, GroundReplayError> {
    if let Some(application) = applications.get(expression) {
        return Ok(*application);
    }
    let application = kernel.app(predicate, encoded)?;
    applications.insert(expression.clone(), application);
    Ok(application)
}

fn extract_clause(
    kernel: &mut Kernel,
    layouts: &[RuleLayout],
    suffixes: &[Ref],
    index: usize,
) -> Result<ThmId, GroundReplayError> {
    let clause = layouts
        .get(index)
        .ok_or_else(|| trace_error("rule index is absent"))?
        .formula;
    let mut theorem = kernel.identity(positive(clause))?;
    if index + 1 < layouts.len() {
        kernel.weaken(theorem, &[positive(suffixes[index + 1])], &[])?;
        theorem = kernel.and_left(theorem, positive(suffixes[index]))?;
    }
    for outer in (0..index).rev() {
        kernel.weaken(theorem, &[positive(layouts[outer].formula)], &[])?;
        theorem = kernel.and_left(theorem, positive(suffixes[outer]))?;
    }
    Ok(theorem)
}

fn modus_ponens(
    kernel: &mut Kernel,
    implication_theorem: ThmId,
    premise_theorem: ThmId,
) -> Result<ThmId, GroundReplayError> {
    let implication = unit_conclusion(kernel, implication_theorem)?;
    let children: Vec<Ref> = kernel
        .arena()
        .children(implication)
        .ok_or_else(|| trace_error("implication has no operands"))?
        .collect();
    if kernel.arena().op2(implication) != Some(Op2::Imp) || children.len() != 2 {
        return Err(trace_error("theorem does not conclude an implication"));
    }
    let premise = unit_conclusion(kernel, premise_theorem)?;
    if premise != children[0] {
        return Err(GroundReplayError::Trace {
            detail: format!(
                "implication antecedent {:?} does not match premise {:?}",
                children[0], premise
            ),
        });
    }
    let consequent = children[1];
    let identity = kernel.identity(positive(consequent))?;
    let applied = kernel.imp_left(premise_theorem, identity, positive(implication))?;
    let theorem = kernel.cut(implication_theorem, applied, positive(implication))?;
    kernel.contract_theorem(theorem)?;
    Ok(theorem)
}

fn unit_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, GroundReplayError> {
    let source = kernel
        .thm()
        .get(theorem)
        .ok_or_else(|| trace_error("theorem slot is absent"))?;
    let mut rows = source.rhs.rows();
    let row = rows
        .next()
        .ok_or_else(|| trace_error("theorem has no conclusion"))?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(trace_error("theorem conclusion is not one positive atom"));
    }
    Ref::new(
        i32::try_from(row[0].magnitude())
            .map_err(|_| trace_error("theorem conclusion is outside Ref"))?,
    )
    .ok_or_else(|| trace_error("theorem conclusion is zero"))
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn trace_error(detail: &str) -> GroundReplayError {
    GroundReplayError::Trace {
        detail: detail.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_logic_metamath::{Proof, Statement, parse, verify_all};

    const DEMO0: &str = include_str!("../../../logic/metamath/tests/fixtures/demo0.mm");

    fn assertion<'a>(db: &'a Database, label: &str) -> &'a Assertion {
        match db.statement_by_label(label) {
            Some(Statement::Assert(assertion)) => assertion,
            _ => panic!("missing assertion {label}"),
        }
    }

    #[test]
    fn verified_demo0_theorem_becomes_a_checked_hol_derivation() {
        let db = parse(DEMO0).expect("parse demo0");
        verify_all(&db).expect("verify demo0");
        let mut session = GroundSession::new(&db).expect("session");
        let imported = session.import(assertion(&db, "th1")).expect("HOL replay");
        let theorem = session
            .kernel()
            .thm()
            .get(imported.theorem)
            .expect("checked theorem");
        assert!(theorem.lhs.rows().next().is_none());
        let mut rows = theorem.rhs.rows();
        let row = rows.next().expect("one conclusion");
        assert!(rows.next().is_none());
        assert_eq!(row, &[positive(imported.proposition)]);
        assert!(imported.rule_instances > 0);
    }

    #[test]
    fn rejected_metamath_proof_cannot_mutate_the_kernel() {
        let db = parse(DEMO0).expect("parse demo0");
        let mut invalid = assertion(&db, "th1").clone();
        invalid.proof = Some(Proof::Normal(vec!["missing".to_owned()]));
        let mut session = GroundSession::new(&db).expect("session");
        let before = session.kernel().arena().clone();
        assert!(session.import(&invalid).is_err());
        assert_eq!(session.kernel().arena(), &before);
    }

    #[test]
    #[ignore = "requires NUCLEUS_METAMATH_CORPUS; full upstream hol.mm replay"]
    fn every_hol_mm_theorem_becomes_a_checked_hol_derivation() {
        let root = std::env::var("NUCLEUS_METAMATH_CORPUS").expect("corpus checkout");
        let source = std::fs::read_to_string(std::path::Path::new(&root).join("hol.mm"))
            .expect("read hol.mm");
        let db = parse(&source).expect("parse hol.mm");
        let verified = verify_all(&db).expect("verify hol.mm");
        let logical: Vec<&Assertion> = db
            .assertions()
            .filter(|assertion| {
                assertion.proof.is_some() && assertion.conclusion.typecode() == "|-"
            })
            .collect();
        let mut session = GroundSession::new(&db).expect("session");
        for theorem in &logical {
            session
                .import(theorem)
                .unwrap_or_else(|error| panic!("HOL replay of {} failed: {error}", theorem.label));
        }
        assert_eq!(logical.len(), verified);
    }

    #[test]
    #[ignore = "requires NUCLEUS_METAMATH_CORPUS; full set.mm verification and HOL replay"]
    fn set_mm_two_plus_two_becomes_a_checked_hol_derivation() {
        let root = std::env::var("NUCLEUS_METAMATH_CORPUS").expect("corpus checkout");
        let source = std::fs::read_to_string(std::path::Path::new(&root).join("set.mm"))
            .expect("read set.mm");
        let db = parse(&source).expect("parse set.mm");
        verify_all(&db).expect("independently verify all of set.mm");
        let mut session = GroundSession::new(&db).expect("session");
        let imported = session
            .import(assertion(&db, "2p2e4"))
            .expect("HOL replay of 2p2e4");
        let theorem = session
            .kernel()
            .thm()
            .get(imported.theorem)
            .expect("checked theorem");
        assert!(theorem.lhs.rows().next().is_none());
        assert_eq!(
            theorem.rhs.rows().next(),
            Some(&[positive(imported.proposition)][..])
        );
    }
}
