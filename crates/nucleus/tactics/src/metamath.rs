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
//!
//! Since `L'` contains only ground instances, exact Metamath expressions are
//! interned as opaque carrier terms. Their structure has already been checked
//! by replay and no rule in `L'` inspects or substitutes inside them. This keeps
//! the checked arena proportional to the number of distinct expressions rather
//! than to their repeated flat-symbol length. The artifact record links the
//! exported expression term back to its canonical flat conclusion.

use std::collections::HashMap;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_hol::{Arena, Kernel, KernelError, Lit, Ref, ThmId, builtin::Op2};
use covalence_logic_hol_derived::{ForallError, forall_elim};
use covalence_logic_metamath::{Assertion, Database, Expr, MmError, ReplayObserver, Subst, replay};

const TYPE_NAME: u64 = 0;
const PREDICATE_NAME: u64 = 1;
const FIRST_EXPRESSION_NAME: u64 = 2;

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

/// Deterministic source-order record for one independently checked theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroundArtifactRecord {
    /// Content address of the exact Metamath source bytes.
    pub corpus: O256,
    /// Zero-based statement position in the parsed database.
    pub statement_index: u64,
    /// Metamath assertion label.
    pub label: String,
    /// Canonical flat Metamath conclusion.
    pub conclusion: String,
    /// Content address of the canonical checked HOL arena bytes.
    pub arena: O256,
    /// The checked theorem handle within `arena`.
    pub theorem: ThmId,
    /// The theorem's encoded Metamath expression within `arena`.
    pub expression: Ref,
    /// The theorem's impredicative derivability proposition within `arena`.
    pub proposition: Ref,
    /// Number of distinct ground logical rule instances used by the proof.
    pub rule_instances: u64,
}

impl GroundArtifactRecord {
    /// Encodes this record in the deterministic `nucleus.metamath-ground.v2`
    /// binary format.
    ///
    /// Integers are fixed-width big-endian. Strings are UTF-8 prefixed by a
    /// big-endian `u64` byte length. The two addresses are their raw 32 bytes.
    /// Concatenated records remain self-delimiting and preserve source order.
    ///
    /// # Errors
    ///
    /// Returns an error only on a platform whose string length cannot fit the
    /// format's `u64` length field.
    pub fn encode(&self) -> Result<Vec<u8>, GroundReplayError> {
        const MAGIC: &[u8] = b"nucleus.metamath-ground.v2\0";
        let mut bytes =
            Vec::with_capacity(MAGIC.len() + self.label.len() + self.conclusion.len() + 128);
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(self.corpus.as_bytes());
        bytes.extend_from_slice(&self.statement_index.to_be_bytes());
        encode_string(&mut bytes, &self.label)?;
        encode_string(&mut bytes, &self.conclusion)?;
        bytes.extend_from_slice(self.arena.as_bytes());
        bytes.extend_from_slice(&self.theorem.get().to_be_bytes());
        bytes.extend_from_slice(&i32::from(self.expression).to_be_bytes());
        bytes.extend_from_slice(&i32::from(self.proposition).to_be_bytes());
        bytes.extend_from_slice(&self.rule_instances.to_be_bytes());
        Ok(bytes)
    }
}

fn encode_string(bytes: &mut Vec<u8>, value: &str) -> Result<(), GroundReplayError> {
    let len = u64::try_from(value.len())
        .map_err(|_| trace_error("string length is outside the artifact format"))?;
    bytes.extend_from_slice(&len.to_be_bytes());
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

/// One sequential replay result, ready for canonical arena serialization.
#[derive(Debug)]
pub struct GroundArtifact {
    /// Stable manifest record for this theorem arena.
    pub record: GroundArtifactRecord,
    /// Independently checked arena addressed by [`record.arena`](Self::record).
    pub arena: Arena,
}

/// Source-ordered, sequential checked replay of every proved logical assertion.
///
/// Each iterator step uses a fresh short-lived kernel. This prevents proof
/// scratch rows from one theorem from slowing later theorems and makes every
/// yielded arena independently serializable and content-addressable. Iterator
/// order is database statement order and therefore independent of scheduling.
pub struct GroundCorpus<'db> {
    db: &'db Database,
    corpus: O256,
    next_statement: usize,
}

impl<'db> GroundCorpus<'db> {
    /// Starts a deterministic sequential replay over `db`.
    #[must_use]
    pub const fn new(db: &'db Database, corpus: O256) -> Self {
        Self {
            db,
            corpus,
            next_statement: 0,
        }
    }
}

impl Iterator for GroundCorpus<'_> {
    type Item = Result<GroundArtifact, GroundReplayError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let statement_index = self.next_statement;
            let statement = self.db.statements().get(statement_index)?;
            self.next_statement += 1;
            let covalence_logic_metamath::Statement::Assert(assertion) = statement else {
                continue;
            };
            if assertion.proof.is_none() || assertion.conclusion.typecode() != "|-" {
                continue;
            }
            return Some(replay_artifact(
                self.db,
                self.corpus,
                statement_index,
                assertion,
            ));
        }
    }
}

fn replay_artifact(
    db: &Database,
    corpus: O256,
    statement_index: usize,
    assertion: &Assertion,
) -> Result<GroundArtifact, GroundReplayError> {
    let mut session = GroundSession::new(db)?;
    let imported = session.import(assertion)?;
    let arena = session.kernel.into_arena();
    let record = GroundArtifactRecord {
        corpus,
        statement_index: u64::try_from(statement_index)
            .map_err(|_| trace_error("statement index is outside the artifact format"))?,
        label: assertion.label.clone(),
        conclusion: assertion.conclusion.render(),
        arena: arena.addr(),
        theorem: imported.theorem,
        expression: imported.expression,
        proposition: imported.proposition,
        rule_instances: u64::try_from(imported.rule_instances)
            .map_err(|_| trace_error("rule count is outside the artifact format"))?,
    };
    Ok(GroundArtifact { record, arena })
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
        rule: Option<usize>,
    },
    Save,
    Heap(usize),
}

#[derive(Default)]
struct Trace {
    events: Vec<Event>,
    // Assigned on first checked occurrence, so later HOL replay need not
    // reconstruct and re-hash expression-sized rule keys.
    rules: Vec<RuleInstance>,
    rule_indices: HashMap<RuleInstance, usize>,
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
        let rule = if target.conclusion.typecode() == "|-" {
            let instance = RuleInstance {
                premises: args[floats..].to_vec(),
                conclusion: pushed.clone(),
            };
            if let Some(index) = self.rule_indices.get(&instance) {
                Some(*index)
            } else {
                let index = self.rules.len();
                self.rule_indices.insert(instance.clone(), index);
                self.rules.push(instance);
                Some(index)
            }
        } else {
            None
        };
        self.events.push(Event::Apply {
            pop: args.len(),
            floats,
            rule,
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

type ExtractionStep = (Ref, Ref);
type ExtractionPath = Vec<ExtractionStep>;

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
    predicate: Ref,
    next_expression_name: u64,
    expressions: HashMap<Expr, Ref>,
}

impl<'db> GroundSession<'db> {
    /// Starts a ground replay session for `db` in a fresh HOL kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the checked kernel rejects the fixed carrier or
    /// predicate declaration.
    pub fn new(db: &'db Database) -> Result<Self, GroundReplayError> {
        let mut kernel = Kernel::new();
        let star = kernel.star()?;
        let phi = kernel.ty_fv(TYPE_NAME, star)?;
        let bool_ty = kernel.bool_ty(star)?;
        let pred_ty = kernel.ty_arr(phi, bool_ty)?;
        let predicate = kernel.tm_fv(PREDICATE_NAME, pred_ty)?;
        Ok(Self {
            db,
            kernel,
            phi,
            bool_ty,
            predicate,
            next_expression_name: FIRST_EXPRESSION_NAME,
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
        let mut expressions = self.expressions.clone();
        let mut next_expression_name = self.next_expression_name;
        let result = import_trace(
            &mut staged,
            self.phi,
            self.bool_ty,
            self.predicate,
            &mut next_expression_name,
            &mut expressions,
            assertion,
            &trace,
        )?;
        self.kernel = staged;
        self.expressions = expressions;
        self.next_expression_name = next_expression_name;
        Ok(result)
    }
}

#[allow(clippy::too_many_arguments)]
fn import_trace(
    kernel: &mut Kernel,
    phi: Ref,
    bool_ty: Ref,
    predicate: Ref,
    next_expression_name: &mut u64,
    expressions: &mut HashMap<Expr, Ref>,
    assertion: &Assertion,
    trace: &Trace,
) -> Result<GroundImport, GroundReplayError> {
    let (layouts, mut predicate_apps) = encode_rules(
        kernel,
        phi,
        predicate,
        next_expression_name,
        expressions,
        &trace.rules,
    )?;
    let (closed, extraction_paths) = closed_formula(kernel, bool_ty, &layouts)?;
    let theorem = replay_events(
        kernel,
        phi,
        bool_ty,
        predicate,
        next_expression_name,
        expressions,
        &trace.events,
        &trace.rules,
        &layouts,
        &extraction_paths,
        closed,
        &mut predicate_apps,
    )?;
    finish_import(
        kernel,
        phi,
        bool_ty,
        predicate,
        next_expression_name,
        expressions,
        assertion,
        closed,
        theorem,
        trace.rules.len(),
        &mut predicate_apps,
    )
}

#[allow(clippy::too_many_arguments)]
fn encode_rules(
    kernel: &mut Kernel,
    phi: Ref,
    predicate: Ref,
    next_expression_name: &mut u64,
    expressions: &mut HashMap<Expr, Ref>,
    rules: &[RuleInstance],
) -> Result<(Vec<RuleLayout>, HashMap<Expr, Ref>), GroundReplayError> {
    let mut layouts = Vec::with_capacity(rules.len());
    let mut predicate_apps = HashMap::<Expr, Ref>::new();
    for rule in rules {
        let conclusion = encode_expr(
            kernel,
            phi,
            next_expression_name,
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
            let encoded = encode_expr(kernel, phi, next_expression_name, expressions, premise)?;
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
    predicate: Ref,
    next_expression_name: &mut u64,
    expressions: &mut HashMap<Expr, Ref>,
    events: &[Event],
    rules: &[RuleInstance],
    layouts: &[RuleLayout],
    extraction_paths: &[ExtractionPath],
    closed: Ref,
    predicate_apps: &mut HashMap<Expr, Ref>,
) -> Result<ThmId, GroundReplayError> {
    let mut stack = Vec::<Slot>::new();
    let mut heap = Vec::<Slot>::new();
    let mut extracted_clauses = vec![None; layouts.len()];
    // An essential expression always denotes the same theorem within this
    // import: the predicate, closed rule set, and expression carrier are fixed.
    let mut essential_theorems = HashMap::<Expr, ThmId>::new();
    for event in events {
        match event {
            Event::Float(expression) => {
                let _ = encode_expr(kernel, phi, next_expression_name, expressions, expression)?;
                stack.push(Slot::Syntax);
            }
            Event::Essential(expression) => {
                if let Some(theorem) = essential_theorems.get(expression) {
                    stack.push(Slot::Proved(*theorem));
                    continue;
                }
                let encoded =
                    encode_expr(kernel, phi, next_expression_name, expressions, expression)?;
                let applied =
                    predicate_app(kernel, predicate, expression, encoded, predicate_apps)?;
                let derivable = derivable_formula(kernel, bool_ty, predicate, closed, applied)?;
                let assumed_derivable = kernel.identity(positive(derivable))?;
                let specialized = forall_elim(kernel, assumed_derivable, predicate)?;
                let assumed_closed = kernel.identity(positive(closed))?;
                let theorem = modus_ponens(kernel, specialized.theorem, assumed_closed)?;
                essential_theorems.insert(expression.clone(), theorem);
                stack.push(Slot::Proved(theorem));
            }
            Event::Apply { pop, floats, rule } => {
                if stack.len() < *pop || *floats > *pop {
                    return Err(trace_error("assertion stack underflow"));
                }
                let args = stack.split_off(stack.len() - pop);
                let Some(index) = *rule else {
                    stack.push(Slot::Syntax);
                    continue;
                };
                let instance = rules
                    .get(index)
                    .ok_or_else(|| trace_error("logical rule instance is absent"))?;
                let mut theorem = if let Some(theorem) = extracted_clauses[index] {
                    theorem
                } else {
                    let theorem = extract_clause(kernel, layouts, extraction_paths, index)?;
                    extracted_clauses[index] = Some(theorem);
                    theorem
                };
                let proof_args = &args[*floats..];
                if proof_args.len() != instance.premises.len() {
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
    predicate: Ref,
    next_expression_name: &mut u64,
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
        next_expression_name,
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

fn encode_expr(
    kernel: &mut Kernel,
    phi: Ref,
    next_expression_name: &mut u64,
    expressions: &mut HashMap<Expr, Ref>,
    expression: &Expr,
) -> Result<Ref, GroundReplayError> {
    if let Some(encoded) = expressions.get(expression) {
        return Ok(*encoded);
    }
    let name = *next_expression_name;
    *next_expression_name = next_expression_name
        .checked_add(1)
        .ok_or_else(|| trace_error("expression-name space is exhausted"))?;
    let encoded = kernel.tm_fv(name, phi)?;
    expressions.insert(expression.clone(), encoded);
    Ok(encoded)
}

fn closed_formula(
    kernel: &mut Kernel,
    bool_ty: Ref,
    layouts: &[RuleLayout],
) -> Result<(Ref, Vec<ExtractionPath>), GroundReplayError> {
    if layouts.is_empty() {
        return Ok((kernel.bool(bool_ty, true)?, Vec::new()));
    }
    let mut extraction_paths = vec![Vec::new(); layouts.len()];
    let closed = balanced_closed_formula(kernel, layouts, 0, layouts.len(), &mut extraction_paths)?;
    Ok((closed, extraction_paths))
}

fn balanced_closed_formula(
    kernel: &mut Kernel,
    layouts: &[RuleLayout],
    start: usize,
    end: usize,
    extraction_paths: &mut [ExtractionPath],
) -> Result<Ref, GroundReplayError> {
    if end - start == 1 {
        return Ok(layouts[start].formula);
    }
    let middle = start + (end - start) / 2;
    let left = balanced_closed_formula(kernel, layouts, start, middle, extraction_paths)?;
    let right = balanced_closed_formula(kernel, layouts, middle, end, extraction_paths)?;
    let parent = kernel.op2(Op2::And, left, right)?;
    for path in &mut extraction_paths[start..middle] {
        path.push((right, parent));
    }
    for path in &mut extraction_paths[middle..end] {
        path.push((left, parent));
    }
    Ok(parent)
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
    extraction_paths: &[ExtractionPath],
    index: usize,
) -> Result<ThmId, GroundReplayError> {
    let clause = layouts
        .get(index)
        .ok_or_else(|| trace_error("rule index is absent"))?
        .formula;
    let mut theorem = kernel.identity(positive(clause))?;
    let path = extraction_paths
        .get(index)
        .ok_or_else(|| trace_error("rule extraction path is absent"))?;
    for &(sibling, parent) in path {
        kernel.weaken(theorem, &[positive(sibling)], &[])?;
        let previous = theorem;
        theorem = kernel.and_left(previous, positive(parent))?;
        if !kernel.remove_theorem(previous) {
            return Err(trace_error("consumed conjunction theorem is absent"));
        }
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
    if !kernel.remove_theorem(identity) || !kernel.remove_theorem(applied) {
        return Err(trace_error("consumed modus ponens theorem is absent"));
    }
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

    const DEMO0: &str = include_str!("../tests/fixtures/demo0.mm");

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
    fn sequential_corpus_artifact_is_byte_deterministic() {
        let db = parse(DEMO0).expect("parse demo0");
        verify_all(&db).expect("verify demo0");
        let corpus = O256::from_bytes(DEMO0.as_bytes());
        let build = || {
            GroundCorpus::new(&db, corpus)
                .map(|artifact| {
                    let artifact = artifact.expect("HOL replay");
                    assert_eq!(artifact.arena.addr(), artifact.record.arena);
                    artifact.record.encode().expect("encode record")
                })
                .collect::<Vec<_>>()
        };
        let first = build();
        let second = build();
        assert_eq!(first, second);
        assert_eq!(first.len(), 1);
    }

    #[test]
    fn ground_expression_interning_assigns_distinct_syntax_rows() {
        let mut kernel = Kernel::new();
        let star = kernel.star().expect("star");
        let phi = kernel.ty_fv(TYPE_NAME, star).expect("carrier");
        let mut next = FIRST_EXPRESSION_NAME;
        let mut expressions = HashMap::new();
        let left = Expr::new("|-", vec!["ph".into()]);
        let right = Expr::new("|-", vec!["ps".into()]);
        let first = encode_expr(&mut kernel, phi, &mut next, &mut expressions, &left)
            .expect("first expression");
        let repeated = encode_expr(&mut kernel, phi, &mut next, &mut expressions, &left)
            .expect("repeated expression");
        let distinct = encode_expr(&mut kernel, phi, &mut next, &mut expressions, &right)
            .expect("distinct expression");
        assert_eq!(first, repeated);
        assert_ne!(first, distinct);
        assert_eq!(expressions.len(), 2);
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
        let imported = GroundCorpus::new(&db, O256::from_bytes(source.as_bytes()))
            .try_fold(0, |count, artifact| artifact.map(|_| count + 1))
            .expect("HOL replay");
        assert_eq!(imported, logical.len());
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

    #[test]
    #[ignore = "requires NUCLEUS_METAMATH_CORPUS and NUCLEUS_METAMATH_LABEL"]
    fn benchmark_one_set_mm_ground_replay() {
        let root = std::env::var("NUCLEUS_METAMATH_CORPUS").expect("corpus checkout");
        let label = std::env::var("NUCLEUS_METAMATH_LABEL").expect("theorem label");
        let repetitions = std::env::var("NUCLEUS_METAMATH_REPETITIONS")
            .map_or(1, |value| value.parse().expect("positive repetition count"));
        assert!(repetitions > 0, "repetition count must be positive");
        let source = std::fs::read_to_string(std::path::Path::new(&root).join("set.mm"))
            .expect("read set.mm");
        let db = parse(&source).expect("parse set.mm");
        for repetition in 0..repetitions {
            let mut session = GroundSession::new(&db).expect("session");
            let started = std::time::Instant::now();
            let imported = session
                .import(assertion(&db, &label))
                .expect("checked HOL replay");
            let replay_ms = started.elapsed().as_secs_f64() * 1_000.0;
            let arena = session.kernel.into_arena();
            eprintln!(
                "{{\"label\":{label:?},\"repetition\":{repetition},\"replay_ms\":{replay_ms:.3},\"rule_instances\":{},\"arena_rows\":{},\"arena\":\"{}\"}}",
                imported.rule_instances,
                arena.len(),
                arena.addr()
            );
        }
    }

    #[test]
    #[ignore = "requires NUCLEUS_METAMATH_CORPUS; full set.mm HOL replay benchmark"]
    fn every_set_mm_theorem_becomes_a_checked_hol_derivation() {
        let root = std::env::var("NUCLEUS_METAMATH_CORPUS").expect("corpus checkout");
        let source = std::fs::read_to_string(std::path::Path::new(&root).join("set.mm"))
            .expect("read set.mm");
        let db = parse(&source).expect("parse set.mm");
        verify_all(&db).expect("independently verify all of set.mm");
        let logical: Vec<&Assertion> = db
            .assertions()
            .filter(|assertion| {
                assertion.proof.is_some() && assertion.conclusion.typecode() == "|-"
            })
            .collect();
        let corpus = O256::from_bytes(source.as_bytes());
        let mut manifest = Vec::new();
        let mut imported = 0;
        let mut replay = GroundCorpus::new(&db, corpus);
        loop {
            let started = std::time::Instant::now();
            let Some(artifact) = replay.next() else {
                break;
            };
            let artifact = artifact.expect("HOL replay");
            let elapsed = started.elapsed();
            manifest.extend(artifact.record.encode().expect("encode record"));
            imported += 1;
            if elapsed >= std::time::Duration::from_secs(1) {
                eprintln!(
                    "set.mm HOL long tail: record {imported}, statement {} ({}), {elapsed:?}, {} rules, {} arena rows",
                    artifact.record.statement_index,
                    artifact.record.label,
                    artifact.record.rule_instances,
                    artifact.arena.len()
                );
            }
            if imported % 1_000 == 0 {
                eprintln!(
                    "set.mm HOL artifact: {imported} records through statement {} ({})",
                    artifact.record.statement_index, artifact.record.label
                );
            }
        }
        assert_eq!(imported, logical.len());
        assert!(logical.len() > 40_000);
        eprintln!(
            "set.mm HOL artifact: {imported} records, {} bytes, {}",
            manifest.len(),
            O256::from_bytes(&manifest)
        );
    }
}
