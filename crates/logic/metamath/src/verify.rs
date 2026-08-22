//! Schematic rule application and the RPN proof checker.
//!
//! A Metamath proof is a sequence of steps evaluated against a stack of
//! expressions:
//!
//! * a `$f`/`$e` hypothesis label pushes its expression;
//! * an assertion label (`$a`/`$p`) pops its mandatory hypotheses, unifies the
//!   floats to build a substitution, checks the essentials and the
//!   distinct-variable conditions, and pushes the substituted conclusion.
//!
//! A proof is valid iff it terminates with exactly one expression on the stack,
//! equal to the claimed conclusion. The checker never trusts the proof: every
//! substitution, typecode, and `$d` constraint is re-derived and re-checked.
//!
//! Both proof encodings are handled: the [`Proof::Normal`] label sequence and
//! the [`Proof::Compressed`] letter scheme (decoded by `decompress_proof`,
//! which recovers the `A`–`T` / `U`–`Y` base-20/5 integers, the `Z` save
//! markers, and the mandatory-hyp / label-block / heap addressing).
//!
//! ## Why the checker re-imposes the reading order
//!
//! A read-as-you-go verifier (`mmverify.py`) cannot cite a label it has not yet
//! read: its label table *is* the prefix of the database processed so far. This
//! crate parses the whole file before checking anything, so every label is
//! visible to every proof — and left unguarded a theorem could cite *itself*
//! (or two theorems each other) and thereby "prove" an arbitrary statement.
//! [`replay`] restores the discipline positionally: a cited label must occur
//! **strictly earlier** in the statement list than the theorem being proved.
//!
//! ## Why `$e` premises are checked for activity but `$f` floats are not
//!
//! An essential hypothesis belongs to the `${ ... $}` block that declares it;
//! a proof that helps itself to another block's premise proves anything. The
//! `$e` hypotheses active where an assertion is stated are *exactly* its
//! mandatory [`Frame::essentials`] (frame construction takes all of them), so
//! membership there **is** the activity test — precise, with no legitimate
//! proof rejected.
//!
//! Floats are weaker. A proof may legitimately cite an active but *non*-mandatory
//! `$f` to introduce a dummy (working) variable — `set.mm` does so around
//! 200 000 times — so frame membership is the wrong test for them, and a parsed
//! [`Database`] does not retain `${ ... $}` markers (they leave no
//! [`Statement`]), so the float's original scope cannot be recovered here.
//! Floats are therefore held to the ordering check alone. That leaves one
//! residual gap: a database that gives the *same* variable two different
//! typecodes in two disjoint scopes could cite the out-of-scope typing. Dummy
//! variables remain constrained by the `$d` check below, which consults the
//! proving theorem's own in-scope `$d` set, so a foreign float buys nothing
//! wherever distinctness is required.

use std::collections::BTreeSet;

use fnv::FnvHashMap;

use crate::database::{Assertion, Database, Frame, Proof, Statement};
use crate::error::MmError;
use crate::expr::{Expr, body_of, render, typecode_of};
use crate::subst::{Subst, apply_subst, vars_in_body};

/// Verify every `$p` theorem in the database. Returns the number verified.
pub fn verify_all(db: &Database) -> Result<usize, MmError> {
    // One shared position table for the whole run: every proof needs it, and it
    // depends only on the database.
    let order = LabelOrder::new(db);
    let mut count = 0;
    for assertion in db.assertions() {
        if assertion.proof.is_some() {
            replay_ordered(db, assertion, &order, &mut ())?;
            count += 1;
        }
    }
    Ok(count)
}

/// Where each labelled statement sits in [`Database::statements`].
///
/// The checker rejects a proof that cites a label declared no earlier than the
/// theorem being proved (see the module docs), which needs both statements'
/// source positions. The table is derived from the public statement list rather
/// than read out of the database, and is built **once** per [`verify_all`] —
/// the standalone [`replay`] / [`verify_assertion`] entry points build one for
/// their single call, which is why bulk verification should go through
/// [`verify_all`].
struct LabelOrder<'a> {
    positions: FnvHashMap<&'a str, usize>,
}

impl<'a> LabelOrder<'a> {
    fn new(db: &'a Database) -> Self {
        let statements = db.statements();
        let mut positions = FnvHashMap::with_capacity_and_hasher(statements.len(), <_>::default());
        for (index, statement) in statements.iter().enumerate() {
            if let Some(label) = statement_label(statement) {
                positions.insert(label, index);
            }
        }
        Self { positions }
    }

    /// The source position of `label`, if the database declares it.
    fn lookup(&self, label: &str) -> Option<usize> {
        self.positions.get(label).copied()
    }

    /// The source position of `label`, or `usize::MAX` if the database declares
    /// no such label — nothing in the database then precedes it.
    fn position(&self, label: &str) -> usize {
        self.lookup(label).unwrap_or(usize::MAX)
    }
}

/// The label a statement declares, if any. `$c`, `$v`, and `$d` are unlabelled.
fn statement_label(statement: &Statement) -> Option<&str> {
    match statement {
        Statement::Float(f) => Some(&f.label),
        Statement::Essential(h) => Some(&h.label),
        Statement::Assert(a) => Some(&a.label),
        Statement::Constant(_) | Statement::Variable(_) | Statement::Disjoint(_) => None,
    }
}

/// An observer notified of every event of a proof replay, in order.
///
/// This is the **only** extension point on the checker: [`replay`] is the single
/// replay implementation, and [`verify_assertion`] is `replay` with a no-op
/// observer. Anything that needs to *watch* a verifying replay — a proof-trace
/// builder, say — implements this rather than forking a second, divergeable
/// verifier. Observers are passive — they cannot influence
/// the stack, the substitution, or any check.
pub trait ReplayObserver {
    /// A `$f` floating hypothesis pushed `pushed`; `depth` is the resulting
    /// stack depth.
    fn float_hyp(&mut self, _label: &str, _pushed: &Expr, _depth: usize) {}
    /// A `$e` essential hypothesis pushed `pushed`.
    fn essential_hyp(&mut self, _label: &str, _pushed: &Expr, _depth: usize) {}
    /// `target` was applied: `args` are the popped mandatory arguments (floats
    /// first, then essentials), `subst` the substitution derived from the
    /// floats and checked against the essentials, `pushed` the substituted
    /// conclusion. Called only *after* every check has passed.
    fn assertion(
        &mut self,
        _label: &str,
        _target: &Assertion,
        _args: &[Expr],
        _subst: &Subst,
        _pushed: &Expr,
        _depth: usize,
    ) {
    }
    /// A `Z` marker saved the top of stack (`saved`) to the heap.
    fn save(&mut self, _saved: &Expr, _depth: usize) {}
    /// A heap backreference re-pushed the entry at `idx`.
    fn heap(&mut self, _idx: usize, _pushed: &Expr, _depth: usize) {}
}

/// The no-op observer: plain verification.
impl ReplayObserver for () {}

/// Verify a single `$p` assertion's proof against the database. `$a` axioms
/// (no proof) verify trivially.
///
/// `assertion` is located in `db` by its own label, so the ordering check binds
/// here exactly as it does under [`verify_all`]. Verifying a whole database one
/// call at a time nevertheless costs a position table per call; use
/// [`verify_all`], which builds one for the run.
pub fn verify_assertion(db: &Database, assertion: &Assertion) -> Result<(), MmError> {
    replay(db, assertion, &mut ())
}

/// Replay `assertion`'s proof, reporting each event to `obs`.
///
/// **This is the verifier.** [`verify_assertion`] is exactly this function with
/// a no-op observer, so an observed replay performs bit-for-bit the same checks
/// — no separate code path exists to drift out of sync.
pub fn replay(
    db: &Database,
    assertion: &Assertion,
    obs: &mut dyn ReplayObserver,
) -> Result<(), MmError> {
    replay_ordered(db, assertion, &LabelOrder::new(db), obs)
}

/// [`replay`] against a position table the caller already has.
fn replay_ordered(
    db: &Database,
    assertion: &Assertion,
    order: &LabelOrder<'_>,
    obs: &mut dyn ReplayObserver,
) -> Result<(), MmError> {
    let Some(proof) = &assertion.proof else {
        return Ok(());
    };
    let theorem = &assertion.label;
    let ctx = Context::new(db, assertion, order);

    let mut stack: Vec<Expr> = Vec::new();

    match proof {
        Proof::Normal(labels) => {
            for label in labels {
                step_label(&ctx, label, &mut stack, obs)?;
            }
        }
        Proof::Compressed { labels, letters } => {
            let steps = decompress_proof(labels, letters, &assertion.frame, db, theorem)?;
            let mut heap: Vec<Expr> = Vec::new();
            for step in &steps {
                match step {
                    ProofStep::Label(label) => {
                        step_label(&ctx, label, &mut stack, obs)?;
                    }
                    ProofStep::Save => {
                        let top = stack
                            .last()
                            .ok_or_else(|| MmError::CompressedProofError {
                                theorem: theorem.clone(),
                                message: "`Z` save with an empty stack".into(),
                            })?
                            .clone();
                        obs.save(&top, stack.len());
                        heap.push(top);
                    }
                    ProofStep::Heap(idx) => {
                        let e = heap
                            .get(*idx)
                            .ok_or_else(|| MmError::CompressedProofError {
                                theorem: theorem.clone(),
                                message: format!("heap backreference {idx} out of range"),
                            })?
                            .clone();
                        stack.push(e);
                        obs.heap(*idx, stack.last().unwrap(), stack.len());
                    }
                }
            }
        }
    }

    if stack.len() != 1 {
        return Err(MmError::StackResidue {
            theorem: theorem.clone(),
            count: stack.len(),
        });
    }
    let result = stack.pop().unwrap();
    if result != assertion.conclusion {
        return Err(MmError::ResultMismatch {
            theorem: theorem.clone(),
            expected: render(&assertion.conclusion),
            found: render(&result),
        });
    }
    Ok(())
}

/// Everything a replay needs that is fixed for the whole of one proof.
///
/// The `$d` set in particular used to be rebuilt inside the step loop — once
/// per *assertion application*, allocating two `String`s per pair — and that
/// dominated verification time on `set.mm`. It depends only on the theorem
/// being proved, so it is built once here and keyed on borrowed names.
struct Context<'a> {
    db: &'a Database,
    /// The theorem whose proof is being replayed.
    current: &'a Assertion,
    order: &'a LabelOrder<'a>,
    /// `current`'s own position in the statement list: a cited label must come
    /// strictly before it. `usize::MAX` when `current` is not itself a statement
    /// of `db` (a synthetic assertion — then nothing in `db` is a forward
    /// reference).
    position: usize,
    /// `current.scope_disjoints` as a set of normalised unordered pairs.
    disjoints: BTreeSet<(&'a str, &'a str)>,
}

impl<'a> Context<'a> {
    fn new(db: &'a Database, current: &'a Assertion, order: &'a LabelOrder<'a>) -> Self {
        Self {
            db,
            current,
            order,
            position: order.position(&current.label),
            disjoints: current
                .scope_disjoints
                .iter()
                .map(|(a, b)| ordered_pair(a, b))
                .collect(),
        }
    }

    /// The label of the theorem being proved, for diagnostics.
    fn theorem(&self) -> &str {
        &self.current.label
    }
}

/// Execute a single label step (shared by both proof encodings): push a
/// hypothesis expression, or apply an assertion.
fn step_label(
    ctx: &Context<'_>,
    label: &str,
    stack: &mut Vec<Expr>,
    obs: &mut dyn ReplayObserver,
) -> Result<(), MmError> {
    let theorem = ctx.theorem();
    // One lookup both resolves the label and locates it: the position *is* the
    // index of the statement it names.
    let position = ctx
        .order
        .lookup(label)
        .ok_or_else(|| MmError::UnknownLabel {
            theorem: theorem.to_string(),
            label: label.to_string(),
        })?;

    // A proof may cite only what a read-as-you-go verifier would already have
    // read. Without this a theorem cites itself and proves anything.
    if position >= ctx.position {
        return Err(MmError::ForwardReference {
            theorem: theorem.to_string(),
            label: label.to_string(),
        });
    }

    match &ctx.db.statements()[position] {
        Statement::Float(f) => {
            stack.push(crate::expr::make_expr(&f.typecode, [f.var.as_str()]));
            obs.float_hyp(label, stack.last().unwrap(), stack.len());
        }
        Statement::Essential(h) => {
            // The active `$e` premises are exactly the mandatory ones, so this
            // is the scope check: an unrelated block's premise is not free.
            if !ctx
                .current
                .frame
                .essentials
                .iter()
                .any(|e| e.label == label)
            {
                return Err(MmError::InactiveHypothesis {
                    theorem: theorem.to_string(),
                    label: label.to_string(),
                });
            }
            stack.push(h.expr.clone());
            obs.essential_hyp(label, stack.last().unwrap(), stack.len());
        }
        Statement::Assert(target) => {
            apply_assertion(ctx, target, label, stack, obs)?;
        }
        _ => {
            return Err(MmError::UnknownLabel {
                theorem: theorem.to_string(),
                label: label.to_string(),
            });
        }
    }
    Ok(())
}

/// A decoded proof step — the common currency of *both* proof encodings, so a
/// consumer (the in-crate verifier or a future HOL replay) can process compressed and normal
/// proofs uniformly with a stack + heap. The heap preserves the compressed
/// proof's **sharing**: re-using a saved sub-proof is a heap push, not a
/// recomputation, so there is no exponential re-expansion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStep {
    /// Reference a statement by label (mandatory hyp, label-block entry, or
    /// prior theorem).
    Label(String),
    /// Save the top of stack to the heap (`Z` marker).
    Save,
    /// Push a previously saved heap entry.
    Heap(usize),
}

/// The proof of `assertion` as a uniform [`ProofStep`] sequence: a
/// [`Proof::Normal`] proof maps to its label steps; a [`Proof::Compressed`]
/// proof is decoded (the `A`–`T`/`U`–`Y` integers, `Z` saves, heap addressing).
/// An axiom (no proof) yields an empty sequence. The consumer runs the steps
/// against a stack, pushing the top on `Save` to a heap and re-pushing on
/// `Heap` — exactly as [`verify_assertion`] does — which is how a compressed
/// proof is replayed *without* expanding its sharing.
pub fn proof_steps(db: &Database, assertion: &Assertion) -> Result<Vec<ProofStep>, MmError> {
    match &assertion.proof {
        None => Ok(Vec::new()),
        Some(Proof::Normal(labels)) => Ok(labels.iter().cloned().map(ProofStep::Label).collect()),
        Some(Proof::Compressed { labels, letters }) => {
            decompress_proof(labels, letters, &assertion.frame, db, &assertion.label)
        }
    }
}

/// Decompress a compressed proof into a sequence of [`ProofStep`]s.
///
/// The proof-integer scheme (per the Metamath spec): the letters `A`–`T`
/// (values 1–20) are *terminal* digits, `U`–`Y` (values 1–5) are *continuation*
/// digits, and `Z` is a save marker. An integer `n` (1-based) addresses, in
/// order: the mandatory hypotheses (floats then essentials), then the
/// label-block entries, then the heap backreferences.
fn decompress_proof(
    labels: &[String],
    letters: &[u8],
    frame: &Frame,
    db: &Database,
    theorem: &str,
) -> Result<Vec<ProofStep>, MmError> {
    let mand_count = frame.floats.len() + frame.essentials.len();
    let label_count = labels.len();

    // Resolve label-block entries to existing labels (validating they exist).
    for l in labels {
        if db.statement_by_label(l).is_none() {
            return Err(MmError::UnknownLabel {
                theorem: theorem.to_owned(),
                label: l.clone(),
            });
        }
    }

    let mut steps = Vec::new();
    let mut heap_count: usize = 0;
    let mut i = 0;

    while i < letters.len() {
        let b = letters[i];

        if b == b'?' {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "incomplete proof (contains `?`)".into(),
            });
        }

        if b == b'Z' {
            steps.push(ProofStep::Save);
            heap_count += 1;
            i += 1;
            continue;
        }

        let n = decode_integer(letters, &mut i, theorem)?;

        // Resolve proof integer n (1-based).
        if n == 0 {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "proof integer 0 is invalid".into(),
            });
        }

        if n <= mand_count {
            // Mandatory hypothesis: floats first, then essentials.
            let idx = n - 1;
            let label = if idx < frame.floats.len() {
                frame.floats[idx].label.clone()
            } else {
                frame.essentials[idx - frame.floats.len()].label.clone()
            };
            steps.push(ProofStep::Label(label));
        } else if n <= mand_count + label_count {
            // Label-block entry.
            let lid = n - mand_count - 1;
            steps.push(ProofStep::Label(labels[lid].clone()));
        } else {
            // Heap backreference.
            let hidx = n - mand_count - label_count - 1;
            if hidx >= heap_count {
                return Err(MmError::CompressedProofError {
                    theorem: theorem.to_owned(),
                    message: format!(
                        "heap backreference {hidx} out of range (heap has {heap_count} entries)"
                    ),
                });
            }
            steps.push(ProofStep::Heap(hidx));
        }
    }

    Ok(steps)
}

/// Decode one proof integer from `letters` starting at `*i`, advancing `*i`
/// past it. The caller must have checked that `*i < letters.len()`.
///
/// The accumulation is **checked**. A proof integer is a big-endian mixed-radix
/// number with no bound on its digit run, and the letter block is untrusted
/// input by construction: a long enough run of `U`–`Y` continuation digits
/// would otherwise panic in debug and, worse, silently wrap in release onto a
/// small — and therefore *valid* — hypothesis or heap index.
fn decode_integer(letters: &[u8], i: &mut usize, theorem: &str) -> Result<usize, MmError> {
    let mut n: usize = 0;
    loop {
        let c = letters[*i];
        *i += 1;
        // Terminal digits `A`-`T` (values 1-20) end the integer; continuation
        // digits `U`-`Y` (values 1-5) extend it.
        let (radix, digit, terminal) = if (b'A'..=b'T').contains(&c) {
            (20, (c - b'A') as usize + 1, true)
        } else if (b'U'..=b'Y').contains(&c) {
            (5, (c - b'U') as usize + 1, false)
        } else if c == b'Z' || c == b'?' {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: format!("unexpected `{}` mid-integer", c as char),
            });
        } else {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: format!("invalid character `{}` in letter block", c as char),
            });
        };

        n = n
            .checked_mul(radix)
            .and_then(|n| n.checked_add(digit))
            .ok_or_else(|| MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "proof integer is too large to address any proof step".into(),
            })?;

        if terminal {
            return Ok(n);
        }
        if *i >= letters.len() {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "letter block ends mid-integer".into(),
            });
        }
    }
}

/// Apply `target` (the asserted rule) within the proof of `current`, popping
/// the mandatory hypotheses off `stack`, checking everything, and pushing the
/// substituted conclusion.
fn apply_assertion(
    ctx: &Context<'_>,
    target: &Assertion,
    step: &str,
    stack: &mut Vec<Expr>,
    obs: &mut dyn ReplayObserver,
) -> Result<(), MmError> {
    let theorem = ctx.theorem();
    let frame = &target.frame;
    let n = frame.mandatory_count();
    if stack.len() < n {
        return Err(MmError::StackUnderflow {
            theorem: theorem.to_string(),
            step: step.to_string(),
        });
    }
    // Pop n args; they correspond to floats (first) then essentials (order).
    let args: Vec<Expr> = stack.split_off(stack.len() - n);

    // --- build substitution from floats ---
    let mut subst = Subst::new();
    for (i, f) in frame.floats.iter().enumerate() {
        let arg = &args[i];
        let arg_tc = typecode_of(arg).ok_or_else(|| MmError::TypecodeMismatch {
            theorem: theorem.to_string(),
            step: step.to_string(),
            var: f.var.clone(),
            expected: f.typecode.clone(),
            found: render(arg),
        })?;
        if arg_tc != f.typecode {
            return Err(MmError::TypecodeMismatch {
                theorem: theorem.to_string(),
                step: step.to_string(),
                var: f.var.clone(),
                expected: f.typecode.clone(),
                found: arg_tc.to_string(),
            });
        }
        let body = body_of(arg).unwrap_or(&[]).to_vec();
        subst.insert(f.var.clone(), body);
    }

    // --- check essentials ---
    for (j, h) in frame.essentials.iter().enumerate() {
        let arg = &args[frame.floats.len() + j];
        let expected = apply_subst(&h.expr, &subst);
        if &expected != arg {
            return Err(MmError::HypothesisMismatch {
                theorem: theorem.to_string(),
                step: step.to_string(),
                expected: render(&expected),
                found: render(arg),
            });
        }
    }

    // --- check distinct-variable ($d) conditions ---
    check_disjoints(ctx, target, step, &subst)?;

    // --- push the substituted conclusion ---
    stack.push(apply_subst(&target.conclusion, &subst));
    obs.assertion(
        step,
        target,
        &args,
        &subst,
        stack.last().unwrap(),
        stack.len(),
    );
    Ok(())
}

/// Check the target assertion's `$d` conditions under the substitution.
///
/// Metamath's rule: if the applied assertion requires `$d a b`, then for every
/// variable `x` occurring in `subst(a)` and every variable `y` occurring in
/// `subst(b)`:
///   1. `x` and `y` must be syntactically distinct, **and**
///   2. the *current* theorem's full in-scope `$d` set must contain `$d x y`.
///
/// (1) alone would be unsound; (2) is what propagates distinctness obligations
/// outward to the theorem's own signature.
///
/// Crucially, (2) consults the proving theorem's `scope_disjoints` — the **full**
/// in-scope `$d` set over *all* variables, including dummy / working variables
/// used only inside the proof — not the mandatory-filtered `frame.disjoints`.
/// The mandatory subset is too small: a perfectly legal `$d` over a proof-local
/// dummy variable would be invisible there, causing a spurious rejection.
///
/// That set lives on the [`Context`], built once per replay: it is the same for
/// every step of a proof, and rebuilding it here (with two `String`s allocated
/// per pair) cost roughly a quarter of `set.mm`'s verification time.
fn check_disjoints(
    ctx: &Context<'_>,
    target: &Assertion,
    step: &str,
    subst: &Subst,
) -> Result<(), MmError> {
    if target.frame.disjoints.is_empty() {
        return Ok(());
    }
    let current = ctx.current;
    let is_var = |s: &str| ctx.db.is_variable(s);

    for (a, b) in &target.frame.disjoints {
        let img_a = subst.get(a).map(|v| v.as_slice()).unwrap_or(&[]);
        let img_b = subst.get(b).map(|v| v.as_slice()).unwrap_or(&[]);
        let vars_a = vars_in_body(img_a, &is_var);
        let vars_b = vars_in_body(img_b, &is_var);

        for &x in &vars_a {
            for &y in &vars_b {
                // (1) substitutions may not share a variable.
                if x == y {
                    return Err(MmError::DisjointViolation {
                        theorem: current.label.clone(),
                        step: step.to_string(),
                        a: a.clone(),
                        b: b.clone(),
                        shared: x.to_string(),
                    });
                }
                // (2) the obligation must be discharged by the current frame.
                if !ctx.disjoints.contains(&ordered_pair(x, y)) {
                    return Err(MmError::DisjointViolation {
                        theorem: current.label.clone(),
                        step: step.to_string(),
                        a: a.clone(),
                        b: b.clone(),
                        shared: format!("{x},{y} not declared $d in `{}`", current.label),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Order a variable pair so `(a, b)` and `(b, a)` compare equal. Borrowed, so
/// normalising a pair for lookup costs no allocation.
fn ordered_pair<'a>(a: &'a str, b: &'a str) -> (&'a str, &'a str) {
    if a <= b { (a, b) } else { (b, a) }
}

/// Decode a single compressed proof integer (test helper). Delegates to
/// [`decode_integer`] rather than restating the digit scheme, so the tested
/// decoder is the one the verifier runs.
#[cfg(test)]
fn decode_compressed_integer(letters: &[u8]) -> Option<usize> {
    if letters.is_empty() {
        return None;
    }
    let mut i = 0;
    decode_integer(letters, &mut i, "<test>").ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    /// The "demo0" database from the Metamath book.
    const DEMO0: &str = "\
        $c 0 + = -> ( ) term wff |- $.\n\
        $v t r s P Q $.\n\
        tt $f term t $.\n\
        tr $f term r $.\n\
        ts $f term s $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        tze $a term 0 $.\n\
        tpl $a term ( t + r ) $.\n\
        weq $a wff t = r $.\n\
        wim $a wff ( P -> Q ) $.\n\
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
        a2 $a |- ( t + 0 ) = t $.\n\
        ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
        th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
            tt tt a1 mp mp $.\n\
    ";

    #[test]
    fn verify_demo0_normal() {
        let db = parse(DEMO0).unwrap();
        assert_eq!(verify_all(&db).unwrap(), 1);
    }

    #[test]
    fn decode_integers() {
        // A=1, B=2, ..., T=20
        assert_eq!(decode_compressed_integer(b"A"), Some(1));
        assert_eq!(decode_compressed_integer(b"B"), Some(2));
        assert_eq!(decode_compressed_integer(b"T"), Some(20));
        // UA=21, UB=22, ..., UT=40
        assert_eq!(decode_compressed_integer(b"UA"), Some(21));
        assert_eq!(decode_compressed_integer(b"UB"), Some(22));
        assert_eq!(decode_compressed_integer(b"UT"), Some(40));
        // VA=41, ..., YT=120
        assert_eq!(decode_compressed_integer(b"VA"), Some(41));
        assert_eq!(decode_compressed_integer(b"YT"), Some(120));
        // UUA=121
        assert_eq!(decode_compressed_integer(b"UUA"), Some(121));
    }

    #[test]
    fn verify_demo0_compressed() {
        // demo0's th1 with a compressed proof (no Z saves).
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= ( tze tpl weq wim a2 a1 mp ) ABCADAADAFABCADABCADAADEAFABCAAGHH $.\n\
        ";
        let db = parse(input).unwrap();
        assert_eq!(verify_all(&db).unwrap(), 1);
    }

    #[test]
    fn verify_compressed_with_save() {
        // demo0's th1 with Z saves reusing repeated subexpressions.
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= ( tze tpl weq wim a2 a1 mp ) ABCADZAADZAFZIIJEKABCAAGHH $.\n\
        ";
        let db = parse(input).unwrap();
        assert_eq!(verify_all(&db).unwrap(), 1);
    }

    #[test]
    fn verify_bad_proof() {
        let input = DEMO0.replace(
            "$= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
            tt tt a1 mp mp $.",
            "$= tt tze tpl tt weq $.",
        );
        let db = parse(&input).unwrap();
        assert!(verify_all(&db).is_err());
    }

    #[test]
    fn verify_unknown_label() {
        let input = "\
            $c term $.\n\
            $v t $.\n\
            tt $f term t $.\n\
            th $p term t $= tt bogus $.\n\
        ";
        let db = parse(input).unwrap();
        let err = verify_all(&db).unwrap_err();
        assert!(matches!(err, MmError::UnknownLabel { .. }));
    }
}
