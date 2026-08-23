//! Proof-producing RUP replay through the checked classical kernel interface.

use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{self, Snafu};
use covalence_logic_hol::{
    Kernel, KernelError, PropId, Ref, ThmId,
    builtin::{Op1, Op2},
};

use crate::{Clause, ClauseId, Step};

/// A clause retained alongside its checked consequence theorem.
#[derive(Clone, Debug)]
struct ClauseRecord {
    literals: Box<[PropId]>,
    term: Ref,
    theorem: ThmId,
}

/// A rejected CNF construction or LRAT proof step.
#[non_exhaustive]
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum Error {
    /// The checked HOL operation rejected the requested construction.
    #[snafu(transparent)]
    Kernel { source: KernelError },
    /// An LRAT literal cannot be interpreted as a signed HOL reference.
    #[snafu(display("LRAT literal {literal} is not a proposition identifier"))]
    InvalidLiteral { literal: i64 },
    /// A CNF atom uses syntax reserved for the canonical CNF spine.
    #[snafu(display("reference {reference:?} is not a canonical CNF atom"))]
    NonAtomicLiteral { reference: Ref },
    /// A learned clause identifier is not monotonically fresh.
    #[snafu(display("clause identifier {id} is not fresh"))]
    NonFreshId { id: ClauseId },
    /// A proof step names a clause which has been forgotten or never existed.
    #[snafu(display("step {step} names clause {clause}, which is not live"))]
    UnknownClause { step: ClauseId, clause: ClauseId },
    /// An ordered hint is neither unit nor conflicting under the current trail.
    #[snafu(display("hint {clause} in step {step} is not unit under the trail"))]
    UselessHint { step: ClauseId, clause: ClauseId },
    /// Ordered reverse unit propagation does not reach a conflict.
    #[snafu(display("step {step} does not propagate to a conflict"))]
    NoConflict { step: ClauseId },
    /// General RAT is deliberately outside the consequence-theorem interface.
    #[snafu(display("step {step} uses unsupported RAT admission"))]
    UnsupportedRat { step: ClauseId },
    /// The proof ends without a checked empty-clause consequence.
    #[snafu(display("the proof does not derive the empty clause"))]
    NoRefutation,
    /// The supplied root is not a canonical CNF opcode tree.
    #[snafu(display("reference {formula:?} is not a canonical CNF formula"))]
    NonCanonicalFormula { formula: Ref },
}

/// Incrementally constructs a deterministic CNF term around a checked kernel.
#[derive(Debug)]
pub struct CnfBuilder {
    kernel: Kernel,
    bool_ty: Ref,
    clauses: Vec<(Box<[PropId]>, Ref)>,
}

impl CnfBuilder {
    /// Starts a CNF formula whose terms have classifier `bool_ty`.
    #[must_use]
    pub const fn new(kernel: Kernel, bool_ty: Ref) -> Self {
        Self {
            kernel,
            bool_ty,
            clauses: Vec::new(),
        }
    }

    /// Appends one clause, preserving its literal order in the canonical OR tree.
    ///
    /// # Errors
    ///
    /// Returns an error if a literal is not a local Boolean atom or construction fails.
    pub fn clause(&mut self, literals: &[PropId]) -> Result<ClauseId, Error> {
        for literal in literals {
            validate_atom(&self.kernel, *literal)?;
        }
        let term = build_clause(&mut self.kernel, self.bool_ty, literals)?;
        self.clauses
            .push((literals.to_vec().into_boxed_slice(), term));
        Ok(u64::try_from(self.clauses.len()).unwrap_or(u64::MAX))
    }

    /// Finishes the CNF spine and returns an incremental LRAT prover.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula or its initial consequence theorems cannot be built.
    pub fn refute(mut self) -> Result<LratProver, Error> {
        let true_ref = self.kernel.bool(self.bool_ty, true)?;
        let false_ref = self.kernel.bool(self.bool_ty, false)?;
        let terms: Vec<_> = self.clauses.iter().map(|(_, term)| *term).collect();
        let formula = build_binary(&mut self.kernel, self.bool_ty, Op2::And, &terms, true_ref)?;
        let formula_prop =
            PropId::positive(formula).map_err(|_| Error::InvalidLiteral { literal: i64::MIN })?;
        let root = self.kernel.assume(formula_prop)?;
        let mut projected = Vec::with_capacity(self.clauses.len());
        project_clauses(&mut self.kernel, root, formula, &terms, &mut projected)?;

        let mut live = BTreeMap::new();
        let mut refutation = None;
        for (index, ((literals, term), theorem)) in
            self.clauses.into_iter().zip(projected).enumerate()
        {
            let theorem = expand_clause(&mut self.kernel, theorem, term, false_ref)?;
            let id = u64::try_from(index + 1).unwrap_or(u64::MAX);
            if literals.is_empty() {
                refutation = Some(self.kernel.weaken(theorem, &[], &[])?);
            }
            live.insert(
                id,
                ClauseRecord {
                    literals,
                    term,
                    theorem,
                },
            );
        }
        Ok(LratProver {
            kernel: self.kernel,
            formula,
            bool_ty: self.bool_ty,
            true_ref,
            false_ref,
            live,
            high_water: u64::try_from(terms.len()).unwrap_or(u64::MAX),
            refutation,
        })
    }
}

/// An incremental userspace LRAT prover backed only by checked HOL rules.
#[derive(Debug)]
pub struct LratProver {
    kernel: Kernel,
    formula: Ref,
    bool_ty: Ref,
    true_ref: Ref,
    false_ref: Ref,
    live: BTreeMap<ClauseId, ClauseRecord>,
    high_water: ClauseId,
    refutation: Option<ThmId>,
}

impl LratProver {
    /// Returns the stable root formula reference.
    #[must_use]
    pub const fn formula(&self) -> Ref {
        self.formula
    }

    /// Returns the canonical truth reference retained by this proof.
    #[must_use]
    pub const fn truth(&self) -> Ref {
        self.true_ref
    }

    /// Returns the canonical falsehood reference retained by this proof.
    #[must_use]
    pub const fn falsehood(&self) -> Ref {
        self.false_ref
    }

    /// Borrows the checked kernel.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the stable HOL term for one live clause.
    #[must_use]
    pub fn clause_term(&self, id: ClauseId) -> Option<Ref> {
        self.live.get(&id).map(|record| record.term)
    }

    /// Applies one parsed LRAT step.
    ///
    /// # Errors
    ///
    /// Returns a typed rejection. RAT steps are always rejected in this version.
    pub fn apply(&mut self, step: &Step) -> Result<(), Error> {
        match step {
            Step::LearnRup {
                id,
                clause,
                ordered_hints,
            } => self.learn_rup(*id, clause, ordered_hints),
            Step::LearnRat { id, .. } => Err(Error::UnsupportedRat { step: *id }),
            Step::Forget { ids } => self.forget(ids),
        }
    }

    /// Admits one fresh clause by ordered reverse unit propagation.
    ///
    /// # Errors
    ///
    /// Returns the first structural or checked-proof rejection without changing live clauses.
    pub fn learn_rup(
        &mut self,
        id: ClauseId,
        clause: &Clause,
        ordered_hints: &[ClauseId],
    ) -> Result<(), Error> {
        if id <= self.high_water {
            return Err(Error::NonFreshId { id });
        }
        let literals = clause_props(clause)?;
        for literal in &literals {
            validate_atom(&self.kernel, *literal)?;
        }
        let mut trail = BTreeMap::<PropId, ThmId>::new();
        let mut temporary = Vec::new();
        for literal in &literals {
            let falsifying = literal.negated();
            let theorem = self.kernel.assume(falsifying)?;
            temporary.push(theorem);
            trail.insert(falsifying, theorem);
        }

        let mut conflict = None;
        for hint in ordered_hints {
            let record = self.live.get(hint).ok_or(Error::UnknownClause {
                step: id,
                clause: *hint,
            })?;
            if record
                .literals
                .iter()
                .any(|literal| trail.contains_key(literal))
            {
                return Err(Error::UselessHint {
                    step: id,
                    clause: *hint,
                });
            }
            let mut theorem = record.theorem;
            let mut open = Vec::new();
            for literal in record.literals.iter().copied() {
                if let Some(reason) = trail.get(&literal.negated()) {
                    theorem = self.kernel.resolve(theorem, *reason, literal)?;
                    temporary.push(theorem);
                } else {
                    open.push(literal);
                }
            }
            match open.as_slice() {
                [] => {
                    conflict = Some(theorem);
                    break;
                }
                [unit] => {
                    trail.insert(*unit, theorem);
                }
                _ => {
                    return Err(Error::UselessHint {
                        step: id,
                        clause: *hint,
                    });
                }
            }
        }
        let mut theorem = conflict.ok_or(Error::NoConflict { step: id })?;
        for literal in &literals {
            let falsifying = literal.negated();
            theorem = if self.kernel.theorem(theorem)?.premises.contains(&falsifying) {
                self.kernel.discharge(theorem, falsifying)?
            } else {
                self.kernel.weaken(theorem, &[], &[*literal])?
            };
            temporary.push(theorem);
        }

        temporary.sort_unstable();
        temporary.dedup();
        temporary.retain(|candidate| *candidate != theorem);
        self.kernel.remove_theorems(&temporary)?;

        let term = build_clause(&mut self.kernel, self.bool_ty, &literals)?;
        self.live.insert(
            id,
            ClauseRecord {
                literals: literals.into_boxed_slice(),
                term,
                theorem,
            },
        );
        self.high_water = id;
        if clause.is_empty() {
            self.refutation = Some(self.kernel.weaken(theorem, &[], &[])?);
        }
        Ok(())
    }

    /// Forgets live clauses and their ephemeral theorem handles atomically.
    ///
    /// # Errors
    ///
    /// Returns an error if any identifier is repeated or not live.
    pub fn forget(&mut self, ids: &[ClauseId]) -> Result<(), Error> {
        let unique: BTreeSet<_> = ids.iter().copied().collect();
        if unique.len() != ids.len() {
            let clause = ids
                .iter()
                .copied()
                .find(|id| ids.iter().filter(|other| *other == id).count() > 1)
                .unwrap_or(0);
            return Err(Error::UnknownClause {
                step: self.high_water,
                clause,
            });
        }
        let theorems = ids
            .iter()
            .map(|id| {
                self.live
                    .get(id)
                    .map(|record| record.theorem)
                    .ok_or(Error::UnknownClause {
                        step: self.high_water,
                        clause: *id,
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.kernel.remove_theorems(&theorems)?;
        for id in ids {
            self.live.remove(id);
        }
        Ok(())
    }

    /// Requires a checked empty-clause consequence and returns the sealed result.
    ///
    /// # Errors
    ///
    /// Returns [`Error::NoRefutation`] unless the witness is exactly `[formula] |- []`.
    pub fn done(self) -> Result<UnsatFormula, Error> {
        let theorem = self.refutation.ok_or(Error::NoRefutation)?;
        let sequent = self.kernel.theorem(theorem)?;
        let formula = PropId::positive(self.formula).map_err(|_| Error::NoRefutation)?;
        if sequent.premises != [formula] || !sequent.conclusions.is_empty() {
            return Err(Error::NoRefutation);
        }
        Ok(UnsatFormula {
            kernel: self.kernel,
            formula: self.formula,
        })
    }
}

/// A kernel containing a checked proof that `formula` is false.
#[derive(Debug)]
pub struct UnsatFormula {
    /// The checked kernel which owns `formula` and its proof state.
    pub kernel: Kernel,
    /// Stable reference to the original canonical CNF term.
    pub formula: Ref,
}

/// Reconstructs the canonical signed clauses encoded beneath `formula`.
///
/// # Errors
///
/// Returns an error if the reference is not a canonical AND-of-OR opcode tree.
pub fn reconstruct(kernel: &Kernel, formula: Ref) -> Result<Vec<Vec<PropId>>, Error> {
    let mut clause_terms = Vec::new();
    flatten_formula(kernel, formula, &mut clause_terms)?;
    clause_terms
        .into_iter()
        .map(|term| {
            let mut clause = Vec::new();
            flatten_clause(kernel, term, &mut clause)?;
            Ok(clause)
        })
        .collect()
}

fn clause_props(clause: &Clause) -> Result<Vec<PropId>, Error> {
    clause
        .iter()
        .map(|literal| {
            PropId::from_raw(literal.get()).map_err(|_| Error::InvalidLiteral {
                literal: literal.get(),
            })
        })
        .collect()
}

fn validate_atom(kernel: &Kernel, proposition: PropId) -> Result<(), Error> {
    let reference = proposition.reference();
    if kernel.arena().op1(reference).is_some()
        || kernel.arena().op2(reference).is_some()
        || kernel.arena().bool_value(reference).is_some()
    {
        return Err(Error::NonAtomicLiteral { reference });
    }
    Ok(())
}

fn literal_term(kernel: &mut Kernel, literal: PropId) -> Result<Ref, Error> {
    if literal.is_positive() {
        Ok(literal.reference())
    } else {
        Ok(kernel.op1(Op1::Not, literal.reference())?)
    }
}

fn build_clause(kernel: &mut Kernel, bool_ty: Ref, literals: &[PropId]) -> Result<Ref, Error> {
    let false_ref = kernel.bool(bool_ty, false)?;
    let terms = literals
        .iter()
        .copied()
        .map(|literal| literal_term(kernel, literal))
        .collect::<Result<Vec<_>, _>>()?;
    build_binary(kernel, bool_ty, Op2::Or, &terms, false_ref)
}

fn build_binary(
    kernel: &mut Kernel,
    _bool_ty: Ref,
    op: Op2,
    terms: &[Ref],
    identity: Ref,
) -> Result<Ref, Error> {
    let Some((&last, prefix)) = terms.split_last() else {
        return Ok(identity);
    };
    prefix.iter().rev().try_fold(last, |right, left| {
        kernel.op2(op, *left, right).map_err(Error::from)
    })
}

fn project_clauses(
    kernel: &mut Kernel,
    theorem: ThmId,
    formula: Ref,
    clauses: &[Ref],
    output: &mut Vec<ThmId>,
) -> Result<(), Error> {
    match clauses {
        [] => Ok(()),
        [_] => {
            output.push(theorem);
            Ok(())
        }
        [_, rest @ ..] => {
            let proposition =
                PropId::positive(formula).map_err(|_| Error::NonCanonicalFormula { formula })?;
            let children: Vec<_> = kernel
                .children(formula)
                .ok_or(Error::NonCanonicalFormula { formula })?
                .collect();
            let left = kernel.expand_conclusion(theorem, proposition, Some(false))?;
            let right = kernel.expand_conclusion(theorem, proposition, Some(true))?;
            output.push(left);
            project_clauses(kernel, right, children[1], rest, output)
        }
    }
}

fn expand_clause(
    kernel: &mut Kernel,
    theorem: ThmId,
    term: Ref,
    false_ref: Ref,
) -> Result<ThmId, Error> {
    let proposition =
        PropId::positive(term).map_err(|_| Error::NonCanonicalFormula { formula: term })?;
    if term == false_ref
        || kernel.arena().bool_value(term) == Some(false)
        || kernel.arena().op1(term) == Some(Op1::Not)
    {
        return kernel
            .expand_conclusion(theorem, proposition, None)
            .map_err(Error::from);
    }
    if kernel.arena().op2(term) == Some(Op2::Or) {
        let children: Vec<_> = kernel
            .children(term)
            .ok_or(Error::NonCanonicalFormula { formula: term })?
            .collect();
        let theorem = kernel.expand_conclusion(theorem, proposition, None)?;
        let theorem = expand_clause(kernel, theorem, children[0], false_ref)?;
        return expand_clause(kernel, theorem, children[1], false_ref);
    }
    Ok(theorem)
}

fn flatten_formula(kernel: &Kernel, formula: Ref, output: &mut Vec<Ref>) -> Result<(), Error> {
    if kernel.arena().bool_value(formula) == Some(true) {
        if !output.is_empty() {
            return Err(Error::NonCanonicalFormula { formula });
        }
        return Ok(());
    }
    if kernel.arena().op2(formula) == Some(Op2::And) {
        let children: Vec<_> = kernel
            .children(formula)
            .ok_or(Error::NonCanonicalFormula { formula })?
            .collect();
        let mut clause = Vec::new();
        flatten_clause(kernel, children[0], &mut clause)?;
        output.push(children[0]);
        return flatten_formula(kernel, children[1], output);
    }
    output.push(formula);
    Ok(())
}

fn flatten_clause(kernel: &Kernel, term: Ref, output: &mut Vec<PropId>) -> Result<(), Error> {
    if kernel.arena().bool_value(term) == Some(false) {
        return Ok(());
    }
    if kernel.arena().op2(term) == Some(Op2::Or) {
        let children: Vec<_> = kernel
            .children(term)
            .ok_or(Error::NonCanonicalFormula { formula: term })?
            .collect();
        decode_literal(kernel, children[0], output)?;
        let before = output.len();
        flatten_clause(kernel, children[1], output)?;
        if output.len() == before {
            return Err(Error::NonCanonicalFormula { formula: term });
        }
        return Ok(());
    }
    decode_literal(kernel, term, output)
}

fn decode_literal(kernel: &Kernel, term: Ref, output: &mut Vec<PropId>) -> Result<(), Error> {
    if kernel.arena().op1(term) == Some(Op1::Not) {
        let child = kernel
            .children(term)
            .and_then(|mut children| children.next())
            .ok_or(Error::NonCanonicalFormula { formula: term })?;
        validate_atom(
            kernel,
            PropId::positive(child).map_err(|_| Error::NonCanonicalFormula { formula: term })?,
        )?;
        output.push(
            PropId::positive(child)
                .map_err(|_| Error::NonCanonicalFormula { formula: term })?
                .negated(),
        );
        return Ok(());
    }
    let atom = PropId::positive(term).map_err(|_| Error::NonCanonicalFormula { formula: term })?;
    validate_atom(kernel, atom)?;
    output.push(atom);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Literal, oracle, parse::Step};

    fn fixture() -> (Kernel, Ref, PropId, PropId) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let p = kernel.tm_fv(1, bool_ty).unwrap();
        let q = kernel.tm_fv(2, bool_ty).unwrap();
        (
            kernel,
            bool_ty,
            PropId::positive(p).unwrap(),
            PropId::positive(q).unwrap(),
        )
    }

    fn clause(literals: &[PropId]) -> Clause {
        Clause::from_signed(literals.iter().map(|literal| literal.get())).unwrap()
    }

    #[test]
    fn builder_reconstructs_the_exact_canonical_spines() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p, q.negated()]).unwrap();
        builder.clause(&[]).unwrap();
        let prover = builder.refute().unwrap();
        assert_eq!(
            reconstruct(prover.kernel(), prover.formula()).unwrap(),
            vec![vec![p, q.negated()], vec![]]
        );
        let formula = prover.formula();
        assert_eq!(prover.done().unwrap().formula, formula);
    }

    #[test]
    fn ordered_rup_refutes_unit_contradiction() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        builder.clause(&[p.negated()]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover
            .apply(&Step::LearnRup {
                id: 3,
                clause: clause(&[]),
                ordered_hints: vec![1, 2],
            })
            .unwrap();
        prover.forget(&[3]).unwrap();
        let result = prover.done().unwrap();
        assert_eq!(
            reconstruct(&result.kernel, result.formula).unwrap(),
            vec![vec![p], vec![p.negated()]]
        );
    }

    #[test]
    fn rup_can_learn_a_nonempty_weakened_clause() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.learn_rup(2, &clause(&[p, q]), &[1]).unwrap();
        assert!(prover.clause_term(2).is_some());
    }

    #[test]
    fn rat_is_explicitly_outside_the_consequence_api() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let step = Step::LearnRat {
            id: 2,
            clause: clause(&[p]),
            pivot: Literal::new(p.get()).unwrap(),
            prefix_rup_hints: vec![],
            groups: vec![],
        };
        assert!(matches!(
            prover.apply(&step),
            Err(Error::UnsupportedRat { step: 2 })
        ));
    }

    #[test]
    fn rup_acceptance_matches_the_legacy_oracle() {
        let (kernel, bool_ty, p, _) = fixture();
        let positive = clause(&[p]);
        let negative = clause(&[p.negated()]);
        let formula = Formula::new([positive.clone(), negative.clone()]);
        let mut oracle = oracle::Kernel::open(&formula);
        assert_eq!(oracle.clause(1), Some(&positive));

        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        builder.clause(&[p.negated()]).unwrap();
        let mut prover = builder.refute().unwrap();
        let empty = clause(&[]);

        assert_eq!(
            prover.learn_rup(3, &empty, &[99]).is_ok(),
            oracle.learn_rup(3, &empty, &[99]).is_ok()
        );
        assert_eq!(
            prover.learn_rup(3, &empty, &[1, 2]).is_ok(),
            oracle.learn_rup(3, &empty, &[1, 2]).is_ok()
        );
        assert!(prover.done().is_ok());
        assert!(oracle.refuted());
    }
}
