//! Proof-producing RUP replay through the checked classical kernel interface.

use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{self, Snafu};
use covalence_logic_hol::{
    Kernel, KernelError, PropId, Ref, ThmId,
    builtin::{Op1, Op2},
};

use crate::{Clause, ClauseId, Literal, Step};

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
    /// A DIMACS variable has no registered HOL atom.
    #[snafu(display("DIMACS variable {variable} has no HOL atom"))]
    UnknownVariable { variable: u64 },
    /// A DIMACS variable is rebound to a different HOL atom.
    #[snafu(display("DIMACS variable {variable} is already bound"))]
    ConflictingVariable { variable: u64 },
    /// A CNF atom uses syntax reserved for the canonical CNF spine.
    #[snafu(display("reference {reference:?} is not a canonical CNF atom"))]
    NonAtomicLiteral { reference: Ref },
    /// A learned clause identifier is not monotonically fresh.
    #[snafu(display("clause identifier {id} is not fresh"))]
    NonFreshId { id: ClauseId },
    /// The initial clause identifier space is exhausted.
    #[snafu(display("CNF has too many clauses"))]
    TooManyClauses,
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
    clauses: Vec<Box<[PropId]>>,
    variables: BTreeMap<u64, Ref>,
}

impl CnfBuilder {
    /// Starts a CNF formula whose terms have classifier `bool_ty`.
    #[must_use]
    pub const fn new(kernel: Kernel, bool_ty: Ref) -> Self {
        Self {
            kernel,
            bool_ty,
            clauses: Vec::new(),
            variables: BTreeMap::new(),
        }
    }

    /// Binds a standard positive DIMACS variable to one positive HOL atom.
    ///
    /// # Errors
    ///
    /// Returns an error for variable zero, a non-atomic reference, or rebinding.
    pub fn bind_variable(&mut self, variable: u64, atom: Ref) -> Result<(), Error> {
        if variable == 0 {
            return Err(Error::UnknownVariable { variable });
        }
        validate_atom(
            &self.kernel,
            PropId::positive(atom).map_err(|_| Error::InvalidLiteral { literal: i64::MIN })?,
        )?;
        match self.variables.get(&variable) {
            Some(bound) if *bound != atom => Err(Error::ConflictingVariable { variable }),
            Some(_) => Ok(()),
            None => {
                self.variables.insert(variable, atom);
                Ok(())
            }
        }
    }

    /// Appends a standard DIMACS clause through the registered atom mapping.
    ///
    /// # Errors
    ///
    /// Returns an error if a variable is unbound or clause construction fails.
    pub fn dimacs_clause(&mut self, literals: &[Literal]) -> Result<ClauseId, Error> {
        let propositions = map_dimacs(&self.variables, literals.iter().copied())?;
        self.clause(&propositions)
    }

    /// Appends one clause, normalizing its literals by sorting and deduplication.
    ///
    /// # Errors
    ///
    /// Returns an error if a literal is not a local Boolean atom or construction fails.
    pub fn clause(&mut self, literals: &[PropId]) -> Result<ClauseId, Error> {
        for literal in literals {
            validate_atom(&self.kernel, *literal)?;
        }
        let id = u64::try_from(self.clauses.len())
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(Error::TooManyClauses)?;
        let mut canonical = literals.to_vec();
        canonical.sort_unstable();
        canonical.dedup();
        self.clauses.push(canonical.into_boxed_slice());
        Ok(id)
    }

    /// Finishes the CNF spine and returns an incremental LRAT prover.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula or its initial consequence theorems cannot be built.
    pub fn refute(mut self) -> Result<LratProver, Error> {
        let true_ref = self.kernel.bool(self.bool_ty, true)?;
        let false_ref = self.kernel.bool(self.bool_ty, false)?;
        let mut canonical_clauses = self.clauses.clone();
        canonical_clauses.sort_unstable();
        canonical_clauses.dedup();
        let mut terms = Vec::with_capacity(canonical_clauses.len());
        for literals in &canonical_clauses {
            terms.push(build_clause(&mut self.kernel, literals, false_ref)?);
        }
        let formula = build_binary(&mut self.kernel, Op2::And, &terms, true_ref)?;
        let formula_prop =
            PropId::positive(formula).map_err(|_| Error::InvalidLiteral { literal: i64::MIN })?;
        let root = self.kernel.assume(formula_prop)?;
        let mut projected = Vec::with_capacity(canonical_clauses.len());
        project_clauses(&mut self.kernel, root, formula, &terms, &mut projected)?;

        let mut canonical = BTreeMap::new();
        for ((literals, term), theorem) in canonical_clauses
            .iter()
            .cloned()
            .zip(terms.iter().copied())
            .zip(projected)
        {
            let theorem = self.kernel.flatten_conclusion(
                theorem,
                PropId::positive(term).map_err(|_| Error::NonCanonicalFormula { formula: term })?,
            )?;
            canonical.insert(literals, (term, theorem));
        }

        let mut live = BTreeMap::new();
        let mut refutation = None;
        for (index, literals) in self.clauses.into_iter().enumerate() {
            let (term, source) = canonical[&literals];
            let theorem = self.kernel.weaken(source, &[], &[])?;
            let id = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(Error::TooManyClauses)?;
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
        let high_water = u64::try_from(live.len()).map_err(|_| Error::TooManyClauses)?;
        Ok(LratProver {
            kernel: self.kernel,
            formula,
            true_ref,
            false_ref,
            variables: self.variables,
            live,
            high_water,
            refutation,
        })
    }
}

/// An incremental userspace LRAT prover backed only by checked HOL rules.
#[derive(Debug)]
pub struct LratProver {
    kernel: Kernel,
    formula: Ref,
    true_ref: Ref,
    false_ref: Ref,
    variables: BTreeMap<u64, Ref>,
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
        let literals = map_dimacs(&self.variables, clause.iter())?;
        self.learn_rup_props(id, &literals, ordered_hints)
    }

    /// Admits one fresh clause expressed directly in the native `PropId` convention.
    ///
    /// # Errors
    ///
    /// Returns the first structural or checked-proof rejection transactionally.
    pub fn learn_rup_props(
        &mut self,
        id: ClauseId,
        literals: &[PropId],
        ordered_hints: &[ClauseId],
    ) -> Result<(), Error> {
        if id <= self.high_water {
            return Err(Error::NonFreshId { id });
        }
        let mut literals = literals.to_vec();
        literals.sort_unstable();
        literals.dedup();
        for literal in &literals {
            validate_atom(&self.kernel, *literal)?;
        }
        let mut temporary = Vec::new();
        let result = self.derive_rup(id, &literals, ordered_hints, &mut temporary);

        let theorem = match result {
            Ok(theorem) => theorem,
            Err(error) => {
                self.reclaim(&mut temporary, None)?;
                return Err(error);
            }
        };

        let term = match build_clause(&mut self.kernel, &literals, self.false_ref) {
            Ok(term) => term,
            Err(error) => {
                self.reclaim(&mut temporary, None)?;
                return Err(error);
            }
        };
        let refutation = if literals.is_empty() {
            match self.kernel.weaken(theorem, &[], &[]) {
                Ok(refutation) => Some(refutation),
                Err(source) => {
                    self.reclaim(&mut temporary, None)?;
                    return Err(Error::Kernel { source });
                }
            }
        } else {
            None
        };
        self.reclaim(&mut temporary, Some(theorem))?;

        let is_empty = literals.is_empty();
        self.live.insert(
            id,
            ClauseRecord {
                literals: literals.into_boxed_slice(),
                term,
                theorem,
            },
        );
        self.high_water = id;
        if is_empty {
            self.refutation = refutation;
        }
        Ok(())
    }

    fn reclaim(&mut self, temporary: &mut Vec<ThmId>, keep: Option<ThmId>) -> Result<(), Error> {
        temporary.sort_unstable();
        temporary.dedup();
        if let Some(keep) = keep {
            temporary.retain(|candidate| *candidate != keep);
        }
        if !temporary.is_empty() {
            self.kernel.remove_theorems(temporary)?;
        }
        Ok(())
    }

    fn derive_rup(
        &mut self,
        id: ClauseId,
        literals: &[PropId],
        ordered_hints: &[ClauseId],
        temporary: &mut Vec<ThmId>,
    ) -> Result<ThmId, Error> {
        let mut trail = BTreeMap::<PropId, ThmId>::new();
        for literal in literals {
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
        for literal in literals {
            let falsifying = literal.negated();
            theorem = if self.kernel.theorem(theorem)?.premises.contains(&falsifying) {
                self.kernel.discharge(theorem, falsifying)?
            } else {
                self.kernel.weaken(theorem, &[], &[*literal])?
            };
            temporary.push(theorem);
        }
        Ok(theorem)
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
            refutation: theorem,
        })
    }
}

/// A kernel containing a checked proof that `formula` is false.
#[derive(Debug)]
pub struct UnsatFormula {
    kernel: Kernel,
    formula: Ref,
    refutation: ThmId,
}

impl UnsatFormula {
    /// Borrows the checked kernel which owns the result.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Returns the stable canonical CNF reference.
    #[must_use]
    pub const fn formula(&self) -> Ref {
        self.formula
    }

    /// Reconstructs the canonical proposition clauses.
    ///
    /// # Errors
    ///
    /// Returns an error if internal CNF syntax is not canonical.
    pub fn reconstruct(&self) -> Result<Vec<Vec<PropId>>, Error> {
        reconstruct(&self.kernel, self.formula)
    }

    /// Rechecks that the retained private witness is `[formula] |- []`.
    ///
    /// # Errors
    ///
    /// Returns an error if the checked witness invariant is absent.
    pub fn verify(&self) -> Result<(), Error> {
        let sequent = self.kernel.theorem(self.refutation)?;
        let formula = PropId::positive(self.formula).map_err(|_| Error::NoRefutation)?;
        if sequent.premises == [formula] && sequent.conclusions.is_empty() {
            Ok(())
        } else {
            Err(Error::NoRefutation)
        }
    }
}

/// Reconstructs the canonical signed clauses encoded beneath `formula`.
///
/// # Errors
///
/// Returns an error if the reference is not a canonical AND-of-OR opcode tree.
pub fn reconstruct(kernel: &Kernel, formula: Ref) -> Result<Vec<Vec<PropId>>, Error> {
    let mut clause_terms = Vec::new();
    flatten_formula(kernel, formula, &mut clause_terms)?;
    let clauses = clause_terms
        .into_iter()
        .map(|term| {
            let mut clause = Vec::new();
            flatten_clause(kernel, term, &mut clause)?;
            if clause.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(Error::NonCanonicalFormula { formula });
            }
            Ok(clause)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if clauses.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(Error::NonCanonicalFormula { formula });
    }
    Ok(clauses)
}

fn map_dimacs(
    variables: &BTreeMap<u64, Ref>,
    literals: impl IntoIterator<Item = Literal>,
) -> Result<Vec<PropId>, Error> {
    literals
        .into_iter()
        .map(|literal| {
            let variable = literal.variable();
            let atom = *variables
                .get(&variable)
                .ok_or(Error::UnknownVariable { variable })?;
            let positive = PropId::positive(atom).map_err(|_| Error::InvalidLiteral {
                literal: literal.get(),
            })?;
            Ok(if literal.get() > 0 {
                positive
            } else {
                positive.negated()
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

fn build_clause(kernel: &mut Kernel, literals: &[PropId], false_ref: Ref) -> Result<Ref, Error> {
    let terms = literals
        .iter()
        .copied()
        .map(|literal| literal_term(kernel, literal))
        .collect::<Result<Vec<_>, _>>()?;
    build_binary(kernel, Op2::Or, &terms, false_ref)
}

fn build_binary(kernel: &mut Kernel, op: Op2, terms: &[Ref], identity: Ref) -> Result<Ref, Error> {
    terms.iter().rev().try_fold(identity, |right, left| {
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

fn flatten_formula(kernel: &Kernel, formula: Ref, output: &mut Vec<Ref>) -> Result<(), Error> {
    if kernel.arena().bool_value(formula) == Some(true) {
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
    Err(Error::NonCanonicalFormula { formula })
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
        return flatten_clause(kernel, children[1], output);
    }
    Err(Error::NonCanonicalFormula { formula: term })
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

    fn dimacs(literals: impl IntoIterator<Item = i64>) -> Clause {
        Clause::from_signed(literals).unwrap()
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
            vec![vec![], vec![p, q.negated()]]
        );
        let formula = prover.formula();
        assert_eq!(prover.done().unwrap().formula(), formula);
    }

    #[test]
    fn reordered_and_duplicated_input_has_one_syntax() {
        let (kernel_a, bool_ty_a, p_a, q_a) = fixture();
        let mut a = CnfBuilder::new(kernel_a, bool_ty_a);
        a.clause(&[q_a, p_a, p_a]).unwrap();
        a.clause(&[p_a.negated()]).unwrap();
        a.clause(&[q_a, p_a]).unwrap();
        let a = a.refute().unwrap();

        let (kernel_b, bool_ty_b, p_b, q_b) = fixture();
        let mut b = CnfBuilder::new(kernel_b, bool_ty_b);
        b.clause(&[p_b.negated()]).unwrap();
        b.clause(&[p_b, q_b]).unwrap();
        let b = b.refute().unwrap();

        assert_eq!(a.formula(), b.formula());
        assert_eq!(a.kernel().arena(), b.kernel().arena());
        assert_eq!(
            reconstruct(a.kernel(), a.formula()).unwrap(),
            reconstruct(b.kernel(), b.formula()).unwrap()
        );
    }

    #[test]
    fn explicit_terminators_distinguish_empty_formula_and_empty_clause() {
        let (kernel, bool_ty, _, _) = fixture();
        let empty_formula = CnfBuilder::new(kernel, bool_ty).refute().unwrap();
        assert_eq!(
            empty_formula
                .kernel()
                .arena()
                .bool_value(empty_formula.formula()),
            Some(true)
        );
        assert_eq!(
            reconstruct(empty_formula.kernel(), empty_formula.formula()).unwrap(),
            Vec::<Vec<PropId>>::new()
        );

        let (kernel, bool_ty, _, _) = fixture();
        let mut empty_clause = CnfBuilder::new(kernel, bool_ty);
        empty_clause.clause(&[]).unwrap();
        let empty_clause = empty_clause.refute().unwrap();
        assert_ne!(empty_formula.formula(), empty_clause.formula());
        assert_eq!(
            reconstruct(empty_clause.kernel(), empty_clause.formula()).unwrap(),
            vec![vec![]]
        );
    }

    #[test]
    fn reconstruction_rejects_noncanonical_duplicates() {
        let (mut kernel, bool_ty, p, _) = fixture();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let clause = kernel.op2(Op2::Or, p.reference(), falsehood).unwrap();
        let repeated = kernel.op2(Op2::And, clause, truth).unwrap();
        let formula = kernel.op2(Op2::And, clause, repeated).unwrap();
        assert!(matches!(
            reconstruct(&kernel, formula),
            Err(Error::NonCanonicalFormula { .. })
        ));

        let repeated_literal = kernel.op2(Op2::Or, p.reference(), clause).unwrap();
        let formula = kernel.op2(Op2::And, repeated_literal, truth).unwrap();
        assert!(matches!(
            reconstruct(&kernel, formula),
            Err(Error::NonCanonicalFormula { .. })
        ));
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
                clause: dimacs([]),
                ordered_hints: vec![1, 2],
            })
            .unwrap();
        prover.forget(&[3]).unwrap();
        let result = prover.done().unwrap();
        assert_eq!(
            result.reconstruct().unwrap(),
            vec![vec![p], vec![p.negated()]]
        );
        result.verify().unwrap();
    }

    #[test]
    fn rup_can_learn_a_nonempty_weakened_clause() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.learn_rup_props(2, &[p, q], &[1]).unwrap();
        assert!(prover.clause_term(2).is_some());
    }

    #[test]
    fn parsed_dimacs_polarity_uses_the_explicit_atom_map() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.bind_variable(1, p.reference()).unwrap();
        builder.bind_variable(2, q.reference()).unwrap();
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.learn_rup(2, &dimacs([1, 2]), &[1]).unwrap();
        let theorem = prover.live[&2].theorem;
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(
            prover.kernel.theorem(theorem).unwrap().conclusions,
            expected
        );
    }

    #[test]
    fn rejected_rup_reclaims_every_temporary_theorem() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let reusable = prover.kernel.assume(p).unwrap();
        prover.kernel.remove_theorems(&[reusable]).unwrap();
        assert!(matches!(
            prover.learn_rup_props(2, &[p], &[99]),
            Err(Error::UnknownClause { .. })
        ));
        assert_eq!(prover.kernel.assume(p).unwrap(), reusable);
    }

    #[test]
    fn rat_is_explicitly_outside_the_consequence_api() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let step = Step::LearnRat {
            id: 2,
            clause: dimacs([1]),
            pivot: Literal::new(1).unwrap(),
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
        let positive = dimacs([1]);
        let negative = dimacs([-1]);
        let formula = Formula::new([positive.clone(), negative.clone()]);
        let mut oracle = oracle::Kernel::open(&formula);
        assert_eq!(oracle.clause(1), Some(&positive));

        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.bind_variable(1, p.reference()).unwrap();
        builder.clause(&[p]).unwrap();
        builder.clause(&[p.negated()]).unwrap();
        let mut prover = builder.refute().unwrap();
        let empty = dimacs([]);

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
