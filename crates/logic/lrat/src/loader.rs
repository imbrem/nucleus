//! Proof-producing RUP replay through the checked classical kernel interface.

use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::{self, Snafu};
use covalence_logic_classical::{
    ClassicalKernel, Error as ClassicalError, RatGroup as ClassicalRatGroup, Refutation, Refuter,
    RowId,
};
use covalence_logic_hol::{
    Kernel, KernelError, Lit, LitVec, Matrix, Ref, ThmId, ThmRef,
    builtin::{Op1, Op2},
};

use crate::{Clause, ClauseId, Formula, Literal, Step};

/// A clause retained alongside its checked consequence theorem.
#[derive(Clone, Debug)]
struct ClauseRecord {
    term: Ref,
    row: RowId,
}

/// A rejected CNF construction or LRAT proof step.
#[non_exhaustive]
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum Error {
    /// The checked HOL operation rejected the requested construction.
    #[snafu(transparent)]
    Kernel { source: KernelError },
    /// The classical refutation checker rejected the requested step.
    #[snafu(transparent)]
    Classical { source: ClassicalError },
    /// An LRAT literal cannot be interpreted as a signed HOL reference.
    #[snafu(display("LRAT literal {literal} is not a signed HOL literal"))]
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
    /// The proof ends without a checked empty-clause consequence.
    #[snafu(display("the proof does not derive the empty clause"))]
    NoRefutation,
    /// The supplied root is not a canonical CNF opcode tree.
    #[snafu(display("reference {formula:?} is not a canonical CNF formula"))]
    NonCanonicalFormula { formula: Ref },
}

/// Converts a DIMACS formula to the classical kernel's dense CNF representation.
///
/// Literal and row order, including duplicates, is preserved.
///
/// # Errors
///
/// Returns an error if a literal or row index does not fit the classical `i32` representation.
pub fn load_cnf(formula: &Formula) -> Result<Matrix, Error> {
    formula
        .clauses()
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|literal| {
                    i32::try_from(literal.get())
                        .ok()
                        .and_then(|value| Lit::try_new(value).ok())
                        .ok_or(Error::InvalidLiteral {
                            literal: literal.get(),
                        })
                })
                .collect::<Result<_, _>>()
        })
        .collect::<Result<Vec<_>, _>>()
        .map(Matrix::new)
}

/// Incremental userspace replay of LRAT over uninterpreted classical atoms.
#[derive(Debug)]
pub struct ClassicalProver {
    refuter: Refuter,
    live: BTreeMap<ClauseId, RowId>,
    high_water: ClauseId,
}

impl ClassicalProver {
    /// Opens the initial DIMACS formula for checked LRAT replay.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula does not fit the classical representation.
    pub fn new(formula: &Formula) -> Result<Self, Error> {
        let goal = load_cnf(formula)?;
        let mut live = BTreeMap::new();
        for index in 0..formula.len() {
            let id = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(Error::TooManyClauses)?;
            let row = i32::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .and_then(RowId::new)
                .ok_or(Error::TooManyClauses)?;
            live.insert(id, row);
        }
        Ok(Self {
            refuter: Refuter::new(goal),
            live,
            high_water: u64::try_from(formula.len()).map_err(|_| Error::TooManyClauses)?,
        })
    }

    fn rows(&self, step: ClauseId, ids: &[ClauseId]) -> Result<Vec<RowId>, Error> {
        ids.iter()
            .map(|id| {
                self.live
                    .get(id)
                    .copied()
                    .ok_or(Error::UnknownClause { step, clause: *id })
            })
            .collect()
    }

    /// Applies one parsed LRAT step.
    ///
    /// # Errors
    ///
    /// Returns the first structural, RUP, or RAT rejection without admitting the step.
    pub fn apply(&mut self, step: &Step) -> Result<(), Error> {
        match step {
            Step::LearnRup {
                id,
                clause,
                ordered_hints,
            } => {
                if *id <= self.high_water {
                    return Err(Error::NonFreshId { id: *id });
                }
                let row = load_cnf(&Formula::new([clause.clone()]))?
                    .rows()
                    .next()
                    .map(LitVec::from_slice)
                    .unwrap_or_default();
                let hints = self.rows(*id, ordered_hints)?;
                let row = self.refuter.learn_rup(row, &hints)?;
                self.live.insert(*id, row);
                self.high_water = *id;
            }
            Step::LearnRat {
                id,
                clause,
                pivot,
                prefix_rup_hints,
                groups,
            } => {
                if *id <= self.high_water {
                    return Err(Error::NonFreshId { id: *id });
                }
                let row = load_cnf(&Formula::new([clause.clone()]))?
                    .rows()
                    .next()
                    .map(LitVec::from_slice)
                    .unwrap_or_default();
                let pivot = i32::try_from(pivot.get())
                    .ok()
                    .and_then(|value| Lit::try_new(value).ok())
                    .ok_or(Error::InvalidLiteral {
                        literal: pivot.get(),
                    })?;
                let prefix = self.rows(*id, prefix_rup_hints)?;
                let groups = groups
                    .iter()
                    .map(|group| {
                        Ok(ClassicalRatGroup {
                            opposing: self.rows(*id, &[group.opposing_clause_id])?[0],
                            hints: self.rows(*id, &group.resolvent_rup_hints)?,
                        })
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                let row = self.refuter.learn_rat(row, pivot, &prefix, &groups)?;
                self.live.insert(*id, row);
                self.high_water = *id;
            }
            Step::Forget { ids } => {
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
                let rows = self.rows(self.high_water, ids)?;
                for row in rows {
                    self.refuter.remove(row)?;
                }
                for id in ids {
                    self.live.remove(id);
                }
            }
        }
        Ok(())
    }

    /// Completes replay after an empty clause has been derived.
    ///
    /// # Errors
    ///
    /// Returns an error if replay has not derived an empty clause.
    pub fn done(self) -> Result<Refutation, Error> {
        self.refuter.done().map_err(Into::into)
    }
}

/// Replays all steps and returns a universally valid classical refutation.
///
/// # Errors
///
/// Returns the first rejected formula, proof step, or incomplete proof.
pub fn replay(formula: &Formula, steps: &[Step]) -> Result<Refutation, Error> {
    let mut prover = ClassicalProver::new(formula)?;
    for step in steps {
        prover.apply(step)?;
    }
    prover.done()
}

/// Incrementally constructs a deterministic CNF term around a checked kernel.
#[derive(Debug)]
pub struct CnfBuilder {
    kernel: Kernel,
    bool_ty: Ref,
    clauses: Vec<Box<[Lit]>>,
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
        validate_atom(&self.kernel, positive(atom))?;
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
    pub fn clause(&mut self, literals: &[Lit]) -> Result<ClauseId, Error> {
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
        let canonical: BTreeMap<_, _> = canonical_clauses
            .iter()
            .cloned()
            .zip(terms.iter().copied())
            .collect();
        let goal = Matrix::new(self.clauses.iter().map(|row| row.iter().copied().collect()));
        let syllogisms = ClassicalKernel::new();
        let refuter = Refuter::new(goal);
        let mut live = BTreeMap::new();
        for (index, literals) in self.clauses.into_iter().enumerate() {
            let term = canonical[&literals];
            let id = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(Error::TooManyClauses)?;
            let row = RowId::new(i32::try_from(index + 1).map_err(|_| Error::TooManyClauses)?)
                .ok_or(Error::TooManyClauses)?;
            live.insert(id, ClauseRecord { term, row });
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
            syllogisms,
            refuter,
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
    syllogisms: ClassicalKernel,
    refuter: Refuter,
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
    /// Returns a typed rejection for malformed, invalid RUP, or invalid RAT evidence.
    pub fn apply(&mut self, step: &Step) -> Result<(), Error> {
        match step {
            Step::LearnRup {
                id,
                clause,
                ordered_hints,
            } => self.learn_rup(*id, clause, ordered_hints),
            Step::LearnRat {
                id,
                clause,
                pivot,
                prefix_rup_hints,
                groups,
            } => self.learn_rat(*id, clause, *pivot, prefix_rup_hints, groups),
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

    /// Admits one fresh clause expressed directly in the native `Lit` convention.
    ///
    /// # Errors
    ///
    /// Returns the first structural or checked-proof rejection transactionally.
    pub fn learn_rup_props(
        &mut self,
        id: ClauseId,
        literals: &[Lit],
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
        let hints = self.rows(id, ordered_hints)?;
        let mut kernel = self.kernel.fork();
        let term = build_clause(&mut kernel, &literals, self.false_ref)?;
        let row = self.refuter.learn_rup(literals.clone().into(), &hints)?;
        self.kernel = kernel;
        self.live.insert(id, ClauseRecord { term, row });
        self.high_water = id;
        Ok(())
    }

    fn rows(&self, step: ClauseId, ids: &[ClauseId]) -> Result<Vec<RowId>, Error> {
        ids.iter()
            .map(|id| {
                self.live
                    .get(id)
                    .map(|record| record.row)
                    .ok_or(Error::UnknownClause { step, clause: *id })
            })
            .collect()
    }

    /// Admits one fresh clause by checked RAT.
    ///
    /// # Errors
    ///
    /// Returns an error if identifiers, literals, or RAT evidence are invalid.
    pub fn learn_rat(
        &mut self,
        id: ClauseId,
        clause: &Clause,
        pivot: Literal,
        prefix_hints: &[ClauseId],
        groups: &[crate::RatGroup],
    ) -> Result<(), Error> {
        if id <= self.high_water {
            return Err(Error::NonFreshId { id });
        }
        let mut literals = map_dimacs(&self.variables, clause.iter())?;
        let pivot = map_dimacs(&self.variables, [pivot])?[0];
        for literal in &literals {
            validate_atom(&self.kernel, *literal)?;
        }
        let prefix = self.rows(id, prefix_hints)?;
        let groups = groups
            .iter()
            .map(|group| {
                Ok(ClassicalRatGroup {
                    opposing: self.rows(id, &[group.opposing_clause_id])?[0],
                    hints: self.rows(id, &group.resolvent_rup_hints)?,
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let refuter_literals = literals.clone();
        literals.sort_unstable();
        literals.dedup();
        let mut kernel = self.kernel.fork();
        let term = build_clause(&mut kernel, &literals, self.false_ref)?;
        let row = self
            .refuter
            .learn_rat(refuter_literals.into(), pivot, &prefix, &groups)?;
        self.kernel = kernel;
        self.live.insert(id, ClauseRecord { term, row });
        self.high_water = id;
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
        let rows = ids
            .iter()
            .map(|id| {
                self.live
                    .get(id)
                    .map(|record| record.row)
                    .ok_or(Error::UnknownClause {
                        step: self.high_water,
                        clause: *id,
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        for row in rows {
            self.refuter.remove(row)?;
        }
        for id in ids {
            self.live.remove(id);
        }
        Ok(())
    }

    /// Requires a checked empty-clause consequence and returns the sealed result.
    ///
    /// # Errors
    ///
    /// Returns [`Error::NoRefutation`] unless the witness is exactly
    /// `[[formula]] ⊢ []`.
    pub fn done(mut self) -> Result<UnsatFormula, Error> {
        let refutation = self.refuter.done()?;
        let universal = self.syllogisms.copy_refutation(&refutation)?;
        self.kernel.syl_mut().copy_refutation(&refutation)?;
        let theorem =
            self.kernel
                .seal_cnf_refutation(&self.syllogisms, universal, positive(self.formula))?;
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
    pub fn reconstruct(&self) -> Result<Vec<Vec<Lit>>, Error> {
        reconstruct(&self.kernel, self.formula)
    }

    /// Rechecks that the retained private witness is `[[formula]] ⊢ []`.
    ///
    /// # Errors
    ///
    /// Returns an error if the checked witness invariant is absent.
    pub fn verify(&self) -> Result<(), Error> {
        let sequent = self
            .kernel
            .thm()
            .get(self.refutation)
            .ok_or(Error::NoRefutation)?;
        let formula = positive(self.formula);
        if is_unit_refutation(&sequent, formula) {
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
pub fn reconstruct(kernel: &Kernel, formula: Ref) -> Result<Vec<Vec<Lit>>, Error> {
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

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn reference(proposition: Lit) -> Ref {
    Ref::new(i32::try_from(proposition.magnitude()).expect("literal magnitude fits i32"))
        .expect("literal magnitude is nonzero")
}

fn is_unit_refutation(theorem: &ThmRef, formula: Lit) -> bool {
    let mut premises = theorem.lhs.rows();
    premises.next() == Some(&[formula][..])
        && premises.next().is_none()
        && theorem.rhs.rows().next().is_none()
}

fn map_dimacs(
    variables: &BTreeMap<u64, Ref>,
    literals: impl IntoIterator<Item = Literal>,
) -> Result<Vec<Lit>, Error> {
    literals
        .into_iter()
        .map(|literal| {
            let variable = literal.variable();
            let atom = *variables
                .get(&variable)
                .ok_or(Error::UnknownVariable { variable })?;
            let positive = positive(atom);
            Ok(if literal.get() > 0 {
                positive
            } else {
                positive.negated()
            })
        })
        .collect()
}

fn validate_atom(kernel: &Kernel, proposition: Lit) -> Result<(), Error> {
    let reference = reference(proposition);
    if kernel.arena().op1(reference).is_some()
        || kernel.arena().op2(reference).is_some()
        || kernel.arena().bool_value(reference).is_some()
    {
        return Err(Error::NonAtomicLiteral { reference });
    }
    Ok(())
}

fn literal_term(kernel: &mut Kernel, literal: Lit) -> Result<Ref, Error> {
    if literal.is_positive() {
        Ok(reference(literal))
    } else {
        Ok(kernel.op1(Op1::Not, reference(literal))?)
    }
}

fn build_clause(kernel: &mut Kernel, literals: &[Lit], false_ref: Ref) -> Result<Ref, Error> {
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

fn flatten_clause(kernel: &Kernel, term: Ref, output: &mut Vec<Lit>) -> Result<(), Error> {
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

fn decode_literal(kernel: &Kernel, term: Ref, output: &mut Vec<Lit>) -> Result<(), Error> {
    if kernel.arena().op1(term) == Some(Op1::Not) {
        let child = kernel
            .children(term)
            .and_then(|mut children| children.next())
            .ok_or(Error::NonCanonicalFormula { formula: term })?;
        validate_atom(kernel, positive(child))?;
        output.push(positive(child).negated());
        return Ok(());
    }
    let atom = positive(term);
    validate_atom(kernel, atom)?;
    output.push(atom);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Formula, Literal, oracle, parse::Step};

    fn fixture() -> (Kernel, Ref, Lit, Lit) {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let p = kernel.tm_fv(1, bool_ty).unwrap();
        let q = kernel.tm_fv(2, bool_ty).unwrap();
        (kernel, bool_ty, positive(p), positive(q))
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
            Vec::<Vec<Lit>>::new()
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
        let clause = kernel.op2(Op2::Or, reference(p), falsehood).unwrap();
        let repeated = kernel.op2(Op2::And, clause, truth).unwrap();
        let formula = kernel.op2(Op2::And, clause, repeated).unwrap();
        assert!(matches!(
            reconstruct(&kernel, formula),
            Err(Error::NonCanonicalFormula { .. })
        ));

        let repeated_literal = kernel.op2(Op2::Or, reference(p), clause).unwrap();
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
    fn rup_refutes_an_arbitrary_compound_hol_predicate() {
        let (mut kernel, bool_ty, _, q) = fixture();
        let predicate_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
        let predicate = kernel.tm_fv(3, predicate_ty).unwrap();
        let application = kernel.app(predicate, reference(q)).unwrap();
        let proposition = positive(application);

        // The SAT atom is a Boolean-valued HOL application, not a Boolean
        // variable. RUP treats it only as an opaque proposition and therefore
        // remains valid for arbitrary predicate semantics.
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[proposition]).unwrap();
        builder.clause(&[proposition.negated()]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.learn_rup_props(3, &[], &[1, 2]).unwrap();

        let result = prover.done().unwrap();
        assert_eq!(
            result.reconstruct().unwrap(),
            vec![vec![proposition], vec![proposition.negated()]]
        );
        result.verify().unwrap();
    }

    #[test]
    fn rup_accepts_a_tautology_without_hints() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut prover = CnfBuilder::new(kernel, bool_ty).refute().unwrap();

        prover.learn_rup_props(1, &[p, p.negated()], &[]).unwrap();

        let row = prover.live[&1].row;
        let mut expected = [p, p.negated()];
        expected.sort_unstable();
        assert_eq!(prover.refuter.row(row).unwrap(), expected);
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
        builder.bind_variable(1, reference(p)).unwrap();
        builder.bind_variable(2, reference(q)).unwrap();
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.learn_rup(2, &dimacs([1, 2]), &[1]).unwrap();
        let row = prover.live[&2].row;
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(prover.refuter.row(row).unwrap(), expected);
    }

    #[test]
    fn learned_clause_survives_deleting_a_source_row() {
        let (kernel, bool_ty, _, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[]).unwrap();
        let mut prover = builder.refute().unwrap();

        prover.learn_rup_props(2, &[], &[1]).unwrap();
        let source = prover.live[&1].row;
        let learned = prover.live[&2].row;
        assert_ne!(source, learned);

        prover.forget(&[1]).unwrap();
        assert!(prover.refuter.row(source).is_err());
        assert!(prover.refuter.row(learned).is_ok());
    }

    #[test]
    fn rup_learning_does_not_mutate_its_source_row() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let source = prover.live[&1].row;
        let source_before = prover.refuter.row(source).unwrap().to_vec();

        prover.learn_rup_props(2, &[p, q], &[1]).unwrap();
        let learned = prover.live[&2].row;
        assert_ne!(source, learned);
        assert_eq!(prover.refuter.row(source).unwrap(), source_before);

        prover.forget(&[2]).unwrap();
        assert!(prover.refuter.row(learned).is_err());
        assert_eq!(prover.refuter.row(source).unwrap(), source_before);
    }

    #[test]
    fn duplicate_initial_clauses_own_distinct_stable_rows() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        builder.clause(&[p]).unwrap();
        builder.clause(&[p.negated()]).unwrap();
        let mut prover = builder.refute().unwrap();

        let forgotten = prover.live[&1].row;
        let retained = prover.live[&2].row;
        assert_ne!(forgotten, retained);
        prover.forget(&[1]).unwrap();

        // Clause 2 retains its independent row throughout replay.
        prover.learn_rup_props(4, &[], &[2, 3]).unwrap();
        assert!(prover.refuter.row(retained).is_ok());
        prover.done().unwrap().verify().unwrap();
    }

    #[test]
    fn rejected_rup_does_not_mutate_the_refuter() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let before = prover.refuter.state().clone();
        let kernel_before = prover.kernel().arena().clone();
        assert!(matches!(
            prover.learn_rup_props(2, &[p, q], &[]),
            Err(Error::Classical {
                source: ClassicalError::NoConflict
            })
        ));
        assert_eq!(prover.refuter.state(), &before);
        assert_eq!(prover.kernel().arena(), &kernel_before);
    }

    #[test]
    fn rat_is_checked_by_the_userspace_refuter() {
        let (kernel, bool_ty, p, _) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.bind_variable(1, reference(p)).unwrap();
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let step = Step::LearnRat {
            id: 2,
            clause: dimacs([1]),
            pivot: Literal::new(1).unwrap(),
            prefix_rup_hints: vec![],
            groups: vec![],
        };
        prover.apply(&step).unwrap();
    }

    #[test]
    fn rat_requires_every_live_opposing_clause_and_accepts_retry() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.bind_variable(1, reference(p)).unwrap();
        builder.bind_variable(2, reference(q)).unwrap();
        builder.clause(&[p.negated(), q]).unwrap();
        builder.clause(&[p]).unwrap();
        let mut prover = builder.refute().unwrap();
        let before = prover.refuter.state().clone();
        let kernel_before = prover.kernel().arena().clone();

        assert!(matches!(
            prover.learn_rat(3, &dimacs([1, 2]), Literal::new(1).unwrap(), &[], &[]),
            Err(Error::Classical {
                source: ClassicalError::IncompleteRat { id: 1 }
            })
        ));
        assert_eq!(prover.refuter.state(), &before);
        assert_eq!(prover.kernel().arena(), &kernel_before);
        assert_eq!(prover.high_water, 2);

        prover
            .learn_rat(
                3,
                &dimacs([1, 2]),
                Literal::new(1).unwrap(),
                &[],
                &[crate::RatGroup {
                    opposing_clause_id: 1,
                    resolvent_rup_hints: vec![2],
                }],
            )
            .unwrap();
        assert_eq!(prover.high_water, 3);
    }

    #[test]
    fn deleting_an_opposing_clause_removes_its_rat_coverage_obligation() {
        let (kernel, bool_ty, p, q) = fixture();
        let mut builder = CnfBuilder::new(kernel, bool_ty);
        builder.bind_variable(1, reference(p)).unwrap();
        builder.clause(&[p.negated(), q]).unwrap();
        let mut prover = builder.refute().unwrap();
        prover.forget(&[1]).unwrap();

        prover
            .learn_rat(2, &dimacs([1]), Literal::new(1).unwrap(), &[], &[])
            .unwrap();
        assert!(prover.clause_term(2).is_some());
        assert!(matches!(
            prover.learn_rup_props(3, &[p], &[1]),
            Err(Error::UnknownClause { step: 3, clause: 1 })
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
        builder.bind_variable(1, reference(p)).unwrap();
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
#[test]
fn standalone_text_and_binary_replay_produce_the_same_refutation() {
    let formula = Formula::from_signed([vec![1], vec![-1]]).unwrap();
    let text = crate::parse::parse_text("3 0 1 2 0\n").unwrap();
    let binary = crate::parse::parse_binary(&[b'a', 6, 0, 2, 4, 0]).unwrap();
    let text = replay(&formula, &text).unwrap();
    let binary = replay(&formula, &binary).unwrap();
    assert_eq!(text.theorem(), binary.theorem());
    assert_eq!(
        text.theorem().lhs.to_rows(),
        load_cnf(&formula).unwrap().to_rows()
    );
}
