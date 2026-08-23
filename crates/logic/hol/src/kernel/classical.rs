//! Checked finite classical sequents over stable local term references.

use std::{
    collections::BTreeMap,
    num::{NonZeroI64, NonZeroU64},
};

use covalence_lib_error::snafu::Snafu;

use super::{Kernel, KernelError};
use crate::{
    Ref,
    builtin::{Op1, Op2},
};

/// A signed Boolean term reference.
///
/// The representation deliberately follows the Ethane wire convention:
/// `-n` denotes positive term `Ref(n)`, while `n` denotes its negation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PropId(NonZeroI64);

/// A failure to construct a losslessly negatable proposition identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("invalid signed proposition identifier {value}"))]
pub struct PropIdError {
    /// Rejected signed value.
    pub value: i64,
}

impl PropId {
    /// Encodes a positive occurrence of `reference`.
    ///
    /// # Errors
    ///
    /// Returns an error when the reference exceeds the signed wire space.
    pub fn positive(reference: Ref) -> Result<Self, PropIdError> {
        let magnitude =
            i64::try_from(reference.get()).map_err(|_| PropIdError { value: i64::MIN })?;
        Ok(Self(NonZeroI64::new(-magnitude).expect("Ref is nonzero")))
    }

    /// Decodes a nonzero, losslessly negatable wire integer.
    ///
    /// # Errors
    ///
    /// Returns an error for zero or `i64::MIN`.
    pub const fn from_raw(value: i64) -> Result<Self, PropIdError> {
        if value == 0 || value == i64::MIN {
            Err(PropIdError { value })
        } else {
            match NonZeroI64::new(value) {
                Some(value) => Ok(Self(value)),
                None => Err(PropIdError { value }),
            }
        }
    }

    /// Returns the signed wire integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0.get()
    }

    /// Returns the complementary proposition.
    #[must_use]
    pub const fn negated(self) -> Self {
        // Constructors exclude MIN and zero.
        Self(NonZeroI64::new(-self.get()).expect("PropId negation is nonzero"))
    }

    /// Returns whether this is a positive occurrence of its term.
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.get() < 0
    }

    /// Returns the underlying unsigned local term reference.
    #[must_use]
    pub const fn reference(self) -> Ref {
        let magnitude = self.get().unsigned_abs();
        Ref::new(magnitude).expect("PropId magnitude is nonzero")
    }
}

/// A stable one-based index into the canonical proposition-set table.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PropSetId(NonZeroU64);

impl PropSetId {
    const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }
    /// Returns the one-based table index.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

/// An ephemeral one-based checked theorem handle.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThmId(NonZeroU64);

impl ThmId {
    const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }
    /// Returns the one-based slot index.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Thm {
    prem: Option<PropSetId>,
    conc: Option<PropSetId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ThmSlot {
    Occupied(Thm),
    Free(Option<ThmId>),
}

/// A borrowing view of `AND(premises) |- OR(conclusions)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Sequent<'a> {
    /// Canonical sorted, deduplicated premises.
    pub premises: &'a [PropId],
    /// Canonical sorted, deduplicated conclusions.
    pub conclusions: &'a [PropId],
}

/// A singleton-conclusion theorem view suitable for ordinary HOL consumers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolTheorem<'a> {
    /// Canonical assumptions.
    pub assumptions: &'a [PropId],
    /// The sole signed Boolean conclusion.
    pub conclusion: PropId,
}

#[derive(Debug, Default)]
pub(super) struct ClassicalState {
    sets: Vec<Box<[PropId]>>,
    set_index: BTreeMap<Box<[PropId]>, PropSetId>,
    theorems: Vec<ThmSlot>,
    free: Option<ThmId>,
}

impl ClassicalState {
    pub(super) const fn new() -> Self {
        Self {
            sets: Vec::new(),
            set_index: BTreeMap::new(),
            theorems: Vec::new(),
            free: None,
        }
    }
}

impl Kernel {
    /// Interns a sorted, deduplicated proposition set. Empty sets are `None`.
    ///
    /// # Errors
    ///
    /// Returns an error if a proposition is not a local Boolean term or the
    /// stable set index space is exhausted.
    pub fn prop_set(&mut self, propositions: &[PropId]) -> Result<Option<PropSetId>, KernelError> {
        let mut canonical = propositions.to_vec();
        canonical.sort_unstable();
        canonical.dedup();
        for proposition in &canonical {
            self.validate_prop(*proposition)?;
        }
        if canonical.is_empty() {
            return Ok(None);
        }
        if let Some(id) = self.classical.set_index.get(canonical.as_slice()) {
            return Ok(Some(*id));
        }
        let next = u64::try_from(self.classical.sets.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .and_then(PropSetId::new)
            .ok_or(KernelError::TooManyPropSets)?;
        let canonical = canonical.into_boxed_slice();
        self.classical.set_index.insert(canonical.clone(), next);
        self.classical.sets.push(canonical);
        Ok(Some(next))
    }

    /// Borrows an interned proposition set.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent.
    pub fn propositions(&self, id: PropSetId) -> Result<&[PropId], KernelError> {
        self.classical
            .sets
            .get(usize::try_from(id.get() - 1).unwrap_or(usize::MAX))
            .map(Box::as_ref)
            .ok_or(KernelError::MissingPropSet { id })
    }

    /// Borrows a checked theorem sequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or deleted.
    pub fn theorem(&self, id: ThmId) -> Result<Sequent<'_>, KernelError> {
        let theorem = self.thm(id)?;
        Ok(Sequent {
            premises: self.set_or_empty(theorem.prem)?,
            conclusions: self.set_or_empty(theorem.conc)?,
        })
    }

    /// Recovers a theorem whose conclusion has exactly one proposition.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem exists and has one conclusion.
    pub fn hol_theorem(&self, id: ThmId) -> Result<HolTheorem<'_>, KernelError> {
        let sequent = self.theorem(id)?;
        let [conclusion] = sequent.conclusions else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "singleton conclusion",
            });
        };
        Ok(HolTheorem {
            assumptions: sequent.premises,
            conclusion: *conclusion,
        })
    }

    /// Introduces `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn assume(&mut self, p: PropId) -> Result<ThmId, KernelError> {
        let set = self.prop_set(&[p])?;
        self.push_thm(Thm {
            prem: set,
            conc: set,
        })
    }

    /// Weakens either side by union with the supplied propositions.
    ///
    /// # Errors
    ///
    /// Returns an error for missing evidence, invalid propositions, or allocation failure.
    pub fn weaken(
        &mut self,
        theorem: ThmId,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<ThmId, KernelError> {
        let old = *self.thm(theorem)?;
        let prem = self.union_set(old.prem, premises)?;
        let conc = self.union_set(old.conc, conclusions)?;
        self.push_thm(Thm { prem, conc })
    }

    /// Discharges one premise into its complementary conclusion.
    ///
    /// This is the classical polarity-transfer rule
    /// `Γ, p |- Δ` to `Γ |- Δ, ¬p`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `premise` occurs on the left side.
    pub fn discharge(&mut self, theorem: ThmId, premise: PropId) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut premises = self.set_or_empty(source.prem)?.to_vec();
        if !remove_sorted(&mut premises, premise) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "premise discharge",
            });
        }
        let conclusions = merge(self.set_or_empty(source.conc)?, &[premise.negated()]);
        let prem = self.prop_set(&premises)?;
        let conc = self.prop_set(&conclusions)?;
        self.push_thm(Thm { prem, conc })
    }

    /// Resolves complementary conclusions of two checked sequents.
    ///
    /// # Errors
    ///
    /// Returns an error unless `pivot` and its complement occur on the
    /// respective right sides.
    pub fn resolve(
        &mut self,
        left: ThmId,
        right: ThmId,
        pivot: PropId,
    ) -> Result<ThmId, KernelError> {
        let lhs = *self.thm(left)?;
        let rhs = *self.thm(right)?;
        let mut left_conc = self.set_or_empty(lhs.conc)?.to_vec();
        let mut right_conc = self.set_or_empty(rhs.conc)?.to_vec();
        if !remove_sorted(&mut left_conc, pivot) || !remove_sorted(&mut right_conc, pivot.negated())
        {
            return Err(KernelError::InvalidTheoremRule { rule: "resolution" });
        }
        let premises = merge(self.set_or_empty(lhs.prem)?, self.set_or_empty(rhs.prem)?);
        let conclusions = merge(&left_conc, &right_conc);
        let prem = self.prop_set(&premises)?;
        let conc = self.prop_set(&conclusions)?;
        self.push_thm(Thm { prem, conc })
    }

    /// Replaces one right-side connective by a sound one-step expansion.
    ///
    /// `branch` selects an operand for conjunctive results and is ignored for
    /// disjunctive results. Repeating this operation expands opcode trees.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the conclusion and names a
    /// supported Boolean opcode with an appropriate branch.
    pub fn expand_conclusion(
        &mut self,
        theorem: ThmId,
        formula: PropId,
        branch: Option<bool>,
    ) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut conc = self.set_or_empty(source.conc)?.to_vec();
        if !remove_sorted(&mut conc, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion expansion",
            });
        }
        let replacement = self.expand_right(formula, branch)?;
        conc = merge(&conc, &replacement);
        let conc = self.prop_set(&conc)?;
        self.push_thm(Thm {
            prem: source.prem,
            conc,
        })
    }

    /// Recursively flattens a disjunctive opcode tree on the right side.
    ///
    /// Negation is pushed through supported opcodes. The operation rejects a
    /// connective whose normalized form is conjunctive, since choosing a
    /// branch is then required for soundness.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the conclusion and every
    /// compound node has a disjunctive normalized form.
    pub fn flatten_conclusion(
        &mut self,
        theorem: ThmId,
        formula: PropId,
    ) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut conclusions = self.set_or_empty(source.conc)?.to_vec();
        if !remove_sorted(&mut conclusions, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion flattening",
            });
        }
        let mut pending = vec![formula];
        let mut leaves = Vec::new();
        while let Some(current) = pending.pop() {
            match self.disjunctive_children(current)? {
                Some(children) => pending.extend(children),
                None => leaves.push(current),
            }
        }
        leaves.sort_unstable();
        leaves.dedup();
        conclusions = merge(&conclusions, &leaves);
        let conc = self.prop_set(&conclusions)?;
        self.push_thm(Thm {
            prem: source.prem,
            conc,
        })
    }

    /// Deletes checked theorem handles atomically.
    ///
    /// # Errors
    ///
    /// Returns an error and changes nothing if any handle is absent, deleted,
    /// or repeated.
    pub fn remove_theorems(&mut self, ids: &[ThmId]) -> Result<(), KernelError> {
        let mut sorted = ids.to_vec();
        sorted.sort_unstable();
        if sorted.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "theorem deletion",
            });
        }
        for id in &sorted {
            self.thm(*id)?;
        }
        for id in sorted {
            let pos = usize::try_from(id.get() - 1).expect("resident theorem index fits usize");
            self.classical.theorems[pos] = ThmSlot::Free(self.classical.free);
            self.classical.free = Some(id);
        }
        Ok(())
    }

    fn validate_prop(&self, proposition: PropId) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(proposition.reference())
            .map(|_| ())
    }
    fn set_or_empty(&self, id: Option<PropSetId>) -> Result<&[PropId], KernelError> {
        match id {
            Some(id) => self.propositions(id),
            None => Ok(&[]),
        }
    }
    fn thm(&self, id: ThmId) -> Result<&Thm, KernelError> {
        match self
            .classical
            .theorems
            .get(usize::try_from(id.get() - 1).unwrap_or(usize::MAX))
        {
            Some(ThmSlot::Occupied(thm)) => Ok(thm),
            _ => Err(KernelError::MissingTheorem { id }),
        }
    }
    fn push_thm(&mut self, theorem: Thm) -> Result<ThmId, KernelError> {
        if let Some(id) = self.classical.free {
            let pos = usize::try_from(id.get() - 1).expect("resident theorem index fits usize");
            let ThmSlot::Free(next) = self.classical.theorems[pos] else {
                unreachable!("free list points to occupied theorem")
            };
            self.classical.free = next;
            self.classical.theorems[pos] = ThmSlot::Occupied(theorem);
            return Ok(id);
        }
        let id = u64::try_from(self.classical.theorems.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .and_then(ThmId::new)
            .ok_or(KernelError::TooManyTheorems)?;
        self.classical.theorems.push(ThmSlot::Occupied(theorem));
        Ok(id)
    }
    fn union_set(
        &mut self,
        old: Option<PropSetId>,
        extra: &[PropId],
    ) -> Result<Option<PropSetId>, KernelError> {
        let mut combined = self.set_or_empty(old)?.to_vec();
        combined.extend_from_slice(extra);
        self.prop_set(&combined)
    }
    fn expand_right(
        &self,
        formula: PropId,
        branch: Option<bool>,
    ) -> Result<Vec<PropId>, KernelError> {
        let reference = formula.reference();
        if let Some(value) = self.arena.bool_value(reference) {
            if value != formula.is_positive() {
                return Ok(Vec::new());
            }
            return Err(KernelError::InvalidTheoremRule {
                rule: "true conclusion expansion",
            });
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let signed = |child| {
            PropId::positive(child)
                .map(|p| {
                    if formula.is_positive() {
                        p
                    } else {
                        p.negated()
                    }
                })
                .map_err(|error| KernelError::InvalidPropId { value: error.value })
        };
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, _) => Ok(vec![signed(children[0])?.negated()]),
            (_, Some(Op2::Or), true) | (_, Some(Op2::And), false) => {
                Ok(vec![signed(children[0])?, signed(children[1])?])
            }
            (_, Some(Op2::And), true) | (_, Some(Op2::Or), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                Ok(vec![signed(children[usize::from(selected)])?])
            }
            (_, Some(Op2::Imp), true) => Ok(vec![
                PropId::positive(children[0])
                    .map_err(|e| KernelError::InvalidPropId { value: e.value })?
                    .negated(),
                PropId::positive(children[1])
                    .map_err(|e| KernelError::InvalidPropId { value: e.value })?,
            ]),
            (_, Some(Op2::Imp), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                let a = PropId::positive(children[0])
                    .map_err(|e| KernelError::InvalidPropId { value: e.value })?;
                let b = PropId::positive(children[1])
                    .map_err(|e| KernelError::InvalidPropId { value: e.value })?
                    .negated();
                Ok(vec![if selected { b } else { a }])
            }
            _ => Err(KernelError::InvalidTheoremRule {
                rule: "conclusion opcode expansion",
            }),
        }
    }

    fn disjunctive_children(&self, formula: PropId) -> Result<Option<Vec<PropId>>, KernelError> {
        let reference = formula.reference();
        if let Some(value) = self.arena.bool_value(reference) {
            if value != formula.is_positive() {
                return Ok(Some(Vec::new()));
            }
            return Ok(None);
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let positive = |child| {
            PropId::positive(child)
                .map_err(|error| KernelError::InvalidPropId { value: error.value })
        };
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, true) => Ok(Some(vec![positive(children[0])?.negated()])),
            (Some(Op1::Not), _, false) => Ok(Some(vec![positive(children[0])?])),
            (_, Some(Op2::Or), true) => {
                Ok(Some(vec![positive(children[0])?, positive(children[1])?]))
            }
            (_, Some(Op2::And), false) => Ok(Some(vec![
                positive(children[0])?.negated(),
                positive(children[1])?.negated(),
            ])),
            (_, Some(Op2::Imp), true) => Ok(Some(vec![
                positive(children[0])?.negated(),
                positive(children[1])?,
            ])),
            (_, Some(Op2::And), true) | (_, Some(Op2::Or | Op2::Imp), false) => {
                Err(KernelError::InvalidTheoremRule {
                    rule: "disjunctive conclusion flattening",
                })
            }
            _ => Ok(None),
        }
    }
}

fn remove_sorted(values: &mut Vec<PropId>, needle: PropId) -> bool {
    match values.binary_search(&needle) {
        Ok(index) => {
            values.remove(index);
            true
        }
        Err(_) => false,
    }
}

fn merge(left: &[PropId], right: &[PropId]) -> Vec<PropId> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut l, mut r) = (0, 0);
    while l < left.len() || r < right.len() {
        let next = match (left.get(l), right.get(r)) {
            (Some(a), Some(b)) if a < b => {
                l += 1;
                *a
            }
            (Some(a), Some(b)) if b < a => {
                r += 1;
                *b
            }
            (Some(a), Some(_)) => {
                l += 1;
                r += 1;
                *a
            }
            (Some(a), None) => {
                l += 1;
                *a
            }
            (None, Some(b)) => {
                r += 1;
                *b
            }
            (None, None) => unreachable!(),
        };
        if result.last() != Some(&next) {
            result.push(next);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Fixture {
        kernel: Kernel,
        p: PropId,
        q: PropId,
    }

    fn fixture() -> Fixture {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let p = kernel.tm_fv(1, bool_ty).unwrap();
        let q = kernel.tm_fv(2, bool_ty).unwrap();
        Fixture {
            kernel,
            p: PropId::positive(p).unwrap(),
            q: PropId::positive(q).unwrap(),
        }
    }

    #[test]
    fn signed_ids_use_inverted_polarity_without_overflow() {
        let reference = Ref::new(7).unwrap();
        let positive = PropId::positive(reference).unwrap();
        assert_eq!(positive.get(), -7);
        assert!(positive.is_positive());
        assert_eq!(positive.reference(), reference);
        assert_eq!(positive.negated().get(), 7);
        assert_eq!(PropId::from_raw(0), Err(PropIdError { value: 0 }));
        assert_eq!(
            PropId::from_raw(i64::MIN),
            Err(PropIdError { value: i64::MIN })
        );
    }

    #[test]
    fn proposition_sets_are_canonical_stable_and_empty_is_none() {
        let Fixture { mut kernel, p, q } = fixture();
        assert_eq!(kernel.prop_set(&[]).unwrap(), None);
        let first = kernel.prop_set(&[q, p, q]).unwrap().unwrap();
        let second = kernel.prop_set(&[p, q]).unwrap().unwrap();
        assert_eq!(first, second);
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(kernel.propositions(first).unwrap(), expected);
    }

    #[test]
    fn deletion_is_atomic_and_reuses_only_ephemeral_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let p_id = kernel.assume(p).unwrap();
        let q_id = kernel.assume(q).unwrap();
        assert!(kernel.remove_theorems(&[p_id, p_id]).is_err());
        assert!(kernel.theorem(p_id).is_ok());
        assert!(kernel.theorem(q_id).is_ok());
        kernel.remove_theorems(&[p_id]).unwrap();
        assert!(matches!(
            kernel.theorem(p_id),
            Err(KernelError::MissingTheorem { .. })
        ));
        assert_eq!(kernel.assume(q.negated()).unwrap(), p_id);
        assert!(kernel.theorem(q_id).is_ok());
    }

    #[test]
    fn weakening_resolution_and_discharge_form_sound_sequents() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.assume(p).unwrap();
        let assumed_not_p = kernel.assume(p.negated()).unwrap();
        let left = kernel.weaken(assumed_p, &[], &[q]).unwrap();
        let right = kernel.weaken(assumed_not_p, &[], &[q]).unwrap();
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_eq!(kernel.theorem(resolved).unwrap().conclusions, [q]);

        let assumed_p = kernel.assume(p).unwrap();
        let assumed_not_p = kernel.assume(p.negated()).unwrap();
        let contradiction = kernel.resolve(assumed_p, assumed_not_p, p).unwrap();
        let with_q = kernel.weaken(contradiction, &[q], &[]).unwrap();
        let discharged = kernel.discharge(with_q, q).unwrap();
        assert_eq!(
            kernel.theorem(discharged).unwrap().conclusions,
            [q.negated()]
        );
    }

    #[test]
    fn opcode_tree_expansion_refutes_p_and_not_p() {
        let Fixture { mut kernel, p, .. } = fixture();
        let not_p_ref = kernel.op1(Op1::Not, p.reference()).unwrap();
        let not_p = PropId::positive(not_p_ref).unwrap();
        let formula_ref = kernel.op2(Op2::And, p.reference(), not_p_ref).unwrap();
        let formula = PropId::positive(formula_ref).unwrap();
        let root = kernel.assume(formula).unwrap();
        let p_clause = kernel
            .expand_conclusion(root, formula, Some(false))
            .unwrap();
        let not_clause = kernel.expand_conclusion(root, formula, Some(true)).unwrap();
        let neg_p_clause = kernel.expand_conclusion(not_clause, not_p, None).unwrap();
        let refutation = kernel.resolve(p_clause, neg_p_clause, p).unwrap();
        let sequent = kernel.theorem(refutation).unwrap();
        assert_eq!(sequent.premises, [formula]);
        assert!(sequent.conclusions.is_empty());
    }

    #[test]
    fn recursive_flattening_handles_or_not_imp_and_false() {
        let Fixture { mut kernel, p, q } = fixture();
        let not_p = kernel.op1(Op1::Not, p.reference()).unwrap();
        let implication = kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap();
        let nested = kernel.op2(Op2::Or, not_p, implication).unwrap();
        let nested = PropId::positive(nested).unwrap();
        let theorem = kernel.assume(nested).unwrap();
        let flattened = kernel.flatten_conclusion(theorem, nested).unwrap();
        let mut expected = vec![p.negated(), q];
        expected.sort_unstable();
        assert_eq!(kernel.theorem(flattened).unwrap().conclusions, expected);

        let bool_ty = kernel.classifier(p.reference()).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let falsehood = PropId::positive(falsehood).unwrap();
        let false_theorem = kernel.assume(falsehood).unwrap();
        let eliminated = kernel
            .expand_conclusion(false_theorem, falsehood, None)
            .unwrap();
        assert!(kernel.theorem(eliminated).unwrap().conclusions.is_empty());
    }

    #[test]
    fn primitive_resolution_is_valid_for_every_boolean_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.assume(p).unwrap();
        let assumed_not_p = kernel.assume(p.negated()).unwrap();
        let left = kernel.weaken(assumed_p, &[q], &[q]).unwrap();
        let right = kernel.weaken(assumed_not_p, &[q], &[q.negated()]).unwrap();
        let result = kernel.resolve(left, right, p).unwrap();
        for p_value in [false, true] {
            for q_value in [false, true] {
                assert!(valid(kernel.theorem(left).unwrap(), p, p_value, q, q_value));
                assert!(valid(
                    kernel.theorem(right).unwrap(),
                    p,
                    p_value,
                    q,
                    q_value
                ));
                assert!(valid(
                    kernel.theorem(result).unwrap(),
                    p,
                    p_value,
                    q,
                    q_value
                ));
            }
        }
    }

    fn valid(sequent: Sequent<'_>, p: PropId, p_value: bool, q: PropId, q_value: bool) -> bool {
        let value = |proposition: PropId| {
            let atom = if proposition.reference() == p.reference() {
                p_value
            } else {
                assert_eq!(proposition.reference(), q.reference());
                q_value
            };
            if proposition.is_positive() {
                atom
            } else {
                !atom
            }
        };
        !sequent.premises.iter().copied().all(&value)
            || sequent.conclusions.iter().copied().any(value)
    }
}
