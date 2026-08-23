//! Checked finite classical sequents over stable local term references.

use std::{
    collections::BTreeMap,
    num::{NonZeroI64, NonZeroU64},
};

use covalence_lib_error::snafu::Snafu;
use smallvec::SmallVec;

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
    /// # Panics
    ///
    /// Panics only if `Ref` violates its global signed-bound or nonzero
    /// representation invariant.
    #[must_use]
    pub fn positive(reference: Ref) -> Self {
        let magnitude = i64::try_from(reference.get()).expect("Ref is globally signed-bounded");
        Self(NonZeroI64::new(-magnitude).expect("Ref is nonzero"))
    }

    /// Decodes a nonzero, losslessly negatable wire integer.
    ///
    /// # Errors
    ///
    /// Returns an error unless the signed magnitude is strictly below
    /// `i64::MAX` and nonzero.
    pub const fn from_raw(value: i64) -> Result<Self, PropIdError> {
        if value == 0 || value.unsigned_abs() >= i64::MAX as u64 {
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
    ///
    /// # Panics
    ///
    /// Panics only if `PropId` violates its nonzero, non-`i64::MIN`
    /// representation invariants.
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
    ///
    /// # Panics
    ///
    /// Panics only if `PropId` violates its nonzero representation invariant.
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
    sets: Vec<SmallVec<[PropId; 2]>>,
    set_index: BTreeMap<SmallVec<[PropId; 2]>, PropSetId>,
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
        let mut canonical = SmallVec::<[PropId; 2]>::from_slice(propositions);
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
            .map(SmallVec::as_slice)
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

    /// Introduces the identity sequent `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn identity(&mut self, p: PropId) -> Result<ThmId, KernelError> {
        let set = self.prop_set(&[p])?;
        self.push_thm(Thm {
            prem: set,
            conc: set,
        })
    }

    /// Compatibility name for [`Self::identity`].
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn assume(&mut self, p: PropId) -> Result<ThmId, KernelError> {
        self.identity(p)
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
        for proposition in premises.iter().chain(conclusions) {
            self.validate_prop(*proposition)?;
        }
        let prem = self.union_set(old.prem, premises)?;
        let conc = self.union_set(old.conc, conclusions)?;
        self.push_thm(Thm { prem, conc })
    }

    /// Cuts a proposition occurring on opposite sides of two sequents.
    ///
    /// From `Γ |- Δ, p` and `p, Π |- Λ`, derives `Γ, Π |- Δ, Λ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorem handles exist and `p` occurs in
    /// the required conclusion and premise.
    pub fn cut(
        &mut self,
        left: ThmId,
        right: ThmId,
        proposition: PropId,
    ) -> Result<ThmId, KernelError> {
        let lhs = *self.thm(left)?;
        let rhs = *self.thm(right)?;
        let mut left_conclusions = self.set_or_empty(lhs.conc)?.to_vec();
        let mut right_premises = self.set_or_empty(rhs.prem)?.to_vec();
        if !remove_sorted(&mut left_conclusions, proposition)
            || !remove_sorted(&mut right_premises, proposition)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "cut" });
        }
        let premises = merge(self.set_or_empty(lhs.prem)?, &right_premises);
        let conclusions = merge(&left_conclusions, self.set_or_empty(rhs.conc)?);
        self.push_sequent(&premises, &conclusions)
    }

    /// Introduces falsity on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless `falsehood` is a signed Boolean literal whose
    /// checked constant value is false.
    pub fn false_left(&mut self, falsehood: PropId) -> Result<ThmId, KernelError> {
        if self.signed_bool_value(falsehood)? != Some(false) {
            return Err(KernelError::InvalidTheoremRule { rule: "false left" });
        }
        self.push_sequent(&[falsehood], &[])
    }

    /// Introduces truth on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless `truth` is a signed Boolean literal whose
    /// checked constant value is true.
    pub fn true_right(&mut self, truth: PropId) -> Result<ThmId, KernelError> {
        if self.signed_bool_value(truth)? != Some(true) {
            return Err(KernelError::InvalidTheoremRule { rule: "true right" });
        }
        self.push_sequent(&[], &[truth])
    }

    /// Moves a conclusion to the left with complementary polarity.
    ///
    /// From `Γ |- Δ, p`, derives `¬p, Γ |- Δ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the conclusion.
    pub fn not_left(&mut self, theorem: ThmId, p: PropId) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut conclusions = self.set_or_empty(source.conc)?.to_vec();
        if !remove_sorted(&mut conclusions, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not left" });
        }
        let premises = merge(self.set_or_empty(source.prem)?, &[p.negated()]);
        self.push_sequent(&premises, &conclusions)
    }

    /// Moves a premise to the right with complementary polarity.
    ///
    /// From `p, Γ |- Δ`, derives `Γ |- Δ, ¬p`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the premise.
    pub fn not_right(&mut self, theorem: ThmId, p: PropId) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut premises = self.set_or_empty(source.prem)?.to_vec();
        if !remove_sorted(&mut premises, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not right" });
        }
        let conclusions = merge(self.set_or_empty(source.conc)?, &[p.negated()]);
        self.push_sequent(&premises, &conclusions)
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
        self.not_right(theorem, premise)
    }

    /// Folds two conjunct premises into their checked conjunction opcode.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands occur in the premise and
    /// `conjunction` is their positive `tm.and` opcode.
    pub fn and_left(&mut self, theorem: ThmId, conjunction: PropId) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(conjunction, Op2::And)?;
        let source = *self.thm(theorem)?;
        let mut premises = self.set_or_empty(source.prem)?.to_vec();
        if !remove_pair(&mut premises, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and left" });
        }
        premises = merge(&premises, &[conjunction]);
        let conclusions = self.set_or_empty(source.conc)?.to_vec();
        self.push_sequent(&premises, &conclusions)
    }

    /// Introduces a checked conjunction on the right, merging contexts.
    ///
    /// # Errors
    ///
    /// Returns an error unless the left and right operand conclusions occur.
    pub fn and_right(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        conjunction: PropId,
    ) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(conjunction, Op2::And)?;
        let lhs = *self.thm(left_theorem)?;
        let rhs = *self.thm(right_theorem)?;
        let mut left_conc = self.set_or_empty(lhs.conc)?.to_vec();
        let mut right_conc = self.set_or_empty(rhs.conc)?.to_vec();
        if !remove_sorted(&mut left_conc, left) || !remove_sorted(&mut right_conc, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and right" });
        }
        let premises = merge(self.set_or_empty(lhs.prem)?, self.set_or_empty(rhs.prem)?);
        let conclusions = merge(&merge(&left_conc, &right_conc), &[conjunction]);
        self.push_sequent(&premises, &conclusions)
    }

    /// Introduces a checked disjunction on the left, merging contexts.
    ///
    /// # Errors
    ///
    /// Returns an error unless the operand premises occur.
    pub fn or_left(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        disjunction: PropId,
    ) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(disjunction, Op2::Or)?;
        let lhs = *self.thm(left_theorem)?;
        let rhs = *self.thm(right_theorem)?;
        let mut left_prem = self.set_or_empty(lhs.prem)?.to_vec();
        let mut right_prem = self.set_or_empty(rhs.prem)?.to_vec();
        if !remove_sorted(&mut left_prem, left) || !remove_sorted(&mut right_prem, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or left" });
        }
        let premises = merge(&merge(&left_prem, &right_prem), &[disjunction]);
        let conclusions = merge(self.set_or_empty(lhs.conc)?, self.set_or_empty(rhs.conc)?);
        self.push_sequent(&premises, &conclusions)
    }

    /// Folds two conclusions into their checked disjunction opcode.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands occur in the conclusion and
    /// `disjunction` is their positive `tm.or` opcode.
    pub fn or_right(&mut self, theorem: ThmId, disjunction: PropId) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(disjunction, Op2::Or)?;
        let source = *self.thm(theorem)?;
        let mut conclusions = self.set_or_empty(source.conc)?.to_vec();
        if !remove_pair(&mut conclusions, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or right" });
        }
        conclusions = merge(&conclusions, &[disjunction]);
        let premises = self.set_or_empty(source.prem)?.to_vec();
        self.push_sequent(&premises, &conclusions)
    }

    /// Introduces a checked implication on the left.
    ///
    /// # Errors
    ///
    /// Returns an error unless the antecedent is a conclusion of `left` and
    /// the consequent is a premise of `right`.
    pub fn imp_left(
        &mut self,
        left_theorem: ThmId,
        right_theorem: ThmId,
        implication: PropId,
    ) -> Result<ThmId, KernelError> {
        let (antecedent, consequent) = self.require_binary(implication, Op2::Imp)?;
        let lhs = *self.thm(left_theorem)?;
        let rhs = *self.thm(right_theorem)?;
        let mut left_conc = self.set_or_empty(lhs.conc)?.to_vec();
        let mut right_prem = self.set_or_empty(rhs.prem)?.to_vec();
        if !remove_sorted(&mut left_conc, antecedent) || !remove_sorted(&mut right_prem, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp left" });
        }
        let premises = merge(
            &merge(self.set_or_empty(lhs.prem)?, &right_prem),
            &[implication],
        );
        let conclusions = merge(&left_conc, self.set_or_empty(rhs.conc)?);
        self.push_sequent(&premises, &conclusions)
    }

    /// Introduces a checked implication on the right.
    ///
    /// # Errors
    ///
    /// Returns an error unless the antecedent occurs in the premise and the
    /// consequent occurs in the conclusion.
    pub fn imp_right(&mut self, theorem: ThmId, implication: PropId) -> Result<ThmId, KernelError> {
        let (antecedent, consequent) = self.require_binary(implication, Op2::Imp)?;
        let source = *self.thm(theorem)?;
        let mut premises = self.set_or_empty(source.prem)?.to_vec();
        let mut conclusions = self.set_or_empty(source.conc)?.to_vec();
        if !remove_sorted(&mut premises, antecedent) || !remove_sorted(&mut conclusions, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp right" });
        }
        conclusions = merge(&conclusions, &[implication]);
        self.push_sequent(&premises, &conclusions)
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

    /// Recursively flattens a conjunctive opcode tree on the left side.
    ///
    /// # Errors
    ///
    /// Returns an error unless `formula` occurs in the premise and every
    /// compound node has a conjunctive normalized form.
    pub fn flatten_premise(
        &mut self,
        theorem: ThmId,
        formula: PropId,
    ) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let mut premises = self.set_or_empty(source.prem)?.to_vec();
        if !remove_sorted(&mut premises, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "premise flattening",
            });
        }
        let leaves = self.collect_tree(formula, TreeSide::Conjunctive)?;
        premises = merge(&premises, &leaves);
        let conclusions = self.set_or_empty(source.conc)?.to_vec();
        self.push_sequent(&premises, &conclusions)
    }

    /// Folds the leaves of a conjunctive opcode tree on the left side.
    ///
    /// # Errors
    ///
    /// Returns an error unless every normalized leaf occurs in the premise.
    pub fn fold_premise(&mut self, theorem: ThmId, formula: PropId) -> Result<ThmId, KernelError> {
        self.fold_tree(theorem, formula, TreeSide::Conjunctive)
    }

    /// Folds the leaves of a disjunctive opcode tree on the right side.
    ///
    /// # Errors
    ///
    /// Returns an error unless every normalized leaf occurs in the conclusion.
    pub fn fold_conclusion(
        &mut self,
        theorem: ThmId,
        formula: PropId,
    ) -> Result<ThmId, KernelError> {
        self.fold_tree(theorem, formula, TreeSide::Disjunctive)
    }

    /// Deletes checked theorem handles atomically.
    ///
    /// # Errors
    ///
    /// Returns an error and changes nothing if any handle is absent, deleted,
    /// or repeated.
    ///
    /// # Panics
    ///
    /// Panics only if the private theorem table violates its indexing
    /// invariant after every requested handle has been validated.
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
    fn push_sequent(
        &mut self,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<ThmId, KernelError> {
        let prem = self.prop_set(premises)?;
        let conc = self.prop_set(conclusions)?;
        self.push_thm(Thm { prem, conc })
    }
    fn signed_bool_value(&self, proposition: PropId) -> Result<Option<bool>, KernelError> {
        self.validate_prop(proposition)?;
        Ok(self.arena.bool_value(proposition.reference()).map(|value| {
            if proposition.is_positive() {
                value
            } else {
                !value
            }
        }))
    }
    fn require_binary(
        &self,
        proposition: PropId,
        expected: Op2,
    ) -> Result<(PropId, PropId), KernelError> {
        self.validate_prop(proposition)?;
        if !proposition.is_positive() || self.arena.op2(proposition.reference()) != Some(expected) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "binary connective",
            });
        }
        let mut children =
            self.arena
                .children(proposition.reference())
                .ok_or(KernelError::MissingDefinition {
                    reference: proposition.reference(),
                })?;
        let left = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        let right = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        Ok((PropId::positive(left), PropId::positive(right)))
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
            let positive = PropId::positive(child);
            if formula.is_positive() {
                positive
            } else {
                positive.negated()
            }
        };
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, _) => Ok(vec![signed(children[0]).negated()]),
            (_, Some(Op2::Or), true) | (_, Some(Op2::And), false) => {
                Ok(vec![signed(children[0]), signed(children[1])])
            }
            (_, Some(Op2::And), true) | (_, Some(Op2::Or), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                Ok(vec![signed(children[usize::from(selected)])])
            }
            (_, Some(Op2::Imp), true) => Ok(vec![
                PropId::positive(children[0]).negated(),
                PropId::positive(children[1]),
            ]),
            (_, Some(Op2::Imp), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                let a = PropId::positive(children[0]);
                let b = PropId::positive(children[1]).negated();
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
        let positive = PropId::positive;
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, true) => Ok(Some(vec![positive(children[0]).negated()])),
            (Some(Op1::Not), _, false) => Ok(Some(vec![positive(children[0])])),
            (_, Some(Op2::Or), true) => {
                Ok(Some(vec![positive(children[0]), positive(children[1])]))
            }
            (_, Some(Op2::And), false) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Imp), true) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]),
            ])),
            (_, Some(Op2::And), true) | (_, Some(Op2::Or | Op2::Imp), false) => {
                Err(KernelError::InvalidTheoremRule {
                    rule: "disjunctive conclusion flattening",
                })
            }
            _ => Ok(None),
        }
    }

    fn conjunctive_children(&self, formula: PropId) -> Result<Option<Vec<PropId>>, KernelError> {
        let reference = formula.reference();
        if let Some(value) = self.arena.bool_value(reference) {
            if value == formula.is_positive() {
                return Ok(Some(Vec::new()));
            }
            return Ok(None);
        }
        let children: Vec<_> = self
            .arena
            .children(reference)
            .ok_or(KernelError::MissingDefinition { reference })?
            .collect();
        let positive = PropId::positive;
        match (
            self.arena.op1(reference),
            self.arena.op2(reference),
            formula.is_positive(),
        ) {
            (Some(Op1::Not), _, true) => Ok(Some(vec![positive(children[0]).negated()])),
            (Some(Op1::Not), _, false) => Ok(Some(vec![positive(children[0])])),
            (_, Some(Op2::And), true) => {
                Ok(Some(vec![positive(children[0]), positive(children[1])]))
            }
            (_, Some(Op2::Or), false) => Ok(Some(vec![
                positive(children[0]).negated(),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Imp), false) => Ok(Some(vec![
                positive(children[0]),
                positive(children[1]).negated(),
            ])),
            (_, Some(Op2::Or | Op2::Imp), true) | (_, Some(Op2::And), false) => {
                Err(KernelError::InvalidTheoremRule {
                    rule: "conjunctive premise flattening",
                })
            }
            _ => Ok(None),
        }
    }

    fn collect_tree(&self, formula: PropId, side: TreeSide) -> Result<Vec<PropId>, KernelError> {
        let mut pending = vec![formula];
        let mut leaves = Vec::new();
        while let Some(current) = pending.pop() {
            let children = match side {
                TreeSide::Conjunctive => self.conjunctive_children(current)?,
                TreeSide::Disjunctive => self.disjunctive_children(current)?,
            };
            match children {
                Some(children) => pending.extend(children),
                None => leaves.push(current),
            }
        }
        leaves.sort_unstable();
        leaves.dedup();
        Ok(leaves)
    }

    fn fold_tree(
        &mut self,
        theorem: ThmId,
        formula: PropId,
        side: TreeSide,
    ) -> Result<ThmId, KernelError> {
        let source = *self.thm(theorem)?;
        let leaves = self.collect_tree(formula, side)?;
        let (mut premises, mut conclusions) = (
            self.set_or_empty(source.prem)?.to_vec(),
            self.set_or_empty(source.conc)?.to_vec(),
        );
        let target = match side {
            TreeSide::Conjunctive => &mut premises,
            TreeSide::Disjunctive => &mut conclusions,
        };
        if leaves.iter().any(|leaf| !remove_sorted(target, *leaf)) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "opcode tree folding",
            });
        }
        *target = merge(target, &[formula]);
        self.push_sequent(&premises, &conclusions)
    }
}

#[derive(Clone, Copy)]
enum TreeSide {
    Conjunctive,
    Disjunctive,
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

fn remove_pair(values: &mut Vec<PropId>, left: PropId, right: PropId) -> bool {
    if !remove_sorted(values, left) {
        return false;
    }
    left == right || remove_sorted(values, right)
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
    use std::collections::BTreeMap;

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
            p: PropId::positive(p),
            q: PropId::positive(q),
        }
    }

    #[test]
    fn signed_ids_use_inverted_polarity_without_overflow() {
        let reference = Ref::new(7).unwrap();
        let positive = PropId::positive(reference);
        assert_eq!(positive.get(), -7);
        assert!(positive.is_positive());
        assert_eq!(positive.reference(), reference);
        assert_eq!(positive.negated().get(), 7);
        assert_eq!(PropId::from_raw(0), Err(PropIdError { value: 0 }));
        assert_eq!(
            PropId::from_raw(i64::MIN),
            Err(PropIdError { value: i64::MIN })
        );
        assert_eq!(
            PropId::from_raw(i64::MAX),
            Err(PropIdError { value: i64::MAX })
        );
        assert_eq!(
            PropId::from_raw(-i64::MAX),
            Err(PropIdError { value: -i64::MAX })
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
    fn checked_theorems_never_enter_the_raw_arena_wire_state() {
        let Fixture { mut kernel, p, .. } = fixture();
        let before = kernel.arena().clone();
        let theorem = kernel.assume(p).unwrap();
        assert!(kernel.theorem(theorem).is_ok());
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.into_arena(), before);
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
        let not_p = PropId::positive(not_p_ref);
        let formula_ref = kernel.op2(Op2::And, p.reference(), not_p_ref).unwrap();
        let formula = PropId::positive(formula_ref);
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
        let nested = PropId::positive(nested);
        let theorem = kernel.assume(nested).unwrap();
        let flattened = kernel.flatten_conclusion(theorem, nested).unwrap();
        let mut expected = vec![p.negated(), q];
        expected.sort_unstable();
        assert_eq!(kernel.theorem(flattened).unwrap().conclusions, expected);

        let bool_ty = kernel.classifier(p.reference()).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let falsehood = PropId::positive(falsehood);
        let false_theorem = kernel.assume(falsehood).unwrap();
        let eliminated = kernel
            .expand_conclusion(false_theorem, falsehood, None)
            .unwrap();
        assert!(kernel.theorem(eliminated).unwrap().conclusions.is_empty());
    }

    #[test]
    fn recursive_tree_folding_round_trips_both_sides() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), q.reference()).unwrap());
        let conjunction_id = kernel.assume(conjunction).unwrap();
        let flat_left = kernel.flatten_premise(conjunction_id, conjunction).unwrap();
        let folded_left = kernel.fold_premise(flat_left, conjunction).unwrap();
        assert_eq!(
            kernel.theorem(folded_left).unwrap(),
            kernel.theorem(conjunction_id).unwrap()
        );

        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let disjunction_id = kernel.assume(disjunction).unwrap();
        let flat_right = kernel
            .flatten_conclusion(disjunction_id, disjunction)
            .unwrap();
        let folded_right = kernel.fold_conclusion(flat_right, disjunction).unwrap();
        assert_eq!(
            kernel.theorem(folded_right).unwrap(),
            kernel.theorem(disjunction_id).unwrap()
        );
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

    #[test]
    fn identity_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.assume(p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn weakening_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.assume(p).unwrap();
        let theorem = kernel.weaken(assumed, &[q], &[q.negated()]).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn cut_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let left = kernel.assume(p).unwrap();
        let right = kernel.assume(p).unwrap();
        let theorem = kernel.cut(left, right, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn constants_are_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let bool_ty = kernel.classifier(p.reference()).unwrap();
        let falsehood = PropId::positive(kernel.bool(bool_ty, false).unwrap());
        let truth = PropId::positive(kernel.bool(bool_ty, true).unwrap());
        let false_left = kernel.false_left(falsehood).unwrap();
        let true_right = kernel.true_right(truth).unwrap();
        assert_valid(&kernel, false_left, &[p, q]);
        assert_valid(&kernel, true_right, &[p, q]);
    }

    #[test]
    fn not_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.assume(p).unwrap();
        let theorem = kernel.not_left(assumed, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn not_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.assume(p).unwrap();
        let theorem = kernel.not_right(assumed, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), q.reference()).unwrap());
        let assumed = kernel.assume(p).unwrap();
        let premise = kernel.weaken(assumed, &[q], &[]).unwrap();
        let theorem = kernel.and_left(premise, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), q.reference()).unwrap());
        let left = kernel.assume(p).unwrap();
        let right = kernel.assume(q).unwrap();
        let theorem = kernel.and_right(left, right, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let left = kernel.assume(p).unwrap();
        let right = kernel.assume(q).unwrap();
        let theorem = kernel.or_left(left, right, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let assumed = kernel.assume(p).unwrap();
        let premise = kernel.weaken(assumed, &[], &[q]).unwrap();
        let theorem = kernel.or_right(premise, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication =
            PropId::positive(kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap());
        let left = kernel.assume(p).unwrap();
        let right = kernel.assume(q).unwrap();
        let theorem = kernel.imp_left(left, right, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication =
            PropId::positive(kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap());
        let assumed = kernel.assume(q).unwrap();
        let premise = kernel.weaken(assumed, &[p], &[]).unwrap();
        let theorem = kernel.imp_right(premise, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn rejected_rules_do_not_allocate_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.assume(p).unwrap();
        assert!(kernel.cut(first, first, q).is_err());
        let second = kernel.assume(q).unwrap();
        assert_eq!(second.get(), first.get() + 1);
        assert!(kernel.and_left(first, q).is_err());
        let third = kernel.assume(q.negated()).unwrap();
        assert_eq!(third.get(), second.get() + 1);
    }

    #[test]
    fn canonical_sets_support_idempotent_connective_rules() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), p.reference()).unwrap());
        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), p.reference()).unwrap());
        let identity = kernel.identity(p).unwrap();
        let and_left = kernel.and_left(identity, conjunction).unwrap();
        let or_right = kernel.or_right(identity, disjunction).unwrap();
        assert_valid(&kernel, and_left, &[p, q]);
        assert_valid(&kernel, or_right, &[p, q]);
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

    fn assert_valid(kernel: &Kernel, theorem: ThmId, atoms: &[PropId]) {
        for mask in 0..(1_usize << atoms.len()) {
            let values: BTreeMap<_, _> = atoms
                .iter()
                .enumerate()
                .map(|(index, atom)| (atom.reference(), mask & (1 << index) != 0))
                .collect();
            let sequent = kernel.theorem(theorem).unwrap();
            assert!(
                !sequent
                    .premises
                    .iter()
                    .copied()
                    .all(|p| evaluate(kernel, p, &values))
                    || sequent
                        .conclusions
                        .iter()
                        .copied()
                        .any(|p| evaluate(kernel, p, &values)),
                "invalid sequent {sequent:?} under mask {mask}"
            );
        }
    }

    fn evaluate(kernel: &Kernel, proposition: PropId, atoms: &BTreeMap<Ref, bool>) -> bool {
        let reference = proposition.reference();
        let positive = if let Some(value) = kernel.arena().bool_value(reference) {
            value
        } else if let Some(op) = kernel.arena().op1(reference) {
            let child = kernel.arena().children(reference).unwrap().next().unwrap();
            match op {
                Op1::Not => !evaluate(kernel, PropId::positive(child), atoms),
            }
        } else if let Some(op) = kernel.arena().op2(reference) {
            let children: Vec<_> = kernel.arena().children(reference).unwrap().collect();
            let left = evaluate(kernel, PropId::positive(children[0]), atoms);
            let right = evaluate(kernel, PropId::positive(children[1]), atoms);
            match op {
                Op2::And => left && right,
                Op2::Or => left || right,
                Op2::Imp => !left || right,
            }
        } else {
            *atoms
                .get(&reference)
                .expect("test valuation covers every atom")
        };
        if proposition.is_positive() {
            positive
        } else {
            !positive
        }
    }
}
