//! Checked finite classical sequents over stable local term references.

use std::num::{NonZeroI64, NonZeroU64};

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

/// A compact, not-necessarily-canonical sequence of propositions.
///
/// Kernel rule boundaries validate, sort, and deduplicate these sequences
/// before storing them in a theorem.
pub type PropVec = SmallVec<[PropId; 2]>;

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

/// An ephemeral one-based checked theorem handle.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThmId(NonZeroU64);

impl ThmId {
    /// Constructs a one-based theorem handle.
    #[must_use]
    pub const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(v) => Some(Self(v)),
            None => None,
        }
    }
    /// Returns the one-based theorem index.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

/// A checked sequent `AND(premises) |- OR(conclusions)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Thm {
    premises: PropVec,
    conclusions: PropVec,
}

impl Thm {
    /// Returns the canonical sorted, deduplicated premises.
    #[must_use]
    pub fn premises(&self) -> &[PropId] {
        &self.premises
    }

    /// Returns the canonical sorted, deduplicated conclusions.
    #[must_use]
    pub fn conclusions(&self) -> &[PropId] {
        &self.conclusions
    }
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
    thms: Vec<Thm>,
    live: Vec<bool>,
    free: Vec<ThmId>,
}

impl ClassicalState {
    pub(super) const fn new() -> Self {
        Self {
            thms: Vec::new(),
            live: Vec::new(),
            free: Vec::new(),
        }
    }
}

impl Kernel {
    /// Borrows a checked theorem sequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent.
    pub fn theorem(&self, id: ThmId) -> Result<&Thm, KernelError> {
        let position = usize::try_from(id.get() - 1).unwrap_or(usize::MAX);
        if self.classical.live.get(position) != Some(&true) {
            return Err(KernelError::MissingTheorem { id });
        }
        self.classical
            .thms
            .get(position)
            .ok_or(KernelError::MissingTheorem { id })
    }

    /// Recovers a theorem whose conclusion has exactly one proposition.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem exists and has one conclusion.
    pub fn hol_theorem(&self, id: ThmId) -> Result<HolTheorem<'_>, KernelError> {
        let sequent = self.theorem(id)?;
        let [conclusion] = sequent.conclusions() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "singleton conclusion",
            });
        };
        Ok(HolTheorem {
            assumptions: sequent.premises(),
            conclusion: *conclusion,
        })
    }

    /// Introduces the identity sequent `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn identity(&mut self, p: PropId) -> Result<ThmId, KernelError> {
        self.push_sequent(&[p], &[p])
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
        let old = self.theorem(theorem)?.clone();
        let mut premises_out = old.premises;
        premises_out.extend_from_slice(premises);
        let mut conclusions_out = old.conclusions;
        conclusions_out.extend_from_slice(conclusions);
        self.push_sequent(&premises_out, &conclusions_out)
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
        let lhs = self.theorem(left)?.clone();
        let rhs = self.theorem(right)?.clone();
        let mut left_conclusions = lhs.conclusions.clone();
        let mut right_premises = rhs.premises.clone();
        if !remove_sorted(&mut left_conclusions, proposition)
            || !remove_sorted(&mut right_premises, proposition)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "cut" });
        }
        let mut premises = lhs.premises;
        premises.extend_from_slice(&right_premises);
        let mut conclusions = left_conclusions;
        conclusions.extend_from_slice(&rhs.conclusions);
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
        let source = self.theorem(theorem)?.clone();
        let mut conclusions = source.conclusions.clone();
        if !remove_sorted(&mut conclusions, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not left" });
        }
        let mut premises = source.premises;
        premises.push(p.negated());
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
        let source = self.theorem(theorem)?.clone();
        let mut premises = source.premises.clone();
        if !remove_sorted(&mut premises, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not right" });
        }
        let mut conclusions = source.conclusions;
        conclusions.push(p.negated());
        self.push_sequent(&premises, &conclusions)
    }

    /// Folds two conjunct premises into their checked conjunction opcode.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands occur in the premise and
    /// `conjunction` is their positive `tm.and` opcode.
    pub fn and_left(&mut self, theorem: ThmId, conjunction: PropId) -> Result<ThmId, KernelError> {
        let (left, right) = self.require_binary(conjunction, Op2::And)?;
        let source = self.theorem(theorem)?.clone();
        let mut premises = source.premises.clone();
        if !remove_pair(&mut premises, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and left" });
        }
        premises.push(conjunction);
        let conclusions = source.conclusions.clone();
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
        let lhs = self.theorem(left_theorem)?.clone();
        let rhs = self.theorem(right_theorem)?.clone();
        let mut left_conc = lhs.conclusions.clone();
        let mut right_conc = rhs.conclusions.clone();
        if !remove_sorted(&mut left_conc, left) || !remove_sorted(&mut right_conc, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and right" });
        }
        let mut premises = lhs.premises;
        premises.extend_from_slice(&rhs.premises);
        let mut conclusions = left_conc;
        conclusions.extend_from_slice(&right_conc);
        conclusions.push(conjunction);
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
        let lhs = self.theorem(left_theorem)?.clone();
        let rhs = self.theorem(right_theorem)?.clone();
        let mut left_prem = lhs.premises.clone();
        let mut right_prem = rhs.premises.clone();
        if !remove_sorted(&mut left_prem, left) || !remove_sorted(&mut right_prem, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or left" });
        }
        let mut premises = left_prem;
        premises.extend_from_slice(&right_prem);
        premises.push(disjunction);
        let mut conclusions = lhs.conclusions;
        conclusions.extend_from_slice(&rhs.conclusions);
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
        let source = self.theorem(theorem)?.clone();
        let mut conclusions = source.conclusions.clone();
        if !remove_pair(&mut conclusions, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or right" });
        }
        conclusions.push(disjunction);
        let premises = source.premises.clone();
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
        let lhs = self.theorem(left_theorem)?.clone();
        let rhs = self.theorem(right_theorem)?.clone();
        let mut left_conc = lhs.conclusions.clone();
        let mut right_prem = rhs.premises.clone();
        if !remove_sorted(&mut left_conc, antecedent) || !remove_sorted(&mut right_prem, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp left" });
        }
        let mut premises = lhs.premises;
        premises.extend_from_slice(&right_prem);
        premises.push(implication);
        let mut conclusions = left_conc;
        conclusions.extend_from_slice(&rhs.conclusions);
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
        let source = self.theorem(theorem)?.clone();
        let mut premises = source.premises.clone();
        let mut conclusions = source.conclusions.clone();
        if !remove_sorted(&mut premises, antecedent) || !remove_sorted(&mut conclusions, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp right" });
        }
        conclusions.push(implication);
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
        let lhs = self.theorem(left)?.clone();
        let rhs = self.theorem(right)?.clone();
        let mut left_conc = lhs.conclusions.clone();
        let mut right_conc = rhs.conclusions.clone();
        if !remove_sorted(&mut left_conc, pivot) || !remove_sorted(&mut right_conc, pivot.negated())
        {
            return Err(KernelError::InvalidTheoremRule { rule: "resolution" });
        }
        let mut premises = lhs.premises;
        premises.extend_from_slice(&rhs.premises);
        let mut conclusions = left_conc;
        conclusions.extend_from_slice(&right_conc);
        self.push_sequent(&premises, &conclusions)
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
        let source = self.theorem(theorem)?.clone();
        let mut conc = source.conclusions.clone();
        if !remove_sorted(&mut conc, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion expansion",
            });
        }
        let replacement = self.expand_right(formula, branch)?;
        conc.extend_from_slice(&replacement);
        self.push_sequent(&source.premises, &conc)
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
        let source = self.theorem(theorem)?.clone();
        let mut conclusions = source.conclusions.clone();
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
        conclusions.extend_from_slice(&leaves);
        self.push_sequent(&source.premises, &conclusions)
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
        let source = self.theorem(theorem)?.clone();
        let mut premises = source.premises.clone();
        if !remove_sorted(&mut premises, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "premise flattening",
            });
        }
        let leaves = self.collect_tree(formula, TreeSide::Conjunctive)?;
        premises.extend_from_slice(&leaves);
        let conclusions = source.conclusions.clone();
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

    /// Removes theorem handles atomically and makes their slots reusable.
    ///
    /// # Errors
    ///
    /// Returns an error and changes nothing if any handle is repeated, absent,
    /// or already removed.
    pub fn remove_theorems(&mut self, ids: &[ThmId]) -> Result<(), KernelError> {
        let mut sorted = ids.to_vec();
        sorted.sort_unstable();
        if sorted.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "theorem deletion",
            });
        }
        for id in &sorted {
            self.theorem(*id)?;
        }
        for id in sorted {
            let position =
                usize::try_from(id.get() - 1).map_err(|_| KernelError::MissingTheorem { id })?;
            self.classical.live[position] = false;
            self.classical.free.push(id);
        }
        Ok(())
    }

    fn validate_prop(&self, proposition: PropId) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(proposition.reference())
            .map(|_| ())
    }
    fn push_thm(&mut self, theorem: Thm) -> Result<ThmId, KernelError> {
        if let Some(id) = self.classical.free.pop() {
            let position =
                usize::try_from(id.get() - 1).expect("resident theorem index fits usize");
            self.classical.thms[position] = theorem;
            self.classical.live[position] = true;
            return Ok(id);
        }
        let id = u64::try_from(self.classical.thms.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .and_then(ThmId::new)
            .ok_or(KernelError::TooManyTheorems)?;
        self.classical.thms.push(theorem);
        self.classical.live.push(true);
        Ok(id)
    }
    fn push_sequent(
        &mut self,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<ThmId, KernelError> {
        let premises = self.canonical_props(premises)?;
        let conclusions = self.canonical_props(conclusions)?;
        self.push_thm(Thm {
            premises,
            conclusions,
        })
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
    fn canonical_props(&self, propositions: &[PropId]) -> Result<PropVec, KernelError> {
        let mut sorted = propositions.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        for proposition in &sorted {
            self.validate_prop(*proposition)?;
        }
        let mut canonical = PropVec::new();
        canonical.extend_from_slice(&sorted);
        Ok(canonical)
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

    fn collect_tree(&self, formula: PropId, side: TreeSide) -> Result<PropVec, KernelError> {
        let mut pending = vec![formula];
        let mut leaves = PropVec::new();
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
        let source = self.theorem(theorem)?.clone();
        let leaves = self.collect_tree(formula, side)?;
        let (mut premises, mut conclusions) = (source.premises.clone(), source.conclusions.clone());
        let target = match side {
            TreeSide::Conjunctive => &mut premises,
            TreeSide::Disjunctive => &mut conclusions,
        };
        if leaves.iter().any(|leaf| !remove_sorted(target, *leaf)) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "opcode tree folding",
            });
        }
        target.push(formula);
        self.push_sequent(&premises, &conclusions)
    }
}

#[derive(Clone, Copy)]
enum TreeSide {
    Conjunctive,
    Disjunctive,
}

fn remove_sorted(values: &mut PropVec, needle: PropId) -> bool {
    match values.binary_search(&needle) {
        Ok(index) => {
            values.remove(index);
            true
        }
        Err(_) => false,
    }
}

fn remove_pair(values: &mut PropVec, left: PropId, right: PropId) -> bool {
    if !remove_sorted(values, left) {
        return false;
    }
    left == right || remove_sorted(values, right)
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
    fn theorem_sets_are_inline_sorted_and_deduplicated() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        let theorem = kernel.weaken(identity, &[q, p, q], &[q, p, q]).unwrap();
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(kernel.theorem(theorem).unwrap().premises(), expected);
        assert_eq!(kernel.theorem(theorem).unwrap().conclusions(), expected);
        assert!(
            !kernel.theorem(theorem).unwrap().premises.spilled(),
            "len={} capacity={}",
            kernel.theorem(theorem).unwrap().premises.len(),
            kernel.theorem(theorem).unwrap().premises.capacity()
        );

        let widened = kernel
            .weaken(theorem, &[p.negated()], &[q.negated()])
            .unwrap();
        assert!(kernel.theorem(widened).unwrap().premises.spilled());
    }

    #[test]
    fn weakening_canonicalizes_hostile_unsorted_input_before_admission() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        let theorem = kernel
            .weaken(identity, &[q, p.negated(), q, p], &[q.negated(), p, q])
            .unwrap();
        let mut expected_premises = vec![p, p.negated(), q];
        expected_premises.sort_unstable();
        let mut expected_conclusions = vec![p, q, q.negated()];
        expected_conclusions.sort_unstable();
        assert_eq!(
            kernel.theorem(theorem).unwrap().premises(),
            expected_premises
        );
        assert_eq!(
            kernel.theorem(theorem).unwrap().conclusions(),
            expected_conclusions
        );
    }

    #[test]
    fn deletion_is_atomic_and_reuses_only_ephemeral_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let p_id = kernel.identity(p).unwrap();
        let q_id = kernel.identity(q).unwrap();
        assert!(kernel.remove_theorems(&[p_id, p_id]).is_err());
        assert!(kernel.theorem(p_id).is_ok());
        assert!(kernel.theorem(q_id).is_ok());
        kernel.remove_theorems(&[p_id]).unwrap();
        assert!(matches!(
            kernel.theorem(p_id),
            Err(KernelError::MissingTheorem { .. })
        ));
        assert_eq!(kernel.identity(q.negated()).unwrap(), p_id);
        assert!(kernel.theorem(q_id).is_ok());
    }

    #[test]
    fn deletion_with_an_absent_handle_is_atomic_and_reuse_is_lifo() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.identity(p).unwrap();
        let second = kernel.identity(q).unwrap();
        let absent = ThmId::new(second.get() + 1).unwrap();
        assert!(kernel.remove_theorems(&[first, absent]).is_err());
        assert!(kernel.theorem(first).is_ok());
        assert!(kernel.theorem(second).is_ok());

        kernel.remove_theorems(&[first, second]).unwrap();
        assert!(kernel.theorem(first).is_err());
        assert!(kernel.theorem(second).is_err());
        assert_eq!(kernel.identity(p.negated()).unwrap(), second);
        assert_eq!(kernel.identity(q.negated()).unwrap(), first);
    }

    #[test]
    fn checked_theorems_never_enter_the_raw_arena_wire_state() {
        let Fixture { mut kernel, p, .. } = fixture();
        let before = kernel.arena().clone();
        let theorem = kernel.identity(p).unwrap();
        assert!(kernel.theorem(theorem).is_ok());
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.into_arena(), before);
    }

    #[test]
    fn conclusion_constant_expansion_eliminates_exactly_signed_false() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let falsehood = PropId::positive(kernel.bool(bool_ty, false).unwrap());
        let truth = PropId::positive(kernel.bool(bool_ty, true).unwrap());

        for signed_false in [falsehood, truth.negated()] {
            let identity = kernel.identity(signed_false).unwrap();
            let expanded = kernel
                .expand_conclusion(identity, signed_false, None)
                .unwrap();
            assert!(kernel.theorem(expanded).unwrap().conclusions().is_empty());
        }

        for signed_true in [truth, falsehood.negated()] {
            let identity = kernel.identity(signed_true).unwrap();
            assert!(
                kernel
                    .expand_conclusion(identity, signed_true, None)
                    .is_err()
            );
        }
    }

    #[test]
    fn weakening_resolution_and_polarity_transfer_form_sound_sequents() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        let left = kernel.weaken(assumed_p, &[], &[q]).unwrap();
        let right = kernel.weaken(assumed_not_p, &[], &[q]).unwrap();
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_eq!(kernel.theorem(resolved).unwrap().conclusions(), [q]);

        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        let contradiction = kernel.resolve(assumed_p, assumed_not_p, p).unwrap();
        let with_q = kernel.weaken(contradiction, &[q], &[]).unwrap();
        let discharged = kernel.not_right(with_q, q).unwrap();
        assert_eq!(
            kernel.theorem(discharged).unwrap().conclusions(),
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
        let root = kernel.identity(formula).unwrap();
        let p_clause = kernel
            .expand_conclusion(root, formula, Some(false))
            .unwrap();
        let not_clause = kernel.expand_conclusion(root, formula, Some(true)).unwrap();
        let neg_p_clause = kernel.expand_conclusion(not_clause, not_p, None).unwrap();
        let refutation = kernel.resolve(p_clause, neg_p_clause, p).unwrap();
        let sequent = kernel.theorem(refutation).unwrap();
        assert_eq!(sequent.premises(), [formula]);
        assert!(sequent.conclusions().is_empty());
    }

    #[test]
    fn recursive_flattening_handles_or_not_imp_and_false() {
        let Fixture { mut kernel, p, q } = fixture();
        let not_p = kernel.op1(Op1::Not, p.reference()).unwrap();
        let implication = kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap();
        let nested = kernel.op2(Op2::Or, not_p, implication).unwrap();
        let nested = PropId::positive(nested);
        let theorem = kernel.identity(nested).unwrap();
        let flattened = kernel.flatten_conclusion(theorem, nested).unwrap();
        let mut expected = vec![p.negated(), q];
        expected.sort_unstable();
        assert_eq!(kernel.theorem(flattened).unwrap().conclusions(), expected);

        let bool_ty = kernel.classifier(p.reference()).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let falsehood = PropId::positive(falsehood);
        let false_theorem = kernel.identity(falsehood).unwrap();
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
        let conjunction_id = kernel.identity(conjunction).unwrap();
        let flat_left = kernel.flatten_premise(conjunction_id, conjunction).unwrap();
        let folded_left = kernel.fold_premise(flat_left, conjunction).unwrap();
        assert_eq!(
            kernel.theorem(folded_left).unwrap(),
            kernel.theorem(conjunction_id).unwrap()
        );

        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let disjunction_id = kernel.identity(disjunction).unwrap();
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
        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
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
        let theorem = kernel.identity(p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn weakening_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        let theorem = kernel.weaken(assumed, &[q], &[q.negated()]).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn cut_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p).unwrap();
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
        let assumed = kernel.identity(p).unwrap();
        let theorem = kernel.not_left(assumed, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn not_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        let theorem = kernel.not_right(assumed, p).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), q.reference()).unwrap());
        let assumed = kernel.identity(p).unwrap();
        let premise = kernel.weaken(assumed, &[q], &[]).unwrap();
        let theorem = kernel.and_left(premise, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction =
            PropId::positive(kernel.op2(Op2::And, p.reference(), q.reference()).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.and_right(left, right, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.or_left(left, right, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction =
            PropId::positive(kernel.op2(Op2::Or, p.reference(), q.reference()).unwrap());
        let assumed = kernel.identity(p).unwrap();
        let premise = kernel.weaken(assumed, &[], &[q]).unwrap();
        let theorem = kernel.or_right(premise, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication =
            PropId::positive(kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.imp_left(left, right, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication =
            PropId::positive(kernel.op2(Op2::Imp, p.reference(), q.reference()).unwrap());
        let assumed = kernel.identity(q).unwrap();
        let premise = kernel.weaken(assumed, &[p], &[]).unwrap();
        let theorem = kernel.imp_right(premise, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn rejected_rules_do_not_allocate_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.identity(p).unwrap();
        assert!(kernel.cut(first, first, q).is_err());
        let second = kernel.identity(q).unwrap();
        assert_eq!(second.get(), first.get() + 1);
        assert!(kernel.and_left(first, q).is_err());
        let third = kernel.identity(q.negated()).unwrap();
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

    fn valid(sequent: &Thm, p: PropId, p_value: bool, q: PropId, q_value: bool) -> bool {
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
        !sequent.premises().iter().copied().all(&value)
            || sequent.conclusions().iter().copied().any(value)
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
