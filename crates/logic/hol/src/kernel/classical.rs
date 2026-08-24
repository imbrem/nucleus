//! Checked finite classical sequents over stable local term references.

use covalence_logic_classical::{ClassicalArena, Clause, Cnf, Cube, Dnf, Thm, ThmId};
pub use covalence_logic_classical::{Lit as PropId, LitError as PropIdError};
use smallvec::SmallVec;

use super::{Kernel, KernelError};
use crate::{
    Ref,
    builtin::{Op1, Op2},
};

/// A compact sequence of propositions.
pub type PropVec = SmallVec<[PropId; 2]>;

fn positive(reference: Ref) -> PropId {
    PropId::positive(reference.get())
}

fn reference(proposition: PropId) -> Ref {
    Ref::new(proposition.magnitude()).expect("PropId magnitude is nonzero")
}

pub(super) type ClassicalState = ClassicalArena;

impl Kernel {
    /// Borrows a checked theorem sequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent.
    pub fn theorem(&self, id: ThmId) -> Result<&Thm, KernelError> {
        self.classical
            .theorem(id)
            .map_err(|_| KernelError::MissingTheorem { id })
    }

    /// Introduces the identity sequent `[p] |- [p]`.
    ///
    /// # Errors
    ///
    /// Returns an error if `p` is not Boolean or allocation fails.
    pub fn identity(&mut self, p: PropId) -> Result<ThmId, KernelError> {
        self.push_sequent(&[p], &[p])
    }

    /// Weakens this theorem in place by adding propositions on either side.
    ///
    /// # Errors
    ///
    /// Returns an error for missing evidence or an invalid proposition.
    pub fn weaken(
        &mut self,
        theorem: ThmId,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<(), KernelError> {
        let old = self.theorem(theorem)?.clone();
        let mut premises_out = old.premises().as_slice().to_vec();
        premises_out.extend(premises.iter().copied().map(unit_clause));
        let mut conclusions_out = old.conclusions().as_slice().to_vec();
        conclusions_out.extend(conclusions.iter().copied().map(unit_cube));
        self.validate_props(premises.iter().chain(conclusions.iter()).copied())?;
        let replacement = Thm::new(Cnf::new(premises_out), Dnf::new(conclusions_out));
        self.replace_theorem(theorem, replacement)
    }

    /// Weakens this theorem with complete left clauses and right cubes.
    ///
    /// Adding a clause strengthens the CNF antecedent. Adding a cube weakens
    /// the DNF consequent. Input order and duplicates are normalized after
    /// every proposition has been checked as a resident Boolean term.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing theorem or an invalid proposition. The
    /// theorem is unchanged on error.
    pub fn weaken_matrix(
        &mut self,
        theorem: ThmId,
        premises: &[Clause],
        conclusions: &[Cube],
    ) -> Result<(), KernelError> {
        self.theorem(theorem)?;
        self.validate_props(
            premises
                .iter()
                .flat_map(Clause::literals)
                .chain(conclusions.iter().flat_map(Cube::literals))
                .copied(),
        )?;
        let mut replacement = self.theorem(theorem)?.clone();
        let mut left = replacement.premises().as_slice().to_vec();
        left.extend_from_slice(premises);
        let mut right = replacement.conclusions().as_slice().to_vec();
        right.extend_from_slice(conclusions);
        replacement = Thm::new(Cnf::new(left), Dnf::new(right));
        self.replace_theorem(theorem, replacement)
    }

    /// Moves one indexed left clause to the right as its pointwise-negated cube.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or clause is absent. The theorem is
    /// unchanged on error.
    pub fn move_clause_right(&mut self, theorem: ThmId, index: usize) -> Result<(), KernelError> {
        self.classical
            .move_clause_right(theorem, index)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "clause transfer right",
            })
    }

    /// Moves one indexed right cube to the left as its pointwise-negated clause.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or cube is absent. The theorem is
    /// unchanged on error.
    pub fn move_cube_left(&mut self, theorem: ThmId, index: usize) -> Result<(), KernelError> {
        self.classical
            .move_cube_left(theorem, index)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "cube transfer left",
            })
    }

    /// Canonicalizes every clause, cube, and matrix row in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem is absent.
    pub fn normalize_theorem(&mut self, theorem: ThmId) -> Result<(), KernelError> {
        self.classical
            .normalize(theorem)
            .map_err(|_| KernelError::MissingTheorem { id: theorem })
    }

    /// Canonicalizes one indexed left clause in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or clause is absent.
    pub fn normalize_clause(&mut self, theorem: ThmId, index: usize) -> Result<(), KernelError> {
        self.classical
            .normalize_clause(theorem, index)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "clause normalization",
            })
    }

    /// Canonicalizes one indexed right cube in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or cube is absent.
    pub fn normalize_cube(&mut self, theorem: ThmId, index: usize) -> Result<(), KernelError> {
        self.classical
            .normalize_cube(theorem, index)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "cube normalization",
            })
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
        let mut left_conclusions = lhs.conclusions().as_slice().to_vec();
        let mut right_premises = rhs.premises().as_slice().to_vec();
        if !remove_unit_cube(&mut left_conclusions, proposition)
            || !remove_unit_clause(&mut right_premises, proposition)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "cut" });
        }
        let mut premises = lhs.premises().as_slice().to_vec();
        premises.extend(right_premises);
        let mut conclusions = left_conclusions;
        conclusions.extend_from_slice(rhs.conclusions().as_slice());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
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

    /// Moves a conclusion to the left with complementary polarity in place.
    ///
    /// From `Γ |- Δ, p`, derives `¬p, Γ |- Δ`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the conclusion.
    pub fn not_left(&mut self, theorem: ThmId, p: PropId) -> Result<(), KernelError> {
        let source = self.theorem(theorem)?.clone();
        let mut conclusions = source.conclusions().as_slice().to_vec();
        if !remove_unit_cube(&mut conclusions, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not left" });
        }
        let mut premises = source.premises().as_slice().to_vec();
        premises.push(unit_clause(p.negated()));
        let replacement = Thm::new(Cnf::new(premises), Dnf::new(conclusions));
        self.replace_theorem(theorem, replacement)
    }

    /// Moves a premise to the right with complementary polarity in place.
    ///
    /// From `p, Γ |- Δ`, derives `Γ |- Δ, ¬p`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `p` occurs in the premise.
    pub fn not_right(&mut self, theorem: ThmId, p: PropId) -> Result<(), KernelError> {
        let source = self.theorem(theorem)?.clone();
        let mut premises = source.premises().as_slice().to_vec();
        if !remove_unit_clause(&mut premises, p) {
            return Err(KernelError::InvalidTheoremRule { rule: "not right" });
        }
        let mut conclusions = source.conclusions().as_slice().to_vec();
        conclusions.push(unit_cube(p.negated()));
        let replacement = Thm::new(Cnf::new(premises), Dnf::new(conclusions));
        self.replace_theorem(theorem, replacement)
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
        let mut premises = source.premises().as_slice().to_vec();
        if !remove_unit_clause_pair(&mut premises, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and left" });
        }
        premises.push(unit_clause(conjunction));
        self.push_theorem(Thm::new(Cnf::new(premises), source.conclusions().clone()))
    }

    /// Introduces a checked conjunction on the right, concatenating contexts.
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
        let mut left_conc = lhs.conclusions().as_slice().to_vec();
        let mut right_conc = rhs.conclusions().as_slice().to_vec();
        if !remove_unit_cube(&mut left_conc, left) || !remove_unit_cube(&mut right_conc, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "and right" });
        }
        let mut premises = lhs.premises().as_slice().to_vec();
        premises.extend_from_slice(rhs.premises().as_slice());
        let mut conclusions = left_conc;
        conclusions.extend(right_conc);
        conclusions.push(unit_cube(conjunction));
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }

    /// Introduces a checked disjunction on the left, concatenating contexts.
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
        let mut left_prem = lhs.premises().as_slice().to_vec();
        let mut right_prem = rhs.premises().as_slice().to_vec();
        if !remove_unit_clause(&mut left_prem, left) || !remove_unit_clause(&mut right_prem, right)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "or left" });
        }
        let mut premises = left_prem;
        premises.extend(right_prem);
        premises.push(unit_clause(disjunction));
        let mut conclusions = lhs.conclusions().as_slice().to_vec();
        conclusions.extend_from_slice(rhs.conclusions().as_slice());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
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
        let mut conclusions = source.conclusions().as_slice().to_vec();
        if !remove_unit_cube_pair(&mut conclusions, left, right) {
            return Err(KernelError::InvalidTheoremRule { rule: "or right" });
        }
        conclusions.push(unit_cube(disjunction));
        self.push_theorem(Thm::new(source.premises().clone(), Dnf::new(conclusions)))
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
        let mut left_conc = lhs.conclusions().as_slice().to_vec();
        let mut right_prem = rhs.premises().as_slice().to_vec();
        if !remove_unit_cube(&mut left_conc, antecedent)
            || !remove_unit_clause(&mut right_prem, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp left" });
        }
        let mut premises = lhs.premises().as_slice().to_vec();
        premises.extend(right_prem);
        premises.push(unit_clause(implication));
        let mut conclusions = left_conc;
        conclusions.extend_from_slice(rhs.conclusions().as_slice());
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
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
        let mut premises = source.premises().as_slice().to_vec();
        let mut conclusions = source.conclusions().as_slice().to_vec();
        if !remove_unit_clause(&mut premises, antecedent)
            || !remove_unit_cube(&mut conclusions, consequent)
        {
            return Err(KernelError::InvalidTheoremRule { rule: "imp right" });
        }
        conclusions.push(unit_cube(implication));
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
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
        let mut left_conc = lhs.conclusions().as_slice().to_vec();
        let mut right_conc = rhs.conclusions().as_slice().to_vec();
        if !remove_unit_cube(&mut left_conc, pivot)
            || !remove_unit_cube(&mut right_conc, pivot.negated())
        {
            return Err(KernelError::InvalidTheoremRule { rule: "resolution" });
        }
        let mut premises = lhs.premises().as_slice().to_vec();
        premises.extend_from_slice(rhs.premises().as_slice());
        let mut conclusions = left_conc;
        conclusions.extend(right_conc);
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
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
        let mut conc = source.conclusions().as_slice().to_vec();
        if !remove_unit_cube(&mut conc, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "conclusion expansion",
            });
        }
        let replacement = self.expand_right(formula, branch)?;
        conc.extend(replacement.into_iter().map(unit_cube));
        self.push_theorem(Thm::new(source.premises().clone(), Dnf::new(conc)))
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
        let mut conclusions = source.conclusions().as_slice().to_vec();
        if !remove_unit_cube(&mut conclusions, formula) {
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
        conclusions.extend(leaves.into_iter().map(unit_cube));
        self.push_theorem(Thm::new(source.premises().clone(), Dnf::new(conclusions)))
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
        let mut premises = source.premises().as_slice().to_vec();
        if !remove_unit_clause(&mut premises, formula) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "premise flattening",
            });
        }
        let leaves = self.collect_tree(formula, TreeSide::Conjunctive)?;
        premises.extend(leaves.into_iter().map(unit_clause));
        self.push_theorem(Thm::new(Cnf::new(premises), source.conclusions().clone()))
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

    /// Copies a checked theorem into a newly allocated or reused slot.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent.
    pub fn copy_theorem(&mut self, source: ThmId) -> Result<ThmId, KernelError> {
        self.classical
            .copy(source)
            .map_err(|_| KernelError::MissingTheorem { id: source })
    }

    /// Removes one theorem. Removed slots are reused by later allocations.
    #[must_use]
    pub fn remove_theorem(&mut self, id: ThmId) -> bool {
        self.classical.remove(id).is_ok()
    }

    fn validate_prop(&self, proposition: PropId) -> Result<(), KernelError> {
        self.require_bool_term::<std::convert::Infallible>(reference(proposition))
            .map(|_| ())
    }
    fn push_theorem(&mut self, mut theorem: Thm) -> Result<ThmId, KernelError> {
        theorem.normalize();
        self.classical
            .insert(theorem)
            .map_err(|_| KernelError::TooManyTheorems)
    }
    fn push_sequent(
        &mut self,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<ThmId, KernelError> {
        let theorem = self.checked_sequent(premises, conclusions)?;
        self.push_theorem(theorem)
    }

    fn checked_sequent(
        &self,
        premises: &[PropId],
        conclusions: &[PropId],
    ) -> Result<Thm, KernelError> {
        let premises = self.canonical_props(premises)?;
        let conclusions = self.canonical_props(conclusions)?;
        Ok(Thm::new(
            Cnf::new(premises.into_iter().map(unit_clause)),
            Dnf::new(conclusions.into_iter().map(unit_cube)),
        ))
    }

    fn replace_theorem(&mut self, id: ThmId, mut theorem: Thm) -> Result<(), KernelError> {
        theorem.normalize();
        self.classical
            .replace(id, theorem)
            .map_err(|_| KernelError::MissingTheorem { id })
    }
    fn signed_bool_value(&self, proposition: PropId) -> Result<Option<bool>, KernelError> {
        self.validate_prop(proposition)?;
        Ok(self.arena.bool_value(reference(proposition)).map(|value| {
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
        if !proposition.is_positive() || self.arena.op2(reference(proposition)) != Some(expected) {
            return Err(KernelError::InvalidTheoremRule {
                rule: "binary connective",
            });
        }
        let mut children =
            self.arena
                .children(reference(proposition))
                .ok_or(KernelError::MissingDefinition {
                    reference: reference(proposition),
                })?;
        let left = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        let right = children.next().ok_or(KernelError::InvalidTheoremRule {
            rule: "binary connective",
        })?;
        Ok((positive(left), positive(right)))
    }
    fn validate_props(
        &self,
        propositions: impl IntoIterator<Item = PropId>,
    ) -> Result<(), KernelError> {
        for proposition in propositions {
            self.validate_prop(proposition)?;
        }
        Ok(())
    }
    fn canonical_props(&self, propositions: &[PropId]) -> Result<PropVec, KernelError> {
        let mut propositions = propositions.to_vec();
        propositions.sort_unstable();
        propositions.dedup();
        for proposition in &propositions {
            self.validate_prop(*proposition)?;
        }
        Ok(PropVec::from_slice(&propositions))
    }
    fn expand_right(
        &self,
        formula: PropId,
        branch: Option<bool>,
    ) -> Result<Vec<PropId>, KernelError> {
        let reference = reference(formula);
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
            let positive = positive(child);
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
            (_, Some(Op2::Imp), true) => {
                Ok(vec![positive(children[0]).negated(), positive(children[1])])
            }
            (_, Some(Op2::Imp), false) => {
                let selected = branch.ok_or(KernelError::InvalidTheoremRule {
                    rule: "conjunctive conclusion expansion",
                })?;
                let a = positive(children[0]);
                let b = positive(children[1]).negated();
                Ok(vec![if selected { b } else { a }])
            }
            _ => Err(KernelError::InvalidTheoremRule {
                rule: "conclusion opcode expansion",
            }),
        }
    }

    fn disjunctive_children(&self, formula: PropId) -> Result<Option<Vec<PropId>>, KernelError> {
        let reference = reference(formula);
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
        let positive = positive;
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
        let reference = reference(formula);
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
        let positive = positive;
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
        Ok(leaves)
    }

    fn fold_tree(
        &mut self,
        theorem: ThmId,
        formula: PropId,
        side: TreeSide,
    ) -> Result<ThmId, KernelError> {
        let source = self.theorem(theorem)?.clone();
        let mut leaves = self.collect_tree(formula, side)?;
        leaves.sort_unstable();
        leaves.dedup();
        let mut premises = source.premises().as_slice().to_vec();
        let mut conclusions = source.conclusions().as_slice().to_vec();
        let matched = match side {
            TreeSide::Conjunctive => leaves
                .iter()
                .all(|leaf| remove_unit_clause(&mut premises, *leaf)),
            TreeSide::Disjunctive => leaves
                .iter()
                .all(|leaf| remove_unit_cube(&mut conclusions, *leaf)),
        };
        if !matched {
            return Err(KernelError::InvalidTheoremRule {
                rule: "opcode tree folding",
            });
        }
        match side {
            TreeSide::Conjunctive => premises.push(unit_clause(formula)),
            TreeSide::Disjunctive => conclusions.push(unit_cube(formula)),
        }
        self.push_theorem(Thm::new(Cnf::new(premises), Dnf::new(conclusions)))
    }
}

#[derive(Clone, Copy)]
enum TreeSide {
    Conjunctive,
    Disjunctive,
}

fn unit_clause(proposition: PropId) -> Clause {
    Clause::new([proposition])
}

fn unit_cube(proposition: PropId) -> Cube {
    Cube::new([proposition])
}

fn remove_unit_clause(clauses: &mut Vec<Clause>, proposition: PropId) -> bool {
    remove_unit_row(clauses, proposition, Clause::as_slice)
}

fn remove_unit_cube(cubes: &mut Vec<Cube>, proposition: PropId) -> bool {
    remove_unit_row(cubes, proposition, Cube::as_slice)
}

fn remove_unit_row<T>(
    rows: &mut Vec<T>,
    proposition: PropId,
    literals: fn(&T) -> &[PropId],
) -> bool {
    let Some(index) = rows.iter().position(|row| literals(row) == [proposition]) else {
        return false;
    };
    rows.remove(index);
    true
}

fn remove_unit_clause_pair(clauses: &mut Vec<Clause>, left: PropId, right: PropId) -> bool {
    if !remove_unit_clause(clauses, left) {
        return false;
    }
    left == right || remove_unit_clause(clauses, right)
}

fn remove_unit_cube_pair(cubes: &mut Vec<Cube>, left: PropId, right: PropId) -> bool {
    if !remove_unit_cube(cubes, left) {
        return false;
    }
    left == right || remove_unit_cube(cubes, right)
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
            p: positive(p),
            q: positive(q),
        }
    }

    fn unit_premises(theorem: &Thm) -> Vec<PropId> {
        theorem
            .premises()
            .clauses()
            .iter()
            .map(|clause| {
                *clause
                    .literals()
                    .first()
                    .filter(|_| clause.literals().len() == 1)
                    .unwrap()
            })
            .collect()
    }

    fn unit_conclusions(theorem: &Thm) -> Vec<PropId> {
        theorem
            .conclusions()
            .cubes()
            .iter()
            .map(|cube| {
                *cube
                    .literals()
                    .first()
                    .filter(|_| cube.literals().len() == 1)
                    .unwrap()
            })
            .collect()
    }

    #[test]
    fn signed_ids_use_inverted_polarity_without_overflow() {
        let term = Ref::new(7).unwrap();
        let positive = positive(term);
        assert_eq!(positive.get(), -7);
        assert!(positive.is_positive());
        assert_eq!(reference(positive), term);
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
    fn theorem_contexts_are_canonical_after_in_place_weakening() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        kernel.weaken(identity, &[q, p, q], &[q, p, q]).unwrap();
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(unit_premises(kernel.theorem(identity).unwrap()), expected);
        assert_eq!(
            unit_conclusions(kernel.theorem(identity).unwrap()),
            expected
        );
        assert!(
            !kernel.theorem(identity).unwrap().premises().clauses()[0]
                .literals()
                .is_empty()
        );
    }

    #[test]
    fn weakening_canonicalizes_hostile_unsorted_input_transactionally() {
        let Fixture { mut kernel, p, q } = fixture();
        let identity = kernel.identity(p).unwrap();
        kernel
            .weaken(identity, &[q, p.negated(), q, p], &[q.negated(), p, q])
            .unwrap();
        let mut expected_premises = vec![p, p.negated(), q];
        expected_premises.sort_unstable();
        let mut expected_conclusions = vec![p, q, q.negated()];
        expected_conclusions.sort_unstable();
        assert_eq!(
            unit_premises(kernel.theorem(identity).unwrap()),
            expected_premises
        );
        assert_eq!(
            unit_conclusions(kernel.theorem(identity).unwrap()),
            expected_conclusions
        );
    }

    #[test]
    fn matrix_weakening_and_indexed_transfer_preserve_non_unit_rows() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let mut clause = Clause::new([q, p.negated()]);
        clause.normalize();
        let mut cube = Cube::new([q.negated(), p]);
        cube.normalize();
        kernel
            .weaken_matrix(
                theorem,
                std::slice::from_ref(&clause),
                std::slice::from_ref(&cube),
            )
            .unwrap();

        let clause_index = kernel
            .theorem(theorem)
            .unwrap()
            .premises()
            .clauses()
            .iter()
            .position(|candidate| candidate == &clause)
            .unwrap();
        kernel.move_clause_right(theorem, clause_index).unwrap();
        assert!(
            kernel
                .theorem(theorem)
                .unwrap()
                .conclusions()
                .cubes()
                .iter()
                .any(|candidate| candidate.literals() == [q.negated(), p])
        );

        let cube_index = kernel
            .theorem(theorem)
            .unwrap()
            .conclusions()
            .cubes()
            .iter()
            .position(|candidate| candidate == &cube)
            .unwrap();
        kernel.move_cube_left(theorem, cube_index).unwrap();
        assert!(
            kernel
                .theorem(theorem)
                .unwrap()
                .premises()
                .clauses()
                .iter()
                .any(|candidate| candidate.literals() == [p.negated(), q])
        );
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn matrix_mutations_reject_bad_inputs_transactionally() {
        let Fixture { mut kernel, p, .. } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let before = kernel.theorem(theorem).unwrap().clone();
        let missing = PropId::from_raw(-999_999).unwrap();
        assert!(
            kernel
                .weaken_matrix(theorem, &[Clause::new([missing])], &[])
                .is_err()
        );
        assert_eq!(kernel.theorem(theorem).unwrap(), &before);
        assert!(kernel.move_clause_right(theorem, usize::MAX).is_err());
        assert!(kernel.move_cube_left(theorem, usize::MAX).is_err());
        assert_eq!(kernel.theorem(theorem).unwrap(), &before);
    }

    #[test]
    fn deletion_reuses_only_ephemeral_theorem_slots() {
        let Fixture { mut kernel, p, q } = fixture();
        let p_id = kernel.identity(p).unwrap();
        let q_id = kernel.identity(q).unwrap();
        assert!(kernel.remove_theorem(p_id));
        assert!(!kernel.remove_theorem(p_id));
        assert!(kernel.theorem(q_id).is_ok());
        assert!(matches!(
            kernel.theorem(p_id),
            Err(KernelError::MissingTheorem { .. })
        ));
        assert_eq!(kernel.identity(q.negated()).unwrap(), p_id);
        assert!(kernel.theorem(q_id).is_ok());
    }

    #[test]
    fn deletion_with_an_absent_handle_is_false_and_reuse_is_lifo() {
        let Fixture { mut kernel, p, q } = fixture();
        let first = kernel.identity(p).unwrap();
        let second = kernel.identity(q).unwrap();
        let absent = ThmId::new(second.get() + 1).unwrap();
        assert!(!kernel.remove_theorem(absent));
        assert!(kernel.theorem(first).is_ok());
        assert!(kernel.theorem(second).is_ok());

        assert!(kernel.remove_theorem(first));
        assert!(kernel.remove_theorem(second));
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
        let falsehood = positive(kernel.bool(bool_ty, false).unwrap());
        let truth = positive(kernel.bool(bool_ty, true).unwrap());

        for signed_false in [falsehood, truth.negated()] {
            let identity = kernel.identity(signed_false).unwrap();
            let expanded = kernel
                .expand_conclusion(identity, signed_false, None)
                .unwrap();
            assert!(
                kernel
                    .theorem(expanded)
                    .unwrap()
                    .conclusions()
                    .cubes()
                    .is_empty()
            );
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
        kernel.weaken(assumed_p, &[], &[q]).unwrap();
        kernel.weaken(assumed_not_p, &[], &[q]).unwrap();
        let (left, right) = (assumed_p, assumed_not_p);
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_eq!(unit_conclusions(kernel.theorem(resolved).unwrap()), [q]);

        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        let contradiction = kernel.resolve(assumed_p, assumed_not_p, p).unwrap();
        kernel.weaken(contradiction, &[q], &[]).unwrap();
        kernel.not_right(contradiction, q).unwrap();
        assert_eq!(
            unit_conclusions(kernel.theorem(contradiction).unwrap()),
            [q.negated()]
        );
    }

    #[test]
    fn opcode_tree_expansion_refutes_p_and_not_p() {
        let Fixture { mut kernel, p, .. } = fixture();
        let not_p_ref = kernel.op1(Op1::Not, reference(p)).unwrap();
        let not_p = positive(not_p_ref);
        let formula_ref = kernel.op2(Op2::And, reference(p), not_p_ref).unwrap();
        let formula = positive(formula_ref);
        let root = kernel.identity(formula).unwrap();
        let p_clause = kernel
            .expand_conclusion(root, formula, Some(false))
            .unwrap();
        let not_clause = kernel.expand_conclusion(root, formula, Some(true)).unwrap();
        let neg_p_clause = kernel.expand_conclusion(not_clause, not_p, None).unwrap();
        let refutation = kernel.resolve(p_clause, neg_p_clause, p).unwrap();
        let sequent = kernel.theorem(refutation).unwrap();
        assert_eq!(unit_premises(sequent), [formula]);
        assert!(sequent.conclusions().cubes().is_empty());
    }

    #[test]
    fn recursive_flattening_handles_or_not_imp_and_false() {
        let Fixture { mut kernel, p, q } = fixture();
        let not_p = kernel.op1(Op1::Not, reference(p)).unwrap();
        let implication = kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap();
        let nested = kernel.op2(Op2::Or, not_p, implication).unwrap();
        let nested = positive(nested);
        let theorem = kernel.identity(nested).unwrap();
        let flattened = kernel.flatten_conclusion(theorem, nested).unwrap();
        assert_eq!(
            unit_conclusions(kernel.theorem(flattened).unwrap()),
            [q, p.negated()]
        );

        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let falsehood = positive(falsehood);
        let false_theorem = kernel.identity(falsehood).unwrap();
        let eliminated = kernel
            .expand_conclusion(false_theorem, falsehood, None)
            .unwrap();
        assert!(
            kernel
                .theorem(eliminated)
                .unwrap()
                .conclusions()
                .cubes()
                .is_empty()
        );
    }

    #[test]
    fn recursive_tree_folding_round_trips_both_sides() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let conjunction_id = kernel.identity(conjunction).unwrap();
        let flat_left = kernel.flatten_premise(conjunction_id, conjunction).unwrap();
        let folded_left = kernel.fold_premise(flat_left, conjunction).unwrap();
        assert_eq!(
            kernel.theorem(folded_left).unwrap(),
            kernel.theorem(conjunction_id).unwrap()
        );

        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
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
    fn recursive_tree_folding_treats_repeated_leaves_idempotently() {
        let Fixture { mut kernel, p, .. } = fixture();
        let repeated_and = positive(kernel.op2(Op2::And, reference(p), reference(p)).unwrap());
        let nested_and = positive(
            kernel
                .op2(Op2::And, reference(repeated_and), reference(p))
                .unwrap(),
        );
        let and_identity = kernel.identity(nested_and).unwrap();
        let flat_left = kernel.flatten_premise(and_identity, nested_and).unwrap();
        assert_eq!(unit_premises(kernel.theorem(flat_left).unwrap()), [p]);
        let folded_left = kernel.fold_premise(flat_left, nested_and).unwrap();
        assert_eq!(
            kernel.theorem(folded_left).unwrap(),
            kernel.theorem(and_identity).unwrap()
        );

        let repeated_or = positive(kernel.op2(Op2::Or, reference(p), reference(p)).unwrap());
        let nested_or = positive(
            kernel
                .op2(Op2::Or, reference(repeated_or), reference(p))
                .unwrap(),
        );
        let or_identity = kernel.identity(nested_or).unwrap();
        let flat_right = kernel.flatten_conclusion(or_identity, nested_or).unwrap();
        assert_eq!(unit_conclusions(kernel.theorem(flat_right).unwrap()), [p]);
        let folded_right = kernel.fold_conclusion(flat_right, nested_or).unwrap();
        assert_eq!(
            kernel.theorem(folded_right).unwrap(),
            kernel.theorem(or_identity).unwrap()
        );
    }

    #[test]
    fn primitive_resolution_is_valid_for_every_boolean_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed_p = kernel.identity(p).unwrap();
        let assumed_not_p = kernel.identity(p.negated()).unwrap();
        kernel.weaken(assumed_p, &[q], &[q]).unwrap();
        kernel.weaken(assumed_not_p, &[q], &[q.negated()]).unwrap();
        let (left, right) = (assumed_p, assumed_not_p);
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
        kernel.weaken(assumed, &[q], &[q.negated()]).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
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
        let bool_ty = kernel.classifier(reference(p)).unwrap();
        let falsehood = positive(kernel.bool(bool_ty, false).unwrap());
        let truth = positive(kernel.bool(bool_ty, true).unwrap());
        let false_left = kernel.false_left(falsehood).unwrap();
        let true_right = kernel.true_right(truth).unwrap();
        assert_valid(&kernel, false_left, &[p, q]);
        assert_valid(&kernel, true_right, &[p, q]);
    }

    #[test]
    fn not_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        kernel.not_left(assumed, p).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
    }

    #[test]
    fn not_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let assumed = kernel.identity(p).unwrap();
        kernel.not_right(assumed, p).unwrap();
        assert_valid(&kernel, assumed, &[p, q]);
    }

    #[test]
    fn and_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(p).unwrap();
        kernel.weaken(assumed, &[q], &[]).unwrap();
        let theorem = kernel.and_left(assumed, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn and_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.and_right(left, right, conjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.or_left(left, right, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn or_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(p).unwrap();
        kernel.weaken(assumed, &[], &[q]).unwrap();
        let theorem = kernel.or_right(assumed, disjunction).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_left_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication = positive(kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap());
        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(q).unwrap();
        let theorem = kernel.imp_left(left, right, implication).unwrap();
        assert_valid(&kernel, theorem, &[p, q]);
    }

    #[test]
    fn imp_right_is_valid_for_every_valuation() {
        let Fixture { mut kernel, p, q } = fixture();
        let implication = positive(kernel.op2(Op2::Imp, reference(p), reference(q)).unwrap());
        let assumed = kernel.identity(q).unwrap();
        kernel.weaken(assumed, &[p], &[]).unwrap();
        let theorem = kernel.imp_right(assumed, implication).unwrap();
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
    fn only_explicit_in_place_rules_mutate_their_evidence_transactionally() {
        let Fixture { mut kernel, p, q } = fixture();
        let unary = kernel.identity(p).unwrap();
        let preserved = kernel.copy_theorem(unary).unwrap();
        kernel.weaken(unary, &[q], &[]).unwrap();
        let mut expected = [p, q];
        expected.sort_unstable();
        assert_eq!(unit_premises(kernel.theorem(unary).unwrap()), expected);
        assert_eq!(unit_premises(kernel.theorem(preserved).unwrap()), [p]);
        let before = kernel.theorem(unary).unwrap().clone();
        let missing = PropId::from_raw(-999_999).unwrap();
        assert!(kernel.weaken(unary, &[missing], &[]).is_err());
        assert_eq!(kernel.theorem(unary).unwrap(), &before);
        assert!(kernel.and_left(unary, q).is_err());
        assert_eq!(kernel.theorem(unary).unwrap(), &before);

        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p.negated()).unwrap();
        let resolved = kernel.resolve(left, right, p).unwrap();
        assert_ne!(resolved, left);
        assert_ne!(resolved, right);
        assert_eq!(
            unit_premises(kernel.theorem(resolved).unwrap()),
            [p, p.negated()]
        );
        assert!(
            kernel
                .theorem(resolved)
                .unwrap()
                .conclusions()
                .cubes()
                .is_empty()
        );
        assert_eq!(unit_conclusions(kernel.theorem(left).unwrap()), [p]);
        assert_eq!(
            unit_conclusions(kernel.theorem(right).unwrap()),
            [p.negated()]
        );
    }

    #[test]
    fn every_in_place_rule_preserves_the_exact_theorem_on_rejection() {
        let Fixture { mut kernel, p, q } = fixture();
        let theorem = kernel.identity(p).unwrap();
        let original = kernel.theorem(theorem).unwrap().clone();
        let missing = PropId::from_raw(-999_999).unwrap();

        assert!(kernel.weaken(theorem, &[missing], &[]).is_err());
        assert_eq!(kernel.theorem(theorem).unwrap(), &original);

        assert!(kernel.not_left(theorem, q).is_err());
        assert_eq!(kernel.theorem(theorem).unwrap(), &original);

        assert!(kernel.not_right(theorem, q).is_err());
        assert_eq!(kernel.theorem(theorem).unwrap(), &original);
    }

    #[test]
    fn copy_delete_and_free_reuse_follow_ephemeral_slot_semantics() {
        let Fixture { mut kernel, p, q } = fixture();
        let source = kernel.identity(p).unwrap();
        let reusable = kernel.identity(q).unwrap();
        assert!(kernel.remove_theorem(reusable));
        let target = kernel.copy_theorem(source).unwrap();
        assert_eq!(target, reusable);
        assert_eq!(
            kernel.theorem(target).unwrap(),
            kernel.theorem(source).unwrap()
        );
        assert!(kernel.remove_theorem(target));
        assert!(kernel.weaken(target, &[q], &[]).is_err());
        assert!(kernel.not_left(target, p).is_err());
        assert!(kernel.not_right(target, p).is_err());
        assert!(kernel.copy_theorem(target).is_err());
        assert_eq!(kernel.identity(q.negated()).unwrap(), target);
    }

    #[test]
    fn repeated_operands_support_idempotent_connective_rules() {
        let Fixture { mut kernel, p, q } = fixture();
        let conjunction = positive(kernel.op2(Op2::And, reference(p), reference(p)).unwrap());
        let disjunction = positive(kernel.op2(Op2::Or, reference(p), reference(p)).unwrap());
        let identity = kernel.identity(p).unwrap();
        let and_left = kernel.and_left(identity, conjunction).unwrap();
        let or_right = kernel.or_right(identity, disjunction).unwrap();
        assert_valid(&kernel, and_left, &[p, q]);
        assert_valid(&kernel, or_right, &[p, q]);
    }

    fn valid(sequent: &Thm, p: PropId, p_value: bool, q: PropId, q_value: bool) -> bool {
        let value = |proposition: PropId| {
            let atom = if reference(proposition) == reference(p) {
                p_value
            } else {
                assert_eq!(reference(proposition), reference(q));
                q_value
            };
            if proposition.is_positive() {
                atom
            } else {
                !atom
            }
        };
        !sequent
            .premises()
            .clauses()
            .iter()
            .all(|clause| clause.literals().iter().copied().any(&value))
            || sequent
                .conclusions()
                .cubes()
                .iter()
                .any(|cube| cube.literals().iter().copied().all(&value))
    }

    fn assert_valid(kernel: &Kernel, theorem: ThmId, atoms: &[PropId]) {
        for mask in 0..(1_usize << atoms.len()) {
            let values: BTreeMap<_, _> = atoms
                .iter()
                .enumerate()
                .map(|(index, atom)| (reference(*atom), mask & (1 << index) != 0))
                .collect();
            let sequent = kernel.theorem(theorem).unwrap();
            assert!(
                !sequent.premises().clauses().iter().all(|clause| clause
                    .literals()
                    .iter()
                    .copied()
                    .any(|p| evaluate(kernel, p, &values)))
                    || sequent.conclusions().cubes().iter().any(|cube| cube
                        .literals()
                        .iter()
                        .copied()
                        .all(|p| evaluate(kernel, p, &values))),
                "invalid sequent {sequent:?} under mask {mask}"
            );
        }
    }

    fn evaluate(kernel: &Kernel, proposition: PropId, atoms: &BTreeMap<Ref, bool>) -> bool {
        let reference = reference(proposition);
        let positive = if let Some(value) = kernel.arena().bool_value(reference) {
            value
        } else if let Some(op) = kernel.arena().op1(reference) {
            let child = kernel.arena().children(reference).unwrap().next().unwrap();
            match op {
                Op1::Not => !evaluate(kernel, positive(child), atoms),
            }
        } else if let Some(op) = kernel.arena().op2(reference) {
            let children: Vec<_> = kernel.arena().children(reference).unwrap().collect();
            let left = evaluate(kernel, positive(children[0]), atoms);
            let right = evaluate(kernel, positive(children[1]), atoms);
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
