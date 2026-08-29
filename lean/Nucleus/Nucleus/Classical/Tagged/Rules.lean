import Nucleus.Classical.Tagged.Abstract

/-!
# Sound rules for tagged classical sequents

The rules in this module are semantic: each preserves truth under every total
completion of an arbitrary partial assignment.  Taking that assignment to be
`Classical.bottom` yields the corresponding syllogism rule.
-/

namespace Nucleus.Classical.Tagged

universe u

variable {Atom : Type u}

namespace Sequent

/-- A pointwise sound transformation of sequents is sound at every partial
assignment. -/
theorem EntailsAt.map {known : Classical.PartialAssignment Atom}
    {source target : Sequent Atom}
    (step : ∀ assignment, source.Holds assignment → target.Holds assignment)
    (holds : source.EntailsAt known) : target.EntailsAt known := by
  intro assignment completes
  exact step assignment (holds assignment completes)

/-- Identity is valid under every partial assignment. -/
theorem entailsAt_identity (known : Classical.PartialAssignment Atom)
    (formula : Formula Atom) :
    EntailsAt known ⟨formula, formula⟩ := by
  intro _ _ premise
  exact premise

/-- Adding a conjunct to the premise preserves a sequent. -/
theorem Holds.lhsAndPush (assignment : Classical.Assignment Atom)
    (lhs : List (Formula Atom)) (rhs pushed : Formula Atom)
    (holds : Holds ⟨Formula.conjunction lhs, rhs⟩ assignment) :
    Holds ⟨Formula.conjunction (lhs ++ [pushed]), rhs⟩ assignment := by
  intro expanded
  apply holds
  rw [Formula.eval_conjunction] at expanded ⊢
  intro child member
  exact expanded child (List.mem_append.mpr (Or.inl member))

/-- Adding a disjunct to the conclusion preserves a sequent. -/
theorem Holds.rhsOrPush (assignment : Classical.Assignment Atom)
    (lhs pushed : Formula Atom) (rhs : List (Formula Atom))
    (holds : Holds ⟨lhs, Formula.disjunction rhs⟩ assignment) :
    Holds ⟨lhs, Formula.disjunction (rhs ++ [pushed])⟩ assignment := by
  intro premise
  obtain ⟨child, member, childTrue⟩ :=
    (Formula.eval_disjunction assignment rhs).mp (holds premise)
  apply (Formula.eval_disjunction assignment (rhs ++ [pushed])).mpr
  exact ⟨child, List.mem_append.mpr (Or.inl member), childTrue⟩

/-- Move a conjunct across a sequent by negating it.  This is the corrected
`CNF, p ⊢ DNF` to `CNF ⊢ DNF, ¬p` mutation. -/
theorem Holds.cross (assignment : Classical.Assignment Atom)
    (cnf dnf : List (Formula Atom)) (formula : Formula Atom)
    (holds : Holds
      ⟨Formula.conjunction (cnf ++ [formula]), Formula.disjunction dnf⟩
      assignment) :
    Holds
      ⟨Formula.conjunction cnf, Formula.disjunction (dnf ++ [formula.neg])⟩
      assignment := by
  intro cnfTrue
  by_cases formulaTrue : formula.Eval assignment
  · have sourcePremise :
        (Formula.conjunction (cnf ++ [formula])).Eval assignment := by
      apply (Formula.eval_conjunction assignment (cnf ++ [formula])).mpr
      intro child member
      rcases List.mem_append.mp member with member | member
      · exact (Formula.eval_conjunction assignment cnf).mp cnfTrue child member
      · have equals : child = formula := List.mem_singleton.mp member
        subst child
        exact formulaTrue
    obtain ⟨child, member, childTrue⟩ :=
      (Formula.eval_disjunction assignment dnf).mp (holds sourcePremise)
    apply (Formula.eval_disjunction assignment (dnf ++ [formula.neg])).mpr
    exact ⟨child, List.mem_append.mpr (Or.inl member), childTrue⟩
  · apply (Formula.eval_disjunction assignment (dnf ++ [formula.neg])).mpr
    refine ⟨formula.neg, List.mem_append.mpr (Or.inr (by simp)), ?_⟩
    exact (Formula.eval_neg formula assignment).mpr formulaTrue

/-- Move a final disjunct back across a sequent, again complementing it. -/
theorem Holds.crossLeft (assignment : Classical.Assignment Atom)
    (cnf dnf : List (Formula Atom)) (formula : Formula Atom)
    (holds : Holds
      ⟨Formula.conjunction cnf, Formula.disjunction (dnf ++ [formula])⟩
      assignment) :
    Holds
      ⟨Formula.conjunction (cnf ++ [formula.neg]), Formula.disjunction dnf⟩
      assignment := by
  intro expandedPremise
  have cnfTrue : (Formula.conjunction cnf).Eval assignment := by
    apply (Formula.eval_conjunction assignment cnf).mpr
    intro child member
    exact (Formula.eval_conjunction assignment (cnf ++ [formula.neg])).mp
      expandedPremise child (List.mem_append.mpr (Or.inl member))
  have negatedTrue : formula.neg.Eval assignment :=
    (Formula.eval_conjunction assignment (cnf ++ [formula.neg])).mp
      expandedPremise formula.neg (List.mem_append.mpr (Or.inr (by simp)))
  obtain ⟨child, member, childTrue⟩ :=
    (Formula.eval_disjunction assignment (dnf ++ [formula])).mp (holds cnfTrue)
  rcases List.mem_append.mp member with member | member
  · exact (Formula.eval_disjunction assignment dnf).mpr ⟨child, member, childTrue⟩
  · have equal : child = formula := List.mem_singleton.mp member
    subst child
    exact False.elim ((Formula.eval_neg formula assignment).mp negatedTrue childTrue)

/-- Permuting conjuncts in a premise preserves a sequent. -/
theorem Holds.lhsAndPermute (assignment : Classical.Assignment Atom)
    {before after : List (Formula Atom)} {rhs : Formula Atom}
    (permutation : before.Perm after)
    (holds : Holds ⟨Formula.conjunction before, rhs⟩ assignment) :
    Holds ⟨Formula.conjunction after, rhs⟩ assignment := by
  intro afterTrue
  apply holds
  apply (Formula.eval_conjunction assignment before).mpr
  intro child member
  exact (Formula.eval_conjunction assignment after).mp afterTrue child
    (permutation.mem_iff.mp member)

/-- Permuting disjuncts in a conclusion preserves a sequent. -/
theorem Holds.rhsOrPermute (assignment : Classical.Assignment Atom)
    {lhs : Formula Atom} {before after : List (Formula Atom)}
    (permutation : before.Perm after)
    (holds : Holds ⟨lhs, Formula.disjunction before⟩ assignment) :
    Holds ⟨lhs, Formula.disjunction after⟩ assignment := by
  intro premise
  obtain ⟨child, member, childTrue⟩ :=
    (Formula.eval_disjunction assignment before).mp (holds premise)
  apply (Formula.eval_disjunction assignment after).mpr
  exact ⟨child, permutation.mem_iff.mp member, childTrue⟩

/-- Removing duplicate conjuncts from a premise preserves a sequent. -/
theorem Holds.lhsAndDedupe [DecidableEq (Formula Atom)]
    (assignment : Classical.Assignment Atom) (lhs : List (Formula Atom))
    (rhs : Formula Atom)
    (holds : Holds ⟨Formula.conjunction lhs, rhs⟩ assignment) :
    Holds ⟨Formula.conjunction lhs.dedup, rhs⟩ assignment := by
  intro dedupedTrue
  apply holds
  apply (Formula.eval_conjunction assignment lhs).mpr
  intro child member
  apply (Formula.eval_conjunction assignment lhs.dedup).mp dedupedTrue
  simpa using member

/-- Removing duplicate disjuncts from a conclusion preserves a sequent. -/
theorem Holds.rhsOrDedupe [DecidableEq (Formula Atom)]
    (assignment : Classical.Assignment Atom) (lhs : Formula Atom)
    (rhs : List (Formula Atom))
    (holds : Holds ⟨lhs, Formula.disjunction rhs⟩ assignment) :
    Holds ⟨lhs, Formula.disjunction rhs.dedup⟩ assignment := by
  intro premise
  obtain ⟨child, member, childTrue⟩ :=
    (Formula.eval_disjunction assignment rhs).mp (holds premise)
  apply (Formula.eval_disjunction assignment rhs.dedup).mpr
  exact ⟨child, by simpa using member, childTrue⟩

/-- Partial-assignment form of left conjunction push. -/
theorem EntailsAt.lhsAndPush (known : Classical.PartialAssignment Atom)
    (lhs : List (Formula Atom)) (rhs pushed : Formula Atom)
    (holds : EntailsAt known ⟨Formula.conjunction lhs, rhs⟩) :
    EntailsAt known ⟨Formula.conjunction (lhs ++ [pushed]), rhs⟩ :=
  holds.map fun assignment ↦ Holds.lhsAndPush assignment lhs rhs pushed

/-- Partial-assignment form of right disjunction push. -/
theorem EntailsAt.rhsOrPush (known : Classical.PartialAssignment Atom)
    (lhs pushed : Formula Atom) (rhs : List (Formula Atom))
    (holds : EntailsAt known ⟨lhs, Formula.disjunction rhs⟩) :
    EntailsAt known ⟨lhs, Formula.disjunction (rhs ++ [pushed])⟩ :=
  holds.map fun assignment ↦ Holds.rhsOrPush assignment lhs pushed rhs

/-- Partial-assignment form of the corrected crossing rule. -/
theorem EntailsAt.cross (known : Classical.PartialAssignment Atom)
    (cnf dnf : List (Formula Atom)) (formula : Formula Atom)
    (holds : EntailsAt known
      ⟨Formula.conjunction (cnf ++ [formula]), Formula.disjunction dnf⟩) :
    EntailsAt known
      ⟨Formula.conjunction cnf, Formula.disjunction (dnf ++ [formula.neg])⟩ :=
  holds.map fun assignment ↦ Holds.cross assignment cnf dnf formula

/-- Partial-assignment form of inverse crossing. -/
theorem EntailsAt.crossLeft (known : Classical.PartialAssignment Atom)
    (cnf dnf : List (Formula Atom)) (formula : Formula Atom)
    (holds : EntailsAt known
      ⟨Formula.conjunction cnf, Formula.disjunction (dnf ++ [formula])⟩) :
    EntailsAt known
      ⟨Formula.conjunction (cnf ++ [formula.neg]), Formula.disjunction dnf⟩ :=
  holds.map fun assignment ↦ Holds.crossLeft assignment cnf dnf formula

/-- Partial-assignment form of left conjunction permutation. -/
theorem EntailsAt.lhsAndPermute (known : Classical.PartialAssignment Atom)
    {before after : List (Formula Atom)} {rhs : Formula Atom}
    (permutation : before.Perm after)
    (holds : EntailsAt known ⟨Formula.conjunction before, rhs⟩) :
    EntailsAt known ⟨Formula.conjunction after, rhs⟩ :=
  holds.map fun assignment ↦ Holds.lhsAndPermute assignment permutation

/-- Partial-assignment form of right disjunction permutation. -/
theorem EntailsAt.rhsOrPermute (known : Classical.PartialAssignment Atom)
    {lhs : Formula Atom} {before after : List (Formula Atom)}
    (permutation : before.Perm after)
    (holds : EntailsAt known ⟨lhs, Formula.disjunction before⟩) :
    EntailsAt known ⟨lhs, Formula.disjunction after⟩ :=
  holds.map fun assignment ↦ Holds.rhsOrPermute assignment permutation

/-- Partial-assignment form of left conjunction deduplication. -/
theorem EntailsAt.lhsAndDedupe [DecidableEq (Formula Atom)]
    (known : Classical.PartialAssignment Atom) (lhs : List (Formula Atom))
    (rhs : Formula Atom)
    (holds : EntailsAt known ⟨Formula.conjunction lhs, rhs⟩) :
    EntailsAt known ⟨Formula.conjunction lhs.dedup, rhs⟩ :=
  holds.map fun assignment ↦ Holds.lhsAndDedupe assignment lhs rhs

/-- Partial-assignment form of right disjunction deduplication. -/
theorem EntailsAt.rhsOrDedupe [DecidableEq (Formula Atom)]
    (known : Classical.PartialAssignment Atom) (lhs : Formula Atom)
    (rhs : List (Formula Atom))
    (holds : EntailsAt known ⟨lhs, Formula.disjunction rhs⟩) :
    EntailsAt known ⟨lhs, Formula.disjunction rhs.dedup⟩ :=
  holds.map fun assignment ↦ Holds.rhsOrDedupe assignment lhs rhs

end Sequent

namespace EntailsAt

/-- Reordering a list of sequents preserves its semantics. -/
theorem permute {known : Classical.PartialAssignment Atom}
    {before after : List (Sequent Atom)} (permutation : before.Perm after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  intro assignment completes sequent member
  exact holds assignment completes sequent (permutation.mem_iff.mpr member)

/-- Removing duplicate sequents preserves its semantics. -/
theorem dedupe [DecidableEq (Sequent Atom)]
    {known : Classical.PartialAssignment Atom}
    (sequents : List (Sequent Atom)) (holds : EntailsAt known sequents) :
    EntailsAt known sequents.dedup := by
  intro assignment completes sequent member
  exact holds assignment completes sequent (by simpa using member)

end EntailsAt

end Nucleus.Classical.Tagged
