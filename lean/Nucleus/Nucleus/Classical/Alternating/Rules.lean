import Nucleus.Classical.Alternating.Abstract

/-!
# Sound rules for untagged alternating sequents

Every preservation theorem is stated at an arbitrary partial assignment.
Taking that assignment to be `bottom` yields the corresponding syllogism
rule.  Crossing and cut use literals: unlike arrays, a literal's meaning does
not depend on which alternating mode its occurrence inherits.
-/

namespace Nucleus.Classical.Alternating

universe u v

variable {Atom : Type u} {Key : Type v}

namespace Expr

theorem eval_array_perm (assignment : Assignment Atom) (mode : Mode)
    (negative : Bool) {before after : List (Expr Atom)}
    (permutation : before.Perm after) :
    eval assignment mode (.array negative before) =
      eval assignment mode (.array negative after) := by
  cases negative with
  | false =>
      simp only [eval_array_positive]
      exact Mode.aggregate_eq_of_perm (permutation.map _)
  | true =>
      simp only [eval_array_negative]
      rw [Mode.aggregate_eq_of_perm (permutation.map _)]

@[simp] theorem eval_array_append_all (assignment : Assignment Atom)
    (left right : List (Expr Atom)) :
    eval assignment .all (.array false (left ++ right)) =
      (eval assignment .all (.array false left) &&
        eval assignment .all (.array false right)) := by
  simp [eval_array_positive, Mode.aggregate_append]

@[simp] theorem eval_array_append_any (assignment : Assignment Atom)
    (left right : List (Expr Atom)) :
    eval assignment .any (.array false (left ++ right)) =
      (eval assignment .any (.array false left) ||
        eval assignment .any (.array false right)) := by
  simp [eval_array_positive, Mode.aggregate_append]

@[simp] theorem eval_array_singleton_literal (assignment : Assignment Atom)
    (mode : Mode) (literal : Literal Atom) :
    eval assignment mode (.array false [.literal literal]) =
      literal.eval assignment := by
  cases mode <;> simp [eval_array_positive, Mode.aggregate]

@[simp] theorem eval_array_singleton (assignment : Assignment Atom)
    (mode : Mode) (child : Expr Atom) :
    eval assignment mode (.array false [child]) =
      eval assignment mode.flip child := by
  cases mode <;> simp [eval_array_positive, Mode.aggregate]

@[simp] theorem eval_negative_empty_all (assignment : Assignment Atom) :
    eval assignment .all (.array true ([] : List (Expr Atom))) = false := by
  simp [eval_array_negative, Mode.aggregate]

@[simp] theorem eval_negative_empty_any (assignment : Assignment Atom) :
    eval assignment .any (.array true ([] : List (Expr Atom))) = true := by
  simp [eval_array_negative, Mode.aggregate]

@[simp] theorem eval_array_dedup [DecidableEq (Expr Atom)]
    (assignment : Assignment Atom) (mode : Mode) (children : List (Expr Atom)) :
    eval assignment mode (.array false children.dedup) =
      eval assignment mode (.array false children) := by
  simp only [eval_array_positive]
  apply Mode.aggregate_eq_of_mem_iff
  intro value
  simp

/-- A sort-by-key result is accepted only with evidence that it permutes the
original children.  The key itself carries no logical authority. -/
theorem eval_array_sortByKey (assignment : Assignment Atom) (mode : Mode)
    (negative : Bool) {before after : List (Expr Atom)}
    (_key : Expr Atom → Key) (checked : before.Perm after) :
    eval assignment mode (.array negative before) =
      eval assignment mode (.array negative after) :=
  eval_array_perm assignment mode negative checked

end Expr

namespace Sequent

private theorem entails_of_holds
    {known : PartialAssignment Atom} {source target : Sequent Atom}
    (sourceEntails : source.EntailsAt known)
    (preserves : ∀ assignment, source.Holds assignment → target.Holds assignment) :
    target.EntailsAt known := by
  intro assignment completes
  exact preserves assignment (sourceEntails assignment completes)

/-- Identity for one literal.  Modes are irrelevant at literal leaves. -/
theorem identity (known : PartialAssignment Atom) (literal : Literal Atom) :
    (Sequent.mk (.array false [.literal literal])
      (.array false [.literal literal])).EntailsAt known := by
  intro assignment _ leftTruth
  simpa [Sequent.Holds] using leftTruth

/-- Appending conjunctive premises strengthens the antecedent. -/
theorem pushLeft {known : PartialAssignment Atom}
    {left extra right : List (Expr Atom)}
    (source : (Sequent.mk (.array false left) (.array false right)).EntailsAt known) :
    (Sequent.mk (.array false (left ++ extra))
      (.array false right)).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds targetLeft
  apply sourceHolds
  have parts :
      (Expr.array false left).eval assignment .all = true ∧
        (Expr.array false extra).eval assignment .all = true := by
    simpa only [Expr.eval_array_append_all, Bool.and_eq_true] using targetLeft
  exact parts.1

/-- Appending disjunctive conclusions weakens the consequent. -/
theorem pushRight {known : PartialAssignment Atom}
    {left right extra : List (Expr Atom)}
    (source : (Sequent.mk (.array false left) (.array false right)).EntailsAt known) :
    (Sequent.mk (.array false left)
      (.array false (right ++ extra))).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  have rightTruth := sourceHolds leftTruth
  simp only [Expr.eval_array_append_any, Bool.or_eq_true]
  exact Or.inl rightTruth

/-- Corrected crossing rule: `Γ, p ⊢ Δ` gives `Γ ⊢ Δ, ¬p`. -/
theorem crossRight {known : PartialAssignment Atom}
    {left right : List (Expr Atom)} (literal : Literal Atom)
    (source : (Sequent.mk
      (.array false (left ++ [.literal literal]))
      (.array false right)).EntailsAt known) :
    (Sequent.mk (.array false left)
      (.array false (right ++ [.literal literal.neg]))).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  by_cases literalTruth : literal.eval assignment = true
  · have sourceLeft :
        (Expr.array false (left ++ [Syn.literal literal])).eval assignment .all = true := by
      simp only [Expr.eval_array_append_all, Expr.eval_array_singleton_literal,
        Bool.and_eq_true]
      exact ⟨leftTruth, literalTruth⟩
    have rightTruth := sourceHolds sourceLeft
    simp only [Expr.eval_array_append_any, Expr.eval_array_singleton_literal,
      Bool.or_eq_true]
    exact Or.inl rightTruth
  · have complementTruth : literal.neg.eval assignment = true := by
      cases truth : literal.eval assignment <;> simp_all
    simp only [Expr.eval_array_append_any, Expr.eval_array_singleton_literal,
      Bool.or_eq_true]
    exact Or.inr complementTruth

/-- Inverse crossing: `Γ ⊢ Δ, ¬p` gives `Γ, p ⊢ Δ`. -/
theorem crossLeft {known : PartialAssignment Atom}
    {left right : List (Expr Atom)} (literal : Literal Atom)
    (source : (Sequent.mk (.array false left)
      (.array false (right ++ [.literal literal.neg]))).EntailsAt known) :
    (Sequent.mk (.array false (left ++ [.literal literal]))
      (.array false right)).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds targetLeft
  have parts :
      (Expr.array false left).eval assignment .all = true ∧
        literal.eval assignment = true := by
    simpa only [Expr.eval_array_append_all, Expr.eval_array_singleton_literal,
      Bool.and_eq_true] using targetLeft
  have leftTruth := parts.1
  have literalTruth := parts.2
  have sourceRight := sourceHolds leftTruth
  simp only [Expr.eval_array_append_any, Expr.eval_array_singleton_literal,
    Bool.or_eq_true] at sourceRight
  rcases sourceRight with rightTruth | complementTruth
  · exact rightTruth
  · simp [Literal.eval_neg, literalTruth] at complementTruth

/-- Cut on a literal shared by a conclusion and a premise. -/
theorem cut {known : PartialAssignment Atom}
    {leftPrem rightPrem leftConc rightConc : List (Expr Atom)}
    (literal : Literal Atom)
    (leftSource : (Sequent.mk (.array false leftPrem)
      (.array false (leftConc ++ [.literal literal]))).EntailsAt known)
    (rightSource : (Sequent.mk
      (.array false (.literal literal :: rightPrem))
      (.array false rightConc)).EntailsAt known) :
    (Sequent.mk (.array false (leftPrem ++ rightPrem))
      (.array false (leftConc ++ rightConc))).EntailsAt known := by
  intro assignment completes premises
  have parts :
      (Expr.array false leftPrem).eval assignment .all = true ∧
        (Expr.array false rightPrem).eval assignment .all = true := by
    simpa only [Expr.eval_array_append_all, Bool.and_eq_true] using premises
  have leftPremises := parts.1
  have rightPremises := parts.2
  have leftResult := leftSource assignment completes leftPremises
  simp only [Expr.eval_array_append_any, Expr.eval_array_singleton_literal,
    Bool.or_eq_true] at leftResult
  rcases leftResult with leftConclusion | literalTruth
  · simp only [Expr.eval_array_append_any, Bool.or_eq_true]
    exact Or.inl leftConclusion
  · have rightInput :
        (Expr.array false (Syn.literal literal :: rightPrem)).eval assignment .all = true := by
      change (Expr.array false ([Syn.literal literal] ++ rightPrem)).eval
        assignment .all = true
      simp only [Expr.eval_array_append_all, Expr.eval_array_singleton_literal,
        Bool.and_eq_true]
      exact ⟨literalTruth, rightPremises⟩
    have rightConclusion := rightSource assignment completes rightInput
    simp only [Expr.eval_array_append_any, Bool.or_eq_true]
    exact Or.inr rightConclusion

/-- Reordering either root is sound only after checking an actual permutation. -/
theorem permute {known : PartialAssignment Atom}
    {leftBefore leftAfter rightBefore rightAfter : List (Expr Atom)}
    (leftPerm : leftBefore.Perm leftAfter)
    (rightPerm : rightBefore.Perm rightAfter)
    (source : (Sequent.mk (.array false leftBefore)
      (.array false rightBefore)).EntailsAt known) :
    (Sequent.mk (.array false leftAfter)
      (.array false rightAfter)).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  have leftBeforeTruth :
      (Expr.array false leftBefore).eval assignment .all = true := by
    rw [Expr.eval_array_perm assignment .all false leftPerm]
    exact leftTruth
  have rightBeforeTruth := sourceHolds leftBeforeTruth
  rw [← Expr.eval_array_perm assignment .any false rightPerm]
  exact rightBeforeTruth

/-- A named sort-by-key boundary: callers may choose any key, but must return
permutation evidence for both sorted roots. -/
theorem sortByKey {known : PartialAssignment Atom}
    {leftBefore leftAfter rightBefore rightAfter : List (Expr Atom)}
    (key : Expr Atom → Key)
    (leftChecked : leftBefore.Perm leftAfter)
    (rightChecked : rightBefore.Perm rightAfter)
    (source : (Sequent.mk (.array false leftBefore)
      (.array false rightBefore)).EntailsAt known) :
    (Sequent.mk (.array false leftAfter)
      (.array false rightAfter)).EntailsAt known := by
  let _ := key
  exact permute leftChecked rightChecked source

/-- Duplicate removal preserves both roots. -/
theorem dedupe [DecidableEq (Expr Atom)] {known : PartialAssignment Atom}
    {left right : List (Expr Atom)}
    (source : (Sequent.mk (.array false left)
      (.array false right)).EntailsAt known) :
    (Sequent.mk (.array false left.dedup)
      (.array false right.dedup)).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  have originalLeft : (Expr.array false left).eval assignment .all = true := by
    rw [← Expr.eval_array_dedup assignment .all left]
    exact leftTruth
  have originalRight := sourceHolds originalLeft
  rw [Expr.eval_array_dedup assignment .any right]
  exact originalRight

/-- The negative empty array is a neutral child: it is true in an `any`
child position and false in an `all` child position. -/
theorem appendUnit {known : PartialAssignment Atom}
    {left right : List (Expr Atom)}
    (source : (Sequent.mk (.array false left)
      (.array false right)).EntailsAt known) :
    (Sequent.mk (.array false (left ++ [.array true []]))
      (.array false (right ++ [.array true []]))).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  have originalLeft : (Expr.array false left).eval assignment .all = true := by
    have parts :
        (Expr.array false left).eval assignment .all = true ∧
          (Expr.array false [Expr.array true []]).eval assignment .all = true := by
      simpa only [Expr.eval_array_append_all, Bool.and_eq_true] using leftTruth
    exact parts.1
  have originalRight := sourceHolds originalLeft
  simp only [Expr.eval_array_append_any, Expr.eval_array_singleton,
    Mode.flip, Expr.eval_negative_empty_all, Bool.or_false]
  exact originalRight

/-- Two unary array layers cancel the two alternating mode flips. -/
theorem flattenDoubleUnary {known : PartialAssignment Atom}
    {left right : Expr Atom}
    (source : (Sequent.mk left.shift.shift right.shift.shift).EntailsAt known) :
    (Sequent.mk left right).EntailsAt known := by
  apply entails_of_holds source
  intro assignment sourceHolds leftTruth
  simpa using sourceHolds (by simpa using leftTruth)

end Sequent

end Nucleus.Classical.Alternating
