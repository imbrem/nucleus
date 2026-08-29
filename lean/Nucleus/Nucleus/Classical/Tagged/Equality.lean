import Nucleus.Classical.Tagged.Abstract

/-!
# Executable equality for nested tagged syntax

Lean cannot derive equality automatically for the nested `Formula`/`List`
recursion.  These mutually recursive Boolean comparators provide an executable
conditional `DecidableEq` whenever atom equality is decidable.
-/

namespace Nucleus.Classical.Tagged

universe u

variable {Atom : Type u}

mutual
  /-- Structural equality for tagged formulas. -/
  def Formula.equal [DecidableEq Atom] : Formula Atom → Formula Atom → Bool
    | .literal left, .literal right =>
        decide (left.atom = right.atom) && decide (left.negative = right.negative)
    | .and leftSign left, .and rightSign right =>
        decide (leftSign = rightSign) && FormulaList.equal left right
    | .or leftSign left, .or rightSign right =>
        decide (leftSign = rightSign) && FormulaList.equal left right
    | .sat leftSign left, .sat rightSign right =>
        decide (leftSign = rightSign) && FormulaList.equal left right
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right

  /-- Structural equality for a nested formula list. -/
  def FormulaList.equal [DecidableEq Atom] :
      List (Formula Atom) → List (Formula Atom) → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        Formula.equal left right && FormulaList.equal lefts rights
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right
end

mutual
  theorem Formula.equal_eq_true [DecidableEq Atom] :
      ∀ left right : Formula Atom, left.equal right = true ↔ left = right
    | .literal left, .literal right => by
        cases left
        cases right
        simp [Formula.equal]
    | .and leftSign left, .and rightSign right => by
        rw [Formula.equal, Bool.and_eq_true, FormulaList.equal_eq_true left right]
        simp
    | .or leftSign left, .or rightSign right => by
        rw [Formula.equal, Bool.and_eq_true, FormulaList.equal_eq_true left right]
        simp
    | .sat leftSign left, .sat rightSign right => by
        rw [Formula.equal, Bool.and_eq_true, FormulaList.equal_eq_true left right]
        simp
    | .literal _, .and _ _ | .literal _, .or _ _ | .literal _, .sat _ _ |
      .and _ _, .literal _ | .and _ _, .or _ _ | .and _ _, .sat _ _ |
      .or _ _, .literal _ | .or _ _, .and _ _ | .or _ _, .sat _ _ |
      .sat _ _, .literal _ | .sat _ _, .and _ _ | .sat _ _, .or _ _ => by
        simp [Formula.equal]
    termination_by left right => sizeOf left + sizeOf right

  theorem FormulaList.equal_eq_true [DecidableEq Atom] :
      ∀ left right : List (Formula Atom),
        FormulaList.equal left right = true ↔ left = right
    | [], [] => by simp [FormulaList.equal]
    | left :: lefts, right :: rights => by
        rw [FormulaList.equal, Bool.and_eq_true,
          Formula.equal_eq_true left right,
          FormulaList.equal_eq_true lefts rights]
        simp
    | [], _ :: _ | _ :: _, [] => by simp [FormulaList.equal]
    termination_by left right => sizeOf left + sizeOf right
end

instance [DecidableEq Atom] : DecidableEq (Formula Atom) := fun left right =>
  if equal : left.equal right = true then
    isTrue ((Formula.equal_eq_true left right).mp equal)
  else
    isFalse fun same => equal ((Formula.equal_eq_true left right).mpr same)

/-- Executable equality for sequents follows from executable formula equality. -/
instance [DecidableEq Atom] : DecidableEq (Sequent Atom) := fun left right =>
  if premise : left.premise = right.premise then
    if conclusion : left.conclusion = right.conclusion then
      isTrue (by cases left; cases right; simp_all)
    else
      isFalse fun same => conclusion (congrArg Sequent.conclusion same)
  else
    isFalse fun same => premise (congrArg Sequent.premise same)

end Nucleus.Classical.Tagged
