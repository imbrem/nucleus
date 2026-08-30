import Nucleus.Classical.Alternating.Abstract

/-!
# Executable equality for alternating syntax

The indexed expression/child-list grammar has mutually recursive executable
equality.  This supplies conditional `DecidableEq` instances without using
classical choice.
-/

namespace Nucleus.Classical.Alternating

universe u

variable {Atom : Type u}

mutual
  def Expr.equal [DecidableEq Atom] : Expr Atom → Expr Atom → Bool
    | .literal left, .literal right =>
        decide (left.atom = right.atom) && decide (left.negative = right.negative)
    | .node leftSign left, .node rightSign right =>
        decide (leftSign = rightSign) && Children.equal left right
    | _, _ => false

  def Children.equal [DecidableEq Atom] : Children Atom → Children Atom → Bool
    | .nil, .nil => true
    | .cons left lefts, .cons right rights =>
        Expr.equal left right && Children.equal lefts rights
    | _, _ => false
end

mutual
  theorem Expr.equal_eq_true [DecidableEq Atom] :
      ∀ left right : Expr Atom, left.equal right = true ↔ left = right
    | .literal left, .literal right => by
        cases left
        cases right
        simp [Expr.equal]
    | .node leftSign left, .node rightSign right => by
        rw [Expr.equal, Bool.and_eq_true, Children.equal_eq_true left right]
        simp
    | .literal _, .node _ _ | .node _ _, .literal _ => by
        simp [Expr.equal]

  theorem Children.equal_eq_true [DecidableEq Atom] :
      ∀ left right : Children Atom, left.equal right = true ↔ left = right
    | .nil, .nil => by simp [Children.equal]
    | .cons left lefts, .cons right rights => by
        rw [Children.equal, Bool.and_eq_true, Expr.equal_eq_true left right,
          Children.equal_eq_true lefts rights]
        simp
    | .nil, .cons _ _ | .cons _ _, .nil => by simp [Children.equal]
end

instance [DecidableEq Atom] : DecidableEq (Expr Atom) := fun left right =>
  if equal : left.equal right = true then
    isTrue ((Expr.equal_eq_true left right).mp equal)
  else
    isFalse fun same => equal ((Expr.equal_eq_true left right).mpr same)

instance [DecidableEq Atom] : DecidableEq (Children Atom) := fun left right =>
  if equal : left.equal right = true then
    isTrue ((Children.equal_eq_true left right).mp equal)
  else
    isFalse fun same => equal ((Children.equal_eq_true left right).mpr same)

instance [DecidableEq Atom] : DecidableEq (Sequent Atom) := fun left right =>
  if leftEqual : left.left = right.left then
    if rightEqual : left.right = right.right then
      isTrue (by cases left; cases right; simp_all)
    else
      isFalse fun same => rightEqual (congrArg Sequent.right same)
  else
    isFalse fun same => leftEqual (congrArg Sequent.left same)

end Nucleus.Classical.Alternating
