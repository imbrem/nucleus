import Nucleus.HolE.Named.Lower

/-!
# Alpha conversion for named HolE

Alpha equivalence is equality after successful lowering.  Keeping successful
lowering in the relation prevents two unresolved type-variable occurrences
from becoming equivalent merely because both lowerings fail.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

def Lowerable (typeScope : TyScope) (termScope : TmScope Sig)
    (expression : Expr Sig sort) : Prop :=
  ∃ lowered, lower typeScope termScope expression = some lowered

def Alpha (typeScope : TyScope) (termScope : TmScope Sig)
    (left right : Expr Sig sort) : Prop :=
  ∃ lowered, lower typeScope termScope left = some lowered ∧
    lower typeScope termScope right = some lowered

theorem Alpha.refl (lowerable : Lowerable typeScope termScope expression) :
    Alpha typeScope termScope expression expression := by
  obtain ⟨lowered, equality⟩ := lowerable
  exact ⟨lowered, equality, equality⟩

theorem Alpha.symm (equivalent : Alpha typeScope termScope left right) :
    Alpha typeScope termScope right left := by
  obtain ⟨lowered, leftEquality, rightEquality⟩ := equivalent
  exact ⟨lowered, rightEquality, leftEquality⟩

theorem Alpha.trans (leftMiddle : Alpha typeScope termScope left middle)
    (middleRight : Alpha typeScope termScope middle right) :
    Alpha typeScope termScope left right := by
  obtain ⟨leftLowered, leftEquality, middleLeftEquality⟩ := leftMiddle
  obtain ⟨rightLowered, middleRightEquality, rightEquality⟩ := middleRight
  have same : leftLowered = rightLowered := by
    rw [middleLeftEquality] at middleRightEquality
    exact Option.some.inj middleRightEquality
  subst rightLowered
  exact ⟨leftLowered, leftEquality, rightEquality⟩

/-- A named expression bundled with evidence that its scope resolves. -/
structure ScopedExpr (Sig : Signature) (typeScope : TyScope)
    (termScope : TmScope Sig) (sort : HolSort) where
  expression : Expr Sig sort
  lowerable : Lowerable typeScope termScope expression

instance : Setoid (ScopedExpr Sig typeScope termScope sort) where
  r left right := Alpha typeScope termScope left.expression right.expression
  iseqv := ⟨
    fun expression => Alpha.refl expression.lowerable,
    Alpha.symm,
    Alpha.trans⟩

theorem Alpha.lower_eq (equivalent : Alpha typeScope termScope left right) :
    lower typeScope termScope left = lower typeScope termScope right := by
  obtain ⟨lowered, leftEquality, rightEquality⟩ := equivalent
  rw [leftEquality, rightEquality]

end Nucleus.HolE.Named
