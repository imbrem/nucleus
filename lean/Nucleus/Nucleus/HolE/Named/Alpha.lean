import Nucleus.HolE.Named.Lower

/-!
# Alpha conversion for named HolE

Alpha equivalence is equality after successful lowering.  Keeping successful
lowering in the relation prevents two unresolved type-variable occurrences
from becoming equivalent merely because both lowerings fail.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

def Lowerable (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (expression : Expr Sig sort) : Prop :=
  ∃ lowered, lower typeScope termScope expression = some lowered

def Alpha (typeScope : TyScope types) (termScope : TmScope Sig depth)
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
structure ScopedExpr (Sig : Signature) (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (sort : HolSort) where
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

/-- The locally nameless expression represented by a scoped named expression. -/
noncomputable def ScopedExpr.lowered
    {Sig : Signature} {types : List Kind} {depth : Nat}
    {typeScope : TyScope types} {termScope : TmScope Sig depth} {sort : HolSort}
    (expression : ScopedExpr Sig typeScope termScope sort) :
    Nucleus.HolE.Expr Sig types sort (scopeDepth sort depth) :=
  Classical.choose (show ∃ lowered,
    lower typeScope termScope expression.expression = some lowered from expression.lowerable)

@[simp] theorem ScopedExpr.lower_lowered
    {Sig : Signature} {types : List Kind} {depth : Nat}
    {typeScope : TyScope types} {termScope : TmScope Sig depth} {sort : HolSort}
    (expression : ScopedExpr Sig typeScope termScope sort) :
    lower typeScope termScope expression.expression = some expression.lowered :=
  Classical.choose_spec (show ∃ lowered,
    lower typeScope termScope expression.expression = some lowered from expression.lowerable)

theorem ScopedExpr.lowered_eq_of_alpha
    {Sig : Signature} {types : List Kind} {depth : Nat}
    {typeScope : TyScope types} {termScope : TmScope Sig depth} {sort : HolSort}
    {left right : ScopedExpr Sig typeScope termScope sort}
    (equivalent : left ≈ right) :
    left.lowered (types := types) (depth := depth) =
      right.lowered (types := types) (depth := depth) := by
  have equality := Alpha.lower_eq equivalent
  rw [left.lower_lowered, right.lower_lowered] at equality
  exact Option.some.inj equality

end Nucleus.HolE.Named
