import Nucleus.Hol.Ethane.Reference
import Nucleus.HolE.Named.Alpha
import Nucleus.HolE.Named.ConversionLaws

/-!
# Ethane alpha and conversion

Named expressions are alpha-equivalent when they lower to the same locally
nameless expression.  Family conversion is the corresponding pullback of the
HolE kernel relation.

`Model` is deliberately opaque to beta and eta.  Its binder is still an
ordinary binder, so renaming that binder is alpha conversion.  The one-step
family beta relation below has congruence rules for arrows, application, and
family lambda, but intentionally no congruence rule for `model`.
-/

namespace Nucleus.Hol.Ethane

universe u
set_option relaxedAutoImplicit true

namespace Expr

def Lowerable (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (expression : Expr Sig Nat sort) : Prop :=
  ∃ lowered, expression.lower typeScope termScope = some lowered

def Alpha (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (left right : Expr Sig Nat sort) : Prop :=
  ∃ lowered,
    left.lower typeScope termScope = some lowered ∧
    right.lower typeScope termScope = some lowered

theorem Alpha.refl (lowerable : Lowerable typeScope termScope expression) :
    Alpha typeScope termScope expression expression := by
  obtain ⟨lowered, lowering⟩ := lowerable
  exact ⟨lowered, lowering, lowering⟩

theorem Alpha.symm (equivalent : Alpha typeScope termScope left right) :
    Alpha typeScope termScope right left := by
  obtain ⟨lowered, leftLowering, rightLowering⟩ := equivalent
  exact ⟨lowered, rightLowering, leftLowering⟩

theorem Alpha.trans (leftMiddle : Alpha typeScope termScope left middle)
    (middleRight : Alpha typeScope termScope middle right) :
    Alpha typeScope termScope left right := by
  obtain ⟨leftLowered, leftLowering, middleLeftLowering⟩ := leftMiddle
  obtain ⟨rightLowered, middleRightLowering, rightLowering⟩ := middleRight
  rw [middleLeftLowering] at middleRightLowering
  cases Option.some.inj middleRightLowering
  exact ⟨leftLowered, leftLowering, rightLowering⟩

theorem Alpha.lower_eq (equivalent : Alpha typeScope termScope left right) :
    left.lower typeScope termScope = right.lower typeScope termScope := by
  obtain ⟨lowered, leftLowering, rightLowering⟩ := equivalent
  rw [leftLowering, rightLowering]

/-- Alpha equivalence between the bodies of two `Model` binders.  The two
binders may use different source names, but both bodies lower to the same term
under their respective extended scopes. -/
def ModelBodyAlpha (typeScope : TyScope types) (leftName rightName : Nat)
    (left right : Tm Sig) : Prop :=
  ∃ lowered,
    left.lowerTm (.cons (kind := .star) leftName typeScope) .nil = some lowered ∧
    right.lowerTm (.cons (kind := .star) rightName typeScope) .nil = some lowered

end Expr

/-- Ethane family conversion is the exact pullback of locally nameless HolE
family conversion. -/
structure FamEq {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (left right : Fam Sig kind) where
  loweredLeft : Nucleus.HolE.Fam Sig types kind
  loweredRight : Nucleus.HolE.Fam Sig types kind
  leftLowering : left.lowerFam typeScope = some loweredLeft
  rightLowering : right.lowerFam typeScope = some loweredRight
  derivation : Nucleus.HolE.FamEq Sig loweredLeft loweredRight

namespace FamEq

def refl {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {kind : Kind} {typeScope : TyScope types}
    {family : Fam Sig kind} {lowered : Nucleus.HolE.Fam Sig types kind}
    (lowering : family.lowerFam typeScope = some lowered) :
    FamEq typeScope family family :=
  ⟨lowered, lowered, lowering, lowering, .refl⟩

def symm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {kind : Kind} {typeScope : TyScope types}
    {left right : Fam Sig kind}
    (conversion : FamEq typeScope left right) :
    FamEq typeScope right left :=
  ⟨conversion.loweredRight, conversion.loweredLeft,
    conversion.rightLowering, conversion.leftLowering, conversion.derivation.symm⟩

def sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {kind : Kind} {typeScope : TyScope types}
    {left right : Fam Sig kind}
    (conversion : FamEq typeScope left right) :
    Nucleus.HolE.FamEq Sig conversion.loweredLeft conversion.loweredRight :=
  conversion.derivation

def complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {kind : Kind} {typeScope : TyScope types}
    {left right : Fam Sig kind}
    {loweredLeft loweredRight : Nucleus.HolE.Fam Sig types kind}
    (leftLowering : left.lowerFam typeScope = some loweredLeft)
    (rightLowering : right.lowerFam typeScope = some loweredRight)
    (derivation : Nucleus.HolE.FamEq Sig loweredLeft loweredRight) :
    FamEq typeScope left right :=
  ⟨loweredLeft, loweredRight, leftLowering, rightLowering, derivation⟩

/-- Renaming the bound type variable of `Model` is alpha conversion, hence a
kernel family conversion.  No conversion of the predicate is performed. -/
noncomputable def modelAlpha {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {typeScope : TyScope types}
    {leftName rightName : Nat} {left right : Tm Sig}
    (equivalent : Expr.ModelBodyAlpha typeScope leftName rightName left right) :
    FamEq typeScope (.model leftName left) (.model rightName right) := by
  let lowered := Classical.choose equivalent
  have lowerings := Classical.choose_spec equivalent
  let leftLowering := lowerings.1
  let rightLowering := lowerings.2
  have leftLowering' : Nucleus.HolE.Named.lowerTm
      (.cons (kind := .star) leftName typeScope) .nil left.toHolE = some lowered :=
    leftLowering
  have rightLowering' : Nucleus.HolE.Named.lowerTm
      (.cons (kind := .star) rightName typeScope) .nil right.toHolE = some lowered :=
    rightLowering
  exact ⟨.model lowered, .model lowered,
    by simp [Expr.lowerFam, Expr.toHolE, Nucleus.HolE.Named.lowerFam, leftLowering'],
    by simp [Expr.lowerFam, Expr.toHolE, Nucleus.HolE.Named.lowerFam, rightLowering'],
    .model rfl⟩

end FamEq

namespace Reduction

/-- One full family-beta step.  This relation descends through the ordinary
computational family constructors, but `Model` is an opaque leaf. -/
inductive FamBeta {Sig : Signature} : {types : List Kind} → {kind : Kind} →
    (typeScope : TyScope types) → Fam Sig kind → Fam Sig kind → Type 1 where
  | root (step : Nucleus.HolE.Named.FamBeta (Sig := Sig) typeScope
      (source.toHolE : Nucleus.HolE.Named.Fam Sig kind)
      (target.toHolE : Nucleus.HolE.Named.Fam Sig kind)) :
      FamBeta typeScope source target
  | arrLeft : FamBeta typeScope left left' →
      FamBeta typeScope (.arr left right) (.arr left' right)
  | arrRight : FamBeta typeScope right right' →
      FamBeta typeScope (.arr left right) (.arr left right')
  | appFunction : FamBeta typeScope function function' →
      FamBeta typeScope (.tyApp function argument) (.tyApp function' argument)
  | appArgument : FamBeta typeScope argument argument' →
      FamBeta typeScope (.tyApp function argument) (.tyApp function argument')
  | tyLam (name : Nat) :
      FamBeta (.cons (kind := domain) name typeScope) body body' →
      FamBeta typeScope (.tyLam name body) (.tyLam name body')

/-- A `Model` node is never the source of a family-beta step.  In particular,
the relation has no hidden congruence rule reducing its predicate. -/
theorem noBetaFromModel (name : Nat) (predicate : Tm Sig) (target : Ty Sig) :
    IsEmpty (FamBeta typeScope (.model name predicate) target) := by
  constructor
  intro step
  cases step with
  | root root =>
      cases lowering : Nucleus.HolE.Named.lowerTm
          (.cons (kind := .star) name typeScope) .nil predicate.toHolE with
      | none =>
          have impossible := root.sourceLowering
          simp [Expr.toHolE, Nucleus.HolE.Named.lowerFam, lowering] at impossible
      | some lowered =>
          have impossible := root.sourceLowering
          simp [Expr.toHolE, Nucleus.HolE.Named.lowerFam, lowering] at impossible

end Reduction

end Nucleus.Hol.Ethane
