import Nucleus.HolE.Named.Alpha

/-!
# Typing named HolE

The named judgment is the exact pullback of the locally nameless judgment
along lowering.  This gives an executable, auditable specification before the
individual named inference rules are exposed as convenience constructors.
-/

namespace Nucleus.HolE.Named

universe u
set_option relaxedAutoImplicit true

inductive Classification (Sig : Signature) : HolSort → Type u where
  | kind {kind : Kind} : Classification Sig (.kind kind)
  | tm (type : Ty Sig) : Classification Sig .tm

noncomputable def lowerClassification (typeScope : TyScope) :
    Classification Sig sort →
      Option (Nucleus.HolE.Classification Sig typeScope.kinds sort)
  | .kind => some .kind
  | .tm A => return .tm (← lowerTy typeScope A)

/-- A named expression checks when its lowering checks in locally nameless HolE. -/
def Checks {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope) (termScope : TmScope Sig)
    (Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds (scopeDepth sort termScope.length))
    (expression : Expr Sig sort) (classification : Classification Sig sort) : Prop :=
  ∃ loweredExpression loweredClassification,
    lower typeScope termScope expression = some loweredExpression ∧
    lowerClassification typeScope classification = some loweredClassification ∧
    Nucleus.HolE.Checks Γ loweredExpression loweredClassification

abbrev Kinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope) (family : Fam Sig kind) : Prop :=
  Checks (Sig := Sig) (sort := .kind kind) typeScope []
    Nucleus.HolE.emptyBound family .kind

abbrev HasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope) (termScope : TmScope Sig)
    (Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds termScope.length)
    (term : Tm Sig) (A : Ty Sig) : Prop :=
  Checks (Sig := Sig) (sort := .tm) typeScope termScope Γ term (.tm A)

theorem checks_iff {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {sort : HolSort} {typeScope : TyScope} {termScope : TmScope Sig}
    {Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds (scopeDepth sort termScope.length)}
    {expression : Expr Sig sort} {classification : Classification Sig sort} :
    Checks typeScope termScope Γ expression classification ↔
      ∃ loweredExpression loweredClassification,
        lower typeScope termScope expression = some loweredExpression ∧
        lowerClassification typeScope classification = some loweredClassification ∧
        Nucleus.HolE.Checks Γ loweredExpression loweredClassification :=
  Iff.rfl

/-- Soundness of named typing with respect to locally nameless typing. -/
theorem Checks.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {sort : HolSort} {typeScope : TyScope} {termScope : TmScope Sig}
    {Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds (scopeDepth sort termScope.length)}
    {expression : Expr Sig sort} {classification : Classification Sig sort}
    (typing : Checks typeScope termScope Γ expression classification) :
    ∃ loweredExpression loweredClassification,
      lower typeScope termScope expression = some loweredExpression ∧
      lowerClassification typeScope classification = some loweredClassification ∧
      Nucleus.HolE.Checks Γ loweredExpression loweredClassification :=
  typing

/-- Completeness for any fixed named preimage of a locally nameless derivation. -/
theorem Checks.complete
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {sort : HolSort} {typeScope : TyScope} {termScope : TmScope Sig}
    {Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds (scopeDepth sort termScope.length)}
    {expression : Expr Sig sort} {classification : Classification Sig sort}
    {loweredExpression : Nucleus.HolE.Expr Sig typeScope.kinds sort
      (scopeDepth sort termScope.length)}
    {loweredClassification : Nucleus.HolE.Classification Sig typeScope.kinds sort}
    (expressionLowering : lower typeScope termScope expression = some loweredExpression)
    (classificationLowering :
      lowerClassification typeScope classification = some loweredClassification)
    (typing : Nucleus.HolE.Checks Γ loweredExpression loweredClassification) :
    Checks typeScope termScope Γ expression classification :=
  ⟨loweredExpression, loweredClassification, expressionLowering,
    classificationLowering, typing⟩

theorem Checks.alpha_left
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {sort : HolSort} {typeScope : TyScope} {termScope : TmScope Sig}
    {Γ : Nucleus.HolE.BoundCtx Sig typeScope.kinds (scopeDepth sort termScope.length)}
    {left right : Expr Sig sort} {classification : Classification Sig sort}
    (equivalent : Alpha typeScope termScope left right)
    (typing : Checks typeScope termScope Γ left classification) :
    Checks typeScope termScope Γ right classification := by
  obtain ⟨lowered, leftLowering, rightLowering⟩ := equivalent
  obtain ⟨typedLowered, loweredClassification, typedLowering,
    classificationLowering, derivation⟩ := typing
  rw [leftLowering] at typedLowering
  have same := Option.some.inj typedLowering
  subst typedLowered
  exact ⟨lowered, loweredClassification, rightLowering,
    classificationLowering, derivation⟩

end Nucleus.HolE.Named
