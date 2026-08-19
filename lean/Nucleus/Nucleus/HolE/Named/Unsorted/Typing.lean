import Nucleus.HolE.Named.Typing
import Nucleus.HolE.Named.Unsorted

/-!
# Typing unsorted named HolE

The judgment is the exact pullback of sorted named typing through
`Unsorted.check`.  It is deliberately specialized to `Nat` names because the
current named kernel lowers `Nat` names to locally nameless free variables.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

/-- An unsorted representation of a classification at a known result sort. -/
inductive Classification (Sig : Signature) : HolSort → Type _ where
  | kind {kind : Kind} : Classification Sig (.kind kind)
  | tm (type : Expr Sig) : Classification Sig .tm

/-- Validate the type contained in an unsorted classification. -/
def checkClassification : Classification Sig sort → Option (Named.Classification Sig sort)
  | .kind => some .kind
  | .tm type => return .tm (← check (.kind .star) type)

/-- Erase the sort index carried by a sorted named classification's type. -/
def eraseClassification : Named.Classification Sig sort → Classification Sig sort
  | .kind => .kind
  | .tm type => .tm (erase type)

@[simp] theorem checkClassification_erase
    (classification : Named.Classification Sig sort) :
    checkClassification (eraseClassification classification) = some classification := by
  cases classification <;> simp [eraseClassification, checkClassification]

/-- An unsorted named expression checks exactly when both it and its
classification sort-check and the resulting sorted named judgment holds. -/
def Checks {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types (Named.scopeDepth sort depth))
    (expression : Expr Sig) (classification : Classification Sig sort) : Prop :=
  ∃ sortedExpression sortedClassification,
    check sort expression = some sortedExpression ∧
    checkClassification classification = some sortedClassification ∧
    Named.Checks typeScope termScope Γ sortedExpression sortedClassification

abbrev Kinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : Named.TyScope types) (family : Expr Sig) (kind : Kind) : Prop :=
  Checks (sort := .kind kind) typeScope .nil Nucleus.HolE.emptyBound family .kind

abbrev HasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (term type : Expr Sig) : Prop :=
  Checks (sort := .tm) typeScope termScope Γ term (.tm type)

theorem Checks.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types (Named.scopeDepth sort depth)}
    {expression : Expr Sig} {classification : Classification Sig sort}
    (typing : Checks typeScope termScope Γ expression classification) :
    ∃ sortedExpression sortedClassification,
      check sort expression = some sortedExpression ∧
      checkClassification classification = some sortedClassification ∧
      Named.Checks typeScope termScope Γ sortedExpression sortedClassification :=
  typing

theorem Checks.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types (Named.scopeDepth sort depth)}
    {expression : Expr Sig} {classification : Classification Sig sort}
    {sortedExpression : Named.Expr Sig Nat sort}
    {sortedClassification : Named.Classification Sig sort}
    (expressionCheck : check sort expression = some sortedExpression)
    (classificationCheck : checkClassification classification = some sortedClassification)
    (typing : Named.Checks typeScope termScope Γ sortedExpression sortedClassification) :
    Checks typeScope termScope Γ expression classification :=
  ⟨sortedExpression, sortedClassification, expressionCheck, classificationCheck, typing⟩

/-- Every sorted named typing derivation has an unsorted preimage. -/
theorem Checks.ofSorted {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types (Named.scopeDepth sort depth)}
    {expression : Named.Expr Sig Nat sort}
    {classification : Named.Classification Sig sort}
    (typing : Named.Checks typeScope termScope Γ expression classification) :
    Checks typeScope termScope Γ (erase expression) (eraseClassification classification) :=
  ⟨expression, classification, check_erase expression,
    checkClassification_erase classification, typing⟩

/-- A term rejected by the sort checker has no typing derivation at that sort. -/
theorem not_checks_of_check_eq_none {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types (Named.scopeDepth sort depth)}
    {expression : Expr Sig} {classification : Classification Sig sort}
    (rejected : check sort expression = none) :
    ¬Checks typeScope termScope Γ expression classification := by
  intro typing
  obtain ⟨sortedExpression, _, checked, _, _⟩ := typing
  rw [rejected] at checked
  contradiction

/-- An ill-sorted type annotation cannot classify a term. -/
theorem not_hasType_of_type_check_eq_none {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {term type : Expr Sig}
    (rejected : check (.kind .star) type = none) :
    ¬HasType typeScope termScope Γ term type := by
  intro typing
  obtain ⟨_, _, _, checked, _⟩ := typing
  simp [checkClassification, rejected] at checked

end Nucleus.HolE.Named.Unsorted
