import Nucleus.Hol.Ethane.Syntax
import Nucleus.HolE.Named.Typing
import Nucleus.HolE.Named.MapLower

/-!
# Ethane sorting and typing

The named Ethane judgments lower to the already checked named HolE fragment.
This file keeps three boundaries explicit: `Syn.check` validates syntactic
sorts, `Checks` validates kinds and term types, and `Expr.lower` removes names.
-/

namespace Nucleus.Hol.Ethane

set_option relaxedAutoImplicit true

abbrev TyScope := Nucleus.HolE.Named.TyScope
abbrev TmScope := Nucleus.HolE.Named.TmScope
abbrev BoundCtx := Nucleus.HolE.BoundCtx

namespace Expr

/-- Lower sorted named Ethane syntax to locally nameless HolE. -/
noncomputable def lower (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (expression : Expr Sig Nat sort) :
    Option (Nucleus.HolE.Expr Sig types sort
      (Nucleus.HolE.Named.scopeDepth sort depth)) :=
  Nucleus.HolE.Named.lower typeScope termScope expression.toHolE

noncomputable def lowerFam (typeScope : TyScope types) (family : Fam Sig kind) :
    Option (Nucleus.HolE.Fam Sig types kind) :=
  Nucleus.HolE.Named.lowerFam typeScope family.toHolE

noncomputable def lowerTy (typeScope : TyScope types) (type : Ty Sig) :
    Option (Nucleus.HolE.Ty Sig types) := lowerFam typeScope type

noncomputable def lowerTm (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (term : Tm Sig) : Option (Nucleus.HolE.Tm Sig types depth) :=
  Nucleus.HolE.Named.lowerTm typeScope termScope term.toHolE

end Expr

/-- The kind or term type expected of a sorted Ethane expression. -/
inductive Classification (Sig : Signature) : HolSort → Type _ where
  | kind {kind : Kind} : Classification Sig (.kind kind)
  | tm (type : Ty Sig) : Classification Sig .tm

namespace Classification

/-- Lower a classification together with its contained type. -/
noncomputable def lower (typeScope : TyScope types) :
    Classification Sig sort → Option (Nucleus.HolE.Classification Sig types sort)
  | .kind => some .kind
  | .tm A => return .tm (← A.lowerTy typeScope)

def toHolE : Classification Sig sort → Nucleus.HolE.Named.Classification Sig sort
  | .kind => .kind
  | .tm A => .tm A.toHolE

end Classification

/-- Checked Ethane is the exact pullback of locally nameless HolE typing. -/
def Checks {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth))
    (expression : Expr Sig Nat sort) (classification : Classification Sig sort) : Prop :=
  ∃ loweredExpression loweredClassification,
    expression.lower typeScope termScope = some loweredExpression ∧
    classification.lower typeScope = some loweredClassification ∧
    Nucleus.HolE.Checks Γ loweredExpression loweredClassification

abbrev Kinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (family : Fam Sig kind) : Prop :=
  Checks typeScope .nil Nucleus.HolE.emptyBound family .kind

abbrev HasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types depth) (term : Tm Sig) (type : Ty Sig) : Prop :=
  Checks (sort := .tm) typeScope termScope Γ term (.tm type)

/-- A checked judgment exposes the corresponding locally nameless judgment. -/
theorem Checks.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Expr Sig Nat sort} {classification : Classification Sig sort}
    (typing : Checks typeScope termScope Γ expression classification) :
    ∃ loweredExpression loweredClassification,
      expression.lower typeScope termScope = some loweredExpression ∧
      classification.lower typeScope = some loweredClassification ∧
      Nucleus.HolE.Checks Γ loweredExpression loweredClassification :=
  typing

/-- Every locally nameless derivation at a fixed Ethane preimage lifts back. -/
theorem Checks.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Expr Sig Nat sort} {classification : Classification Sig sort}
    {loweredExpression : Nucleus.HolE.Expr Sig types sort
      (Nucleus.HolE.Named.scopeDepth sort depth)}
    {loweredClassification : Nucleus.HolE.Classification Sig types sort}
    (expressionLowering : expression.lower typeScope termScope = some loweredExpression)
    (classificationLowering : classification.lower typeScope = some loweredClassification)
    (typing : Nucleus.HolE.Checks Γ loweredExpression loweredClassification) :
    Checks typeScope termScope Γ expression classification :=
  ⟨loweredExpression, loweredClassification, expressionLowering,
    classificationLowering, typing⟩

namespace Syn

/-- An unsorted classification whose result sort remains known externally. -/
inductive Classification (Sig : Signature) : HolSort → Type _ where
  | kind {kind : Kind} : Classification Sig (.kind kind)
  | tm (type : Syn Sig) : Classification Sig .tm

def Classification.check : Classification Sig sort →
    Option (Nucleus.Hol.Ethane.Classification Sig sort)
  | .kind => some .kind
  | .tm A => return .tm (← A.check (.kind .star))

def Classification.erase : Nucleus.Hol.Ethane.Classification Sig sort → Classification Sig sort
  | .kind => .kind
  | .tm A => .tm A.erase

@[simp] theorem Classification.check_erase
    (classification : Nucleus.Hol.Ethane.Classification Sig sort) :
    (Nucleus.Hol.Ethane.Syn.Classification.erase classification).check =
      some classification := by
  cases classification <;> simp [Nucleus.Hol.Ethane.Syn.Classification.erase,
    Nucleus.Hol.Ethane.Syn.Classification.check]

/-- Unsorted typing first checks every sort and then applies checked typing. -/
def Checks {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth))
    (expression : Syn Sig) (classification : Classification Sig sort) : Prop :=
  ∃ sortedExpression sortedClassification,
    expression.check sort = some sortedExpression ∧
    classification.check = some sortedClassification ∧
    Nucleus.Hol.Ethane.Checks typeScope termScope Γ sortedExpression sortedClassification

abbrev Kinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (family : Syn Sig) (kind : Kind) : Prop :=
  Checks (sort := .kind kind) typeScope .nil Nucleus.HolE.emptyBound family .kind

abbrev HasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types depth) (term type : Syn Sig) : Prop :=
  Checks (sort := .tm) typeScope termScope Γ term (.tm type)

theorem Checks.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Syn Sig} {classification : Classification Sig sort}
    (typing : Checks typeScope termScope Γ expression classification) :
    ∃ sortedExpression sortedClassification,
      expression.check sort = some sortedExpression ∧
      classification.check = some sortedClassification ∧
      Nucleus.Hol.Ethane.Checks typeScope termScope Γ sortedExpression sortedClassification :=
  typing

theorem Checks.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Syn Sig} {classification : Classification Sig sort}
    {sortedExpression : Expr Sig Nat sort}
    {sortedClassification : Nucleus.Hol.Ethane.Classification Sig sort}
    (expressionCheck : expression.check sort = some sortedExpression)
    (classificationCheck : classification.check = some sortedClassification)
    (typing : Nucleus.Hol.Ethane.Checks typeScope termScope Γ
      sortedExpression sortedClassification) :
    Checks typeScope termScope Γ expression classification :=
  ⟨sortedExpression, sortedClassification, expressionCheck, classificationCheck, typing⟩

/-- Every checked expression has an unsorted preimage. -/
theorem Checks.ofExpr {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Expr Sig Nat sort}
    {classification : Nucleus.Hol.Ethane.Classification Sig sort}
    (typing : Nucleus.Hol.Ethane.Checks typeScope termScope Γ expression classification) :
    Checks typeScope termScope Γ expression.erase
      (Nucleus.Hol.Ethane.Syn.Classification.erase classification) :=
  ⟨expression, classification, Expr.check_erase expression,
    Classification.check_erase classification, typing⟩

theorem not_checks_of_check_eq_none {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : BoundCtx Sig types (Nucleus.HolE.Named.scopeDepth sort depth)}
    {expression : Syn Sig} {classification : Classification Sig sort}
    (rejected : expression.check sort = none) :
    ¬Checks typeScope termScope Γ expression classification := by
  rintro ⟨_, _, checked, _⟩
  rw [rejected] at checked
  contradiction

end Syn

end Nucleus.Hol.Ethane
