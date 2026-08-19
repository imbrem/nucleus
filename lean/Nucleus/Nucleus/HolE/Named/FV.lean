import Nucleus.HolE.FVar
import Nucleus.HolE.Named.Syntax

/-!
# Free variables of named HolE

The support records both term and type variables.  Removing a binder removes
only its exact syntactic `(name, sort)` pair; an occurrence with the same index
and a different annotation remains free.
-/

namespace Nucleus.HolE.Named

open Nucleus.HolE

set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

abbrev TypedFVar (Sig : Signature) (Name : Type := Nat) := FVar Name (Ty Sig Name)
abbrev Support (Sig : Signature) (Name : Type := Nat) := Finset (TypedFVar Sig Name)

private def tyVariable (name : Name) (kind : Kind) : TypedFVar Sig Name :=
  ⟨name, .ty kind⟩

private def tmVariable (name : Name) (type : Ty Sig Name) : TypedFVar Sig Name :=
  ⟨name, .tm type⟩

/-- The finite support of a named expression. -/
noncomputable def fvars : Expr Sig Name sort → Support Sig Name
  | .boolTy => ∅
  | .arr A B => fvars A ∪ fvars B
  | .tyApp F A => fvars F ∪ fvars A
  | @Expr.tyLam _ _ domain _ name body =>
      (fvars body).erase (tyVariable name domain)
  | .tyFv name kind => {tyVariable name kind}
  | .sub A name predicate =>
      fvars A ∪ (fvars predicate).erase (tmVariable name A)
  | .tyExists name predicate =>
      (fvars predicate).erase (tyVariable name .star)
  | .model name predicate =>
      (fvars predicate).erase (tyVariable name .star)
  | .primFam _ => ∅
  | .primTm _ => ∅
  | .tmFv name A => insert (tmVariable name A) (fvars A)
  | .app function argument => fvars function ∪ fvars argument
  | .lam name A body => fvars A ∪ (fvars body).erase (tmVariable name A)
  | .bool _ => ∅
  | .eq A left right => fvars A ∪ fvars left ∪ fvars right
  | .eps A predicate => fvars A ∪ fvars predicate
  | .abs A name predicate value =>
      fvars A ∪ (fvars predicate).erase (tmVariable name A) ∪ fvars value
  | .rep A name predicate value =>
      fvars A ∪ (fvars predicate).erase (tmVariable name A) ∪ fvars value

noncomputable def tyFvars (expression : Expr Sig Name sort) : Support Sig Name :=
  FVar.tyvars (fvars expression)

noncomputable def tmFvars (expression : Expr Sig Name sort) : Support Sig Name :=
  FVar.tmvars (fvars expression)

noncomputable def fvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.indices (fvars expression)

noncomputable def tyFvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.tyIndices (fvars expression)

noncomputable def tmFvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.tmIndices (fvars expression)

noncomputable def fvarsByIndex (expression : Expr Sig Name sort) :
    Nucleus.Dict Name (Finset (FVarSort (Ty Sig Name))) :=
  FVar.byIndex (fvars expression)

/-- No name is used with two distinct syntactic sorts. -/
def NoNameConfusion (expression : Expr Sig Name sort) : Prop :=
  FVar.NoNameConfusion (fvars expression)

/-- Conversion-equivalent annotations at one name are syntactically equal. -/
def NoConvConfusion (conv : Ty Sig Name → Ty Sig Name → Prop)
    (expression : Expr Sig Name sort) : Prop :=
  FVar.NoConvConfusion conv (fvars expression)

theorem noNameConfusion_noConvConfusion {sort : HolSort}
    {expression : Expr Sig Name sort} (clear : NoNameConfusion expression)
    (conv : Ty Sig Name → Ty Sig Name → Prop) :
    Named.NoConvConfusion conv expression :=
  FVar.noNameConfusion_noConvConfusion clear conv

@[simp] theorem fvars_letTm (name : Name) (A : Ty Sig Name)
    (value body : Tm Sig Name) :
    fvars (letTm name A value body) =
      (fvars A ∪ (fvars body).erase (tmVariable name A)) ∪ fvars value := by
  simp [letTm, fvars]

end Nucleus.HolE.Named
