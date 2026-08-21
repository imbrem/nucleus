import Nucleus.Hol.Ethane.Syntax
import Nucleus.HolE.FVar

/-!
# Free variables of Ethane syntax

Variable identity includes the exact syntactic kind or type annotation.  A
binder removes only the matching `(name, sort)` pair from finite support.
-/

namespace Nucleus.Hol.Ethane

open Nucleus.HolE
set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

abbrev TypedFVar (Sig : Signature) (Name : Type := Nat) := FVar Name (Ty Sig Name)
abbrev Support (Sig : Signature) (Name : Type := Nat) := Finset (TypedFVar Sig Name)

namespace Expr

private def tyVariable (name : Name) (kind : Kind) : TypedFVar Sig Name :=
  ⟨name, .ty kind⟩

private def tmVariable (name : Name) (type : Ty Sig Name) : TypedFVar Sig Name :=
  ⟨name, .tm type⟩

/-- Finite support of a sorted Ethane expression. -/
noncomputable def fvars : Expr Sig Name sort → Support Sig Name
  | .boolTy => ∅
  | .arr A B => A.fvars ∪ B.fvars
  | .tyApp F A => F.fvars ∪ A.fvars
  | @Expr.tyLam _ _ domain _ name body =>
      body.fvars.erase (tyVariable name domain)
  | .tyFv name kind => {tyVariable name kind}
  | .tyExists name predicate => predicate.fvars.erase (tyVariable name .star)
  | .model name predicate => predicate.fvars.erase (tyVariable name .star)
  | .primFam _ | .primTm _ | .bool _ => ∅
  | .tmFv name A => insert (tmVariable name A) A.fvars
  | .app function argument => function.fvars ∪ argument.fvars
  | .lam name A body => A.fvars ∪ body.fvars.erase (tmVariable name A)
  | .eq A left right => A.fvars ∪ left.fvars ∪ right.fvars
  | .eps A predicate => A.fvars ∪ predicate.fvars

noncomputable def tyFvars (expression : Expr Sig Name sort) : Support Sig Name :=
  FVar.tyvars expression.fvars

noncomputable def tmFvars (expression : Expr Sig Name sort) : Support Sig Name :=
  FVar.tmvars expression.fvars

noncomputable def fvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.indices expression.fvars

noncomputable def tyFvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.tyIndices expression.fvars

noncomputable def tmFvarIndices (expression : Expr Sig Name sort) : Finset Name :=
  FVar.tmIndices expression.fvars

noncomputable def fvarsByIndex (expression : Expr Sig Name sort) :
    Nucleus.Dict Name (Finset (FVarSort (Ty Sig Name))) :=
  FVar.byIndex expression.fvars

def NoNameConfusion (expression : Expr Sig Name sort) : Prop :=
  FVar.NoNameConfusion expression.fvars

def NoConvConfusion (conv : Ty Sig Name → Ty Sig Name → Prop)
    (expression : Expr Sig Name sort) : Prop :=
  FVar.NoConvConfusion conv expression.fvars

theorem noNameConfusion_noConvConfusion {Sig : Signature} {Name : Type}
    {sort : HolSort} {expression : Expr Sig Name sort}
    (clear : NoNameConfusion expression)
    (conv : Ty Sig Name → Ty Sig Name → Prop) : NoConvConfusion conv expression :=
  FVar.noNameConfusion_noConvConfusion clear conv

end Expr

end Nucleus.Hol.Ethane
