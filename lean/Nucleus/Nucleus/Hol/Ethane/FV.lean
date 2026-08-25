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

/-- Every name an expression mentions, in binding or occurrence position.

Distinct from `fvarIndices`, and deliberately so: a binder erases its own name
from the free support, but `mapNames` renames binders too.  Anything choosing
fresh names for a construction that will later be materialized through
`mapNames` therefore has to clear the *bound* names as well, which is what this
measures.  It also forgets the type annotation that `fvars` keeps, because a
name collision after renaming is a collision whatever the annotation said. -/
noncomputable def nameIndices : Expr Sig Name sort → Finset Name
  | .boolTy | .primFam _ | .primTm _ | .bool _ => ∅
  | .arr A B => A.nameIndices ∪ B.nameIndices
  | .tyApp F A => F.nameIndices ∪ A.nameIndices
  | .tyLam name body => insert name body.nameIndices
  | .tyFv name _ => {name}
  | .tyExists name predicate => insert name predicate.nameIndices
  | .model name predicate => insert name predicate.nameIndices
  | .tmFv name A => insert name A.nameIndices
  | .app function argument => function.nameIndices ∪ argument.nameIndices
  | .lam name A body => insert name (A.nameIndices ∪ body.nameIndices)
  | .eq A left right => A.nameIndices ∪ left.nameIndices ∪ right.nameIndices
  | .eps A predicate => A.nameIndices ∪ predicate.nameIndices

/-- Renaming an expression renames exactly the names it mentions. -/
@[simp] theorem nameIndices_mapNames (f : Name → Name')
    (expression : Expr Sig Name sort) :
    (expression.mapNames f).nameIndices = expression.nameIndices.image f := by
  induction expression <;>
    simp_all [mapNames, nameIndices, Finset.image_union, Finset.image_insert]

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
