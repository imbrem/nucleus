import Nucleus.HolE.Substitution

/-!
# Capture-avoiding free-variable substitution

A substitution is polymorphic in the ambient type-variable context.  This is
necessary because free term variables may occur below type binders.  Every
replacement is closed with respect to term binders, so inserting it below a
lambda cannot capture a de Bruijn variable.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A typed term free-variable substitution at every type-variable scope. -/
abbrev FSub (Sig : Signature) :=
  {types : List Kind} → (name : Nat) → Ty Sig types → Option (Tm Sig types 0)

private def placeClosed (replacement : Tm Sig types 0) : Tm Sig types depth :=
  rename Fin.elim0 replacement

/-- Simultaneous, capture-avoiding substitution of typed term free variables. -/
def fsubst (σ : FSub Sig) :
    Expr Sig types sort depth → Expr Sig types sort depth
  | .boolTy => .boolTy
  | .arr A B => .arr (fsubst σ A) (fsubst σ B)
  | .tyApp F A => .tyApp (fsubst σ F) (fsubst σ A)
  | .tyLam body => .tyLam (fsubst σ body)
  | .tyBv item => .tyBv item
  | .sub A predicate => .sub (fsubst σ A) (fsubst σ predicate)
  | .tyExists predicate => .tyExists (fsubst σ predicate)
  | .tyForall predicate => .tyForall (fsubst σ predicate)
  | .model predicate => .model (fsubst σ predicate)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .bv index
  | .fv name A =>
      match σ name A with
      | some replacement => placeClosed replacement
      | none => .fv name (fsubst σ A)
  | .app function argument => .app (fsubst σ function) (fsubst σ argument)
  | .lam A body => .lam (fsubst σ A) (fsubst σ body)
  | .bool value => .bool value
  | .eq A left right => .eq (fsubst σ A) (fsubst σ left) (fsubst σ right)
  | .eps A predicate => .eps (fsubst σ A) (fsubst σ predicate)
  | .abs A predicate value =>
      .abs (fsubst σ A) (fsubst σ predicate) (fsubst σ value)
  | .rep A predicate value =>
      .rep (fsubst σ A) (fsubst σ predicate) (fsubst σ value)

def emptyFSub : FSub Sig := fun _ _ => none

@[simp] theorem fsubst_empty (expression : Expr Sig types sort depth) :
    fsubst emptyFSub expression = expression := by
  induction expression <;> simp_all [fsubst, emptyFSub]

end Nucleus.HolE
