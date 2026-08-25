import Nucleus.HolE

/-!
# Renaming typed free term variables

Locally nameless binders are unaffected.  The operation only changes the
natural-number component of each typed free term variable, including free
variables occurring in predicates nested inside types.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Uniformly rename the names of typed free term variables. -/
def renameFv (ρ : Nat → Nat) :
    Expr Sig types sort depth → Expr Sig types sort depth
  | .boolTy => .boolTy
  | .arr A B => .arr (renameFv ρ A) (renameFv ρ B)
  | .tyApp F A => .tyApp (renameFv ρ F) (renameFv ρ A)
  | .tyLam body => .tyLam (renameFv ρ body)
  | .tyBv item => .tyBv item
  | .sub A predicate => .sub (renameFv ρ A) (renameFv ρ predicate)
  | .tyExists predicate => .tyExists (renameFv ρ predicate)
  | .tyForall predicate => .tyForall (renameFv ρ predicate)
  | .model predicate => .model (renameFv ρ predicate)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .bv index
  | .fv name A => .fv (ρ name) (renameFv ρ A)
  | .app function argument => .app (renameFv ρ function) (renameFv ρ argument)
  | .lam A body => .lam (renameFv ρ A) (renameFv ρ body)
  | .bool value => .bool value
  | .eq A left right => .eq (renameFv ρ A) (renameFv ρ left) (renameFv ρ right)
  | .eps A predicate => .eps (renameFv ρ A) (renameFv ρ predicate)
  | .abs A predicate value =>
      .abs (renameFv ρ A) (renameFv ρ predicate) (renameFv ρ value)
  | .rep A predicate value =>
      .rep (renameFv ρ A) (renameFv ρ predicate) (renameFv ρ value)

@[simp] theorem renameFv_id (expression : Expr Sig types sort depth) :
    renameFv id expression = expression := by
  induction expression <;> simp_all [renameFv]

theorem renameFv_comp (g f : Nat → Nat)
    (expression : Expr Sig types sort depth) :
    renameFv g (renameFv f expression) = renameFv (g ∘ f) expression := by
  induction expression <;> simp_all [renameFv]

end Nucleus.HolE
