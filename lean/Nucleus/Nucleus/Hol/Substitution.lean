import Nucleus.Hol.Syntax

/-! Capture-avoiding substitution for raw monomorphic HOL terms. -/

universe u

namespace Nucleus.Hol

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Rename term variables. Type annotations are closed with respect to the
ambient term context; subtype predicates have their own fixed context. -/
def Expr.rename {Base : Type u} (ρ : Nat → Nat) : Tm Base → Tm Base
  | .tmVar n => .tmVar (ρ n)
  | .tmApp f x => .tmApp (f.rename ρ) (x.rename ρ)
  | .tmLam A t => .tmLam A (t.rename (liftRen ρ))
  | .tmBool b => .tmBool b
  | .tmEq A x y => .tmEq A (x.rename ρ) (y.rename ρ)
  | .tmEps A p => .tmEps A (p.rename ρ)
  | .tmAbs A p x => .tmAbs A p (x.rename ρ)
  | .tmRep A p x => .tmRep A p (x.rename ρ)

def liftSub {Base : Type u} (σ : Nat → Tm Base) : Nat → Tm Base
  | 0 => .tmVar 0
  | n + 1 => (σ n).rename Nat.succ

def Expr.subst {Base : Type u} (σ : Nat → Tm Base) : Tm Base → Tm Base
  | .tmVar n => σ n
  | .tmApp f x => .tmApp (f.subst σ) (x.subst σ)
  | .tmLam A t => .tmLam A (t.subst (liftSub σ))
  | .tmBool b => .tmBool b
  | .tmEq A x y => .tmEq A (x.subst σ) (y.subst σ)
  | .tmEps A p => .tmEps A (p.subst σ)
  | .tmAbs A p x => .tmAbs A p (x.subst σ)
  | .tmRep A p x => .tmRep A p (x.subst σ)

def Expr.inst {Base : Type u} (t x : Tm Base) : Tm Base :=
  t.subst (fun | 0 => x | n + 1 => .tmVar n)

end Nucleus.Hol
