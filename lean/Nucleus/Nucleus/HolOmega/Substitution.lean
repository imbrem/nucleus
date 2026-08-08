import Nucleus.HolOmega.Syntax

/-!
# Substitution

Capture-avoiding de Bruijn renaming and substitution.

Because the syntax is one indexed family, each operation is a single recursive
definition covering both sorts, rather than a `mutual` pair that has to be kept
in step by hand.

Type-level operations traverse terms as well, since a subtype holds a predicate
term. Term-level operations do **not** traverse types: a type never mentions a
free term variable of the ambient context, because a subtype's predicate lives
in the fixed context determined by its carrier. That asymmetry is a direct
consequence of the tree-shaped discipline, and it is why `Expr.subst` can leave
every type it meets alone.
-/

universe u

namespace Nucleus.HolOmega

/-- Push a renaming under one binder. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Rename type variables. -/
def Expr.renameTy {Base : Type u} (ρ : Nat → Nat) :
    {s : ExprSort} → Expr Base s → Expr Base s
  | _, .base A => .base A
  | _, .tyVar n => .tyVar (ρ n)
  | _, .tyLam K A => .tyLam K (A.renameTy (liftRen ρ))
  | _, .tyApp F A => .tyApp (F.renameTy ρ) (A.renameTy ρ)
  | _, .tyBool => .tyBool
  | _, .tyArr A B => .tyArr (A.renameTy ρ) (B.renameTy ρ)
  | _, .tySub A p => .tySub (A.renameTy ρ) (p.renameTy ρ)
  | _, .tmVar n => .tmVar n
  | _, .tmApp f x => .tmApp (f.renameTy ρ) (x.renameTy ρ)
  | _, .tmLam A t => .tmLam (A.renameTy ρ) (t.renameTy ρ)
  | _, .tmTyApp f A => .tmTyApp (f.renameTy ρ) (A.renameTy ρ)
  | _, .tmTyLam K t => .tmTyLam K (t.renameTy (liftRen ρ))
  | _, .tmBool b => .tmBool b
  | _, .tmEq A x y => .tmEq (A.renameTy ρ) (x.renameTy ρ) (y.renameTy ρ)
  | _, .tmEps A p => .tmEps (A.renameTy ρ) (p.renameTy ρ)
  | _, .tmAbs A p x => .tmAbs (A.renameTy ρ) (p.renameTy ρ) (x.renameTy ρ)
  | _, .tmRep A p x => .tmRep (A.renameTy ρ) (p.renameTy ρ) (x.renameTy ρ)

/-- Push a type substitution under one binder. -/
def liftSub {Base : Type u} (σ : Nat → Ty Base) : Nat → Ty Base
  | 0 => .tyVar 0
  | n + 1 => (σ n).renameTy Nat.succ

/-- Substitute type variables. -/
def Expr.substTy {Base : Type u} (σ : Nat → Ty Base) :
    {s : ExprSort} → Expr Base s → Expr Base s
  | _, .base A => .base A
  | _, .tyVar n => σ n
  | _, .tyLam K A => .tyLam K (A.substTy (liftSub σ))
  | _, .tyApp F A => .tyApp (F.substTy σ) (A.substTy σ)
  | _, .tyBool => .tyBool
  | _, .tyArr A B => .tyArr (A.substTy σ) (B.substTy σ)
  | _, .tySub A p => .tySub (A.substTy σ) (p.substTy σ)
  | _, .tmVar n => .tmVar n
  | _, .tmApp f x => .tmApp (f.substTy σ) (x.substTy σ)
  | _, .tmLam A t => .tmLam (A.substTy σ) (t.substTy σ)
  | _, .tmTyApp f A => .tmTyApp (f.substTy σ) (A.substTy σ)
  | _, .tmTyLam K t => .tmTyLam K (t.substTy (liftSub σ))
  | _, .tmBool b => .tmBool b
  | _, .tmEq A x y => .tmEq (A.substTy σ) (x.substTy σ) (y.substTy σ)
  | _, .tmEps A p => .tmEps (A.substTy σ) (p.substTy σ)
  | _, .tmAbs A p x => .tmAbs (A.substTy σ) (p.substTy σ) (x.substTy σ)
  | _, .tmRep A p x => .tmRep (A.substTy σ) (p.substTy σ) (x.substTy σ)

/-- Rename term variables. Types are left alone: they cannot mention a free
term variable of the ambient context. -/
def Expr.rename {Base : Type u} (ρ : Nat → Nat) : Tm Base → Tm Base
  | .tmVar n => .tmVar (ρ n)
  | .tmApp f x => .tmApp (f.rename ρ) (x.rename ρ)
  | .tmLam A t => .tmLam A (t.rename (liftRen ρ))
  | .tmTyApp f A => .tmTyApp (f.rename ρ) A
  | .tmTyLam K t => .tmTyLam K (t.rename ρ)
  | .tmBool b => .tmBool b
  | .tmEq A x y => .tmEq A (x.rename ρ) (y.rename ρ)
  | .tmEps A p => .tmEps A (p.rename ρ)
  | .tmAbs A p x => .tmAbs A p (x.rename ρ)
  | .tmRep A p x => .tmRep A p (x.rename ρ)

/-- Push a term substitution under one binder. -/
def liftTmSub {Base : Type u} (σ : Nat → Tm Base) : Nat → Tm Base
  | 0 => .tmVar 0
  | n + 1 => (σ n).rename Nat.succ

/-- Substitute term variables. -/
def Expr.subst {Base : Type u} (σ : Nat → Tm Base) : Tm Base → Tm Base
  | .tmVar n => σ n
  | .tmApp f x => .tmApp (f.subst σ) (x.subst σ)
  | .tmLam A t => .tmLam A (t.subst (liftTmSub σ))
  | .tmTyApp f A => .tmTyApp (f.subst σ) A
  | .tmTyLam K t => .tmTyLam K (t.subst σ)
  | .tmBool b => .tmBool b
  | .tmEq A x y => .tmEq A (x.subst σ) (y.subst σ)
  | .tmEps A p => .tmEps A (p.subst σ)
  | .tmAbs A p x => .tmAbs A p (x.subst σ)
  | .tmRep A p x => .tmRep A p (x.subst σ)

/-- Replace the outermost type variable. One definition serves both sorts,
since `substTy` covers the whole family. -/
def Expr.instTy {Base : Type u} {s : ExprSort} (e : Expr Base s) (X : Ty Base) :
    Expr Base s :=
  e.substTy (fun | 0 => X | n + 1 => .tyVar n)

/-- Replace the outermost term variable. -/
def Expr.inst {Base : Type u} (t x : Tm Base) : Tm Base :=
  t.subst (fun | 0 => x | n + 1 => .tmVar n)

end Nucleus.HolOmega
