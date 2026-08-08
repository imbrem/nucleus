import Mathlib.Tactic
import Nucleus.HolOmega.Substitution

/-! # Ranked higher-kinded HOL-omega trees without subtypes -/

universe u

namespace Nucleus.HolOmegaSimple

abbrev Kind := HolOmega.Kind
abbrev RKind := HolOmega.RKind
abbrev KindCtx := List RKind

inductive ExprSort where | ty | tm

/-- The subtype-free fragment.  It retains the complete ranked type-operator
language and the primitive Boolean, equality, and choice terms. -/
inductive Expr (Base : Type u) : ExprSort → Type u
  | base : Base → Expr Base .ty
  | tyVar : Nat → Expr Base .ty
  | tyLam : RKind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | tyAll : RKind → Expr Base .ty → Expr Base .ty
  | tyEx : RKind → Expr Base .ty → Expr Base .ty
  | tyBool : Expr Base .ty
  | tyArr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | tmVar : Nat → Expr Base .tm
  | tmApp : Expr Base .tm → Expr Base .tm → Expr Base .tm
  | tmLam : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | tmTyApp : Expr Base .tm → Expr Base .ty → Expr Base .tm
  | tmTyLam : RKind → Expr Base .tm → Expr Base .tm
  | tmPack : RKind → Expr Base .ty → Expr Base .ty → Expr Base .tm → Expr Base .tm
  | tmUnpack : RKind → Expr Base .ty → Expr Base .ty → Expr Base .tm →
      Expr Base .tm → Expr Base .tm
  | tmBool : Bool → Expr Base .tm
  | tmEq : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | tmEps : Expr Base .ty → Expr Base .tm → Expr Base .tm

abbrev Ty (Base : Type u) := Expr Base .ty
abbrev Tm (Base : Type u) := Expr Base .tm
abbrev TmCtx (Base : Type u) := List (Ty Base)

variable {Base : Type u}

namespace Expr

def renameTy (ρ : Nat → Nat) : {s : ExprSort} → Expr Base s → Expr Base s
  | _, .base c => .base c
  | _, .tyVar n => .tyVar (ρ n)
  | _, .tyLam RK A => .tyLam RK (A.renameTy (HolOmega.liftRen ρ))
  | _, .tyApp F X => .tyApp (F.renameTy ρ) (X.renameTy ρ)
  | _, .tyAll RK A => .tyAll RK (A.renameTy (HolOmega.liftRen ρ))
  | _, .tyEx RK A => .tyEx RK (A.renameTy (HolOmega.liftRen ρ))
  | _, .tyBool => .tyBool
  | _, .tyArr A B => .tyArr (A.renameTy ρ) (B.renameTy ρ)
  | _, .tmVar n => .tmVar n
  | _, .tmApp f x => .tmApp (f.renameTy ρ) (x.renameTy ρ)
  | _, .tmLam A t => .tmLam (A.renameTy ρ) (t.renameTy ρ)
  | _, .tmTyApp f X => .tmTyApp (f.renameTy ρ) (X.renameTy ρ)
  | _, .tmTyLam RK t => .tmTyLam RK (t.renameTy (HolOmega.liftRen ρ))
  | _, .tmPack RK A X t =>
      .tmPack RK (A.renameTy (HolOmega.liftRen ρ)) (X.renameTy ρ) (t.renameTy ρ)
  | _, .tmUnpack RK A B k p =>
      .tmUnpack RK (A.renameTy (HolOmega.liftRen ρ)) (B.renameTy ρ)
        (k.renameTy (HolOmega.liftRen ρ)) (p.renameTy ρ)
  | _, .tmBool b => .tmBool b
  | _, .tmEq A x y => .tmEq (A.renameTy ρ) (x.renameTy ρ) (y.renameTy ρ)
  | _, .tmEps A p => .tmEps (A.renameTy ρ) (p.renameTy ρ)

abbrev liftTy (e : Expr Base s) := e.renameTy Nat.succ

def liftSub (σ : Nat → Ty Base) : Nat → Ty Base
  | 0 => .tyVar 0
  | n + 1 => (σ n).renameTy Nat.succ

def substTy (σ : Nat → Ty Base) : {s : ExprSort} → Expr Base s → Expr Base s
  | _, .base c => .base c
  | _, .tyVar n => σ n
  | _, .tyLam RK A => .tyLam RK (A.substTy (liftSub σ))
  | _, .tyApp F X => .tyApp (F.substTy σ) (X.substTy σ)
  | _, .tyAll RK A => .tyAll RK (A.substTy (liftSub σ))
  | _, .tyEx RK A => .tyEx RK (A.substTy (liftSub σ))
  | _, .tyBool => .tyBool
  | _, .tyArr A B => .tyArr (A.substTy σ) (B.substTy σ)
  | _, .tmVar n => .tmVar n
  | _, .tmApp f x => .tmApp (f.substTy σ) (x.substTy σ)
  | _, .tmLam A t => .tmLam (A.substTy σ) (t.substTy σ)
  | _, .tmTyApp f X => .tmTyApp (f.substTy σ) (X.substTy σ)
  | _, .tmTyLam RK t => .tmTyLam RK (t.substTy (liftSub σ))
  | _, .tmPack RK A X t =>
      .tmPack RK (A.substTy (liftSub σ)) (X.substTy σ) (t.substTy σ)
  | _, .tmUnpack RK A B k p =>
      .tmUnpack RK (A.substTy (liftSub σ)) (B.substTy σ)
        (k.substTy (liftSub σ)) (p.substTy σ)
  | _, .tmBool b => .tmBool b
  | _, .tmEq A x y => .tmEq (A.substTy σ) (x.substTy σ) (y.substTy σ)
  | _, .tmEps A p => .tmEps (A.substTy σ) (p.substTy σ)

def instTy (e : Expr Base s) (X : Ty Base) : Expr Base s :=
  e.substTy (fun | 0 => X | n + 1 => .tyVar n)

end Expr

abbrev TmCtx.liftTy (Γ : TmCtx Base) := Γ.map Expr.liftTy

end Nucleus.HolOmegaSimple

namespace Nucleus.HolOmega

variable {Base : Type u}

/-- Erase subtype refinements while retaining their carrier.  Abstraction and
representation are the identity after erasure, as both have the erased
carrier type. -/
def Ty.toSimple : Ty Base → HolOmegaSimple.Ty Base
  | .base c => .base c
  | .tyVar n => .tyVar n
  | .tyLam RK A => .tyLam RK (Ty.toSimple A)
  | .tyApp F X => .tyApp (Ty.toSimple F) (Ty.toSimple X)
  | .tyAll RK A => .tyAll RK (Ty.toSimple A)
  | .tyEx RK A => .tyEx RK (Ty.toSimple A)
  | .tyBool => .tyBool
  | .tyArr A B => .tyArr (Ty.toSimple A) (Ty.toSimple B)
  | .tySub A _ => Ty.toSimple A

def Tm.toSimple : Tm Base → HolOmegaSimple.Tm Base
  | .tmVar n => .tmVar n
  | .tmApp f x => .tmApp (Tm.toSimple f) (Tm.toSimple x)
  | .tmLam A t => .tmLam (Ty.toSimple A) (Tm.toSimple t)
  | .tmTyApp f X => .tmTyApp (Tm.toSimple f) (Ty.toSimple X)
  | .tmTyLam RK t => .tmTyLam RK (Tm.toSimple t)
  | .tmPack RK A X t => .tmPack RK (Ty.toSimple A) (Ty.toSimple X) (Tm.toSimple t)
  | .tmUnpack RK A B k p =>
      .tmUnpack RK (Ty.toSimple A) (Ty.toSimple B) (Tm.toSimple k) (Tm.toSimple p)
  | .tmBool b => .tmBool b
  | .tmEq A x y => .tmEq (Ty.toSimple A) (Tm.toSimple x) (Tm.toSimple y)
  | .tmEps A p => .tmEps (Ty.toSimple A) (Tm.toSimple p)
  | .tmAbs _ _ x => Tm.toSimple x
  | .tmRep _ _ x => Tm.toSimple x

def Expr.toSimple : {s : ExprSort} → Expr Base s →
    HolOmegaSimple.Expr Base (match s with | .ty => .ty | .tm => .tm)
  | .ty, A => Ty.toSimple A
  | .tm, t => Tm.toSimple t

abbrev TmCtx.toSimple (Γ : TmCtx Base) : HolOmegaSimple.TmCtx Base :=
  Γ.map Ty.toSimple

theorem Expr.toSimple_renameTy (e : Expr Base s) (ρ : Nat → Nat) :
    Expr.toSimple (e.renameTy ρ) =
      HolOmegaSimple.Expr.renameTy ρ (Expr.toSimple e) := by
  induction e generalizing ρ <;> simp [HolOmega.Expr.renameTy,
    Expr.toSimple, Ty.toSimple, Tm.toSimple, HolOmegaSimple.Expr.renameTy] <;> aesop

theorem Ty.toSimple_renameTy (A : Ty Base) (ρ : Nat → Nat) :
    Ty.toSimple (A.renameTy ρ) =
      HolOmegaSimple.Expr.renameTy ρ (Ty.toSimple A) :=
  Expr.toSimple_renameTy A ρ

theorem TmCtx.toSimple_liftTy (Γ : TmCtx Base) :
    Γ.liftTy.toSimple = Γ.toSimple.liftTy := by
  induction Γ <;> simp [TmCtx.liftTy, TmCtx.toSimple,
    HolOmegaSimple.TmCtx.liftTy, Ty.toSimple_renameTy, *]

end Nucleus.HolOmega
