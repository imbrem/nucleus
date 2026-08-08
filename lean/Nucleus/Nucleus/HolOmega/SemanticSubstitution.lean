import Mathlib
import Nucleus.HolOmega.Semantics

universe u v

namespace Nucleus.HolOmega

open Kernel

namespace Semantic

/-- A raw de Bruijn renaming which is well typed between kind contexts. -/
structure Ren (Δ Δ' : KindCtx) where
  fn : Nat → Nat
  maps : ∀ n RK, Δ[n]? = some RK → Δ'[fn n]? = some RK

def Ren.lift (R : Ren Δ Δ') : Ren (RK :: Δ) (RK :: Δ') where
  fn := liftRen R.fn
  maps := by
    intro n L h
    cases n with
    | zero => simpa using h
    | succ n => simpa [liftRen] using R.maps n L (by simpa using h)

/-- The target kind environment realizes the same variables as the source
environment through `R`. -/
def Ren.Compatible {U : Kernel.Universe} (R : Ren Δ Δ')
    (ρ : Kernel.Kind.Env U Δ) (ρ' : Kernel.Kind.Env U Δ') : Prop :=
  ∀ n RK (h : Δ[n]? = some RK),
    Kernel.Kind.Env.lookup h ρ = Kernel.Kind.Env.lookup (R.maps n RK h) ρ'

theorem Ren.compatible_lift {U : Kernel.Universe} {R : Ren Δ Δ'}
    {ρ : Kernel.Kind.Env U Δ} {ρ' : Kernel.Kind.Env U Δ'}
    (hR : R.Compatible ρ ρ') (X : Kernel.Kind.Val U RK) :
    R.lift.Compatible (X, ρ) (X, ρ') := by
  intro n L h
  cases n with
  | zero =>
    simp only [Kernel.Kind.Env.lookup]
  | succ n =>
    simpa [Ren.lift, liftRen, Kernel.Kind.Env.lookup] using hR n L (by simpa using h)

def TmCtx.renameTy (R : Semantic.Ren Δ Δ') (Γ : TmCtx Base) : TmCtx Base :=
  Γ.map (Expr.renameTy R.fn)

def RawEnv.renameTy (R : Semantic.Ren Δ Δ') :
    {Γ : TmCtx Base} → RawEnv U Γ → RawEnv U (TmCtx.renameTy R Γ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, RawEnv.renameTy R γ.2)

@[simp] theorem RawEnv.lookup_renameTy (R : Semantic.Ren Δ Δ')
    {Γ : TmCtx Base} {γ : RawEnv U Γ} {n A} (h : Γ[n]? = some A) :
    RawEnv.lookup (U := U) (by simpa [TmCtx.renameTy] using congrArg (Expr.renameTy R.fn) h)
        (RawEnv.renameTy R γ) = RawEnv.lookup h γ := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons C Γ ih =>
    cases n with
    | zero => simp [RawEnv.lookup, RawEnv.renameTy]
    | succ n => simpa [RawEnv.lookup, RawEnv.renameTy] using ih (by simpa using h)

def DenoteIndex.renameTy {Base : Type u} {U : Kernel.Universe.{v}}
    {Δ Δ' : KindCtx} (R : Semantic.Ren Δ Δ')
    (ρ' : Kernel.Kind.Env U Δ') : DenoteIndex Base U → DenoteIndex Base U
  | .kinded _ _ A RK x => .kinded Δ' ρ' (A.renameTy R.fn) RK x
  | .hasType _ _ Γ γ t A x => .hasType Δ' ρ' (TmCtx.renameTy R Γ)
      (RawEnv.renameTy R γ) (t.renameTy R.fn) (A.renameTy R.fn) x

set_option maxHeartbeats 1600000 in
theorem Denotes.renameTy {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ Δ' : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    (R : Semantic.Ren Δ Δ') (ρ' : Kernel.Kind.Env U Δ')
    (hR : R.Compatible ρ ρ') {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.renameTy R ρ' i) := by
  induction h <;> simp only [DenoteIndex.renameTy, Expr.renameTy, TmCtx.renameTy] at *
  all_goals aesop (add safe constructors Denotes) (add safe cases Denotes)

def Ren.weaken (Δ : KindCtx) (RK : RKind) : Ren Δ (RK :: Δ) where
  fn := Nat.succ
  maps := by intro n L h; simpa using h

theorem Ren.compatible_weaken {U : Kernel.Universe} (ρ : Kernel.Kind.Env U Δ)
    (X : Kernel.Kind.Val U RK) : (Ren.weaken Δ RK).Compatible ρ (X, ρ) := by
  intro n L h
  induction Δ generalizing n L with
  | nil => simp at h
  | cons J Δ ih =>
    cases n with
    | zero => simp [Kernel.Kind.Env.lookup]
    | succ n => simpa [Kernel.Kind.Env.lookup] using ih (by simpa using h) ρ.2

/-- A syntactic type substitution realizes a semantic kind environment. -/
def SubDenotes {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ)
    (ρ' : Kernel.Kind.Env U Δ') (σ : Nat → Ty Base) : Prop :=
  ∀ n RK (h : Δ[n]? = some RK),
    TyDenotes B ρ' (σ n) RK (Kernel.Kind.Env.lookup h ρ)

theorem SubDenotes.lift {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {ρ' : Kernel.Kind.Env U Δ'} {σ : Nat → Ty Base}
    (hσ : SubDenotes B ρ ρ' σ) (X : Kernel.Kind.Val U RK) :
    SubDenotes B (X, ρ) (X, ρ') (liftSub σ) := by
  intro n L h
  cases n with
  | zero =>
    simp only [liftSub]
    exact .tyVar (by simpa using h)
  | succ n =>
    simp only [liftSub]
    have hs := hσ n L (by simpa using h)
    simpa only [DenoteIndex.renameTy] using
      hs.renameTy (Ren.weaken Δ' RK) (X, ρ') (Ren.compatible_weaken ρ' X)

def TmCtx.substTy (σ : Nat → Ty Base) (Γ : TmCtx Base) : TmCtx Base :=
  Γ.map (Expr.substTy σ)

def RawEnv.substTy (σ : Nat → Ty Base) :
    {Γ : TmCtx Base} → RawEnv U Γ → RawEnv U (TmCtx.substTy σ Γ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, RawEnv.substTy σ γ.2)

@[simp] theorem RawEnv.lookup_substTy (σ : Nat → Ty Base)
    {Γ : TmCtx Base} {γ : RawEnv U Γ} {n A} (h : Γ[n]? = some A) :
    RawEnv.lookup (U := U) (by simpa [TmCtx.substTy] using congrArg (Expr.substTy σ) h)
        (RawEnv.substTy σ γ) = RawEnv.lookup h γ := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons C Γ ih =>
    cases n with
    | zero => simp [RawEnv.lookup, RawEnv.substTy]
    | succ n => simpa [RawEnv.lookup, RawEnv.substTy] using ih (by simpa using h)

def DenoteIndex.substTy {Base : Type u} {U : Kernel.Universe.{v}}
    {Δ Δ' : KindCtx} (σ : Nat → Ty Base) (ρ' : Kernel.Kind.Env U Δ') :
    DenoteIndex Base U → DenoteIndex Base U
  | .kinded _ _ A RK x => .kinded Δ' ρ' (A.substTy σ) RK x
  | .hasType _ _ Γ γ t A x => .hasType Δ' ρ' (TmCtx.substTy σ Γ)
      (RawEnv.substTy σ γ) (t.substTy σ) (A.substTy σ) x

set_option maxHeartbeats 1600000 in
theorem Denotes.substTy {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ Δ' : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    {ρ' : Kernel.Kind.Env U Δ'} {σ : Nat → Ty Base}
    (hσ : SubDenotes B ρ ρ' σ) {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.substTy σ ρ' i) := by
  induction h <;> simp only [DenoteIndex.substTy, Expr.substTy, TmCtx.substTy] at *
  all_goals aesop (add safe constructors Denotes) (add safe cases Denotes)

def instSub (X : Ty Base) : Nat → Ty Base
  | 0 => X
  | n + 1 => .tyVar n

@[simp] theorem instSub_eq (e : Expr Base s) (X : Ty Base) :
    e.substTy (instSub X) = e.instTy X := rfl

theorem SubDenotes.inst {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {RK : RKind} {X : Ty Base} {x : Kernel.Kind.Val U RK}
    (hX : TyDenotes B ρ X RK x) : SubDenotes B (x, ρ) ρ (instSub X) := by
  intro n L h
  cases n with
  | zero =>
    simp at h
    subst L
    exact hX
  | succ n =>
    simp only [instSub]
    exact .tyVar (by simpa using h)

theorem TyDenotes.instTy {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    {RK : RKind} {A X : Ty Base} {x : Kernel.Kind.Val U RK} {s : Nat}
    {a : Kernel.Kind.Val U ⟨.star, s⟩}
    (hA : TyDenotes B (x, ρ) A ⟨.star, s⟩ a)
    (hX : TyDenotes B ρ X RK x) : TyDenotes B ρ (A.instTy X) ⟨.star, s⟩ a := by
  simpa only [DenoteIndex.substTy, instSub_eq] using hA.substTy (SubDenotes.inst hX)

theorem Denotes.weakenTy {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    (X : Kernel.Kind.Val U RK) {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.renameTy (Ren.weaken Δ RK) (X, ρ) i) :=
  h.renameTy (Ren.weaken Δ RK) (X, ρ) (Ren.compatible_weaken ρ X)

end Semantic

end Nucleus.HolOmega
