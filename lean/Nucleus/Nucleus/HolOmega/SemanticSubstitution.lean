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

/-- Every model-independent conversion certificate preserves the denoted
universe code, uniformly in the universe, base interpretation, and kind
environment.  This is the sole semantic interface consumed by `CONV`. -/
theorem TyConv.sound {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {A C : Ty Base}
    (h : TyConv Δ A C) (ρ : Kernel.Kind.Env U Δ) {r : Nat}
    {a : Kernel.Kind.Val U ⟨.star, r⟩}
    (hA : TyDenotes B ρ A ⟨.star, r⟩ a) :
    ∃ s (c : Kernel.Kind.Val U ⟨.star, s⟩),
      TyDenotes B ρ C ⟨.star, s⟩ c ∧ a.val = c.val := by
  induction h with
  | alpha h => subst C; exact ⟨r, a, hA, rfl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨s, b, hB, hab⟩ := ih₁ ρ hA
    obtain ⟨q, c, hC, hbc⟩ := ih₂ ρ hB
    exact ⟨q, c, hC, hab.trans hbc⟩
  | tyBeta RK A X =>
    cases hA with
    | tyApp hf hX =>
      cases hf with
      | tyLam hbody =>
        exact ⟨r, _, TyDenotes.instTy (hbody _) hX, rfl⟩

theorem TmDenotes.convert {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    {Γ : TmCtx Base} {γ : RawEnv U Γ} {t : Tm Base} {A C : Ty Base}
    {x : Omega U} {r : Nat} {a : Kernel.Kind.Val U ⟨.star, r⟩}
    (hAC : TyConv Δ A C) (ht : TmDenotes B ρ γ t A x)
    (hA : TyDenotes B ρ A ⟨.star, r⟩ a) (hxa : x.code = a.val) :
    ∃ s c, TmDenotes B ρ γ t C x ∧ TyDenotes B ρ C ⟨.star, s⟩ c ∧
      x.code = c.val := by
  obtain ⟨s, c, hC, hac⟩ := hAC.sound ρ hA
  have hxc := hxa.trans hac
  exact ⟨s, c, .tmConv hAC ht hC hxc, hC, hxc⟩

theorem Denotes.weakenTy {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {ρ : Kernel.Kind.Env U Δ}
    (X : Kernel.Kind.Val U RK) {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.renameTy (Ren.weaken Δ RK) (X, ρ) i) :=
  h.renameTy (Ren.weaken Δ RK) (X, ρ) (Ren.compatible_weaken ρ X)

/-- A well-typed renaming of term variables. -/
structure TmRen (Γ Γ' : TmCtx Base) where
  fn : Nat → Nat
  maps : ∀ n A, Γ[n]? = some A → Γ'[fn n]? = some A

def TmRen.lift (R : TmRen Γ Γ') : TmRen (A :: Γ) (A :: Γ') where
  fn := liftRen R.fn
  maps := by
    intro n C h
    cases n with
    | zero => simpa using h
    | succ n => simpa [liftRen] using R.maps n C (by simpa using h)

def TmRen.Compatible (R : TmRen Γ Γ') (γ : RawEnv U Γ) (γ' : RawEnv U Γ') : Prop :=
  ∀ n A (h : Γ[n]? = some A), RawEnv.lookup h γ = RawEnv.lookup (R.maps n A h) γ'

theorem TmRen.compatible_lift {R : TmRen Γ Γ'} {γ : RawEnv U Γ} {γ' : RawEnv U Γ'}
    (hR : R.Compatible γ γ') (x : Omega U) : R.lift.Compatible (x, γ) (x, γ') := by
  intro n C h
  cases n with
  | zero => simp [RawEnv.lookup]
  | succ n => simpa [TmRen.lift, liftRen, RawEnv.lookup] using hR n C (by simpa using h)

def TmRen.weaken (Γ : TmCtx Base) (A : Ty Base) : TmRen Γ (A :: Γ) where
  fn := Nat.succ
  maps := by intro n C h; simpa using h

theorem TmRen.compatible_weaken (γ : RawEnv U Γ) (x : Omega U) :
    (TmRen.weaken Γ A).Compatible γ (x, γ) := by
  intro n C h
  induction Γ generalizing n C with
  | nil => simp at h
  | cons D Γ ih =>
    cases n with
    | zero => simp [RawEnv.lookup]
    | succ n => simpa [RawEnv.lookup] using ih (by simpa using h) γ.2

def DenoteIndex.renameTm {Base : Type u} {U : Kernel.Universe.{v}}
    {Γ Γ' : TmCtx Base} (R : TmRen Γ Γ') (γ' : RawEnv U Γ') :
    DenoteIndex Base U → DenoteIndex Base U
  | i@(.kinded ..) => i
  | .hasType Δ ρ _ _ t A x => .hasType Δ ρ Γ' γ' (t.rename R.fn) A x

set_option maxHeartbeats 1600000 in
theorem Denotes.renameTm {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Γ Γ' : TmCtx Base} {γ : RawEnv U Γ}
    (R : TmRen Γ Γ') (γ' : RawEnv U Γ') (hR : R.Compatible γ γ')
    {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.renameTm R γ' i) := by
  induction h <;> simp only [DenoteIndex.renameTm, Expr.rename] at *
  all_goals aesop (add safe constructors Denotes) (add safe cases Denotes)

def TmSubDenotes {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ)
    (γ : RawEnv U Γ) (γ' : RawEnv U Γ') (σ : Nat → Tm Base) : Prop :=
  ∀ n A (h : Γ[n]? = some A), TmDenotes B ρ γ' (σ n) A (RawEnv.lookup h γ)

theorem TmSubDenotes.lift {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {γ : RawEnv U Γ} {γ' : RawEnv U Γ'} {σ : Nat → Tm Base}
    (hσ : TmSubDenotes B ρ γ γ' σ) (x : Omega U) :
    TmSubDenotes B ρ (x, γ) (x, γ') (liftTmSub σ) := by
  intro n C h
  cases n with
  | zero => exact .tmVar (by simpa using h)
  | succ n =>
    simp only [liftTmSub]
    have hs := hσ n C (by simpa using h)
    simpa only [DenoteIndex.renameTm] using
      hs.renameTm (TmRen.weaken Γ' C) (x, γ') (TmRen.compatible_weaken γ' x)

def DenoteIndex.substTm {Base : Type u} {U : Kernel.Universe.{v}}
    {Γ' : TmCtx Base} (σ : Nat → Tm Base) (γ' : RawEnv U Γ') :
    DenoteIndex Base U → DenoteIndex Base U
  | i@(.kinded ..) => i
  | .hasType Δ ρ _ _ t A x => .hasType Δ ρ Γ' γ' (t.subst σ) A x

set_option maxHeartbeats 1600000 in
theorem Denotes.substTm {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {γ : RawEnv U Γ} {γ' : RawEnv U Γ'} {σ : Nat → Tm Base}
    (hσ : TmSubDenotes B ρ γ γ' σ) {i : DenoteIndex Base U} (h : Denotes B i) :
    Denotes B (DenoteIndex.substTm σ γ' i) := by
  induction h <;> simp only [DenoteIndex.substTm, Expr.subst] at *
  all_goals aesop (add safe constructors Denotes) (add safe cases Denotes)

def instTmSub (x : Tm Base) : Nat → Tm Base
  | 0 => x
  | n + 1 => .tmVar n

@[simp] theorem instTmSub_eq (t x : Tm Base) : t.subst (instTmSub x) = t.inst x := rfl

theorem TmSubDenotes.inst {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {γ : RawEnv U Γ} {A : Ty Base} {x : Tm Base} {xv : Omega U}
    (hx : TmDenotes B ρ γ x A xv) :
    TmSubDenotes B ρ (xv, γ) γ (instTmSub x) := by
  intro n C h
  cases n with
  | zero =>
    simp at h
    subst C
    exact hx
  | succ n => exact .tmVar (by simpa using h)

theorem TmDenotes.inst {B : BaseSemantics Base U} {ρ : Kernel.Kind.Env U Δ}
    {γ : RawEnv U Γ} {A C : Ty Base} {t x : Tm Base} {xv tv : Omega U}
    (ht : TmDenotes B ρ (xv, γ) t C tv) (hx : TmDenotes B ρ γ x A xv) :
    TmDenotes B ρ γ (t.inst x) C tv := by
  simpa only [DenoteIndex.substTm, instTmSub_eq] using ht.substTm (TmSubDenotes.inst hx)

end Semantic

end Nucleus.HolOmega
