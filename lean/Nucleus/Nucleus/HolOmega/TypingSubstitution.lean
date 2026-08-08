import Mathlib.Tactic
import Nucleus.HolOmega.Typing

/-! # Syntactic regularity of HOL-omega typing -/

universe u

namespace Nucleus.HolOmega

variable {Base : Type u}

def TmRen (Γ Γ' : TmCtx Base) (ρ : Nat → Nat) : Prop :=
  ∀ ⦃n A⦄, Γ[n]? = some A → Γ'[ρ n]? = some A

def TmSub (Δ : KindCtx) (Γ Γ' : TmCtx Base) (σ : Nat → Tm Base) : Prop :=
  ∀ ⦃n A⦄, Γ[n]? = some A → HasType Δ Γ' (σ n) A

theorem TmRen.lift (h : TmRen Γ Γ' ρ) :
    TmRen (A :: Γ) (A :: Γ') (liftRen ρ) := by
  intro n B hn
  cases n with
  | zero => simpa [liftRen] using hn
  | succ n => exact h (by simpa using hn)

theorem TmRen.mapLiftTy (h : TmRen Γ Γ' ρ) :
    TmRen Γ.liftTy Γ'.liftTy ρ := by
  intro n A hn
  simp only [TmCtx.liftTy, List.getElem?_map] at hn ⊢
  rcases hn' : Γ[n]? with _ | B
  · simp [hn'] at hn
  · simp [hn'] at hn
    subst A
    simp [h hn']

theorem Judgement.renameTm {i : JudgementIndex Base} (h : Judgement i) :
    match i with
    | .kinded .. => True
    | .hasType Δ Γ t A => ∀ Γ' ρ, TmRen Γ Γ' ρ → HasType Δ Γ' (t.rename ρ) A := by
  induction h with
  | base | tyVar | tyLam | tyApp | tyAll | tyBool | tyArr | tySub | subsume => trivial
  | tmVar hn =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmVar (hρ hn)
  | tmApp _ _ ihf ihx =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmApp (ihf Γ' ρ hρ) (ihx Γ' ρ hρ)
  | tmLam hA _ _ iht =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmLam hA (iht _ _ hρ.lift)
  | tmTyApp _ _ ihf _ =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmTyApp (ihf _ _ hρ) ‹_›
  | tmTyLam _ iht =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmTyLam (iht _ _ hρ.mapLiftTy)
  | tmBool =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using (Judgement.tmBool (Δ := _) (Γ := Γ'))
  | tmEq hA _ _ _ ihx ihy =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmEq hA (ihx _ _ hρ) (ihy _ _ hρ)
  | tmEps hA _ _ ihp =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmEps hA (ihp _ _ hρ)
  | tmAbs hA hp _ _ _ ihx =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmAbs hA hp (ihx _ _ hρ)
  | tmRep hA hp _ _ _ ihx =>
      intro Γ' ρ hρ
      simpa [Expr.rename] using Judgement.tmRep hA hp (ihx _ _ hρ)

theorem HasType.rename (h : HasType Δ Γ t A) (hρ : TmRen Γ Γ' ρ) :
    HasType Δ Γ' (t.rename ρ) A := Judgement.renameTm h Γ' ρ hρ

theorem TmRen.succ : TmRen Γ (A :: Γ) Nat.succ := by
  intro n B hn
  simpa using hn

theorem HasType.weaken (h : HasType Δ Γ t A) :
    HasType Δ (B :: Γ) (t.rename Nat.succ) A := h.rename TmRen.succ

def TyRen (Δ Δ' : KindCtx) (ρ : Nat → Nat) : Prop :=
  ∀ ⦃n RK⦄, Δ[n]? = some RK → Δ'[ρ n]? = some RK

def TmCtx.renameTy (Γ : TmCtx Base) (ρ : Nat → Nat) : TmCtx Base :=
  Γ.map (Expr.renameTy ρ)

theorem TyRen.lift {RK : RKind} (h : TyRen Δ Δ' ρ) :
    TyRen (RK :: Δ) (RK :: Δ') (liftRen ρ) := by
  intro n S hn
  cases n with
  | zero => simpa [liftRen] using hn
  | succ n => exact h (by simpa using hn)

theorem liftRen_comp_succ (ρ : Nat → Nat) :
    liftRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := by
  funext n
  rfl

theorem liftRen_comp (ρ τ : Nat → Nat) :
    liftRen τ ∘ liftRen ρ = liftRen (τ ∘ ρ) := by
  funext n
  cases n <;> rfl

@[simp] theorem liftRen_comp_apply (ρ τ : Nat → Nat) (n : Nat) :
    liftRen τ (liftRen ρ n) = liftRen (fun x => τ (ρ x)) n := by
  cases n <;> rfl

theorem Expr.renameTy_comp (e : Expr Base s) (ρ τ : Nat → Nat) :
    (e.renameTy ρ).renameTy τ = e.renameTy (τ ∘ ρ) := by
  induction e generalizing ρ τ <;>
    simp [Expr.renameTy, Function.comp_def, *]

theorem TmCtx.renameTy_lift (Γ : TmCtx Base) (ρ : Nat → Nat) :
    Γ.liftTy.renameTy (liftRen ρ) = (Γ.renameTy ρ).liftTy := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
      simp only [TmCtx.liftTy, TmCtx.renameTy, List.map_cons]
      rw [Expr.renameTy_comp, liftRen_comp_succ, ← Expr.renameTy_comp]
      exact congrArg (List.cons _) ih

end Nucleus.HolOmega
