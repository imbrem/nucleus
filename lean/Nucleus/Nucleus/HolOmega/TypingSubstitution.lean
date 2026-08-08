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
  | conv _ hc ih =>
      intro Γ' ρ hρ
      exact Judgement.conv (ih _ _ hρ) hc
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

/-- Formation of every entry in a raw term context.  This is the natural
extrinsic counterpart of the kernel's intrinsically formed `Ctx`. -/
def TmCtx.Wf (Δ : KindCtx) (Γ : TmCtx Base) : Prop :=
  ∀ A ∈ Γ, ∃ r, Kinded Δ A ⟨.star, r⟩

theorem TmCtx.Wf.lookup {n : Nat} {A : Ty Base}
    (hΓ : TmCtx.Wf Δ Γ) (hn : Γ[n]? = some A) :
    ∃ r, Kinded Δ A ⟨.star, r⟩ := by
  apply hΓ A
  exact List.mem_of_getElem? hn

/-- A typed raw term with the formation evidence that is implicit in every
kernel term.  Bare `HasType` is intentionally weaker because `tmVar` accepts
an arbitrary raw context entry. -/
structure TypedTerm (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base) (A : Ty Base) : Prop where
  typing : HasType Δ Γ t A
  formed : ∃ r, Kinded Δ A ⟨.star, r⟩

def ArrowParts {Base : Type u} : JudgementIndex Base → Prop
  | .kinded Δ (.tyArr A B) ⟨.star, _⟩ =>
      (∃ s, Kinded Δ A ⟨.star, s⟩) ∧ (∃ s, Kinded Δ B ⟨.star, s⟩)
  | _ => True

theorem Judgement.arrowParts {i : JudgementIndex Base} (h : Judgement i) :
    ArrowParts i := by
  induction h <;> try trivial
  case tyArr hA hB ihA ihB => exact ⟨⟨_, hA⟩, ⟨_, hB⟩⟩
  case subsume Δ A r s h hrs ih => cases A <;> exact ih

theorem kinded_arr_left (h : Kinded Δ (.tyArr A B) ⟨.star, r⟩) :
    ∃ s, Kinded Δ A ⟨.star, s⟩ := (Judgement.arrowParts h).1

theorem kinded_arr_right (h : Kinded Δ (.tyArr A B) ⟨.star, r⟩) :
    ∃ s, Kinded Δ B ⟨.star, s⟩ := (Judgement.arrowParts h).2

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

theorem liftSub_renameTy (σ : Nat → Ty Base) (ρ : Nat → Nat) :
    (fun n => (liftSub σ n).renameTy (liftRen ρ)) =
      liftSub (fun n => (σ n).renameTy ρ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      change ((σ n).renameTy Nat.succ).renameTy (liftRen ρ) =
        ((σ n).renameTy ρ).renameTy Nat.succ
      rw [Expr.renameTy_comp, Expr.renameTy_comp]
      exact congrArg (fun τ => (σ n).renameTy τ) (liftRen_comp_succ ρ)

theorem liftSub_comp_liftRen (σ : Nat → Ty Base) (ρ : Nat → Nat) :
    (fun n => liftSub σ (liftRen ρ n)) = liftSub (fun n => σ (ρ n)) := by
  funext n
  cases n <;> rfl

theorem Expr.renameTy_substTy (e : Expr Base s) (σ : Nat → Ty Base)
    (ρ : Nat → Nat) :
    (e.substTy σ).renameTy ρ =
      e.substTy (fun n => (σ n).renameTy ρ) := by
  induction e generalizing σ ρ <;>
    simp only [Expr.substTy, Expr.renameTy, *]
  all_goals rw [liftSub_renameTy]

theorem Expr.substTy_renameTy (e : Expr Base s) (ρ : Nat → Nat)
    (σ : Nat → Ty Base) :
    (e.renameTy ρ).substTy σ = e.substTy (fun n => σ (ρ n)) := by
  induction e generalizing ρ σ <;>
    simp only [Expr.renameTy, Expr.substTy, *]
  all_goals rw [liftSub_comp_liftRen]

theorem Expr.renameTy_instTy (e : Expr Base s) (X : Ty Base) (ρ : Nat → Nat) :
    (e.instTy X).renameTy ρ =
      (e.renameTy (liftRen ρ)).instTy (X.renameTy ρ) := by
  rw [Expr.instTy, Expr.renameTy_substTy, Expr.instTy, Expr.substTy_renameTy]
  congr 1
  funext n
  cases n <;> rfl

theorem TmCtx.lookup_renameTy {Γ : TmCtx Base} {n : Nat} {A : Ty Base}
    (hn : Γ[n]? = some A) :
    (Γ.renameTy ρ)[n]? = some (A.renameTy ρ) := by
  simpa [TmCtx.renameTy, List.getElem?_map, hn]

theorem TyConv.renameTy (h : TyConv Δ A B) (hρ : TyRen Δ Δ' ρ) :
    TyConv Δ' (A.renameTy ρ) (B.renameTy ρ) := by
  induction h with
  | alpha h => exact .alpha (congrArg (Expr.renameTy ρ) h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | tyBeta RK A X =>
      rw [Expr.renameTy_instTy]
      exact .tyBeta RK (A.renameTy (liftRen ρ)) (X.renameTy ρ)

theorem Judgement.renameTy {i : JudgementIndex Base} (h : Judgement i) :
    match i with
    | .kinded Δ A RK => ∀ Δ' ρ, TyRen Δ Δ' ρ → Kinded Δ' (A.renameTy ρ) RK
    | .hasType Δ Γ t A => ∀ Δ' ρ, TyRen Δ Δ' ρ →
        HasType Δ' (Γ.renameTy ρ) (t.renameTy ρ) (A.renameTy ρ) := by
  induction h with
  | base => intro Δ' ρ hρ; exact .base
  | tyVar hn => intro Δ' ρ hρ; exact .tyVar (hρ hn)
  | tyLam _ ih => intro Δ' ρ hρ; exact .tyLam (ih _ _ hρ.lift)
  | tyApp _ _ ihF ihX => intro Δ' ρ hρ; exact .tyApp (ihF _ _ hρ) (ihX _ _ hρ)
  | tyAll _ ih => intro Δ' ρ hρ; exact .tyAll (ih _ _ hρ.lift)
  | tyBool => intro Δ' ρ hρ; exact .tyBool
  | tyArr _ _ ihA ihB => intro Δ' ρ hρ; exact .tyArr (ihA _ _ hρ) (ihB _ _ hρ)
  | tySub _ _ ihA ihp => intro Δ' ρ hρ; exact .tySub (ihA _ _ hρ) (ihp _ _ hρ)
  | subsume _ hrs ih => intro Δ' ρ hρ; exact .subsume (ih _ _ hρ) hrs
  | conv _ hc ih => intro Δ' ρ hρ; exact .conv (ih _ _ hρ) (hc.renameTy hρ)
  | tmVar hn => intro Δ' ρ hρ; exact .tmVar (TmCtx.lookup_renameTy hn)
  | tmApp _ _ ihf ihx => intro Δ' ρ hρ; exact .tmApp (ihf _ _ hρ) (ihx _ _ hρ)
  | tmLam _ _ ihA iht =>
      intro Δ' ρ hρ
      exact .tmLam (ihA _ _ hρ) (by simpa [TmCtx.renameTy] using iht _ _ hρ)
  | tmTyApp _ _ ihf ihX =>
      intro Δ' ρ hρ
      rw [Expr.renameTy_instTy]
      exact .tmTyApp (ihf _ _ hρ) (ihX _ _ hρ)
  | tmTyLam _ iht =>
      intro Δ' ρ hρ
      exact .tmTyLam (by simpa [TmCtx.renameTy_lift] using iht _ _ hρ.lift)
  | tmBool => intro Δ' ρ hρ; exact .tmBool
  | tmEq _ _ _ ihA ihx ihy => intro Δ' ρ hρ; exact .tmEq (ihA _ _ hρ) (ihx _ _ hρ) (ihy _ _ hρ)
  | tmEps _ _ ihA ihp => intro Δ' ρ hρ; exact .tmEps (ihA _ _ hρ) (ihp _ _ hρ)
  | tmAbs _ _ _ ihA ihp ihx => intro Δ' ρ hρ; exact .tmAbs (ihA _ _ hρ) (ihp _ _ hρ) (ihx _ _ hρ)
  | tmRep _ _ _ ihA ihp ihx => intro Δ' ρ hρ; exact .tmRep (ihA _ _ hρ) (ihp _ _ hρ) (ihx _ _ hρ)

theorem HasType.renameTy (h : HasType Δ Γ t A) (hρ : TyRen Δ Δ' ρ) :
    HasType Δ' (Γ.renameTy ρ) (t.renameTy ρ) (A.renameTy ρ) :=
  Judgement.renameTy h Δ' ρ hρ

theorem TyRen.succ {RK : RKind} : TyRen Δ (RK :: Δ) Nat.succ := by
  intro n S hn
  simpa using hn

theorem HasType.weakenTy {RK : RKind} (h : HasType Δ Γ t A) :
    HasType (RK :: Δ) Γ.liftTy t.liftTy A.liftTy := by
  simpa [TmCtx.renameTy] using h.renameTy TyRen.succ

theorem TmSub.lift (h : TmSub Δ Γ Γ' σ) :
    TmSub Δ (A :: Γ) (A :: Γ') (liftTmSub σ) := by
  intro n B hn
  cases n with
  | zero =>
      simp at hn
      subst B
      simpa [liftTmSub] using Judgement.tmVar (Δ := Δ) (Γ := A :: Γ') (n := 0) rfl
  | succ n =>
      simpa [liftTmSub] using (h (by simpa using hn)).weaken (B := A)

theorem TmSub.mapLiftTy {RK : RKind} (h : TmSub Δ Γ Γ' σ) :
    TmSub (RK :: Δ) Γ.liftTy Γ'.liftTy (fun n => (σ n).liftTy) := by
  intro n A hn
  simp only [TmCtx.liftTy, List.getElem?_map] at hn
  rcases hn' : Γ[n]? with _ | B
  · simp [hn'] at hn
  · simp [hn'] at hn
    subst A
    exact (h hn').weakenTy

theorem Judgement.substTm {i : JudgementIndex Base} (h : Judgement i) :
    match i with
    | .kinded .. => True
    | .hasType Δ Γ t A => ∀ Γ' σ, TmSub Δ Γ Γ' σ → HasType Δ Γ' (t.subst σ) A := by
  induction h with
  | base | tyVar | tyLam | tyApp | tyAll | tyBool | tyArr | tySub | subsume => trivial
  | conv _ hc ih => intro Γ' σ hσ; exact .conv (ih _ _ hσ) hc
  | tmVar hn => intro Γ' σ hσ; simpa [Expr.subst] using hσ hn
  | tmApp _ _ ihf ihx => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmApp (ihf _ _ hσ) (ihx _ _ hσ)
  | tmLam hA _ _ iht => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmLam hA (iht _ _ hσ.lift)
  | tmTyApp _ hX ihf _ => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmTyApp (ihf _ _ hσ) hX
  | tmTyLam _ iht => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmTyLam (iht _ _ hσ.mapLiftTy)
  | tmBool => intro Γ' σ hσ; simpa [Expr.subst] using (Judgement.tmBool (Δ := _) (Γ := Γ'))
  | tmEq hA _ _ _ ihx ihy => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmEq hA (ihx _ _ hσ) (ihy _ _ hσ)
  | tmEps hA _ _ ihp => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmEps hA (ihp _ _ hσ)
  | tmAbs hA hp _ _ _ ihx => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmAbs hA hp (ihx _ _ hσ)
  | tmRep hA hp _ _ _ ihx => intro Γ' σ hσ; simpa [Expr.subst] using Judgement.tmRep hA hp (ihx _ _ hσ)

theorem HasType.subst (h : HasType Δ Γ t A) (hσ : TmSub Δ Γ Γ' σ) :
    HasType Δ Γ' (t.subst σ) A := Judgement.substTm h Γ' σ hσ

end Nucleus.HolOmega
