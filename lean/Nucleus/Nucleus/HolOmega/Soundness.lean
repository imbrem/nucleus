import Nucleus.HolOmega.Semantics

/-!
# Soundness of formation and typing

`SoundModel` bundles operations on a common carrier with exactly the closure
laws the rules use — no more. The carrier is assigned to *raw* types, so open
contexts have a semantics before any well-kindedness judgement is imposed.

Denotation is relational (`TyDenotes`, `TmDenotes`) rather than functional, so
no computational content has to be extracted from a proof-irrelevant
derivation.

The payload is `Judgement.sound`: every well-kinded type denotes something, and
every well-typed term denotes something *in the carrier of its type*. Because
`Judgement` is a single indexed relation, that is one induction with a motive
defined by cases on the index, rather than a hand-written recursor.
-/

universe u v

namespace Nucleus.HolOmega

def KindEnv.lookup {Ω : Type v} {Δ : KindCtx} {n : Nat} {K : Kind}
    (h : Δ[n]? = some K) (ρ : KindEnv Ω Δ) : Kind.denote Ω K := by
  induction Δ generalizing n K with
  | nil => simp at h
  | cons L Δ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst K
      exact ρ.1
    | succ n => exact ih (by simpa using h) ρ.2

def envLookupNat {Ty : Type u} {El : Ty → Type v} {Γ : List Ty}
    {n : Nat} {A : Ty} (h : Γ[n]? = some A) (γ : Env El Γ) : El A := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst A
      exact γ.1
    | succ n => exact ih (by simpa using h) γ.2

/-- Operations on a common carrier, with exactly the closure laws the rules
use. See `Semantics.lean` for why this shape rather than an intrinsically-typed
one. -/
structure SoundModel (Base : Type u) (Ω : Type v) where
  carrier : Ty Base → Set Ω
  app : Ω → Ω → Ω
  lam : (Ω → Ω) → Ω
  tyApp : Ω → (K : Kind) → Kind.denote Ω K → Ω
  tyLam : (K : Kind) → (Kind.denote Ω K → Ω) → Ω
  bool : Bool → Ω
  equal : Ω → Ω → Ω
  epsilon : (Ω → Ω) → Ω
  abs : Tm Base → (Ω → Ω) → Ω → Ω
  rep : Tm Base → (Ω → Ω) → Ω → Ω
  app_mem : ∀ {A B f x}, f ∈ carrier (.tyArr A B) → x ∈ carrier A →
    app f x ∈ carrier B
  lam_mem : ∀ {A B} (f : Ω → Ω),
    (∀ x, x ∈ carrier A → f x ∈ carrier B) → lam f ∈ carrier (.tyArr A B)
  tyApp_mem : ∀ {F X A K} (a : Kind.denote Ω K) {f},
    f ∈ carrier (.tyApp F X) → tyApp f K a ∈ carrier (.tyApp F A)
  tyLam_mem : ∀ {K A} (f : Kind.denote Ω K → Ω),
    (∀ X, f X ∈ carrier A) → tyLam K f ∈ carrier (.tyLam K A)
  bool_mem : ∀ b, bool b ∈ carrier .tyBool
  equal_mem : ∀ {A x y}, x ∈ carrier A → y ∈ carrier A →
    equal x y ∈ carrier .tyBool
  epsilon_mem : ∀ {A} (p : Ω → Ω),
    (∀ x, x ∈ carrier A → p x ∈ carrier .tyBool) → epsilon p ∈ carrier A
  abs_mem : ∀ {A P} (p : Ω → Ω) {x},
    (∀ y, y ∈ carrier A → p y ∈ carrier .tyBool) → x ∈ carrier A →
    abs P p x ∈ carrier (.tySub A P)
  rep_mem : ∀ {A P} (p : Ω → Ω) {x},
    (∀ y, y ∈ carrier A → p y ∈ carrier .tyBool) →
    x ∈ carrier (.tySub A P) → rep P p x ∈ carrier A

/-- Relational interpretation of types. -/
inductive TyDenotes {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    {Δ : KindCtx} → KindEnv Ω Δ → Ty Base → (K : Kind) → Kind.denote Ω K →
    Prop
  | base {Δ ρ A} : TyDenotes M (Δ := Δ) ρ (.base A) .star (M.carrier (.base A))
  | tyVar {Δ ρ n K} (h : Δ[n]? = some K) :
      TyDenotes M ρ (.tyVar n) K (ρ.lookup h)
  | tyLam {Δ ρ A K L} {f : Kind.denote Ω K → Kind.denote Ω L} :
      (∀ X, TyDenotes M (Δ := K :: Δ) (X, ρ) A L (f X)) →
      TyDenotes M ρ (.tyLam K A) (.arr K L) f
  | tyApp {Δ ρ F X K L} {f : Kind.denote Ω K → Kind.denote Ω L}
      {x : Kind.denote Ω K} :
      TyDenotes M (Δ := Δ) ρ F (.arr K L) f → TyDenotes M ρ X K x →
      TyDenotes M ρ (.tyApp F X) L (f x)
  | tyBool {Δ ρ} : TyDenotes M (Δ := Δ) ρ .tyBool .star (M.carrier .tyBool)
  | tyArr {Δ ρ A B} :
      TyDenotes M (Δ := Δ) ρ (.tyArr A B) .star (M.carrier (.tyArr A B))
  | tySub {Δ ρ A p} :
      TyDenotes M (Δ := Δ) ρ (.tySub A p) .star (M.carrier (.tySub A p))

def CtxValid {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    (Γ : TmCtx Base) → Env (fun _ => Ω) Γ → Prop
  | [], _ => True
  | A :: Γ, γ => γ.1 ∈ M.carrier A ∧ CtxValid M Γ γ.2

/-- Relational interpretation of terms. -/
inductive TmDenotes {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    {Δ : KindCtx} → KindEnv Ω Δ → {Γ : TmCtx Base} →
      Env (fun _ => Ω) Γ → Tm Base → Ω → Prop
  | tmVar {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {n A}
      (h : Γ[n]? = some A) :
      TmDenotes M (Δ := Δ) ρ γ (.tmVar n) (envLookupNat h γ)
  | tmApp {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {f x fv xv} :
      TmDenotes M (Δ := Δ) ρ γ f fv → TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.tmApp f x) (M.app fv xv)
  | tmLam {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {A t} {f : Ω → Ω} :
      (∀ x, x ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := A :: Γ) (x, γ) t (f x)) →
      TmDenotes M ρ γ (.tmLam A t) (M.lam f)
  | tmTyApp {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {f A K fv a} :
      TmDenotes M (Δ := Δ) ρ γ f fv → TyDenotes M ρ A K a →
      TmDenotes M ρ γ (.tmTyApp f A) (M.tyApp fv K a)
  | tmTyLam {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {K t}
      {f : Kind.denote Ω K → Ω} :
      (∀ X, TmDenotes M (Δ := K :: Δ) (X, ρ) γ t (f X)) →
      TmDenotes M ρ γ (.tmTyLam K t) (M.tyLam K f)
  | tmBool {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {b} :
      TmDenotes M (Δ := Δ) ρ (Γ := Γ) γ (.tmBool b) (M.bool b)
  | tmEq {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {A x y xv yv} :
      TmDenotes M (Δ := Δ) ρ γ x xv → TmDenotes M ρ γ y yv →
      TmDenotes M ρ γ (.tmEq A x y) (M.equal xv yv)
  | tmEps {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {A p pv} :
      TmDenotes M (Δ := Δ) ρ γ p pv →
      TmDenotes M ρ γ (.tmEps A p) (M.epsilon (fun x => M.app pv x))
  | tmAbs {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {A P x xv}
      {p : Ω → Ω} :
      (∀ y, y ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := [A]) (y, PUnit.unit) P (p y)) →
      TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.tmAbs A P x) (M.abs P p xv)
  | tmRep {Δ ρ} {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} {A P x xv}
      {p : Ω → Ω} :
      (∀ y, y ∈ M.carrier A →
        TmDenotes M (Δ := Δ) ρ (Γ := [A]) (y, PUnit.unit) P (p y)) →
      TmDenotes M ρ γ x xv →
      TmDenotes M ρ γ (.tmRep A P x) (M.rep P p xv)

/-- What soundness asserts, per judgement form. -/
def Sound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω) :
    JudgementIndex Base → Prop
  | .kinded Δ A K => ∀ ρ : KindEnv Ω Δ, ∃ a, TyDenotes M ρ A K a
  | .hasType Δ Γ t A => ∀ (ρ : KindEnv Ω Δ) (γ : Env (fun _ => Ω) Γ),
      CtxValid M Γ γ → ∃ x, TmDenotes M ρ γ t x ∧ x ∈ M.carrier A

theorem CtxValid.lookup {Base : Type u} {Ω : Type v} {M : SoundModel Base Ω}
    {Γ : TmCtx Base} {γ : Env (fun _ => Ω) Γ} (hγ : CtxValid M Γ γ)
    {n : Nat} {A : Ty Base} (h : Γ[n]? = some A) :
    envLookupNat h γ ∈ M.carrier A := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons B Γ ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst A
      exact hγ.1
    | succ n => exact ih hγ.2 (by simpa using h)

/-- Every well-kinded type denotes, and every well-typed term denotes an
element of its type's carrier. -/
theorem Judgement.sound {Base : Type u} {Ω : Type v} (M : SoundModel Base Ω)
    {i : JudgementIndex Base} (h : Judgement i) : Sound M i := by
  classical
  induction h with
  | base => exact fun _ => ⟨_, .base⟩
  | tyVar hn => exact fun _ => ⟨_, .tyVar hn⟩
  | tyLam _ ih =>
    intro ρ
    choose f hf using fun X => ih (X, ρ)
    exact ⟨f, .tyLam hf⟩
  | tyApp _ _ ihf ihx =>
    intro ρ
    obtain ⟨f, hfd⟩ := ihf ρ
    obtain ⟨x, hxd⟩ := ihx ρ
    exact ⟨f x, .tyApp hfd hxd⟩
  | tyBool => exact fun _ => ⟨_, .tyBool⟩
  | tyArr => exact fun _ => ⟨_, .tyArr⟩
  | tySub => exact fun _ => ⟨_, .tySub⟩
  | tmVar hn => exact fun _ γ hγ => ⟨_, .tmVar hn, hγ.lookup hn⟩
  | tmApp _ _ ihf ihx =>
    intro ρ γ hγ
    obtain ⟨fv, hfd, hfm⟩ := ihf ρ γ hγ
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.app fv xv, .tmApp hfd hxd, M.app_mem hfm hxm⟩
  | @tmLam _ A _ t B _ _ _ iht =>
    intro ρ γ hγ
    let f : Ω → Ω := fun x =>
      if hx : x ∈ M.carrier A then Classical.choose (iht ρ (x, γ) ⟨hx, hγ⟩)
      else M.bool false
    have hf : ∀ x, x ∈ M.carrier A →
        TmDenotes M ρ (Γ := A :: _) (x, γ) t (f x) ∧ f x ∈ M.carrier B := by
      intro x hx
      simp only [f, dif_pos hx]
      exact Classical.choose_spec (iht ρ (x, γ) ⟨hx, hγ⟩)
    exact ⟨M.lam f, .tmLam fun x hx => (hf x hx).1,
      M.lam_mem f fun x hx => (hf x hx).2⟩
  | @tmTyApp _ _ _ _ _ _ K _ _ ihf ihA =>
    intro ρ γ hγ
    obtain ⟨fv, hfd, hfm⟩ := ihf ρ γ hγ
    obtain ⟨a, ha⟩ := ihA ρ
    exact ⟨M.tyApp fv K a, .tmTyApp hfd ha, M.tyApp_mem a hfm⟩
  | @tmTyLam K _ _ _ _ _ iht =>
    intro ρ γ hγ
    choose f hf using fun X => iht (X, ρ) γ hγ
    exact ⟨M.tyLam K f, .tmTyLam fun X => (hf X).1,
      M.tyLam_mem f fun X => (hf X).2⟩
  | tmBool => exact fun _ _ _ => ⟨_, .tmBool, M.bool_mem _⟩
  | tmEq _ _ _ _ ihx ihy =>
    intro ρ γ hγ
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    obtain ⟨yv, hyd, hym⟩ := ihy ρ γ hγ
    exact ⟨M.equal xv yv, .tmEq hxd hyd, M.equal_mem hxm hym⟩
  | tmEps _ _ _ ihp =>
    intro ρ γ hγ
    obtain ⟨pv, hpd, hpm⟩ := ihp ρ γ hγ
    exact ⟨M.epsilon fun x => M.app pv x, .tmEps hpd,
      M.epsilon_mem _ fun x hx => M.app_mem hpm hx⟩
  | @tmAbs _ A P _ x _ _ _ _ ihp ihx =>
    intro ρ γ hγ
    let p : Ω → Ω := fun y =>
      if hy : y ∈ M.carrier A then
        Classical.choose (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
      else M.bool false
    have hpd : ∀ y, y ∈ M.carrier A →
        TmDenotes M ρ (Γ := [A]) (y, PUnit.unit) P (p y) ∧
          p y ∈ M.carrier .tyBool := by
      intro y hy
      simp only [p, dif_pos hy]
      exact Classical.choose_spec (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.abs P p xv, .tmAbs (fun y hy => (hpd y hy).1) hxd,
      M.abs_mem p (fun y hy => (hpd y hy).2) hxm⟩
  | @tmRep _ A P _ x _ _ _ _ ihp ihx =>
    intro ρ γ hγ
    let p : Ω → Ω := fun y =>
      if hy : y ∈ M.carrier A then
        Classical.choose (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
      else M.bool false
    have hpd : ∀ y, y ∈ M.carrier A →
        TmDenotes M ρ (Γ := [A]) (y, PUnit.unit) P (p y) ∧
          p y ∈ M.carrier .tyBool := by
      intro y hy
      simp only [p, dif_pos hy]
      exact Classical.choose_spec (ihp ρ (y, PUnit.unit) ⟨hy, trivial⟩)
    obtain ⟨xv, hxd, hxm⟩ := ihx ρ γ hγ
    exact ⟨M.rep P p xv, .tmRep (fun y hy => (hpd y hy).1) hxd,
      M.rep_mem p (fun y hy => (hpd y hy).2) hxm⟩

end Nucleus.HolOmega
