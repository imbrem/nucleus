import Mathlib
import Nucleus.HolOmega.SemanticSubstitution

universe u v

namespace Nucleus.HolOmega

open Kernel Semantic

/-- Every raw context entry denotes a code, and its tagged environment value
matches every possible denotation of that entry. -/
def CtxValid {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ) :
    (Γ : TmCtx Base) → RawEnv U Γ → Prop
  | [], _ => True
  | A :: Γ, γ =>
      (∃ r a, TyDenotes B ρ A ⟨.star, r⟩ a) ∧
      (∀ r a, TyDenotes B ρ A ⟨.star, r⟩ a → γ.1.code = a.val) ∧
      CtxValid B ρ Γ γ.2

theorem CtxValid.tail (h : CtxValid B ρ (A :: Γ) γ) :
    CtxValid B ρ Γ γ.2 := h.2.2

theorem CtxValid.head_exists (h : CtxValid B ρ (A :: Γ) γ) :
    ∃ r a, TyDenotes B ρ A ⟨.star, r⟩ a := h.1

theorem CtxValid.head_code (h : CtxValid B ρ (A :: Γ) γ)
    (hA : TyDenotes B ρ A ⟨.star, r⟩ a) : γ.1.code = a.val := h.2.1 r a hA

theorem CtxValid.lookup {Γ : TmCtx Base} {γ : RawEnv U Γ}
    (hγ : CtxValid B ρ Γ γ) (h : Γ[n]? = some A) :
    (∃ r a, TyDenotes B ρ A ⟨.star, r⟩ a) ∧
    ∀ r a, TyDenotes B ρ A ⟨.star, r⟩ a → (RawEnv.lookup h γ).code = a.val := by
  induction Γ generalizing n A with
  | nil => simp at h
  | cons C Γ ih =>
    cases n with
    | zero =>
      simp at h
      subst C
      exact ⟨hγ.head_exists, fun r a hA => hγ.head_code hA⟩
    | succ n => exact ih hγ.tail (by simpa using h)

/-- Semantic soundness of formation and typing.  The existential type
denotation is semantic regularity; the universal clause lets eliminators join
independently obtained denotations using coherence. -/
def Sound {Base : Type u} {U : Kernel.Universe.{v}} (B : BaseSemantics Base U) :
    JudgementIndex Base → Prop
  | .kinded Δ A RK => ∀ ρ : Kernel.Kind.Env U Δ, ∃ v, TyDenotes B ρ A RK v
  | .hasType Δ Γ t A => ∀ (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ),
      CtxValid B ρ Γ γ →
      (∃ r a, TyDenotes B ρ A ⟨.star, r⟩ a) ∧
      ∀ r a, TyDenotes B ρ A ⟨.star, r⟩ a →
        ∃ x, TmDenotes B ρ γ t A x ∧ x.code = a.val

set_option maxHeartbeats 3200000 in
theorem Judgement.sound {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) {i : JudgementIndex Base} (d : Judgement i) :
    Sound B i := by
  induction d <;> simp only [Sound] at *
  all_goals aesop (add safe constructors Denotes) (add safe cases Denotes)

end Nucleus.HolOmega
