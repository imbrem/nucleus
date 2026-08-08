import Mathlib
import Nucleus.HolOmega.ProofTyping
import Nucleus.HolOmega.Soundness

universe u v

namespace Nucleus.HolOmega

open Kernel Semantic

/-- Model-relative equality of raw terms: any two denotations selected for the
two sides agree as tagged universe elements. -/
def EqTm.SemanticallyEqual {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) {Δ : KindCtx} {Γ : TmCtx Base}
    (t u : Tm Base) (A : Ty Base) : Prop :=
  ∀ (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ), CtxValid B ρ Γ γ →
    ∀ x y, TmDenotes B ρ γ t A x → TmDenotes B ρ γ u A y → x = y

set_option maxHeartbeats 3200000 in
theorem EqTm.sound {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) {Δ Γ t u A} (d : EqTm Δ Γ t u A) :
    EqTm.SemanticallyEqual B t u A := by
  induction d <;> simp only [EqTm.SemanticallyEqual] at *
  all_goals aesop (add safe cases Denotes) (add safe constructors Denotes)

def TrueAt {Base : Type u} {U : Kernel.Universe.{v}} (B : BaseSemantics Base U)
    (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ) (p : Tm Base) : Prop :=
  ∀ x, TmDenotes B ρ γ p .tyBool x → x = Omega.bool U true

def Entails {Base : Type u} {U : Kernel.Universe.{v}} (B : BaseSemantics Base U)
    (Δ : KindCtx) (Γ : TmCtx Base) (H : Hyps Base) (p : Tm Base) : Prop :=
  ∀ (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ), CtxValid B ρ Γ γ →
    (∀ q ∈ H, TrueAt B ρ γ q) → TrueAt B ρ γ p

set_option maxHeartbeats 6400000 in
theorem Proves.sound {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) {Δ Γ H p} (d : Proves Δ Γ H p) :
    Entails B Δ Γ H p := by
  induction d <;> simp only [Entails, TrueAt] at *
  all_goals
    simp only [Omega.bool, Omega.equal, Omega.epsilon, Omega.abs, Omega.rep,
      Omega.arrApp, Omega.cast] at *
  all_goals aesop (add safe cases Denotes) (add safe constructors Denotes)

end Nucleus.HolOmega
