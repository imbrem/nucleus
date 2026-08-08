import Mathlib
import Nucleus.HolOmega.Soundness

universe u v

namespace Nucleus.HolOmega

open Kernel

/-- Sorted, model-independent alpha-beta equivalence.  Formation evidence on
beta is what makes expansion sound.  Subtype congruence is deliberately only
available through `alpha`: changing a carrier changes the fixed raw context
of its embedded predicate term. -/
inductive TyEquiv {Base : Type u} (Δ : KindCtx) : Ty Base → Ty Base → Prop
  | alpha (h : A = B) : TyEquiv Δ A B
  | symm : TyEquiv Δ A B → TyEquiv Δ B A
  | trans : TyEquiv Δ A B → TyEquiv Δ B C → TyEquiv Δ A C
  | tyLam (h : TyEquiv (RK :: Δ) A B) :
      TyEquiv Δ (.tyLam RK A) (.tyLam RK B)
  | tyAppFn (h : TyEquiv Δ F G) : TyEquiv Δ (.tyApp F X) (.tyApp G X)
  | tyAppArg (h : TyEquiv Δ X Y) : TyEquiv Δ (.tyApp F X) (.tyApp F Y)
  | tyAll (h : TyEquiv (RK :: Δ) A B) : TyEquiv Δ (.tyAll RK A) (.tyAll RK B)
  | tyArrLeft (h : TyEquiv Δ A B) : TyEquiv Δ (.tyArr A C) (.tyArr B C)
  | tyArrRight (h : TyEquiv Δ A B) : TyEquiv Δ (.tyArr C A) (.tyArr C B)
  | tyBeta (hA : Kinded (RK :: Δ) A ⟨L, RK.rank⟩) (hX : Kinded Δ X RK) :
      TyEquiv Δ (.tyApp (.tyLam RK A) X) (A.instTy X)

def TyEquiv.Side {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (Δ : KindCtx) (A C : Ty Base) : Prop :=
  ∀ (ρ : Kernel.Kind.Env U Δ) (RK : RKind) (a : Kernel.Kind.Val U RK),
    TyDenotes B ρ A RK a →
    match RK with
    | ⟨.star, _⟩ => ∃ s c, TyDenotes B ρ C ⟨.star, s⟩ c ∧ a.val = c.val
    | _ => ∃ c, TyDenotes B ρ C RK c ∧ a = c

def TyEquiv.SemanticallyEqual {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (Δ : KindCtx) (A C : Ty Base) : Prop :=
  TyEquiv.Side B Δ A C ∧ TyEquiv.Side B Δ C A

set_option maxHeartbeats 6400000 in
theorem TyEquiv.sound {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {A C : Ty Base}
    (h : TyEquiv Δ A C) : TyEquiv.SemanticallyEqual B Δ A C := by
  induction h <;> simp only [TyEquiv.SemanticallyEqual, TyEquiv.Side] at *
  all_goals aesop (add safe cases Denotes) (add safe constructors Denotes)

/-- Conversion-enabled typing is a separate closure of the stable core
judgement, preserving its ordinary induction principle. -/
inductive ConvHasType {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base) :
    Tm Base → Ty Base → Prop
  | core : HasType Δ Γ t A → ConvHasType Δ Γ t A
  | conv : ConvHasType Δ Γ t A → TyEquiv Δ A C → ConvHasType Δ Γ t C

inductive ConvTmDenotes {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ) :
    Tm Base → Ty Base → Omega U → Prop
  | core : TmDenotes B ρ γ t A x → ConvTmDenotes B ρ γ t A x
  | conv {r} {c : Kernel.Kind.Val U ⟨.star, r⟩} :
      TyEquiv Δ A C → ConvTmDenotes B ρ γ t A x → TyDenotes B ρ C ⟨.star, r⟩ c →
      x.code = c.val → ConvTmDenotes B ρ γ t C x

def ConvHasType.Sound {Base : Type u} {U : Kernel.Universe.{v}}
    (B : BaseSemantics Base U) {Δ : KindCtx} {Γ : TmCtx Base}
    (t : Tm Base) (A : Ty Base) : Prop :=
  ∀ (ρ : Kernel.Kind.Env U Δ) (γ : RawEnv U Γ), CtxValid B ρ Γ γ →
    (∃ r a, TyDenotes B ρ A ⟨.star, r⟩ a) ∧
    ∀ r a, TyDenotes B ρ A ⟨.star, r⟩ a →
      ∃ x, ConvTmDenotes B ρ γ t A x ∧ x.code = a.val

set_option maxHeartbeats 6400000 in
theorem ConvHasType.sound {Base : Type u} {U : Kernel.Universe.{v}}
    {B : BaseSemantics Base U} {Δ : KindCtx} {Γ : TmCtx Base}
    {t : Tm Base} {A : Ty Base} (h : ConvHasType Δ Γ t A) :
    ConvHasType.Sound B t A := by
  induction h <;> simp only [ConvHasType.Sound] at *
  all_goals aesop (add safe constructors ConvTmDenotes) (add safe cases Denotes)

namespace TyEquiv.Regression

theorem reverse_beta (hA : Kinded (RK :: Δ) A ⟨L, RK.rank⟩)
    (hX : Kinded Δ X RK) :
    TyEquiv Δ (A.instTy X) (.tyApp (.tyLam RK A) X) :=
  (TyEquiv.tyBeta hA hX).symm

theorem beta_under_arrows (hA : Kinded (RK :: Δ) A ⟨.star, RK.rank⟩)
    (hX : Kinded Δ X RK) :
    TyEquiv Δ (.tyArr C (.tyApp (.tyLam RK A) X))
      (.tyArr C (A.instTy X)) :=
  TyEquiv.tyArrRight (TyEquiv.tyBeta hA hX)

theorem reverse_beta_nested_app
    (hA : Kinded (RK :: Δ) A ⟨L, RK.rank⟩) (hX : Kinded Δ X RK) :
    TyEquiv Δ (.tyApp F (A.instTy X))
      (.tyApp F (.tyApp (.tyLam RK A) X)) :=
  TyEquiv.tyAppArg (TyEquiv.symm (TyEquiv.tyBeta hA hX))

theorem beta_under_all
    (hA : Kinded (RK :: Q :: Δ) A ⟨.star, RK.rank⟩)
    (hX : Kinded (Q :: Δ) X RK) :
    TyEquiv Δ (.tyAll Q (.tyApp (.tyLam RK A) X))
      (.tyAll Q (A.instTy X)) :=
  TyEquiv.tyAll (TyEquiv.tyBeta hA hX)

end TyEquiv.Regression

end Nucleus.HolOmega
