import Nucleus.HolOmegaSimple.Syntax
import Nucleus.HolOmega.Typing

/-! # Formation and typing for subtype-free ranked HOL-omega -/

universe u

namespace Nucleus.HolOmegaSimple

inductive JudgementIndex (Base : Type u) where
  | kinded (Δ : KindCtx) (A : Ty Base) (RK : RKind)
  | hasType (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base) (A : Ty Base)

inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | base : Judgement (.kinded Δ (.base c) ⟨.star, r⟩)
  | tyVar {RK : RKind} : Δ[n]? = some RK → Judgement (.kinded Δ (.tyVar n) RK)
  | tyLam {RK : RKind} : Judgement (.kinded (RK :: Δ) A ⟨L, RK.rank⟩) →
      Judgement (.kinded Δ (.tyLam RK A) ⟨.arr RK.kind L, RK.rank⟩)
  | tyApp : Judgement (.kinded Δ F ⟨.arr K L, r⟩) →
      Judgement (.kinded Δ X ⟨K, r⟩) →
      Judgement (.kinded Δ (.tyApp F X) ⟨L, r⟩)
  | tyAll {RK : RKind} : Judgement (.kinded (RK :: Δ) A ⟨.star, s⟩) →
      Judgement (.kinded Δ (.tyAll RK A) ⟨.star, max RK.rank s + 2⟩)
  | tyBool : Judgement (.kinded Δ .tyBool ⟨.star, r⟩)
  | tyArr : Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.kinded Δ B ⟨.star, r⟩) →
      Judgement (.kinded Δ (.tyArr A B) ⟨.star, r⟩)
  | subsume : Judgement (.kinded Δ A ⟨.star, r⟩) → r ≤ s →
      Judgement (.kinded Δ A ⟨.star, s⟩)
  | tmVar : Γ[n]? = some A → Judgement (.hasType Δ Γ (.tmVar n) A)
  | tmApp : Judgement (.hasType Δ Γ f (.tyArr A B)) →
      Judgement (.hasType Δ Γ x A) → Judgement (.hasType Δ Γ (.tmApp f x) B)
  | tmLam : Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ (A :: Γ) t B) →
      Judgement (.hasType Δ Γ (.tmLam A t) (.tyArr A B))
  | tmTyApp {RK : RKind} : Judgement (.hasType Δ Γ f (.tyAll RK B)) →
      Judgement (.kinded Δ X RK) →
      Judgement (.hasType Δ Γ (.tmTyApp f X) (B.instTy X))
  | tmTyLam {RK : RKind} : Judgement (.hasType (RK :: Δ) Γ.liftTy t A) →
      Judgement (.hasType Δ Γ (.tmTyLam RK t) (.tyAll RK A))
  | tmBool : Judgement (.hasType Δ Γ (.tmBool b) .tyBool)
  | tmEq : Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ Γ x A) → Judgement (.hasType Δ Γ y A) →
      Judgement (.hasType Δ Γ (.tmEq A x y) .tyBool)
  | tmEps : Judgement (.kinded Δ A ⟨.star, r⟩) →
      Judgement (.hasType Δ Γ p (.tyArr A .tyBool)) →
      Judgement (.hasType Δ Γ (.tmEps A p) A)

abbrev Kinded {Base : Type u} (Δ : KindCtx) (A : Ty Base) (RK : RKind) :=
  Judgement (.kinded Δ A RK)
abbrev HasType {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base)
    (t : Tm Base) (A : Ty Base) := Judgement (.hasType Δ Γ t A)

variable {Base : Type u}

/-- The kind shape synthesized by a raw type, deliberately forgetting rank.
Ranks are not unique: `base` and `tyBool` inhabit every rank, and `subsume`
raises any `star` derivation. -/
def kindOf (Δ : KindCtx) : Ty Base → Option Kind
  | .base _ => some .star
  | .tyVar n => (Δ[n]?).map (·.kind)
  | .tyLam RK A => (kindOf (RK :: Δ) A).map (.arr RK.kind)
  | .tyApp F _ => match kindOf Δ F with
      | some (.arr _ L) => some L
      | _ => none
  | .tyAll _ _ => some .star
  | .tyBool => some .star
  | .tyArr _ _ => some .star

theorem Judgement.kindOf_eq {i : JudgementIndex Base} (h : Judgement i) :
    match i with
    | .kinded Δ A RK => kindOf Δ A = some RK.kind
    | .hasType .. => True := by
  induction h with
  | base => simp [kindOf]
  | tyVar h => simp [kindOf, h]
  | tyLam _ ih => simp [kindOf, ih]
  | tyApp _ _ ihF _ => simp [kindOf, ihF]
  | tyAll => simp [kindOf]
  | tyBool => simp [kindOf]
  | tyArr => simp [kindOf]
  | subsume _ _ ih => exact ih
  | tmVar | tmApp | tmLam | tmTyApp | tmTyLam | tmBool | tmEq | tmEps => trivial

theorem Kinded.kindOf_eq {RK : RKind} (h : Kinded Δ A RK) :
    kindOf Δ A = some RK.kind := Judgement.kindOf_eq h

/-- Kind *shape* is unique.  Exact ranked kinds are intentionally not: for
example `tyBool` has both `star@0` and `star@1`. -/
theorem Kinded.kind_unique {RK₁ RK₂ : RKind}
    (h₁ : Kinded Δ A RK₁) (h₂ : Kinded Δ A RK₂) :
    RK₁.kind = RK₂.kind := by
  have h := h₁.kindOf_eq.symm.trans h₂.kindOf_eq
  exact Option.some.inj h

end Nucleus.HolOmegaSimple

namespace Nucleus.HolOmega

variable {Base : Type u}

/-- Erasing a well-formed HOL-omega type (including a subtype) preserves its
ranked formation derivation.  The `tySub` case becomes exactly its carrier's
induction hypothesis. -/
theorem Judgement.toSimpleKinded {i : JudgementIndex Base} (h : Judgement i) :
    match i with
    | .kinded Δ A RK => HolOmegaSimple.Kinded Δ (Ty.toSimple A) RK
    | .hasType .. => True := by
  induction h with
  | base => simpa [Ty.toSimple] using (HolOmegaSimple.Judgement.base (Base := Base))
  | tyVar h => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.tyVar h
  | tyLam _ ih => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.tyLam ih
  | tyApp _ _ ihF ihX => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.tyApp ihF ihX
  | tyAll _ ih => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.tyAll ih
  | tyBool => simpa [Ty.toSimple] using (HolOmegaSimple.Judgement.tyBool (Base := Base))
  | tyArr _ _ ihA ihB => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.tyArr ihA ihB
  | tySub _ _ ihA _ => simpa [Ty.toSimple] using ihA
  | subsume _ hrs ih => simpa [Ty.toSimple] using HolOmegaSimple.Judgement.subsume ih hrs
  | conv => trivial
  | tmVar | tmApp | tmLam | tmTyApp | tmTyLam | tmBool | tmEq | tmEps | tmAbs | tmRep => trivial

theorem Kinded.toSimple {RK : RKind} (h : Kinded Δ A RK) :
    HolOmegaSimple.Kinded Δ (Ty.toSimple A) RK := Judgement.toSimpleKinded h

end Nucleus.HolOmega
