/-
SPDX-FileCopyrightText: 2026 Nucleus contributors
SPDX-License-Identifier: CC0-1.0
-/

import Nucleus.HolOmega.Syntax

/-!
# Formation and typing

Type formation and term typing as a **single** inductive relation indexed by
`JudgementIndex`, for the same reason the syntax is a single family: one
ordinary induction principle, so `induction` works and proofs are not forced
through a hand-written recursor with one motive per judgement.

The rules are syntax-directed. Each constructor checks only its immediate
children and the indicated context lookup, so there is no global
well-formedness pass hidden anywhere, and a derivation can be checked — later,
addressed — a node at a time.

`Kinded` and `HasType` survive as abbreviations, so the two judgements still
read as separate notions where that is clearer.
-/

universe u

namespace Nucleus.HolOmega

/-- A common index for the formation and typing judgements. -/
inductive JudgementIndex (Base : Type u) : Type u
  | kinded (Δ : KindCtx) (A : Ty Base) (K : Kind)
  | hasType (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base) (A : Ty Base)

/-- `Δ ⊢ A : K` and `Δ; Γ ⊢ t : A`, as one relation. -/
inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | base : Judgement (.kinded Δ (.base A) .star)
  | tyVar : Δ[n]? = some K → Judgement (.kinded Δ (.tyVar n) K)
  | tyLam : Judgement (.kinded (K :: Δ) A L) →
      Judgement (.kinded Δ (.tyLam K A) (.arr K L))
  | tyApp : Judgement (.kinded Δ F (.arr K L)) → Judgement (.kinded Δ X K) →
      Judgement (.kinded Δ (.tyApp F X) L)
  | tyBool : Judgement (.kinded Δ .tyBool .star)
  | tyArr : Judgement (.kinded Δ A .star) → Judgement (.kinded Δ B .star) →
      Judgement (.kinded Δ (.tyArr A B) .star)
  | tySub : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ [A] p .tyBool) →
      Judgement (.kinded Δ (.tySub A p) .star)
  | tmVar : Γ[n]? = some A → Judgement (.hasType Δ Γ (.tmVar n) A)
  | tmApp : Judgement (.hasType Δ Γ f (.tyArr A B)) →
      Judgement (.hasType Δ Γ x A) → Judgement (.hasType Δ Γ (.tmApp f x) B)
  | tmLam : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ (A :: Γ) t B) →
      Judgement (.hasType Δ Γ (.tmLam A t) (.tyArr A B))
  | tmTyApp : Judgement (.hasType Δ Γ f (.tyApp F X)) →
      Judgement (.kinded Δ A K) →
      Judgement (.hasType Δ Γ (.tmTyApp f A) (.tyApp F A))
  | tmTyLam : Judgement (.hasType (K :: Δ) Γ t A) →
      Judgement (.hasType Δ Γ (.tmTyLam K t) (.tyLam K A))
  | tmBool : Judgement (.hasType Δ Γ (.tmBool b) .tyBool)
  | tmEq : Judgement (.kinded Δ A .star) → Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ y A) →
      Judgement (.hasType Δ Γ (.tmEq A x y) .tyBool)
  | tmEps : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ Γ p (.tyArr A .tyBool)) →
      Judgement (.hasType Δ Γ (.tmEps A p) A)
  | tmAbs : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ [A] p .tyBool) → Judgement (.hasType Δ Γ x A) →
      Judgement (.hasType Δ Γ (.tmAbs A p x) (.tySub A p))
  | tmRep : Judgement (.kinded Δ A .star) →
      Judgement (.hasType Δ [A] p .tyBool) →
      Judgement (.hasType Δ Γ x (.tySub A p)) →
      Judgement (.hasType Δ Γ (.tmRep A p x) A)

/-- `Δ ⊢ A : K`. -/
abbrev Kinded {Base : Type u} (Δ : KindCtx) (A : Ty Base) (K : Kind) : Prop :=
  Judgement (.kinded Δ A K)

/-- `Δ; Γ ⊢ t : A`. -/
abbrev HasType {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base) (t : Tm Base)
    (A : Ty Base) : Prop :=
  Judgement (.hasType Δ Γ t A)

end Nucleus.HolOmega
