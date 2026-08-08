import Nucleus.Hol.Syntax
import Nucleus.HolOmega.Typing

/-! Syntax-directed formation and typing for ordinary HOL. -/

universe u

namespace Nucleus.Hol

inductive JudgementIndex (Base : Type u) where
  | kinded (A : Ty Base)
  | hasType (Γ : Ctx Base) (t : Tm Base) (A : Ty Base)

inductive Judgement {Base : Type u} : JudgementIndex Base → Prop
  | base : Judgement (.kinded (.base c))
  | tyBool : Judgement (.kinded .tyBool)
  | tyArr : Judgement (.kinded A) → Judgement (.kinded B) →
      Judgement (.kinded (.tyArr A B))
  | tySub : Judgement (.kinded A) → Judgement (.hasType [A] p .tyBool) →
      Judgement (.kinded (.tySub A p))
  | tmVar : Γ[n]? = some A → Judgement (.hasType Γ (.tmVar n) A)
  | tmApp : Judgement (.hasType Γ f (.tyArr A B)) → Judgement (.hasType Γ x A) →
      Judgement (.hasType Γ (.tmApp f x) B)
  | tmLam : Judgement (.kinded A) → Judgement (.hasType (A :: Γ) t B) →
      Judgement (.hasType Γ (.tmLam A t) (.tyArr A B))
  | tmBool : Judgement (.hasType Γ (.tmBool b) .tyBool)
  | tmEq : Judgement (.kinded A) → Judgement (.hasType Γ x A) →
      Judgement (.hasType Γ y A) → Judgement (.hasType Γ (.tmEq A x y) .tyBool)
  | tmEps : Judgement (.kinded A) → Judgement (.hasType Γ p (.tyArr A .tyBool)) →
      Judgement (.hasType Γ (.tmEps A p) A)
  | tmAbs : Judgement (.kinded A) → Judgement (.hasType [A] p .tyBool) →
      Judgement (.hasType Γ x A) → Judgement (.hasType Γ (.tmAbs A p x) (.tySub A p))
  | tmRep : Judgement (.kinded A) → Judgement (.hasType [A] p .tyBool) →
      Judgement (.hasType Γ x (.tySub A p)) → Judgement (.hasType Γ (.tmRep A p x) A)

variable {Base : Type u} {i : JudgementIndex Base}

abbrev Kinded (A : Ty Base) := @Judgement Base (.kinded A)
abbrev HasType (Γ : Ctx Base) (t : Tm Base) (A : Ty Base) :=
  @Judgement Base (.hasType Γ t A)

def Ctx.toOmega (Γ : Ctx Base) : HolOmega.TmCtx Base := Γ.map Expr.toOmega

@[simp] theorem Ctx.toOmega_cons : Ctx.toOmega (A :: Γ) = A.toOmega :: Ctx.toOmega Γ := rfl

/-- The ordinary type checker is literally a subsystem of the HOL-omega one,
at empty kind context and rank zero. -/
theorem Judgement.toOmega :
    (h : @Judgement Base i) → match i with
      | .kinded A => HolOmega.Kinded [] A.toOmega ⟨HolOmega.Kind.star, 0⟩
      | .hasType Γ t A => HolOmega.HasType [] Γ.toOmega t.toOmega A.toOmega := by
  intro h
  induction h with
  | base => exact .base
  | tyBool => exact .tyBool
  | tyArr _ _ ihA ihB => exact .tyArr ihA ihB
  | tySub _ _ ihA ihp => exact .tySub ihA ihp
  | tmVar h => exact .tmVar (by simp [Ctx.toOmega, h])
  | tmApp _ _ ihf ihx => exact .tmApp ihf ihx
  | tmLam _ _ ihA iht => exact .tmLam ihA iht
  | tmBool => exact .tmBool
  | tmEq _ _ _ ihA ihx ihy => exact .tmEq ihA ihx ihy
  | tmEps _ _ ihA ihp => exact .tmEps ihA ihp
  | tmAbs _ _ _ ihA ihp ihx => exact .tmAbs ihA ihp ihx
  | tmRep _ _ _ ihA ihp ihx => exact .tmRep ihA ihp ihx

end Nucleus.Hol
