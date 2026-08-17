import Nucleus.HolE.EmptySyntax
import Nucleus.HolSurface

/-!
# Audited Rust-to-Lean HolE constructor map

The `core` cases lower one-for-one to `HolE Empty`. Links and casts are surface
cases. After resolution and validation, links yield a closed core type or term.
A cast lowers to its operand when conversion succeeds and to an arbitrary
inhabitant of its target type otherwise.
-/

namespace Nucleus.HolSurface.RustMapping

open Nucleus.HolE.Empty

inductive CoreConstructor where
  | kindStar | kindArr
  | boolTy | arr | tyApp | tyLam | tyBv | sub | tyExists | model
  | bv | fv | app | lam | bool | eq | eps | abs | rep
  deriving DecidableEq

inductive Lowering where
  | core (constructor : CoreConstructor)
  | closedTypeLink
  | closedTermLink
  | typeCast
  deriving DecidableEq

def lowering : Tag → Lowering
  | .kindStar => .core .kindStar
  | .kindArr => .core .kindArr
  | .tyBool => .core .boolTy
  | .tyArr => .core .arr
  | .tyApp => .core .tyApp
  | .tyLam => .core .tyLam
  | .tyBv => .core .tyBv
  | .tySub => .core .sub
  | .tyExists => .core .tyExists
  | .tyModel => .core .model
  | .tyLink => .closedTypeLink
  | .tmBv => .core .bv
  | .tmFv => .core .fv
  | .tmApp => .core .app
  | .tmLam => .core .lam
  | .tmBool => .core .bool
  | .tmEq => .core .eq
  | .tmEps => .core .eps
  | .tmAbs => .core .abs
  | .tmRep => .core .rep
  | .tmLink => .closedTermLink
  | .tmCast => .typeCast

theorem lowering_injective : Function.Injective lowering := by
  intro a b h
  cases a <;> cases b <;> simp_all [lowering]

/-- The checked Lean implementation of the `TM_CAST` lowering contract. -/
noncomputable abbrev lowerCast {types : List Nucleus.Hol.Kind} {depth : Nat}
    {Γ : Nucleus.HolE.Empty.Ctx types depth} {A : Nucleus.HolE.Empty.Ty types}
    (term : Nucleus.HolE.Empty.Term Γ A) (target : Nucleus.HolE.Empty.Ty types) :
    Nucleus.HolE.Empty.Term Γ target :=
  Term.cast term target

theorem lowerCast_wellTyped {types : List Nucleus.Hol.Kind} {depth : Nat}
    {Γ : Nucleus.HolE.Empty.Ctx types depth} {A : Nucleus.HolE.Empty.Ty types}
    (term : Nucleus.HolE.Empty.Term Γ A) (target : Nucleus.HolE.Empty.Ty types) :
    Nucleus.HolE.HasType Γ.raw (lowerCast term target).raw target.raw :=
  Term.cast_typing term target

theorem lowerCast_of_typeEquality {types : List Nucleus.Hol.Kind} {depth : Nat}
    {Γ : Nucleus.HolE.Empty.Ctx types depth} {A : Nucleus.HolE.Empty.Ty types}
    (term : Nucleus.HolE.Empty.Term Γ A) (target : Nucleus.HolE.Empty.Ty types)
    (typeEquality : A.raw = target.raw) :
    (lowerCast term target).raw = term.raw :=
  Term.cast_of_raw_eq term target typeEquality

end Nucleus.HolSurface.RustMapping
