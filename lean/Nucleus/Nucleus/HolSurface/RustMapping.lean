import Nucleus.HolE.EmptySyntax
import Nucleus.HolSurface

/-!
# Audited Rust-to-Lean HolE constructor map

The `core` cases lower one-for-one to `HolE Empty`. Links are the only surface
cases: after resolution and validation they disappear, yielding a closed core
type or term with their recorded annotation.
-/

namespace Nucleus.HolSurface.RustMapping

inductive CoreConstructor where
  | kindStar | kindArr
  | boolTy | arr | tyApp | tyLam | tyBv | sub | tyExists | model
  | bv | fv | app | lam | bool | eq | eps | abs | rep
  deriving DecidableEq

inductive Lowering where
  | core (constructor : CoreConstructor)
  | closedTypeLink
  | closedTermLink
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

theorem lowering_injective : Function.Injective lowering := by
  intro a b h
  cases a <;> cases b <;> simp_all [lowering]

end Nucleus.HolSurface.RustMapping
