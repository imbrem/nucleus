import Nucleus.HolE.EmptySyntax
import Nucleus.HolSurface

/-!
# Audited Rust-to-Lean HolE constructor map

Each core constructor of Rust's v0 `Expr` has exactly one case below.
References, binder kinds, and finite de Bruijn indices are resolved and
checked by the later LCF pass; this file records which raw `HolE Empty`
constructor that pass must construct. In particular, the pass infers `tmEq`'s
shared operand type from its two children. `tmCast` lowers through
`HolE.Empty.Term.cast`, since it is deliberately a total surface operation
rather than a raw `HolE.Expr` constructor.
-/

namespace Nucleus.HolSurface.RustMapping

inductive CoreFormer where
  | kindStar | kindArr
  | boolTy | arr | tyApp | tyLam | tyBv | sub | tyExists | model
  | tmBv | tmFv | tmApp | tmLam | tmBool | eq | eps | abs | rep | cast | nat
  deriving DecidableEq

def coreFormer : Expr → CoreFormer
  | .kindStar => .kindStar
  | .kindArr .. => .kindArr
  | .tyBool => .boolTy
  | .tyArr .. => .arr
  | .tyApp .. => .tyApp
  | .tyLam .. => .tyLam
  | .tyBv .. => .tyBv
  | .tySub .. => .sub
  | .tyExists .. => .tyExists
  | .tyModel .. => .model
  | .tmBv .. => .tmBv
  | .tmFv .. => .tmFv
  | .tmApp .. => .tmApp
  | .tmLam .. => .tmLam
  | .tmBool .. => .tmBool
  | .tmEq .. => .eq
  | .tmEps .. => .eps
  | .tmAbs .. => .abs
  | .tmRep .. => .rep
  | .tmCast .. => .cast
  | .tmNat .. => .nat

theorem coreFormer_surjective : Function.Surjective coreFormer := by
  intro former
  cases former
  · exact ⟨.kindStar, rfl⟩
  · exact ⟨.kindArr ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyBool, rfl⟩
  · exact ⟨.tyArr ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyApp ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyLam ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyBv 0, rfl⟩
  · exact ⟨.tySub ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyExists ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tyModel ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmBv 0, rfl⟩
  · exact ⟨.tmFv 0 ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmApp ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmLam ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmBool false, rfl⟩
  · exact ⟨.tmEq ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmEps ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmAbs ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩
      ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmRep ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩
      ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmCast ⟨1, by decide, by decide⟩ ⟨1, by decide, by decide⟩, rfl⟩
  · exact ⟨.tmNat 0, rfl⟩

end Nucleus.HolSurface.RustMapping
