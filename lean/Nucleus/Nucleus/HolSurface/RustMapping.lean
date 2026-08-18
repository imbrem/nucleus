import Nucleus.HolE.EmptySyntax
import Nucleus.HolSurface

/-!
# Audited Rust-to-Lean HolE type-former map

Each constructor of Rust's v0 `Expr` has exactly one case below.  References
are resolved and checked by the later LCF pass; this file records which raw
`HolE Empty` constructor that pass must construct.
-/

namespace Nucleus.HolSurface.RustMapping

inductive CoreTypeFormer where
  | kindStar | kindArr
  | boolTy | arr | app | lam | bv | sub | model
  deriving DecidableEq

def typeFormer : Expr → CoreTypeFormer
  | .kindStar => .kindStar
  | .kindArr .. => .kindArr
  | .tyBool => .boolTy
  | .tyArr .. => .arr
  | .tyApp .. => .app
  | .tyLam .. => .lam
  | .tyBv .. => .bv
  | .tySub .. => .sub
  | .tyModel .. => .model

theorem typeFormer_surjective : Function.Surjective typeFormer := by
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
  · exact ⟨.tyModel ⟨1, by decide, by decide⟩, rfl⟩

end Nucleus.HolSurface.RustMapping
