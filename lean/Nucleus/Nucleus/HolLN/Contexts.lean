import Nucleus.HolLN.VariantSoundness

/-!
# Serializable bound-variable contexts

Free variables carry their syntactic types directly, so there is no separate
free-variable context. Bound contexts remain finite serializable syntax.
-/

namespace Nucleus.HolLN

universe u v

variable {Base : Type u} {depth : Nat}

inductive Tree.Context.Bound (Expr : Type v) : Nat → Type v where
  | empty : Tree.Context.Bound Expr 0
  | extend {depth : Nat} (type : Expr) (tail : Tree.Context.Bound Expr depth) :
      Tree.Context.Bound Expr (depth + 1)
  deriving Repr

namespace Tree.Context.Bound

def map (f : α → β) : {depth : Nat} → Tree.Context.Bound α depth → Tree.Context.Bound β depth
  | _, .empty => .empty
  | _, .extend A tail => .extend (f A) (map f tail)

def traverse (f : α → Option β) : {depth : Nat} →
    Tree.Context.Bound α depth → Option (Tree.Context.Bound β depth)
  | _, .empty => some .empty
  | _, .extend A tail => return .extend (← f A) (← traverse f tail)

def denote : {depth : Nat} → Tree.Context.Bound (Ty Base) depth → BoundCtx Base depth
  | _, .empty => emptyBound
  | _, .extend A tail => extendBound A tail.denote

@[simp] theorem traverse_map (f : α → β) (g : β → Option α)
    (inverse : ∀ x, g (f x) = some x) (ctx : Tree.Context.Bound α depth) :
    traverse g (map f ctx) = some ctx := by
  induction ctx <;> simp_all [map, traverse]

end Tree.Context.Bound

abbrev OriginalBoundContext (Base : Type u) (depth : Nat) :=
  Tree.Context.Bound (Ty Base) depth

namespace Tree.Sorted

abbrev BoundContext (Base : Type u) (depth : Nat) :=
  Tree.Context.Bound (Tree.Sorted Base .ty) depth

def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkDepth .ty 0)

def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth :=
  Γ.map Erasure.toSorted

@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ :=
  Tree.Context.Bound.traverse_map _ _ Erasure.checkDepth_toSorted Γ

def HasTypeIn (Γ : BoundContext Base depth) (t : Tree.Sorted Base .tm)
    (A : Tree.Sorted Base .ty) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ HasType Γ₀.denote t A

def EqTmIn (Γ : BoundContext Base depth) (t u : Tree.Sorted Base .tm)
    (A : Tree.Sorted Base .ty) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ EqTm Γ₀.denote t u A

def ProvesIn (Γ : BoundContext Base depth) (H : List (Tree.Sorted Base .tm))
    (p : Tree.Sorted Base .tm) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ Proves Γ₀.denote H p

end Tree.Sorted

namespace Tree.Scoped

abbrev BoundContext (Base : Type u) (depth : Nat) :=
  Tree.Context.Bound (Tree.Scoped Base 0) depth

def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkSort .ty)

def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth :=
  Γ.map Erasure.toScoped

@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ :=
  Tree.Context.Bound.traverse_map _ _ Erasure.checkSort_toScoped Γ

def HasTypeIn (Γ : BoundContext Base depth) (t : Tree.Scoped Base depth)
    (A : Tree.Scoped Base 0) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ HasType Γ₀.denote t A

def EqTmIn (Γ : BoundContext Base depth) (t u : Tree.Scoped Base depth)
    (A : Tree.Scoped Base 0) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ EqTm Γ₀.denote t u A

def ProvesIn (Γ : BoundContext Base depth) (H : List (Tree.Scoped Base depth))
    (p : Tree.Scoped Base depth) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ Proves Γ₀.denote H p

end Tree.Scoped

namespace Tree.Raw

abbrev BoundContext (Base : Type u) (depth : Nat) :=
  Tree.Context.Bound (Tree.Raw Base) depth

def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkRaw .ty 0)

def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth :=
  Γ.map Erasure.toRaw

@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ :=
  Tree.Context.Bound.traverse_map _ _ Erasure.checkRaw_toRaw Γ

def HasTypeIn (Γ : BoundContext Base depth) (t A : Tree.Raw Base) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ HasType Γ₀.denote t A

def EqTmIn (Γ : BoundContext Base depth) (t u A : Tree.Raw Base) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ EqTm Γ₀.denote t u A

def ProvesIn (Γ : BoundContext Base depth) (H : List (Tree.Raw Base))
    (p : Tree.Raw Base) : Prop :=
  ∃ Γ₀, decodeBound Γ = some Γ₀ ∧ Proves Γ₀.denote H p

def fuseBound : {depth : Nat} → BoundContext Base depth → Tree.Raw Base
  | _, .empty => .emptyCtx
  | _, .extend A tail => .boundCtx A (fuseBound tail)

def checkBound : (depth : Nat) → Tree.Raw Base → Option (BoundContext Base depth)
  | 0, .emptyCtx => some .empty
  | d + 1, .boundCtx A tail => return .extend A (← checkBound d tail)
  | _, _ => none

@[simp] theorem checkBound_fuseBound (Γ : BoundContext Base depth) :
    checkBound depth (fuseBound Γ) = some Γ := by
  induction Γ <;> simp_all [fuseBound, checkBound]

def HasTypeFused (Γ : Tree.Raw Base) (depth : Nat) (t A : Tree.Raw Base) : Prop :=
  ∃ Γ₀, checkBound depth Γ = some Γ₀ ∧ HasTypeIn Γ₀ t A

def EqTmFused (Γ : Tree.Raw Base) (depth : Nat) (t u A : Tree.Raw Base) : Prop :=
  ∃ Γ₀, checkBound depth Γ = some Γ₀ ∧ EqTmIn Γ₀ t u A

def ProvesFused (Γ : Tree.Raw Base) (depth : Nat) (H : List (Tree.Raw Base))
    (p : Tree.Raw Base) : Prop :=
  ∃ Γ₀, checkBound depth Γ = some Γ₀ ∧ ProvesIn Γ₀ H p

end Tree.Raw

namespace Tree.Context.Json

def encodeBoundSorted (Γ : Tree.Sorted.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound (Γ.map Erasure.sortedToRaw))

def encodeBoundScoped (Γ : Tree.Scoped.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound (Γ.map Erasure.scopedToRaw))

def encodeBoundRaw (Γ : Tree.Raw.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound Γ)

end Tree.Context.Json

end Nucleus.HolLN
