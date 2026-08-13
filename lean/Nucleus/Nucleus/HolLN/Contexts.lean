import Nucleus.HolLN.VariantSoundness

/-!
# Serializable context presentations

Contexts are finite syntax rather than functions.  `FreeContext` and
`BoundContext` can hold any of the four expression representations.  At the
fully erased corner, the same `Unindexed` inductive also has context nodes;
strict checkers recognize those nodes and reject mixed trees.
-/

namespace Nucleus.HolLN

universe u v

set_option linter.style.longLine false

variable {Base : Type u} {depth : Nat}

inductive FreeContext (Expr : Type v) where
  | empty
  | extend (name : Nat) (type : Expr) (tail : FreeContext Expr)
  deriving Repr

inductive BoundContext (Expr : Type v) : Nat → Type v where
  | empty : BoundContext Expr 0
  | extend {depth : Nat} (type : Expr) (tail : BoundContext Expr depth) :
      BoundContext Expr (depth + 1)
  deriving Repr

namespace FreeContext

def map (f : α → β) : FreeContext α → FreeContext β
  | .empty => .empty
  | .extend name A tail => .extend name (f A) (map f tail)

def traverse (f : α → Option β) : FreeContext α → Option (FreeContext β)
  | .empty => some .empty
  | .extend name A tail => return .extend name (← f A) (← traverse f tail)

def denote : FreeContext (Ty Base) → FreeCtx Base
  | .empty => emptyContext
  | .extend name A tail => extendFree tail.denote name A

@[simp] theorem traverse_map (f : α → β) (g : β → Option α)
    (inverse : ∀ x, g (f x) = some x) (ctx : FreeContext α) :
    traverse g (map f ctx) = some ctx := by
  induction ctx <;> simp_all [map, traverse]

end FreeContext

namespace BoundContext

def map (f : α → β) : {depth : Nat} → BoundContext α depth → BoundContext β depth
  | _, .empty => .empty
  | _, .extend A tail => .extend (f A) (map f tail)

def traverse (f : α → Option β) : {depth : Nat} →
    BoundContext α depth → Option (BoundContext β depth)
  | _, .empty => some .empty
  | _, .extend A tail => return .extend (← f A) (← traverse f tail)

def denote : {depth : Nat} → BoundContext (Ty Base) depth → BoundCtx Base depth
  | _, .empty => emptyBound
  | _, .extend A tail => extendBound A tail.denote

@[simp] theorem traverse_map (f : α → β) (g : β → Option α)
    (inverse : ∀ x, g (f x) = some x) (ctx : BoundContext α depth) :
    traverse g (map f ctx) = some ctx := by
  induction ctx <;> simp_all [map, traverse]

end BoundContext

abbrev OriginalFreeContext (Base : Type u) := FreeContext (Ty Base)
abbrev OriginalBoundContext (Base : Type u) (depth : Nat) := BoundContext (Ty Base) depth

namespace NoDepth

abbrev FreeCtxS (Base : Type u) := FreeContext (NoDepth Base .ty)
abbrev BoundCtxS (Base : Type u) (depth : Nat) := BoundContext (NoDepth Base .ty) depth

def decodeFree (Δ : FreeCtxS Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkDepth .ty 0)
def decodeBound (Γ : BoundCtxS Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkDepth .ty 0)

def encodeFree (Δ : OriginalFreeContext Base) : FreeCtxS Base := Δ.map Erasure.noDepth
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundCtxS Base depth := Γ.map Erasure.noDepth

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := FreeContext.traverse_map _ _ Erasure.checkDepth_noDepth Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := BoundContext.traverse_map _ _ Erasure.checkDepth_noDepth Γ

def HasTypeIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t : NoDepth Base .tm) (A : NoDepth Base .ty) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t u : NoDepth Base .tm) (A : NoDepth Base .ty) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (H : List (NoDepth Base .tm)) (p : NoDepth Base .tm) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.noDepth t₀ = t ∧ Erasure.noDepth u₀ = u ∧ Erasure.noDepth A₀ = A ∧
        ∀ (freeEnv : FreeEnv Δ₀.denote) (boundEnv : BoundEnv Γ₀.denote)
            {left right : DenoteTy A₀},
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv t₀ A₀ left →
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, equality⟩
  rcases equality.sound with ⟨t₀, u₀, A₀, proof, ht, hu, hA, sound⟩
  exact ⟨Δ₀, Γ₀, hΔ, hΓ, t₀, u₀, A₀, proof, ht, hu, hA, sound⟩

theorem ProvesIn.sound (h : ProvesIn Δ Γ H p) :
    ∃ Δ₀ Γ₀ H₀ p₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      Nonempty (Nucleus.HolLN.Proves Δ₀.denote Γ₀.denote H₀ p₀) ∧
      H₀.map Erasure.noDepth = H ∧ Erasure.noDepth p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeCtxS Base) (.empty : BoundCtxS Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

end NoDepth

namespace NoSort

abbrev FreeCtxS (Base : Type u) := FreeContext (NoSort Base 0)
abbrev BoundCtxS (Base : Type u) (depth : Nat) := BoundContext (NoSort Base 0) depth

def decodeFree (Δ : FreeCtxS Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkSort .ty)
def decodeBound (Γ : BoundCtxS Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkSort .ty)

def encodeFree (Δ : OriginalFreeContext Base) : FreeCtxS Base := Δ.map Erasure.noSort
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundCtxS Base depth := Γ.map Erasure.noSort

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := FreeContext.traverse_map _ _ Erasure.checkSort_noSort Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := BoundContext.traverse_map _ _ Erasure.checkSort_noSort Γ

def HasTypeIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t : NoSort Base depth) (A : NoSort Base 0) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t u : NoSort Base depth) (A : NoSort Base 0) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (H : List (NoSort Base depth)) (p : NoSort Base depth) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.noSort t₀ = t ∧ Erasure.noSort u₀ = u ∧ Erasure.noSort A₀ = A ∧
        ∀ (freeEnv : FreeEnv Δ₀.denote) (boundEnv : BoundEnv Γ₀.denote)
            {left right : DenoteTy A₀},
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv t₀ A₀ left →
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, equality⟩
  rcases equality.sound with ⟨t₀, u₀, A₀, proof, ht, hu, hA, sound⟩
  exact ⟨Δ₀, Γ₀, hΔ, hΓ, t₀, u₀, A₀, proof, ht, hu, hA, sound⟩

theorem ProvesIn.sound (h : ProvesIn Δ Γ H p) :
    ∃ Δ₀ Γ₀ H₀ p₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      Nonempty (Nucleus.HolLN.Proves Δ₀.denote Γ₀.denote H₀ p₀) ∧
      H₀.map Erasure.noSort = H ∧ Erasure.noSort p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeCtxS Base) (.empty : BoundCtxS Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

end NoSort

namespace Unindexed

abbrev FreeCtxS (Base : Type u) := FreeContext (Unindexed Base)
abbrev BoundCtxS (Base : Type u) (depth : Nat) := BoundContext (Unindexed Base) depth

def decodeFree (Δ : FreeCtxS Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkUnindexed .ty 0)
def decodeBound (Γ : BoundCtxS Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkUnindexed .ty 0)

def encodeFree (Δ : OriginalFreeContext Base) : FreeCtxS Base := Δ.map Erasure.unindexed
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundCtxS Base depth := Γ.map Erasure.unindexed

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := FreeContext.traverse_map _ _ Erasure.checkUnindexed_unindexed Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := BoundContext.traverse_map _ _ Erasure.checkUnindexed_unindexed Γ

def HasTypeIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t A : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (t u A : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeCtxS Base) (Γ : BoundCtxS Base depth)
    (H : List (Unindexed Base)) (p : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.unindexed t₀ = t ∧ Erasure.unindexed u₀ = u ∧ Erasure.unindexed A₀ = A ∧
        ∀ (freeEnv : FreeEnv Δ₀.denote) (boundEnv : BoundEnv Γ₀.denote)
            {left right : DenoteTy A₀},
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv t₀ A₀ left →
          Eval Δ₀.denote Γ₀.denote freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, equality⟩
  rcases equality.sound with ⟨t₀, u₀, A₀, proof, ht, hu, hA, sound⟩
  exact ⟨Δ₀, Γ₀, hΔ, hΓ, t₀, u₀, A₀, proof, ht, hu, hA, sound⟩

theorem ProvesIn.sound (h : ProvesIn Δ Γ H p) :
    ∃ Δ₀ Γ₀ H₀ p₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      Nonempty (Nucleus.HolLN.Proves Δ₀.denote Γ₀.denote H₀ p₀) ∧
      H₀.map Erasure.unindexed = H ∧ Erasure.unindexed p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeCtxS Base) (.empty : BoundCtxS Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

/-! The fused representation uses `Unindexed` itself for contexts. -/
def fuseFree : FreeCtxS Base → Unindexed Base
  | .empty => .emptyCtx
  | .extend name A tail => .freeCtx name A (fuseFree tail)

def fuseBound : {depth : Nat} → BoundCtxS Base depth → Unindexed Base
  | _, .empty => .emptyCtx
  | _, .extend A tail => .boundCtx A (fuseBound tail)

def checkFree : Unindexed Base → Option (FreeCtxS Base)
  | .emptyCtx => some .empty
  | .freeCtx name A tail => return .extend name A (← checkFree tail)
  | _ => none

def checkBound : (depth : Nat) → Unindexed Base → Option (BoundCtxS Base depth)
  | 0, .emptyCtx => some .empty
  | d + 1, .boundCtx A tail => return .extend A (← checkBound d tail)
  | _, _ => none

@[simp] theorem checkFree_fuseFree (Δ : FreeCtxS Base) : checkFree (fuseFree Δ) = some Δ := by
  induction Δ <;> simp_all [fuseFree, checkFree]

@[simp] theorem checkBound_fuseBound (Γ : BoundCtxS Base depth) :
    checkBound depth (fuseBound Γ) = some Γ := by
  induction Γ <;> simp_all [fuseBound, checkBound]

def HasTypeFused (Δ Γ : Unindexed Base) (depth : Nat) (t A : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    HasTypeIn Δ₀ Γ₀ t A

def EqTmFused (Δ Γ : Unindexed Base) (depth : Nat) (t u A : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    EqTmIn Δ₀ Γ₀ t u A

def ProvesFused (Δ Γ : Unindexed Base) (depth : Nat)
    (H : List (Unindexed Base)) (p : Unindexed Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    ProvesIn Δ₀ Γ₀ H p

theorem EqTmFused.sound (h : EqTmFused Δ Γ depth t u A) :
    ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
      EqTmIn Δ₀ Γ₀ t u A := h

theorem ProvesFused.sound (h : ProvesFused Δ Γ depth H p) :
    ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
      ProvesIn Δ₀ Γ₀ H p := h

theorem fused_empty_not_proves_false :
    ¬ ProvesFused (.emptyCtx : Unindexed Base) .emptyCtx 0 [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false_in proof

end Unindexed

/-! Context serialization uses the fused representation, so context nodes and
expression nodes share exactly one JSON carrier and vocabulary. -/
namespace ContextJson

def encodeFreeNoDepth (Δ : NoDepth.FreeCtxS Base) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseFree (Δ.map Erasure.noDepthToUnindexed))
def encodeBoundNoDepth (Γ : NoDepth.BoundCtxS Base depth) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseBound (Γ.map Erasure.noDepthToUnindexed))

def encodeFreeNoSort (Δ : NoSort.FreeCtxS Base) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseFree (Δ.map Erasure.noSortToUnindexed))
def encodeBoundNoSort (Γ : NoSort.BoundCtxS Base depth) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseBound (Γ.map Erasure.noSortToUnindexed))

def encodeFreeUnindexed (Δ : Unindexed.FreeCtxS Base) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseFree Δ)
def encodeBoundUnindexed (Γ : Unindexed.BoundCtxS Base depth) : Json.Tree Base :=
  VariantJson.encode (Unindexed.fuseBound Γ)

@[simp] theorem encodeFree_embeddings_agree (Δ : OriginalFreeContext Base) :
    encodeFreeNoDepth (NoDepth.encodeFree Δ) = encodeFreeNoSort (NoSort.encodeFree Δ) := by
  induction Δ <;> simp_all [encodeFreeNoDepth, encodeFreeNoSort, NoDepth.encodeFree,
    NoSort.encodeFree, FreeContext.map, Unindexed.fuseFree, Erasure.square,
    VariantJson.encode]

@[simp] theorem encodeBound_embeddings_agree (Γ : OriginalBoundContext Base depth) :
    encodeBoundNoDepth (NoDepth.encodeBound Γ) = encodeBoundNoSort (NoSort.encodeBound Γ) := by
  induction Γ <;> simp_all [encodeBoundNoDepth, encodeBoundNoSort, NoDepth.encodeBound,
    NoSort.encodeBound, BoundContext.map, Unindexed.fuseBound, Erasure.square,
    VariantJson.encode]

end ContextJson

end Nucleus.HolLN
