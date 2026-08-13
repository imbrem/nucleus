import Nucleus.HolLN.VariantSoundness

/-!
# Serializable context presentations

Contexts are finite syntax rather than functions.  `Tree.Context.Free` and
`Tree.Context.Bound` can hold any of the four expression representations.  At the
fully erased corner, the same `Tree.Raw` inductive also has context nodes;
strict checkers recognize those nodes and reject mixed trees.
-/

namespace Nucleus.HolLN

universe u v

set_option linter.style.longLine false

variable {Base : Type u} {depth : Nat}

inductive Tree.Context.Free (Expr : Type v) where
  | empty
  | extend (name : Nat) (type : Expr) (tail : Tree.Context.Free Expr)
  deriving Repr

inductive Tree.Context.Bound (Expr : Type v) : Nat → Type v where
  | empty : Tree.Context.Bound Expr 0
  | extend {depth : Nat} (type : Expr) (tail : Tree.Context.Bound Expr depth) :
      Tree.Context.Bound Expr (depth + 1)
  deriving Repr

namespace Tree.Context.Free

def map (f : α → β) : Tree.Context.Free α → Tree.Context.Free β
  | .empty => .empty
  | .extend name A tail => .extend name (f A) (map f tail)

def traverse (f : α → Option β) : Tree.Context.Free α → Option (Tree.Context.Free β)
  | .empty => some .empty
  | .extend name A tail => return .extend name (← f A) (← traverse f tail)

def denote : Tree.Context.Free (Ty Base) → FreeCtx Base
  | .empty => emptyContext
  | .extend name A tail => extendFree tail.denote name A

@[simp] theorem traverse_map (f : α → β) (g : β → Option α)
    (inverse : ∀ x, g (f x) = some x) (ctx : Tree.Context.Free α) :
    traverse g (map f ctx) = some ctx := by
  induction ctx <;> simp_all [map, traverse]

end Tree.Context.Free

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

abbrev OriginalFreeContext (Base : Type u) := Tree.Context.Free (Ty Base)
abbrev OriginalBoundContext (Base : Type u) (depth : Nat) := Tree.Context.Bound (Ty Base) depth

namespace Tree.Sorted

abbrev FreeContext (Base : Type u) := Tree.Context.Free (Tree.Sorted Base .ty)
abbrev BoundContext (Base : Type u) (depth : Nat) := Tree.Context.Bound (Tree.Sorted Base .ty) depth

def decodeFree (Δ : FreeContext Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkDepth .ty 0)
def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkDepth .ty 0)

def encodeFree (Δ : OriginalFreeContext Base) : FreeContext Base := Δ.map Erasure.toSorted
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth := Γ.map Erasure.toSorted

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := Tree.Context.Free.traverse_map _ _ Erasure.checkDepth_toSorted Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := Tree.Context.Bound.traverse_map _ _ Erasure.checkDepth_toSorted Γ

def HasTypeIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t : Tree.Sorted Base .tm) (A : Tree.Sorted Base .ty) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t u : Tree.Sorted Base .tm) (A : Tree.Sorted Base .ty) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (H : List (Tree.Sorted Base .tm)) (p : Tree.Sorted Base .tm) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem HasTypeIn.sound (h : HasTypeIn Δ Γ t A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      HasType Δ₀.denote Γ₀.denote t A := h

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.toSorted t₀ = t ∧ Erasure.toSorted u₀ = u ∧ Erasure.toSorted A₀ = A ∧
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
      H₀.map Erasure.toSorted = H ∧ Erasure.toSorted p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeContext Base) (.empty : BoundContext Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

end Tree.Sorted

namespace Tree.Scoped

abbrev FreeContext (Base : Type u) := Tree.Context.Free (Tree.Scoped Base 0)
abbrev BoundContext (Base : Type u) (depth : Nat) := Tree.Context.Bound (Tree.Scoped Base 0) depth

def decodeFree (Δ : FreeContext Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkSort .ty)
def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkSort .ty)

def encodeFree (Δ : OriginalFreeContext Base) : FreeContext Base := Δ.map Erasure.toScoped
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth := Γ.map Erasure.toScoped

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := Tree.Context.Free.traverse_map _ _ Erasure.checkSort_toScoped Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := Tree.Context.Bound.traverse_map _ _ Erasure.checkSort_toScoped Γ

def HasTypeIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t u : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (H : List (Tree.Scoped Base depth)) (p : Tree.Scoped Base depth) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem HasTypeIn.sound (h : HasTypeIn Δ Γ t A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      HasType Δ₀.denote Γ₀.denote t A := h

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.toScoped t₀ = t ∧ Erasure.toScoped u₀ = u ∧ Erasure.toScoped A₀ = A ∧
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
      H₀.map Erasure.toScoped = H ∧ Erasure.toScoped p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeContext Base) (.empty : BoundContext Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

end Tree.Scoped

namespace Tree.Raw

abbrev FreeContext (Base : Type u) := Tree.Context.Free (Tree.Raw Base)
abbrev BoundContext (Base : Type u) (depth : Nat) := Tree.Context.Bound (Tree.Raw Base) depth

def decodeFree (Δ : FreeContext Base) : Option (OriginalFreeContext Base) :=
  Δ.traverse (Erasure.checkRaw .ty 0)
def decodeBound (Γ : BoundContext Base depth) : Option (OriginalBoundContext Base depth) :=
  Γ.traverse (Erasure.checkRaw .ty 0)

def encodeFree (Δ : OriginalFreeContext Base) : FreeContext Base := Δ.map Erasure.toRaw
def encodeBound (Γ : OriginalBoundContext Base depth) : BoundContext Base depth := Γ.map Erasure.toRaw

@[simp] theorem decodeFree_encodeFree (Δ : OriginalFreeContext Base) :
    decodeFree (encodeFree Δ) = some Δ := Tree.Context.Free.traverse_map _ _ Erasure.checkRaw_toRaw Δ
@[simp] theorem decodeBound_encodeBound (Γ : OriginalBoundContext Base depth) :
    decodeBound (encodeBound Γ) = some Γ := Tree.Context.Bound.traverse_map _ _ Erasure.checkRaw_toRaw Γ

def HasTypeIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t A : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    HasType Δ₀.denote Γ₀.denote t A

def EqTmIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (t u A : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    EqTm Δ₀.denote Γ₀.denote t u A

def ProvesIn (Δ : FreeContext Base) (Γ : BoundContext Base depth)
    (H : List (Tree.Raw Base)) (p : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
    Proves Δ₀.denote Γ₀.denote H p

theorem HasTypeIn.sound (h : HasTypeIn Δ Γ t A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      HasType Δ₀.denote Γ₀.denote t A := h

theorem EqTmIn.sound (h : EqTmIn Δ Γ t u A) :
    ∃ Δ₀ Γ₀, decodeFree Δ = some Δ₀ ∧ decodeBound Γ = some Γ₀ ∧
      ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ₀.denote Γ₀.denote t₀ u₀ A₀) ∧
        Erasure.toRaw t₀ = t ∧ Erasure.toRaw u₀ = u ∧ Erasure.toRaw A₀ = A ∧
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
      H₀.map Erasure.toRaw = H ∧ Erasure.toRaw p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ₀.denote) (Γ := Γ₀.denote) H₀ p₀ := by
  rcases h with ⟨Δ₀, Γ₀, hΔ, hΓ, proof⟩
  rcases proof.sound with ⟨H₀, p₀, hp, hH, hP, sound⟩
  exact ⟨Δ₀, Γ₀, H₀, p₀, hΔ, hΓ, hp, hH, hP, sound⟩

theorem empty_not_proves_false_in :
    ¬ ProvesIn (.empty : FreeContext Base) (.empty : BoundContext Base 0) [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false proof

/-! The fused representation uses `Tree.Raw` itself for contexts. -/
def fuseFree : FreeContext Base → Tree.Raw Base
  | .empty => .emptyCtx
  | .extend name A tail => .freeCtx name A (fuseFree tail)

def fuseBound : {depth : Nat} → BoundContext Base depth → Tree.Raw Base
  | _, .empty => .emptyCtx
  | _, .extend A tail => .boundCtx A (fuseBound tail)

def checkFree : Tree.Raw Base → Option (FreeContext Base)
  | .emptyCtx => some .empty
  | .freeCtx name A tail => return .extend name A (← checkFree tail)
  | _ => none

def checkBound : (depth : Nat) → Tree.Raw Base → Option (BoundContext Base depth)
  | 0, .emptyCtx => some .empty
  | d + 1, .boundCtx A tail => return .extend A (← checkBound d tail)
  | _, _ => none

@[simp] theorem checkFree_fuseFree (Δ : FreeContext Base) : checkFree (fuseFree Δ) = some Δ := by
  induction Δ <;> simp_all [fuseFree, checkFree]

@[simp] theorem checkBound_fuseBound (Γ : BoundContext Base depth) :
    checkBound depth (fuseBound Γ) = some Γ := by
  induction Γ <;> simp_all [fuseBound, checkBound]

def HasTypeFused (Δ Γ : Tree.Raw Base) (depth : Nat) (t A : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    HasTypeIn Δ₀ Γ₀ t A

def EqTmFused (Δ Γ : Tree.Raw Base) (depth : Nat) (t u A : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    EqTmIn Δ₀ Γ₀ t u A

def ProvesFused (Δ Γ : Tree.Raw Base) (depth : Nat)
    (H : List (Tree.Raw Base)) (p : Tree.Raw Base) : Prop :=
  ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
    ProvesIn Δ₀ Γ₀ H p

theorem HasTypeFused.sound (h : HasTypeFused Δ Γ depth t A) :
    ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
      HasTypeIn Δ₀ Γ₀ t A := h

theorem EqTmFused.sound (h : EqTmFused Δ Γ depth t u A) :
    ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
      EqTmIn Δ₀ Γ₀ t u A := h

theorem ProvesFused.sound (h : ProvesFused Δ Γ depth H p) :
    ∃ Δ₀ Γ₀, checkFree Δ = some Δ₀ ∧ checkBound depth Γ = some Γ₀ ∧
      ProvesIn Δ₀ Γ₀ H p := h

theorem fused_empty_not_proves_false :
    ¬ ProvesFused (.emptyCtx : Tree.Raw Base) .emptyCtx 0 [] (.bool false) := by
  rintro ⟨Δ, Γ, hΔ, hΓ, proof⟩
  have eΔ : Δ = .empty := Option.some.inj hΔ.symm
  have eΓ : Γ = .empty := Option.some.inj hΓ.symm
  subst Δ; subst Γ
  exact empty_not_proves_false_in proof

end Tree.Raw

/-! Context serialization uses the fused representation, so context nodes and
expression nodes share exactly one JSON carrier and vocabulary. -/
namespace Tree.Json

def encodeFreeSorted (Δ : Tree.Sorted.FreeContext Base) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseFree (Δ.map Erasure.sortedToRaw))
def encodeBoundSorted (Γ : Tree.Sorted.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound (Γ.map Erasure.sortedToRaw))

def encodeFreeScoped (Δ : Tree.Scoped.FreeContext Base) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseFree (Δ.map Erasure.scopedToRaw))
def encodeBoundScoped (Γ : Tree.Scoped.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound (Γ.map Erasure.scopedToRaw))

def encodeFreeRaw (Δ : Tree.Raw.FreeContext Base) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseFree Δ)
def encodeBoundRaw (Γ : Tree.Raw.BoundContext Base depth) : Json.Tree Base :=
  Tree.Json.encode (Tree.Raw.fuseBound Γ)

@[simp] theorem encodeFree_embeddings_agree (Δ : OriginalFreeContext Base) :
    encodeFreeSorted (Tree.Sorted.encodeFree Δ) = encodeFreeScoped (Tree.Scoped.encodeFree Δ) := by
  induction Δ <;> simp_all [encodeFreeSorted, encodeFreeScoped, Tree.Sorted.encodeFree,
    Tree.Scoped.encodeFree, Tree.Context.Free.map, Tree.Raw.fuseFree, Erasure.square,
    Tree.Json.encode]

@[simp] theorem encodeBound_embeddings_agree (Γ : OriginalBoundContext Base depth) :
    encodeBoundSorted (Tree.Sorted.encodeBound Γ) = encodeBoundScoped (Tree.Scoped.encodeBound Γ) := by
  induction Γ <;> simp_all [encodeBoundSorted, encodeBoundScoped, Tree.Sorted.encodeBound,
    Tree.Scoped.encodeBound, Tree.Context.Bound.map, Tree.Raw.fuseBound, Erasure.square,
    Tree.Json.encode]

end Tree.Json

end Nucleus.HolLN
