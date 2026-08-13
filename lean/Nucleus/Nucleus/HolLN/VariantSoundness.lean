import Nucleus.HolLN.Consistency
import Nucleus.HolLN.Variants

/-!
# Soundness and consistency of the erased presentations

Raw trees never contain evidence.  The proof judgments below are the images of
the kernel judgment, and their soundness theorems recover the unique kernel
objects and the original semantic theorem.
-/

namespace Nucleus.HolLN

universe u

set_option linter.style.longLine false

variable {Base : Type u} {depth : Nat}

namespace Tree.Sorted

def Proves (Δ : FreeCtx Base) (Γ : BoundCtx Base depth)
    (H : List (Tree.Sorted Base .tm)) (p : Tree.Sorted Base .tm) : Prop :=
  ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
    H₀.map Erasure.toSorted = H ∧ Erasure.toSorted p₀ = p

theorem HasType.sound (h : HasType Δ Γ t A) :
    ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.toSorted t₀ = t ∧
      Erasure.toSorted A₀ = A ∧ ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ),
        ∃ value : DenoteTy A₀, Eval Δ Γ freeEnv boundEnv t₀ A₀ value := by
  rcases h with ⟨t₀, A₀, typing, rfl, rfl⟩
  exact ⟨t₀, A₀, typing, rfl, rfl, typing.eval_exists⟩

theorem EqTm.sound (h : EqTm Δ Γ t u A) :
    ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
      Erasure.toSorted t₀ = t ∧ Erasure.toSorted u₀ = u ∧ Erasure.toSorted A₀ = A ∧
      ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) {left right : DenoteTy A₀},
        Eval Δ Γ freeEnv boundEnv t₀ A₀ left →
        Eval Δ Γ freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl⟩
  exact ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl, equality.sound⟩

theorem Proves.sound (h : Proves Δ Γ H p) :
    ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
      H₀.map Erasure.toSorted = H ∧ Erasure.toSorted p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ) (Γ := Γ) H₀ p₀ := by
  rcases h with ⟨H₀, p₀, ⟨proof⟩, rfl, rfl⟩
  exact ⟨H₀, p₀, ⟨proof⟩, rfl, rfl, proof.sound⟩

theorem empty_not_proves_false :
    ¬ Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0)
      [] (.bool false) := by
  rintro ⟨H, p, proof, mapped, erased⟩
  have hH : H = [] := List.eq_nil_of_map_eq_nil mapped
  subst H
  have hp : p = (.bool false : ClosedTm Base) :=
    Erasure.toSorted_injective erased
  subst p
  exact Nucleus.HolLN.empty_not_proves_false proof

end Tree.Sorted

namespace Tree.Scoped

def Proves (Δ : FreeCtx Base) (Γ : BoundCtx Base depth)
    (H : List (Tree.Scoped Base depth)) (p : Tree.Scoped Base depth) : Prop :=
  ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
    H₀.map Erasure.toScoped = H ∧ Erasure.toScoped p₀ = p

theorem HasType.sound (h : HasType Δ Γ t A) :
    ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.toScoped t₀ = t ∧
      Erasure.toScoped A₀ = A ∧ ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ),
        ∃ value : DenoteTy A₀, Eval Δ Γ freeEnv boundEnv t₀ A₀ value := by
  rcases h with ⟨t₀, A₀, typing, rfl, rfl⟩
  exact ⟨t₀, A₀, typing, rfl, rfl, typing.eval_exists⟩

theorem EqTm.sound (h : EqTm Δ Γ t u A) :
    ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
      Erasure.toScoped t₀ = t ∧ Erasure.toScoped u₀ = u ∧ Erasure.toScoped A₀ = A ∧
      ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) {left right : DenoteTy A₀},
        Eval Δ Γ freeEnv boundEnv t₀ A₀ left →
        Eval Δ Γ freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl⟩
  exact ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl, equality.sound⟩

theorem Proves.sound (h : Proves Δ Γ H p) :
    ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
      H₀.map Erasure.toScoped = H ∧ Erasure.toScoped p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ) (Γ := Γ) H₀ p₀ := by
  rcases h with ⟨H₀, p₀, ⟨proof⟩, rfl, rfl⟩
  exact ⟨H₀, p₀, ⟨proof⟩, rfl, rfl, proof.sound⟩

theorem empty_not_proves_false :
    ¬ Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0)
      [] (.bool false) := by
  rintro ⟨H, p, proof, mapped, erased⟩
  have hH : H = [] := List.eq_nil_of_map_eq_nil mapped
  subst H
  have hp : p = (.bool false : ClosedTm Base) := Erasure.toScoped_injective erased
  subst p
  exact Nucleus.HolLN.empty_not_proves_false proof

end Tree.Scoped

namespace Tree.Raw

def Proves (Δ : FreeCtx Base) (Γ : BoundCtx Base depth)
    (H : List (Tree.Raw Base)) (p : Tree.Raw Base) : Prop :=
  ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
    H₀.map Erasure.toRaw = H ∧ Erasure.toRaw p₀ = p

theorem HasType.sound (h : HasType Δ Γ t A) :
    ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.toRaw t₀ = t ∧
      Erasure.toRaw A₀ = A ∧ ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ),
        ∃ value : DenoteTy A₀, Eval Δ Γ freeEnv boundEnv t₀ A₀ value := by
  rcases h with ⟨t₀, A₀, typing, rfl, rfl⟩
  exact ⟨t₀, A₀, typing, rfl, rfl, typing.eval_exists⟩

theorem EqTm.sound (h : EqTm Δ Γ t u A) :
    ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
      Erasure.toRaw t₀ = t ∧ Erasure.toRaw u₀ = u ∧ Erasure.toRaw A₀ = A ∧
      ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) {left right : DenoteTy A₀},
        Eval Δ Γ freeEnv boundEnv t₀ A₀ left →
        Eval Δ Γ freeEnv boundEnv u₀ A₀ right → left = right := by
  rcases h with ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl⟩
  exact ⟨t₀, u₀, A₀, ⟨equality⟩, rfl, rfl, rfl, equality.sound⟩

theorem Proves.sound (h : Proves Δ Γ H p) :
    ∃ H₀ p₀, Nonempty (Nucleus.HolLN.Proves Δ Γ H₀ p₀) ∧
      H₀.map Erasure.toRaw = H ∧ Erasure.toRaw p₀ = p ∧
      Nucleus.HolLN.Entails (Δ := Δ) (Γ := Γ) H₀ p₀ := by
  rcases h with ⟨H₀, p₀, ⟨proof⟩, rfl, rfl⟩
  exact ⟨H₀, p₀, ⟨proof⟩, rfl, rfl, proof.sound⟩

theorem empty_not_proves_false :
    ¬ Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0)
      [] (.bool false) := by
  rintro ⟨H, p, proof, mapped, erased⟩
  have hH : H = [] := List.eq_nil_of_map_eq_nil mapped
  subst H
  have hp : p = (.bool false : ClosedTm Base) := Erasure.toRaw_injective erased
  subst p
  exact Nucleus.HolLN.empty_not_proves_false proof

end Tree.Raw

end Nucleus.HolLN
