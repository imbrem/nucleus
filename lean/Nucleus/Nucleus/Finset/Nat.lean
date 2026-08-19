import Mathlib.Data.Finset.Fold

/-! # Utilities for finite sets of natural numbers -/

namespace Finset

/-- A natural number strictly greater than every member of the finite set. -/
def freshNat (values : Finset Nat) : Nat :=
  values.fold max 0 id + 1

theorem lt_freshNat {value : Nat} {values : Finset Nat}
    (membership : value ∈ values) : value < values.freshNat := by
  simp only [freshNat, Nat.lt_add_one_iff, Finset.le_fold_max]
  exact Or.inr ⟨value, membership, le_rfl⟩

@[simp] theorem freshNat_not_mem (values : Finset Nat) :
    values.freshNat ∉ values := by
  intro membership
  exact (Nat.lt_irrefl values.freshNat) (lt_freshNat membership)

end Finset
