import Mathlib.Probability.Distributions.Uniform

/-! # Uniform probability on finite types -/

namespace Nucleus.FiniteUniform

/-- Exact event mass as favorable outcomes over all outcomes. -/
def mass [Fintype α] (event : Finset α) : ℚ :=
  event.card / Fintype.card α

/-- The same ratio in Mathlib's measure codomain. -/
noncomputable def ennMass [Fintype α] (event : Finset α) : ENNReal :=
  event.card / Fintype.card α

noncomputable def pmf (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.uniformOfFintype α

@[simp] theorem outerMeasure_apply [Fintype α] [Nonempty α] (event : Finset α) :
    (pmf α).toOuterMeasure (event : Set α) = ennMass event := by
  unfold pmf
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [ennMass]

@[simp] theorem mass_univ [Fintype α] [Nonempty α] :
    mass (Finset.univ : Finset α) = 1 := by
  simp [mass, Fintype.card_ne_zero]

theorem mass_le_one [Fintype α] [Nonempty α] (event : Finset α) : mass event ≤ 1 := by
  have card_pos : (0 : ℚ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [mass, div_le_one card_pos]
  exact_mod_cast Finset.card_le_univ event

end Nucleus.FiniteUniform
