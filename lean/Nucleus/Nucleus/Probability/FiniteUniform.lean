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

end Nucleus.FiniteUniform
