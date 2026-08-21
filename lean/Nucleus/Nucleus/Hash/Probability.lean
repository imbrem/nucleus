import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pigeonhole
import Nucleus.Hash.Basic
import Nucleus.Probability.FiniteUniform

/-! # Uniform finite hash samples -/

namespace Nucleus.Hash

/-- An ordered sample of `count` values. -/
abbrev Sample (count width : Nat) := Fin count → Hash width

namespace Sample

variable {count width : Nat}

def toList (sample : Sample count width) : List (Hash width) :=
  List.ofFn sample

def HasCollision (sample : Sample count width) : Prop :=
  ¬Function.Injective sample

noncomputable instance (sample : Sample count width) : Decidable sample.HasCollision :=
  Classical.propDecidable _

@[simp] theorem hasCollision_iff_not_nodup (sample : Sample count width) :
    sample.HasCollision ↔ ¬sample.toList.Nodup := by
  simp [HasCollision, toList, List.nodup_ofFn]

end Sample

variable {count width : Nat}

noncomputable def uniform (width : Nat) : PMF (Hash width) :=
  FiniteUniform.pmf (Hash width)

noncomputable def uniformSamples (count width : Nat) : PMF (Sample count width) :=
  FiniteUniform.pmf (Sample count width)

/-- Probability that one uniform hash belongs to `seen`. -/
noncomputable def seenMass (seen : Finset (Hash width)) : ℚ :=
  FiniteUniform.mass seen

@[simp] theorem seenMass_eq (seen : Finset (Hash width)) :
    seenMass seen = seen.card / 2 ^ width := by
  simp [seenMass, FiniteUniform.mass]

noncomputable def collisionEvent (count width : Nat) : Finset (Sample count width) :=
  Finset.univ.filter Sample.HasCollision

noncomputable def collisionMass (count width : Nat) : ℚ :=
  FiniteUniform.mass (collisionEvent count width)

theorem hasCollision_of_card_lt (h : 2 ^ width < count)
    (sample : Sample count width) : sample.HasCollision := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt sample (by simpa using h)
  exact fun injective => hij (injective heq)

@[simp] theorem collisionMass_eq_one (h : 2 ^ width < count) :
    collisionMass count width = 1 := by
  have all : collisionEvent count width = Finset.univ := by
    unfold collisionEvent
    apply Finset.filter_eq_self.mpr
    intro sample _
    exact hasCollision_of_card_lt h sample
  rw [collisionMass, all]
  exact FiniteUniform.mass_univ

@[simp] theorem collisionMass_succ_card :
    collisionMass (2 ^ width + 1) width = 1 := by
  apply collisionMass_eq_one
  omega

theorem injectiveSample_count :
    (Finset.univ.filter (Function.Injective : Sample count width → Prop)).card =
      (2 ^ width).descFactorial count := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr
    (Equiv.subtypeInjectiveEquivEmbedding (Fin count) (Hash width))]
  simp

theorem collisionEvent_card :
    (collisionEvent count width).card =
      (2 ^ width) ^ count - (2 ^ width).descFactorial count := by
  have partition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Sample count width)))
    (Function.Injective : Sample count width → Prop)
  rw [injectiveSample_count] at partition
  have total : (Finset.univ : Finset (Sample count width)).card =
      (2 ^ width) ^ count := by simp
  rw [total] at partition
  have event_eq : collisionEvent count width =
      Finset.univ.filter fun sample : Sample count width => ¬Function.Injective sample := by
    ext sample
    simp [collisionEvent, Sample.HasCollision]
  rw [event_eq]
  omega

theorem collisionMass_eq :
    collisionMass count width =
      (((2 ^ width) ^ count - (2 ^ width).descFactorial count : Nat) : ℚ) /
        ((2 ^ width) ^ count : Nat) := by
  simp [collisionMass, FiniteUniform.mass, collisionEvent_card]

end Nucleus.Hash
