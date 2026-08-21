import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Pigeonhole
import Nucleus.Hash.PMF

/-! # Uniform finite hash samples -/

namespace Nucleus.Hash

/-- An ordered sample of `count` values. -/
abbrev Sample (count width : Nat) := Fin count → Hash width

namespace Sample

variable {count width prefixWidth : Nat}

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

variable {count width prefixWidth : Nat}

noncomputable def uniformSamples (count width : Nat) : PMF (Sample count width) :=
  FiniteUniform.pmf (Sample count width)

/-- A uniform hash has any fixed `prefixWidth`-bit prefix with mass `2⁻prefixWidth`. -/
@[simp] theorem prefixMass (fixed : Hash prefixWidth) (suffixWidth : Nat) :
    FiniteUniform.mass (HashPMF.prefixValues fixed suffixWidth) = 1 / 2 ^ prefixWidth := by
  simp only [FiniteUniform.mass, HashPMF.prefixValues_card,
    Fintype.card_congr BitVec.equivFin.toEquiv,
    Fintype.card_fin, pow_add, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  norm_num
  ac_rfl

@[simp] theorem zeroPrefixMass (prefixWidth suffixWidth : Nat) :
    FiniteUniform.mass (HashPMF.prefixValues (0#prefixWidth) suffixWidth) =
      1 / 2 ^ prefixWidth :=
  prefixMass _ _

/-- Hashes agreeing with `expected` on every selected bit. -/
noncomputable def maskEvent (mask expected : Hash width) : Finset (Hash width) :=
  Finset.univ.filter fun value => value &&& mask = expected &&& mask

@[simp] theorem mem_maskEvent (value mask expected : Hash width) :
    value ∈ maskEvent mask expected ↔ value &&& mask = expected &&& mask := by
  simp [maskEvent]

/-- XOR by a fixed hash is a permutation. -/
def xorEquiv (mask : Hash width) : Hash width ≃ Hash width where
  toFun value := value ^^^ mask
  invFun value := value ^^^ mask
  left_inv value := by simp [BitVec.xor_assoc]
  right_inv value := by simp [BitVec.xor_assoc]

/-- XOR by an arbitrary fixed value preserves uniform event mass. -/
@[simp] theorem mass_image_xor (mask : Hash width) (event : Finset (Hash width)) :
    FiniteUniform.mass (event.image (xorEquiv mask)) = FiniteUniform.mass event := by
  simp [FiniteUniform.mass, Finset.card_image_of_injective, (xorEquiv mask).injective]

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

def birthdayBound (count width : Nat) : ℚ :=
  (count : ℚ) ^ 2 / 2 ^ width

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

theorem collisionMass_le_pow_sub :
    collisionMass count width ≤
      ((((2 ^ width) ^ count - (2 ^ width + 1 - count) ^ count : Nat) : ℚ) /
        ((2 ^ width) ^ count : Nat)) := by
  rw [collisionMass_eq]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.sub_le_sub_left
      ((2 ^ width).pow_sub_le_descFactorial count) ((2 ^ width) ^ count)
  · positivity

end Nucleus.Hash
