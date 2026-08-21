import Mathlib.Data.Fintype.Pi
import Nucleus.Hash.Blake3
import Nucleus.Hash.Probability

/-! # Random-compression collision bounds -/

namespace Nucleus.Blake3

abbrev Query := Params × Block

private def compressionEquiv : Compression ≃ (Query → Hash 256) where
  toFun compression query := compression query.1 query.2
  invFun oracle := ⟨fun params block => oracle (params, block)⟩
  left_inv compression := by cases compression; rfl
  right_inv oracle := by rfl

noncomputable instance : Fintype Compression :=
  Fintype.ofEquiv (Query → Hash 256) compressionEquiv.symm

noncomputable instance : DecidableEq Compression := Classical.decEq _

instance : Nonempty Compression := ⟨⟨fun _ _ => 0⟩⟩

structure CompressionPMF where
  pmf : PMF Compression

instance : Coe (CompressionPMF) (PMF Compression) := ⟨CompressionPMF.pmf⟩

instance : CoeFun CompressionPMF fun _ => Compression → ENNReal :=
  ⟨fun distribution => distribution.pmf⟩

@[ext] theorem CompressionPMF.ext {left right : CompressionPMF}
    (equal : left.pmf = right.pmf) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def CompressionPMF.constant (compression : Compression) : CompressionPMF :=
  ⟨PMF.pure compression⟩

noncomputable def CompressionPMF.uniform : CompressionPMF :=
  ⟨FiniteUniform.pmf Compression⟩

noncomputable def CompressionPMF.eventMass (distribution : CompressionPMF)
    (event : Finset Compression) : ENNReal :=
  distribution.pmf.toOuterMeasure (event : Set Compression)

@[simp] theorem CompressionPMF.uniform_eventMass (event : Finset Compression) :
    CompressionPMF.uniform.eventMass event = FiniteUniform.ennMass event := by
  exact FiniteUniform.outerMeasure_apply event

def HasHashCollision (compression : Compression) (initial : Hash 256)
    (inputs : Finset Bytes) : Prop :=
  ¬Function.Injective fun input : inputs => (compression.hash initial input).value

noncomputable instance (compression : Compression) (initial : Hash 256)
    (inputs : Finset Bytes) : Decidable (HasHashCollision compression initial inputs) :=
  Classical.propDecidable _

noncomputable def hashCollisionEvent (initial : Hash 256) (inputs : Finset Bytes) :
    Finset Compression :=
  Finset.univ.filter fun compression => HasHashCollision compression initial inputs

noncomputable def hashCollisionMass (initial : Hash 256) (inputs : Finset Bytes) : ℚ :=
  FiniteUniform.mass (hashCollisionEvent initial inputs)

noncomputable def hashCollisionENNMass (initial : Hash 256) (inputs : Finset Bytes) : ENNReal :=
  CompressionPMF.uniform.eventMass (hashCollisionEvent initial inputs)

@[simp] theorem hashCollisionENNMass_eq (initial : Hash 256) (inputs : Finset Bytes) :
    hashCollisionENNMass initial inputs =
      FiniteUniform.ennMass (hashCollisionEvent initial inputs) := by
  exact CompressionPMF.uniform_eventMass _

theorem hasHashCollision_of_card_lt (initial : Hash 256) (inputs : Finset Bytes)
    (more : 2 ^ 256 < inputs.card) (compression : Compression) :
    HasHashCollision compression initial inputs := by
  intro injective
  have bound := Fintype.card_le_of_injective
    (f := fun input : inputs => (compression.hash initial input).value) injective
  simp only [Fintype.card_coe, Hash.card] at bound
  omega

@[simp] theorem hashCollisionMass_eq_one (initial : Hash 256) (inputs : Finset Bytes)
    (more : 2 ^ 256 < inputs.card) : hashCollisionMass initial inputs = 1 := by
  have all : hashCollisionEvent initial inputs = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro compression _
    exact hasHashCollision_of_card_lt initial inputs more compression
  rw [hashCollisionMass, all]
  exact FiniteUniform.mass_univ

theorem hashCollisionMass_le_one (initial : Hash 256) (inputs : Finset Bytes) :
    hashCollisionMass initial inputs ≤ 1 :=
  FiniteUniform.mass_le_one _

theorem not_hasHashCollision_of_card_le_one (initial : Hash 256) (inputs : Finset Bytes)
    (small : inputs.card ≤ 1) (compression : Compression) :
    ¬HasHashCollision compression initial inputs := by
  intro collision
  apply collision
  intro left right _
  apply Subtype.ext
  exact Finset.card_le_one.mp small left.val left.property right.val right.property

theorem hashCollisionMass_eq_zero (initial : Hash 256) (inputs : Finset Bytes)
    (small : inputs.card ≤ 1) : hashCollisionMass initial inputs = 0 := by
  have empty : hashCollisionEvent initial inputs = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro compression _
    exact not_hasHashCollision_of_card_le_one initial inputs small compression
  rw [hashCollisionMass, empty]
  simp only [FiniteUniform.mass, Finset.card_empty, Nat.cast_zero, zero_div]

/-- A coarse bound requiring no transcript-independence argument. -/
def simpleCollisionBound (inputs : Finset Bytes) : ℚ :=
  if inputs.card ≤ 1 then 0 else 1

theorem hashCollisionMass_le_simpleBound (initial : Hash 256) (inputs : Finset Bytes) :
    hashCollisionMass initial inputs ≤ simpleCollisionBound inputs := by
  unfold simpleCollisionBound
  split
  · rw [hashCollisionMass_eq_zero initial inputs ‹inputs.card ≤ 1›]
  · exact hashCollisionMass_le_one initial inputs

/-- Compression calls available to a birthday reduction over `inputs`. -/
def totalCallBudget (inputs : Finset Bytes) : Nat :=
  ∑ input ∈ inputs, callBudget input.length

def totalByteSize (inputs : Finset Bytes) : Nat :=
  ∑ input ∈ inputs, input.length

theorem callBudget_le_size (byteLength : Nat) :
    callBudget byteLength ≤ 2 * byteLength + 1086 := by
  have blocksBound := Nat.div_le_self (byteLength + 63) 64
  have chunksBound := Nat.div_le_self (byteLength + 1023) 1024
  unfold callBudget blockCount chunkCount
  omega

theorem totalCallBudget_le_size (inputs : Finset Bytes) :
    totalCallBudget inputs ≤ 2 * totalByteSize inputs + 1086 * inputs.card := by
  unfold totalCallBudget totalByteSize
  calc
    ∑ input ∈ inputs, callBudget input.length ≤
        ∑ input ∈ inputs, (2 * input.length + 1086) := by
      exact Finset.sum_le_sum fun input _ => callBudget_le_size input.length
    _ = 2 * (∑ input ∈ inputs, input.length) + 1086 * inputs.card := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

/-- Birthday collision mass for independent 256-bit answers at the call budget. -/
noncomputable def callCollisionMass (inputs : Finset Bytes) : ℚ :=
  Hash.collisionMass (totalCallBudget inputs) 256

theorem callCollisionMass_eq (inputs : Finset Bytes) :
    callCollisionMass inputs =
      (((2 ^ 256) ^ totalCallBudget inputs -
        (2 ^ 256).descFactorial (totalCallBudget inputs) : Nat) : ℚ) /
        ((2 ^ 256) ^ totalCallBudget inputs : Nat) := by
  exact Hash.collisionMass_eq

@[simp] theorem callCollisionMass_eq_one (inputs : Finset Bytes)
    (more : 2 ^ 256 < totalCallBudget inputs) : callCollisionMass inputs = 1 := by
  exact Hash.collisionMass_eq_one more

end Nucleus.Blake3
