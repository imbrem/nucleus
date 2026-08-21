import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-! # Fixed-width hashes -/

namespace Nucleus

/-- An `n`-bit hash value. -/
abbrev Hash (n : Nat) := BitVec n

namespace Hash

noncomputable instance : Fintype (Hash n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) BitVec.equivFin.symm.toEquiv

@[simp] theorem card : Fintype.card (Hash n) = 2 ^ n := by
  rw [Fintype.card_congr BitVec.equivFin.toEquiv]
  simp

/-- Bits from most to least significant. -/
def bits (value : Hash n) : List Bool :=
  List.ofFn fun i : Fin n => value.getMsbD i

@[simp] theorem bits_length (value : Hash n) : value.bits.length = n := by
  simp [bits]

def bitListEmbedding : Hash n ↪ List Bool where
  toFun := bits
  inj' left right equal := by
    have functions :
        (fun i : Fin n => left.getMsbD i) = (fun i : Fin n => right.getMsbD i) :=
      List.ofFn_injective equal
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    exact congrFun functions ⟨i, hi⟩

/-- Zero-extension as an infinite bit stream. -/
def stream (value : Hash n) : Nat → Bool := value.getMsbD

def EventuallyZero (values : Nat → Bool) : Prop :=
  ∃ cutoff, ∀ i, cutoff ≤ i → values i = false

def eventuallyZeroEmbedding : Hash n ↪ {values : Nat → Bool // EventuallyZero values} where
  toFun value := ⟨value.stream, n, fun i hi => by simp [stream, BitVec.getMsbD, hi]⟩
  inj' left right equal := by
    apply BitVec.eq_of_getMsbD_eq
    intro i _
    exact congrFun (congrArg Subtype.val equal) i

/-- Number of leading zero bits. -/
def leadingZeros (value : Hash n) : Nat := value.clz.toNat

def leadingZeroWeightRat (value : Hash n) : ℚ :=
  (2 : ℚ)⁻¹ ^ value.leadingZeros

noncomputable def leadingZeroWeightReal (value : Hash n) : ℝ :=
  (2 : ℝ)⁻¹ ^ value.leadingZeros

theorem leadingZeros_le (value : Hash n) : value.leadingZeros ≤ n := by
  have bound := BitVec.clz_le (x := value)
  change value.clz.toNat ≤ (BitVec.ofNat n n).toNat at bound
  unfold leadingZeros
  simpa using bound

end Hash

end Nucleus
