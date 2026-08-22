import Nucleus.Hash.Basic
import Nucleus.Bytes
import Mathlib.Data.Nat.Digits.Lemmas

/-! # 256-bit objects -/

namespace Nucleus

/-- A 256-bit hash. -/
abbrev O256 := Hash 256

namespace O256

/-- Big-endian bytes, matching unsigned and lexicographic O256 order. -/
def bytes (value : O256) : List UInt8 :=
  (Nat.digitsAppend 256 32 value.toNat).reverse.map UInt8.ofNat

@[simp] theorem bytes_length (value : O256) : value.bytes.length = 32 := by
  simp only [bytes, List.length_map, List.length_reverse]
  apply Nat.length_digitsAppend (by decide)
  simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] using value.isLt

/-- Parse exactly 32 big-endian bytes. -/
def ofList? (values : List UInt8) : Option O256 :=
  if values.length = 32 then
    some <| BitVec.ofNat 256 <| Nat.ofDigits 256 <| values.reverse.map UInt8.toNat
  else
    none

@[simp] theorem ofList?_bytes (value : O256) : ofList? value.bytes = some value := by
  let digits := Nat.digitsAppend 256 32 value.toNat
  have value_lt : value.toNat < 256 ^ 32 := by
    simpa [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] using value.isLt
  have digits_length : digits.length = 32 :=
    Nat.length_digitsAppend (b := 256) (by decide) 32 value_lt
  have digit_lt : ∀ digit ∈ digits, digit < 256 := by
    exact fun digit member => Nat.lt_of_mem_digitsAppend (by decide) 32 digit member
  have map_roundtrip (values : List Nat) (bounded : ∀ digit ∈ values, digit < 256) :
      (values.map UInt8.ofNat).map UInt8.toNat = values := by
    rw [List.map_map]
    have congruence :
        List.map (UInt8.toNat ∘ UInt8.ofNat) values = List.map id values := by
      apply List.map_congr_left
      intro digit member
      exact UInt8.toNat_ofNat_of_lt (bounded digit member)
    simpa only [List.map_id] using congruence
  unfold ofList? bytes
  rw [if_pos (by simpa [digits] using digits_length)]
  rw [List.map_reverse]
  rw [map_roundtrip digits.reverse (by
    intro digit member
    exact digit_lt digit (List.mem_reverse.mp member))]
  simp only [List.reverse_reverse]
  change some (BitVec.ofNat 256 (Nat.ofDigits 256 digits)) = some value
  simp [digits, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits, BitVec.ofNat_toNat]

/-- Compact byte encoding. -/
def encode (value : O256) : Bytes := ⟨value.bytes.toByteArray⟩

@[simp] theorem encode_length (value : O256) : value.encode.length = 32 := by
  simp [encode, Bytes.length, bytes_length]

end O256

end Nucleus
