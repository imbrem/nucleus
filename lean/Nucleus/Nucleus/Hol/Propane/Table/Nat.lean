import Mathlib.Data.Nat.Digits.Lemmas
import Nucleus.Bytes

/-!
# Propane table encoding for naturals

Propane syntax carries a Lean `Nat`.  This module separately specifies the
canonical unsigned big-endian byte representation available to a table codec:
zero is `[0]`; every other value has no leading zero byte.  It matches Rust's
`covalence-data-num::Num` boundary representation.

Whether a table stores a small value inline or points at these bytes is an
encoding decision and does not change the decoded Propane expression.
-/

namespace Nucleus.Hol.Propane.Table.NatCodec

/-- Little-endian base-256 digits, with an explicit digit for zero. -/
def digits (value : Nat) : List Nat :=
  if value = 0 then [0] else Nat.digits 256 value

/-- Encode a natural as its shortest unsigned big-endian byte string. -/
def encode (value : Nat) : Nucleus.Bytes :=
  Nucleus.Bytes.ofList ((digits value).reverse.map UInt8.ofNat)

/-- Interpret unsigned big-endian bytes.  This accepts non-normal syntax; use
`Normal` at the checked table boundary. -/
def decode (bytes : Nucleus.Bytes) : Nat :=
  Nat.ofDigits 256 (bytes.toList.reverse.map UInt8.toNat)

private theorem digits_lt (value : Nat) : ∀ digit ∈ digits value, digit < 256 := by
  intro digit member
  simp only [digits] at member
  split at member
  · simp_all
  · exact Nat.digits_lt_base (by decide) member

private theorem map_bytes_roundtrip (values : List Nat)
    (bounded : ∀ value ∈ values, value < 256) :
    (values.map UInt8.ofNat).map UInt8.toNat = values := by
  rw [List.map_map]
  have congruence :
      List.map (UInt8.toNat ∘ UInt8.ofNat) values = List.map id values := by
    apply List.map_congr_left
    intro value member
    exact UInt8.toNat_ofNat_of_lt (bounded value member)
  simpa only [List.map_id] using congruence

private theorem ofDigits_digits (value : Nat) :
    Nat.ofDigits 256 (digits value) = value := by
  simp only [digits]
  split
  · simp_all
  · exact Nat.ofDigits_digits 256 value

@[simp] theorem decode_encode (value : Nat) : decode (encode value) = value := by
  rw [decode, encode, Nucleus.Bytes.toList_ofList]
  rw [List.map_reverse]
  rw [map_bytes_roundtrip (digits value).reverse (by
    intro digit member
    exact digits_lt value digit (List.mem_reverse.mp member))]
  rw [List.reverse_reverse]
  exact ofDigits_digits value

/-- Canonical syntax is exactly the re-encoding of its numeric meaning. -/
def Normal (bytes : Nucleus.Bytes) : Prop :=
  bytes = encode (decode bytes)

theorem normal_encode (value : Nat) : Normal (encode value) := by
  simp [Normal]

/-- Bytes accepted by the canonical table decoder. -/
structure Checked where
  bytes : Nucleus.Bytes
  normal : Normal bytes

namespace Checked

def value (literal : Checked) : Nat := decode literal.bytes

def ofNat (value : Nat) : Checked where
  bytes := encode value
  normal := normal_encode value

@[simp] theorem value_ofNat (value : Nat) : (ofNat value).value = value :=
  decode_encode value

@[ext] theorem ext {left right : Checked} (equal : left.bytes = right.bytes) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Canonical table bytes are in bijection with mathematical naturals. -/
def equivNat : Checked ≃ Nat where
  toFun := value
  invFun := ofNat
  left_inv literal := by
    apply ext
    exact literal.normal.symm
  right_inv := value_ofNat

end Checked

end Nucleus.Hol.Propane.Table.NatCodec
