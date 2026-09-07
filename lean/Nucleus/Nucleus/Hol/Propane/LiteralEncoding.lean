import Nucleus.Hol.Propane.LiteralWire
import Mathlib.Data.List.Induction

/-!
# Canonical numeric payload encoding

Natural payloads use the shortest unsigned big-endian spelling. Nonnegative
integers reserve the high sign bit; negative integers complement the spelling
of their predecessor magnitude. These are concrete base-256 algorithms, with
general canonicality and decoder roundtrip proofs. Inline placement remains
an independent constructor optimization.
-/

namespace Nucleus.Hol.Propane.LiteralEncoding

open LiteralWire

private def cutoff (signed : Bool) : Nat := if signed then 128 else 256

private theorem quotient_smaller (signed : Bool) (value : Nat)
    (large : ¬value < cutoff signed) : value / 256 < value := by
  apply Nat.div_lt_self
  · cases signed <;> simp [cutoff] at large <;> omega
  · decide

/-- The sign-reserving version may insert one leading zero octet. -/
private def digits (signed : Bool) (value : Nat) : List UInt8 :=
  if value < cutoff signed then [UInt8.ofNat value]
  else digits signed (value / 256) ++ [UInt8.ofNat (value % 256)]
termination_by value
decreasing_by exact quotient_smaller signed value (by assumption)

def encodeNat (value : Nat) : List UInt8 := digits false value

private def complement (byte : UInt8) : UInt8 := UInt8.ofNat (255 - byte.toNat)

def encodeInt : Int → List UInt8
  | .ofNat value => digits true value
  | .negSucc value => (digits true value).map complement

private theorem unsigned_append (bytes : List UInt8) (byte : UInt8) :
    unsigned (bytes ++ [byte]) = unsigned bytes * 256 + byte.toNat := by
  simp [unsigned, List.foldl_append]

private theorem unsigned_singleton (byte : UInt8) : unsigned [byte] = byte.toNat := by
  simp [unsigned]

private theorem unsigned_digits (sign : Bool) (value : Nat) :
    unsigned (digits sign value) = value := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      rw [digits]
      split
      · rename_i small
        rw [unsigned_singleton, UInt8.toNat_ofNat_of_lt']
        change value < 256
        cases sign <;> simp [cutoff] at small <;> omega
      · rename_i large
        rw [unsigned_append, ih _ (quotient_smaller sign value large),
          UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide))]
        simpa [Nat.mul_comm] using Nat.div_add_mod value 256

private theorem digits_head (sign : Bool) (value : Nat) :
    ∃ first rest, digits sign value = first :: rest ∧ first.toNat < cutoff sign := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      rw [digits]
      split
      · rename_i small
        refine ⟨UInt8.ofNat value, [], rfl, ?_⟩
        rw [UInt8.toNat_ofNat_of_lt']
        · exact small
        · change value < 256
          cases sign <;> simp [cutoff] at small <;> omega
      · rename_i large
        obtain ⟨first, rest, prefixEq, bounded⟩ :=
          ih _ (quotient_smaller sign value large)
        exact ⟨first, rest ++ [UInt8.ofNat (value % 256)], by rw [prefixEq]; rfl, bounded⟩

private theorem canonical_nat_digits (value : Nat) : canonicalNat (digits false value) = true := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      rw [digits]
      split
      · rfl
      · rename_i large
        have smaller := quotient_smaller false value large
        have previous := ih _ smaller
        have magnitude := unsigned_digits false (value / 256)
        obtain ⟨first, rest, prefixEq, _⟩ := digits_head false (value / 256)
        rw [prefixEq] at previous magnitude ⊢
        have nonzero : first.toNat ≠ 0 := by
          cases rest with
          | nil =>
              rw [unsigned_singleton] at magnitude
              have : 256 ≤ value := by simpa [cutoff] using large
              have positive : 0 < value / 256 := Nat.div_pos this (by decide)
              omega
          | cons second rest => simpa [canonicalNat] using previous
        cases rest <;> simp [canonicalNat, nonzero]

private theorem canonical_int_digits (value : Nat) : canonicalInt (digits true value) = true := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      rw [digits]
      split
      · rfl
      · rename_i large
        have previous := ih _ (quotient_smaller true value large)
        have magnitude := unsigned_digits true (value / 256)
        obtain ⟨first, rest, prefixEq, bounded⟩ := digits_head true (value / 256)
        have highClear : first.toNat < 128 := by simpa [cutoff] using bounded
        have notFF : first.toNat ≠ 255 := by omega
        rw [prefixEq] at previous magnitude ⊢
        cases rest with
        | nil =>
            rw [unsigned_singleton] at magnitude
            by_cases zero : first.toNat = 0
            · have low : value < 256 := by omega
              have high : 128 ≤ value := by simpa [cutoff] using large
              simpa [canonicalInt, zero, Nat.mod_eq_of_lt low] using high
            · simp [canonicalInt, zero, notFF]
        | cons second rest => simpa [canonicalInt] using previous

private theorem complement_value (byte : UInt8) :
    (complement byte).toNat = 255 - byte.toNat := by
  apply UInt8.toNat_ofNat_of_lt'
  change 255 - byte.toNat < 256
  omega

private theorem canonical_complement (bytes : List UInt8) :
    canonicalInt (bytes.map complement) = canonicalInt bytes := by
  cases bytes with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          have firstBound := first.toNat_lt_size
          have secondBound := second.toNat_lt_size
          change first.toNat < 256 at firstBound
          change second.toNat < 256 at secondBound
          simp only [List.map_cons, canonicalInt, complement_value]
          apply Bool.eq_iff_iff.mpr
          simp
          omega

private theorem unsigned_complement (bytes : List UInt8) :
    unsigned (bytes.map complement) + unsigned bytes + 1 = 256 ^ bytes.length := by
  induction bytes using List.reverseRecOn with
  | nil => simp [unsigned]
  | append_singleton bytes byte ih =>
      have bounded := byte.toNat_lt_size
      change byte.toNat < 256 at bounded
      simp only [List.map_append, List.map_cons, List.map_nil, unsigned_append,
        complement_value, List.length_append, List.length_singleton, pow_succ]
      omega

@[simp] theorem unsigned_encodeNat (value : Nat) : unsigned (encodeNat value) = value :=
  unsigned_digits false value

@[simp] theorem canonical_encodeNat (value : Nat) : canonicalNat (encodeNat value) = true :=
  canonical_nat_digits value

@[simp] theorem canonical_encodeInt (value : Int) : canonicalInt (encodeInt value) = true := by
  cases value with
  | ofNat value => exact canonical_int_digits value
  | negSucc value =>
      exact (canonical_complement (digits true value)).trans (canonical_int_digits value)

@[simp] theorem signed_encodeInt (value : Int) : signed (encodeInt value) = value := by
  cases value with
  | ofNat value =>
      obtain ⟨first, rest, prefixEq, bounded⟩ := digits_head true value
      have highClear : first.toNat < 128 := by simpa [cutoff] using bounded
      have unsignedValue := unsigned_digits true value
      have signFalse : (digits true value).head?.any (fun byte => byte.toNat ≥ 128) = false := by
        rw [prefixEq]
        simp [show ¬first.toNat ≥ 128 from by omega]
      simp [encodeInt, signed, signFalse, unsignedValue]
  | negSucc value =>
      obtain ⟨first, rest, prefixEq, bounded⟩ := digits_head true value
      have highSet : (complement first).toNat ≥ 128 := by
        rw [complement_value]
        simp only [cutoff, ↓reduceIte] at bounded
        omega
      have sum := unsigned_complement (digits true value)
      rw [unsigned_digits] at sum
      have signTrue : ((digits true value).map complement).head?.any
          (fun byte => byte.toNat ≥ 128) = true := by
        rw [prefixEq]
        simp [highSet]
      simp only [encodeInt, signed, signTrue, ↓reduceIte, List.length_map]
      have sumInt : (unsigned ((digits true value).map complement) : Int) + value + 1 =
          (256 : Int) ^ (digits true value).length := by exact_mod_cast sum
      rw [Int.negSucc_eq]
      omega

/-- General resident-natural encoder/decoder agreement, under the allocation bound. -/
theorem decode_encodeNat (value : Nat) (bounded : (encodeNat value).length ≤ maxPayloadBytes) :
    decodeConstant (.nat (encodeNat value)) = some (.nat value) := by
  simp [decodeConstant, bounded]

/-- General resident-integer encoder/decoder agreement, under the allocation bound. -/
theorem decode_encodeInt (value : Int) (bounded : (encodeInt value).length ≤ maxPayloadBytes) :
    decodeConstant (.int (encodeInt value)) = some (.int value) := by
  simp [decodeConstant, bounded]

/-- Every word bit pattern has its unique signed inline spelling, including i64. -/
theorem decode_encodeWord (width : Width) (value : BitVec width.bits) :
    decodeWordInline width value.toInt = some (.word width value) := by
  simp [decodeWordInline, BitVec.le_toInt, BitVec.toInt_lt]

/-- Resident byte payloads have no additional value-level encoding. -/
theorem decode_encodeBytes (value : List UInt8) (bounded : value.length ≤ maxPayloadBytes) :
    decodeConstant (.bytes value) = some (.bytes value) := by
  simp [decodeConstant, bounded]

end Nucleus.Hol.Propane.LiteralEncoding
