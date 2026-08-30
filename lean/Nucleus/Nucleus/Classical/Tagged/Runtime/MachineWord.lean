import Nucleus.Classical.Tagged.Runtime

/-!
# Machine-word representation

`Word payloadWidth` is sign-magnitude: one polarity bit above an unsigned
payload.  This module gives the exact bijection with a `payloadWidth + 1` bit
unsigned integer used by Rust.  For widths of at least two, the polarity bit
does not affect the low LIT/AND/OR/SAT tag bits.
-/

namespace Nucleus.Classical.Tagged.Runtime.MachineWord

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- Pack polarity into the bit immediately above the payload. -/
def pack (word : Word payloadWidth) : Fin (2 ^ (payloadWidth + 1)) :=
  ⟨word.payload.val + if word.negative then 2 ^ payloadWidth else 0, by
    have payloadBound := word.payload.isLt
    cases word.negative <;> simp [Nat.pow_succ] <;> omega⟩

/-- Recover sign-magnitude fields from one machine integer. -/
def unpack (machine : Fin (2 ^ (payloadWidth + 1))) : Word payloadWidth :=
  ⟨decide (2 ^ payloadWidth ≤ machine.val),
    ⟨machine.val % 2 ^ payloadWidth, Nat.mod_lt _ (Nat.two_pow_pos _)⟩⟩

@[simp] theorem unpack_pack (word : Word payloadWidth) :
    unpack (pack word) = word := by
  cases word with
  | mk negative payload =>
      cases negative with
      | false =>
          have bound := payload.isLt
          simp [unpack, pack, Nat.mod_eq_of_lt bound]
      | true =>
          have bound := payload.isLt
          have modulusPositive := Nat.two_pow_pos payloadWidth
          have modulo : (payload.val + 2 ^ payloadWidth) % 2 ^ payloadWidth =
              payload.val := by
            rw [Nat.add_mod]
            simp [Nat.mod_eq_of_lt bound]
          simp [unpack, pack, modulo]

@[simp] theorem pack_unpack (machine : Fin (2 ^ (payloadWidth + 1))) :
    pack (unpack machine) = machine := by
  apply Fin.ext
  change (machine.val % 2 ^ payloadWidth +
      if decide (2 ^ payloadWidth ≤ machine.val) then
        2 ^ payloadWidth else 0) = machine.val
  by_cases upper : 2 ^ payloadWidth ≤ machine.val
  · have machineBound := machine.isLt
    have belowDouble : machine.val < 2 ^ payloadWidth + 2 ^ payloadWidth := by
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.two_mul] using machineBound
    have remainder : machine.val % 2 ^ payloadWidth =
        machine.val - 2 ^ payloadWidth := by
      rw [Nat.mod_eq_sub_mod upper]
      apply Nat.mod_eq_of_lt
      omega
    simp [upper, remainder]
  · have below : machine.val < 2 ^ payloadWidth := Nat.lt_of_not_ge upper
    simp [upper, Nat.mod_eq_of_lt below]

/-- The high polarity bit round-trips exactly. -/
theorem negative_iff (word : Word payloadWidth) :
    2 ^ payloadWidth ≤ (pack word).val ↔ word.negative = true := by
  cases word with
  | mk negative payload =>
      cases negative with
      | false => simp [pack, payload.isLt]
      | true => simp [pack]

/-- At ordinary tagged widths, the high polarity bit leaves the low two tag
bits unchanged. -/
theorem pack_mod_four (word : Word payloadWidth) (width : 2 ≤ payloadWidth) :
    (pack word).val % 4 = word.tag := by
  cases word with
  | mk negative payload =>
      cases negative with
      | false => simp [pack, Word.tag]
      | true =>
          obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le width
          simp [pack, Word.tag, Nat.add_mod, Nat.pow_add]

/-- Packing is injective, so raw machine equality is exact word equality. -/
theorem pack_injective : Function.Injective (@pack payloadWidth) := by
  intro left right equal
  rw [← unpack_pack left, ← unpack_pack right, equal]

end Nucleus.Classical.Tagged.Runtime.MachineWord
