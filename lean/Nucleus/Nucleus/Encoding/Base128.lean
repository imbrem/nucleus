import Nucleus.Cbor.Bytes
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Defs

/-!
# Base-128 variable-length integer encodings

The representation types deliberately store compact `Bytes`. Validity and
normality are byte predicates: a valid value contains exactly one complete
number, while a normal value additionally uses its shortest representation.
`Vlq128` is the big-endian base-128 counterpart of little-endian LEB128.
-/

namespace Nucleus

namespace Base128

/-- Payload of a base-128 group, discarding the continuation bit. -/
def payload (byte : UInt8) : Nat := byte.toNat % 128

/-- Whether another group follows. -/
def continued (byte : UInt8) : Bool := 128 ≤ byte.toNat

/-- Certificate that a nonempty byte sequence contains exactly one terminated
base-128 number: every byte except the last continues, and the last
terminates. -/
inductive ValidBytes (bytes : Bytes) : Prop where
  | intro (pre : List UInt8) (last : UInt8)
      (bytes_eq : bytes.data.toList = pre ++ [last])
      (prefix_continues : ∀ byte ∈ pre, continued byte = true)
      (last_terminates : continued last = false) : ValidBytes bytes

/-- Validity is decidable from the finite byte sequence. -/
noncomputable instance (bytes : Bytes) : Decidable (ValidBytes bytes) :=
  Classical.propDecidable _

/-- Little-endian numeric interpretation of the seven-bit payload groups. -/
def decodeLittle (bytes : Bytes) : Nat :=
  Nat.ofDigits 128 (bytes.data.toList.map payload)

/-- Big-endian numeric interpretation. -/
def decodeBig (bytes : Bytes) : Nat :=
  Nat.ofDigits 128 (bytes.data.toList.reverse.map payload)

/-- A valid base-128 number is shortest exactly when a multi-byte value's
most-significant payload group is nonzero. -/
def LittleNormal (bytes : Bytes) : Prop :=
  ValidBytes bytes ∧
    bytes.data.toList.length = 1 ∨
      (bytes.data.toList.getLast?.map payload).getD 0 ≠ 0

/-- Big-endian shortest form: a multi-byte value has a nonzero first payload. -/
def BigNormal (bytes : Bytes) : Prop :=
  ValidBytes bytes ∧
    bytes.data.toList.length = 1 ∨
      (bytes.data.toList.head?.map payload).getD 0 ≠ 0

end Base128

/-- Bytes holding exactly one unsigned LEB128 number. -/
structure Leb128 where
  bytes : Bytes
  valid : Base128.ValidBytes bytes

namespace Leb128

/-- Shortest unsigned LEB128 representation. -/
structure Normal extends Leb128 where
  normal : Base128.LittleNormal bytes

/-- Decode a valid unsigned LEB128 value. -/
def value (encoded : Leb128) : Nat := Base128.decodeLittle encoded.bytes

/-- Numeric comparison, independent of representation length. -/
def Le (a b : Leb128) : Prop := a.value ≤ b.value

def Lt (a b : Leb128) : Prop := a.value < b.value

instance : LE Leb128 := ⟨Le⟩
instance : LT Leb128 := ⟨Lt⟩

theorem le_iff_value_le (a b : Leb128) : a ≤ b ↔ a.value ≤ b.value := Iff.rfl
theorem lt_iff_value_lt (a b : Leb128) : a < b ↔ a.value < b.value := Iff.rfl

end Leb128

/-- Bytes holding exactly one big-endian base-128 VLQ number. -/
structure Vlq128 where
  bytes : Bytes
  valid : Base128.ValidBytes bytes

namespace Vlq128

/-- Shortest big-endian VLQ128 representation. -/
structure Normal extends Vlq128 where
  normal : Base128.BigNormal bytes

def value (encoded : Vlq128) : Nat := Base128.decodeBig encoded.bytes

end Vlq128

namespace ZigZag

/-- Zigzag maps signed integers bijectively to naturals. -/
def encode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- Inverse zigzag interpretation. -/
def decode (n : Nat) : Int :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

@[simp] theorem decode_encode : ∀ value : Int, decode (encode value) = value := by
  intro value
  cases value with
  | ofNat n => simp [encode, decode]
  | negSucc n =>
      simp [encode, decode, Nat.mul_add_div]

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

end ZigZag

/-- A signed integer represented by shortest LEB128 of its zigzag image. -/
structure ZigZagLeb128 extends Leb128.Normal

namespace ZigZagLeb128

def value (encoded : ZigZagLeb128) : Int :=
  ZigZag.decode encoded.toNormal.toLeb128.value

end ZigZagLeb128

end Nucleus
