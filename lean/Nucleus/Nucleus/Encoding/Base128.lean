import Nucleus.Cbor.Bytes
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

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
      (bytes_eq : bytes.data.data.toList = pre ++ [last])
      (prefix_continues : ∀ byte ∈ pre, continued byte = true)
      (last_terminates : continued last = false) : ValidBytes bytes

/-- Validity is decidable from the finite byte sequence. -/
noncomputable instance (bytes : Bytes) : Decidable (ValidBytes bytes) :=
  Classical.propDecidable _

/-- Little-endian numeric interpretation of the seven-bit payload groups. -/
def decodeLittle (bytes : Bytes) : Nat :=
  Nat.ofDigits 128 (bytes.data.data.toList.map payload)

/-- Big-endian numeric interpretation. -/
def decodeBig (bytes : Bytes) : Nat :=
  Nat.ofDigits 128 (bytes.data.data.toList.reverse.map payload)

/-- Canonical base-128 payload digits; zero has the single digit zero. -/
def digits (n : Nat) : List Nat := if n = 0 then [0] else Nat.digits 128 n

private def mark : List Nat → List UInt8
  | [] => []
  | [digit] => [UInt8.ofNat digit]
  | digit :: rest => UInt8.ofNat (digit + 128) :: mark rest

/-- Shortest unsigned LEB128 bytes. Construction uses the compact underlying
array; the logical list view is only used for proofs. -/
def encodeLittle (n : Nat) : Bytes :=
  ⟨ByteArray.mk (mark (digits n)).toArray⟩

/-- Shortest big-endian base-128 VLQ bytes. -/
def encodeBig (n : Nat) : Bytes :=
  ⟨ByteArray.mk (mark (digits n).reverse).toArray⟩

private theorem digits_ne_nil (n : Nat) : digits n ≠ [] := by
  simp only [digits]
  split <;> simp_all [Nat.digits_ne_nil_iff_ne_zero]

private theorem digits_lt (n : Nat) : ∀ d ∈ digits n, d < 128 := by
  intro d hd
  simp only [digits] at hd
  split at hd
  · simp_all
  · exact Nat.digits_lt_base (by omega) hd

private theorem payload_ofNat (d : Nat) (h : d < 128) :
    payload (UInt8.ofNat d) = d := by
  simp [payload]
  omega

private theorem payload_ofNat_continued (d : Nat) (h : d < 128) :
    payload (UInt8.ofNat (d + 128)) = d := by
  simp [payload, UInt8.toNat_ofNat]
  omega

private theorem continued_ofNat (d : Nat) (h : d < 128) :
    continued (UInt8.ofNat d) = false := by
  simp [continued]
  omega

private theorem continued_ofNat_add (d : Nat) (h : d < 128) :
    continued (UInt8.ofNat (d + 128)) = true := by
  simp [continued, UInt8.toNat_ofNat]
  omega

private theorem map_payload_mark (ds : List Nat) (h : ∀ d ∈ ds, d < 128) :
    (mark ds).map payload = ds := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
      cases rest with
      | nil => simp [mark, payload_ofNat d (h d (by simp))]
      | cons e tail =>
          simp only [mark, List.map_cons, List.cons.injEq]
          constructor
          · exact payload_ofNat_continued d (h d (by simp))
          · apply ih
            intro x hx
            exact h x (by simp [hx])

private theorem valid_mark (ds : List Nat) (hne : ds ≠ [])
    (h : ∀ d ∈ ds, d < 128) :
    ValidBytes ⟨ByteArray.mk (mark ds).toArray⟩ := by
  induction ds with
  | nil => contradiction
  | cons d rest ih =>
      cases rest with
      | nil =>
          refine .intro [] (UInt8.ofNat d) ?_ ?_ ?_
          · simp [mark]
          · simp
          · exact continued_ofNat d (h d (by simp))
      | cons e tail =>
          have tailValid := ih (by simp) (by
            intro x hx
            exact h x (by simp [hx]))
          cases tailValid with
          | intro pre last bytes_eq hpre last_term =>
              refine .intro (UInt8.ofNat (d + 128) :: pre) last ?_ ?_ last_term
              · simpa [mark] using congrArg (fun xs => UInt8.ofNat (d + 128) :: xs) bytes_eq
              · intro byte hbyte
                simp only [List.mem_cons] at hbyte
                rcases hbyte with rfl | hbyte
                · exact continued_ofNat_add d (h d (by simp))
                · exact hpre byte hbyte

private theorem ofDigits_digits (n : Nat) : Nat.ofDigits 128 (digits n) = n := by
  simp only [digits]
  split
  · simp_all
  · exact Nat.ofDigits_digits 128 n

@[simp] theorem decodeLittle_encodeLittle (n : Nat) :
    decodeLittle (encodeLittle n) = n := by
  rw [decodeLittle, encodeLittle]
  simp only [map_payload_mark _ (digits_lt n)]
  exact ofDigits_digits n

@[simp] theorem decodeBig_encodeBig (n : Nat) :
    decodeBig (encodeBig n) = n := by
  rw [decodeBig, encodeBig]
  simp only [List.map_reverse]
  rw [map_payload_mark _, List.reverse_reverse]
  · exact ofDigits_digits n
  · intro d hd
    exact digits_lt n d (List.mem_reverse.mp hd)

theorem valid_encodeLittle (n : Nat) : ValidBytes (encodeLittle n) :=
  valid_mark (digits n) (digits_ne_nil n) (digits_lt n)

theorem valid_encodeBig (n : Nat) : ValidBytes (encodeBig n) :=
  valid_mark (digits n).reverse (by simpa using digits_ne_nil n) (by
    intro d hd
    exact digits_lt n d (List.mem_reverse.mp hd))

/-- A valid base-128 number is shortest exactly when a multi-byte value's
most-significant payload group is nonzero. -/
def LittleNormal (bytes : Bytes) : Prop :=
  ValidBytes bytes ∧ bytes = encodeLittle (decodeLittle bytes)

/-- Big-endian shortest form: a multi-byte value has a nonzero first payload. -/
def BigNormal (bytes : Bytes) : Prop :=
  ValidBytes bytes ∧ bytes = encodeBig (decodeBig bytes)

end Base128

/-- Bytes holding exactly one unsigned LEB128 number. -/
structure Leb128 where
  bytes : Bytes
  valid : Base128.ValidBytes bytes

namespace Leb128

@[ext] theorem ext {a b : Leb128} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  simp_all

/-- Shortest unsigned LEB128 representation. -/
structure Normal extends Leb128 where
  normal : Base128.LittleNormal bytes

@[ext] theorem Normal.ext {a b : Normal} (h : a.bytes = b.bytes) : a = b := by
  cases a with
  | mk a _ =>
      cases b with
      | mk b _ =>
          have hab : a = b := Leb128.ext h
          cases hab
          rfl

/-- Decode a valid unsigned LEB128 value. -/
def value (encoded : Leb128) : Nat := Base128.decodeLittle encoded.bytes

/-- Numeric comparison, independent of representation length. -/
def Le (a b : Leb128) : Prop := a.value ≤ b.value

def Lt (a b : Leb128) : Prop := a.value < b.value

instance : LE Leb128 := ⟨Le⟩
instance : LT Leb128 := ⟨Lt⟩

theorem le_iff_value_le (a b : Leb128) : a ≤ b ↔ a.value ≤ b.value := Iff.rfl
theorem lt_iff_value_lt (a b : Leb128) : a < b ↔ a.value < b.value := Iff.rfl

/-- The unique shortest LEB128 representation of a natural number. -/
def Normal.ofNat (n : Nat) : Normal where
  bytes := Base128.encodeLittle n
  valid := Base128.valid_encodeLittle n
  normal := ⟨Base128.valid_encodeLittle n, by simp⟩

@[simp] theorem Normal.value_ofNat (n : Nat) : (Normal.ofNat n).toLeb128.value = n :=
  Base128.decodeLittle_encodeLittle n

/-- Shortest LEB128 byte strings are in bijection with naturals. -/
def normalEquivNat : Normal ≃ Nat where
  toFun n := n.toLeb128.value
  invFun := Normal.ofNat
  left_inv n := by
    apply Normal.ext
    exact n.normal.2.symm
  right_inv := Normal.value_ofNat

end Leb128

/-- Bytes holding exactly one big-endian base-128 VLQ number. -/
structure Vlq128 where
  bytes : Bytes
  valid : Base128.ValidBytes bytes

namespace Vlq128

@[ext] theorem ext {a b : Vlq128} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  simp_all

/-- Shortest big-endian VLQ128 representation. -/
structure Normal extends Vlq128 where
  normal : Base128.BigNormal bytes

@[ext] theorem Normal.ext {a b : Normal} (h : a.bytes = b.bytes) : a = b := by
  cases a with
  | mk a _ =>
      cases b with
      | mk b _ =>
          have hab : a = b := Vlq128.ext h
          cases hab
          rfl

def value (encoded : Vlq128) : Nat := Base128.decodeBig encoded.bytes

def Normal.ofNat (n : Nat) : Normal where
  bytes := Base128.encodeBig n
  valid := Base128.valid_encodeBig n
  normal := ⟨Base128.valid_encodeBig n, by simp⟩

@[simp] theorem Normal.value_ofNat (n : Nat) : (Normal.ofNat n).toVlq128.value = n :=
  Base128.decodeBig_encodeBig n

/-- Shortest big-endian VLQ128 byte strings are in bijection with naturals. -/
def normalEquivNat : Normal ≃ Nat where
  toFun n := n.toVlq128.value
  invFun := Normal.ofNat
  left_inv n := by
    apply Normal.ext
    exact n.normal.2.symm
  right_inv := Normal.value_ofNat

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

@[simp] theorem encode_decode (n : Nat) : encode (decode n) = n := by
  simp only [decode]
  split_ifs with even
  · have hmod : n % 2 = 0 := even
    simp [encode]
    omega
  · have hmod : n % 2 = 1 := by omega
    simp [encode]
    omega

/-- Zigzag is a bijection between signed integers and naturals. -/
def equivNat : Int ≃ Nat where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

end ZigZag

/-- LEB128 bytes interpreted through zigzag. Non-normal values remain
representable; zigzag changes numeric interpretation, not byte syntax. -/
abbrev ZigZagLeb128 := Leb128

namespace ZigZagLeb128

/-- Shortest zigzag LEB128 is exactly shortest unsigned LEB128. -/
abbrev Normal := Leb128.Normal

def value (encoded : ZigZagLeb128) : Int := ZigZag.decode (Leb128.value encoded)

/-- The shortest zigzag LEB128 representation of a signed integer. -/
def Normal.ofInt (value : Int) : Normal := Leb128.Normal.ofNat (ZigZag.encode value)

@[simp] theorem Normal.value_ofInt (n : Int) : value (Normal.ofInt n).toLeb128 = n := by
  simp [value, Normal.ofInt]

/-- Normal zigzag LEB128 byte strings are in bijection with integers. -/
def normalEquivInt : Normal ≃ Int where
  toFun n := value n.toLeb128
  invFun := Normal.ofInt
  left_inv n := by
    apply Leb128.Normal.ext
    change Base128.encodeLittle
      (ZigZag.encode (ZigZag.decode (Base128.decodeLittle n.bytes))) = n.bytes
    rw [ZigZag.encode_decode]
    exact n.normal.2.symm
  right_inv := Normal.value_ofInt

end ZigZagLeb128

end Nucleus
