import Nucleus.Cbor.General

/-!
# CBOR integer profiles

The basic CBOR integer range is `-2^64 .. 2^64-1`. Two useful specific data
models refine or extend it: signed 64-bit application integers, and arbitrary
mathematical integers using standard bignum tags 2 and 3 outside the basic
range. Preferred serialization never uses a bignum when a basic integer fits.
-/

namespace Nucleus

/-- Scalar vocabulary whose integer case is restricted by construction to
signed 64-bit values. -/
inductive Int64CborScalar where
  | null
  | bool (value : Bool)
  | integer (value : Int64)
  | float64 (bits : UInt64)
  | text (value : String)
  | bytes (value : Bytes)
  deriving DecidableEq

/-- String-key CBOR restricted to signed 64-bit integer values. -/
abbrev Int64Cbor := Json Int64CborScalar

/-- Scalar vocabulary extending CBOR integers to arbitrary mathematical
integers. -/
inductive BigIntCborScalar where
  | null
  | bool (value : Bool)
  | integer (value : Int)
  | float64 (bits : UInt64)
  | text (value : String)
  | bytes (value : Bytes)
  deriving DecidableEq

/-- String-key CBOR with arbitrary mathematical integers. -/
abbrev BigIntCbor := Json BigIntCborScalar

namespace Cbor

private def ofInt64Integer (value : Int64) : CborInteger :=
  match value.toInt with
  | .ofNat n => .unsigned (UInt64.ofNat n)
  | .negSucc n => .negative (UInt64.ofNat n)

/-- Minimal unsigned big-endian base-256 digits; zero is the empty byte
string, as specified for the bignum tag content. -/
private def magnitudeDigits (n : Nat) : List UInt8 :=
  if _h : n = 0 then []
  else magnitudeDigits (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _h) (by decide)

private def magnitudeBytes (n : Nat) : Bytes :=
  ⟨(magnitudeDigits n).toByteArray⟩

private def ofNatInteger (n : Nat) : Cbor :=
  if n ≤ Bytes.maxDefiniteLength then
    .primitive (.integer (.unsigned (UInt64.ofNat n)))
  else .tag 2 (.primitive (.bytes (magnitudeBytes n)))

private def ofNegSuccInteger (n : Nat) : Cbor :=
  if n ≤ Bytes.maxDefiniteLength then
    .primitive (.integer (.negative (UInt64.ofNat n)))
  else .tag 3 (.primitive (.bytes (magnitudeBytes n)))

/-- Preferred semantic representation of an arbitrary integer: basic major
type 0/1 when it fits, otherwise bignum tag 2/3 over minimal big-endian bytes. -/
def ofInt : Int → Cbor
  | .ofNat n => ofNatInteger n
  | .negSucc n => ofNegSuccInteger n

private def primitiveOfInt64Scalar : Int64CborScalar → CborPrimitive
  | .null => .null
  | .bool false => .false
  | .bool true => .true
  | .integer value => .integer (ofInt64Integer value)
  | .float64 bits => .float64 bits
  | .text value => .text value
  | .bytes value => .bytes value

private def int64IxOf : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def rawOfInt64 : {i : JsonIx} →
    RawSyn String Int64CborScalar i → CborSyn (int64IxOf i)
  | _, .scalar scalar => .primitive (primitiveOfInt64Scalar scalar)
  | _, .list items => .array (rawOfInt64 items)
  | _, .map entries => .map (rawOfInt64 entries)
  | _, .nil => .arrayNil
  | _, .cons head tail => .arrayCons (rawOfInt64 head) (rawOfInt64 tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail => .mapCons (.primitive (.text key))
      (rawOfInt64 value) (rawOfInt64 tail)

/-- Total injection of signed-64-bit CBOR into general CBOR. -/
noncomputable def ofInt64 (value : Int64Cbor) : Cbor := rawOfInt64 value.toRaw

private def rawOfBigInt : {i : JsonIx} →
    RawSyn String BigIntCborScalar i → CborSyn (int64IxOf i)
  | _, .scalar (.integer value) => ofInt value
  | _, .scalar .null => .primitive .null
  | _, .scalar (.bool false) => .primitive .false
  | _, .scalar (.bool true) => .primitive .true
  | _, .scalar (.float64 bits) => .primitive (.float64 bits)
  | _, .scalar (.text value) => .primitive (.text value)
  | _, .scalar (.bytes value) => .primitive (.bytes value)
  | _, .list items => .array (rawOfBigInt items)
  | _, .map entries => .map (rawOfBigInt entries)
  | _, .nil => .arrayNil
  | _, .cons head tail => .arrayCons (rawOfBigInt head) (rawOfBigInt tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail => .mapCons (.primitive (.text key))
      (rawOfBigInt value) (rawOfBigInt tail)

/-- Total injection of arbitrary-integer CBOR into general CBOR. -/
noncomputable def ofBigInt (value : BigIntCbor) : Cbor := rawOfBigInt value.toRaw

end Cbor

end Nucleus
