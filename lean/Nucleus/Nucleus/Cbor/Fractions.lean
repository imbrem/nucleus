import Nucleus.Cbor.Integers
import Nucleus.Number.Radix

/-!
# CBOR decimal fractions and bigfloats

RFC 8949 tags 4 and 5 contain exactly `[exponent, mantissa]`. Tag 4 denotes
`mantissa * 10^exponent`; tag 5 denotes `mantissa * 2^exponent`. The exponent
must use a basic CBOR integer, while the mantissa may use bignum tags 2/3.
-/

namespace Nucleus

/-- JSON-shaped CBOR scalars extended with exact decimal and dyadic values. -/
inductive FractionCborScalar where
  | null
  | bool (value : Bool)
  | integer (value : Int)
  | decimal (value : DecimalFractionRep)
  | dyadic (value : DyadicRep)
  | float64 (bits : UInt64)
  | text (value : String)
  | bytes (value : Bytes)
  deriving DecidableEq

/-- String-key CBOR with arbitrary integers, decimal fractions, and bigfloats. -/
abbrev FractionCbor := Json FractionCborScalar

namespace Cbor

/-- Convert an arbitrary integer to a basic CBOR integer when it is in the
basic range `-2^64 .. 2^64-1`. -/
def basicInteger? : Int → Option CborInteger
  | .ofNat n =>
      if n ≤ Bytes.maxDefiniteLength then some (.unsigned (UInt64.ofNat n)) else none
  | .negSucc n =>
      if n ≤ Bytes.maxDefiniteLength then some (.negative (UInt64.ofNat n)) else none

private def pair (first second : Cbor) : Cbor :=
  .array (.arrayCons first (.arrayCons second .arrayNil))

/-- Valid tag-4 representation. Failure means only that the exponent is
outside the basic CBOR integer range; the mantissa is unrestricted. -/
def ofDecimal? (number : DecimalFractionRep) : Option Cbor := do
  let exponent ← basicInteger? number.exponent
  some (.tag 4 (pair (.primitive (.integer exponent)) (ofInt number.mantissa)))

/-- Valid tag-5 representation. Failure means only that the exponent is
outside the basic CBOR integer range; the mantissa is unrestricted. -/
def ofDyadic? (number : DyadicRep) : Option Cbor := do
  let exponent ← basicInteger? number.exponent
  some (.tag 5 (pair (.primitive (.integer exponent)) (ofInt number.mantissa)))

private def ofFractionScalar? : FractionCborScalar → Option Cbor
  | .null => some (.primitive .null)
  | .bool false => some (.primitive .false)
  | .bool true => some (.primitive .true)
  | .integer value => some (ofInt value)
  | .decimal value => ofDecimal? value
  | .dyadic value => ofDyadic? value
  | .float64 bits => some (.primitive (.float64 bits))
  | .text value => some (.primitive (.text value))
  | .bytes value => some (.primitive (.bytes value))

private def fractionIxOf : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def rawOfFraction? : {i : JsonIx} → RawSyn String FractionCborScalar i →
    Option (CborSyn (fractionIxOf i))
  | _, .scalar scalar => ofFractionScalar? scalar
  | _, .list items => .array <$> rawOfFraction? items
  | _, .map entries => .map <$> rawOfFraction? entries
  | _, .nil => some .arrayNil
  | _, .cons head tail => .arrayCons <$> rawOfFraction? head <*> rawOfFraction? tail
  | _, .objNil => some .mapNil
  | _, .objCons key value tail => .mapCons (.primitive (.text key))
      <$> rawOfFraction? value <*> rawOfFraction? tail

/-- Inject the exact-fraction profile into general CBOR. Failure occurs exactly
when some decimal/dyadic exponent is outside the basic CBOR integer range. -/
noncomputable def ofFraction? (value : FractionCbor) : Option Cbor :=
  rawOfFraction? value.toRaw

@[simp] theorem basicInteger?_ofNat {n : Nat}
    (h : n ≤ Bytes.maxDefiniteLength) :
    basicInteger? (.ofNat n) = some (.unsigned (UInt64.ofNat n)) := by
  simp [basicInteger?, h]

@[simp] theorem basicInteger?_negSucc {n : Nat}
    (h : n ≤ Bytes.maxDefiniteLength) :
    basicInteger? (.negSucc n) = some (.negative (UInt64.ofNat n)) := by
  simp [basicInteger?, h]

end Cbor

end Nucleus
