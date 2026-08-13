import Nucleus.Cbor.Subsets

/-!
# Definite-length CBOR bounds

Ordinary CBOR encoding is total on finite values because indefinite-length
items can be chunked. RFC 8949 deterministic encoding forbids indefinite
lengths, so it needs every byte/text/array/map length to fit CBOR's 64-bit
argument field. `Reasonable` is the decidable, inductive domain predicate for
that relation; it is not a predicate for CBOR encodability in general.

A later wire-format module should define RFC deterministic encoding as a
relation `RfcDeterministicEncoding : Cbor → Bytes → Prop` and a total chosen
encoder `encode : Cbor → Bytes`. Its central agreement theorem should be:

`Reasonable value → (RfcDeterministicEncoding value bytes ↔ bytes = encode value)`.

Consequently:

* existence and uniqueness of an RFC-related byte string follow immediately
  for reasonable values;
* uniqueness is proved directly by agreement with the same total encoder that
  also handles unreasonable values;
* no byte string is related to an unreasonable value.

Outside this RFC-defined domain, the total encoder can deterministically use
indefinite containers and maximal `2^64 - 1` chunks. That remains valid CBOR,
but is deliberately not called “RFC deterministic encoding”.
-/

namespace Nucleus

namespace CborSyn

/-- Recursive domain on which all lengths required by RFC deterministic
encoding are representable by definite-length heads. -/
inductive Reasonable : {i : CborIx} → CborSyn i → Prop where
  | integer (value : CborInteger) : Reasonable (.primitive (.integer value))
  | bytes (value : Bytes) (fits : value.length ≤ Bytes.maxDefiniteLength) :
      Reasonable (.primitive (.bytes value))
  | text (value : String) (fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength) :
      Reasonable (.primitive (.text value))
  | simple (value : UInt8) : Reasonable (.primitive (.simple value))
  | float16 (bits : UInt16) : Reasonable (.primitive (.float16 bits))
  | float32 (bits : UInt32) : Reasonable (.primitive (.float32 bits))
  | float64 (bits : UInt64) : Reasonable (.primitive (.float64 bits))
  | array (items : CborSyn .array)
      (fits : items.arrayLength ≤ Bytes.maxDefiniteLength)
      (reasonable : Reasonable items) : Reasonable (.array items)
  | map (entries : CborSyn .map)
      (fits : entries.mapLength ≤ Bytes.maxDefiniteLength)
      (reasonable : Reasonable entries) : Reasonable (.map entries)
  | tag (number : UInt64) (content : Cbor)
      (reasonable : Reasonable content) : Reasonable (.tag number content)
  | arrayNil : Reasonable .arrayNil
  | arrayCons (head : Cbor) (tail : CborSyn .array)
      (headReasonable : Reasonable head) (tailReasonable : Reasonable tail) :
      Reasonable (.arrayCons head tail)
  | mapNil : Reasonable .mapNil
  | mapCons (key value : Cbor) (tail : CborSyn .map)
      (keyReasonable : Reasonable key) (valueReasonable : Reasonable value)
      (tailReasonable : Reasonable tail) : Reasonable (.mapCons key value tail)

/-- The refinement can be enforced at API boundaries. A later executable
encoder will supply the structurally recursive Boolean decision procedure
alongside its wire implementation; the data-model layer needs no evaluator. -/
noncomputable instance reasonableDecidable {i : CborIx} (value : CborSyn i) :
    Decidable (Reasonable value) := Classical.propDecidable _

end CborSyn

end Nucleus
