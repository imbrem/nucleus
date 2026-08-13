import Nucleus.Cbor.Subsets

/-!
# Definite-length CBOR bounds

Ordinary CBOR encoding is total on finite values because indefinite-length
items can be chunked. Deterministic encoding forbids indefinite lengths, so it
needs every byte/text/array/map length to fit CBOR's 64-bit argument field.
`Reasonable` states exactly those recursive data-model bounds, independently
of any particular encoder implementation.
-/

namespace Nucleus

namespace CborSyn

private def lengthFits (length : Nat) : Prop := length ≤ Bytes.maxDefiniteLength

/-- Recursive domain on which a deterministic, definite-length encoder has
representable container and string lengths. -/
def Reasonable : {i : CborIx} → CborSyn i → Prop
  | _, .primitive (.bytes bytes) => lengthFits bytes.length
  | _, .primitive (.text text) => lengthFits text.toUTF8.size
  | _, .primitive _ => True
  | _, .array items => lengthFits items.arrayLength ∧ items.Reasonable
  | _, .map entries => lengthFits entries.mapLength ∧ entries.Reasonable
  | _, .tag _ content => content.Reasonable
  | _, .arrayNil => True
  | _, .arrayCons head tail => head.Reasonable ∧ tail.Reasonable
  | _, .mapNil => True
  | _, .mapCons key value tail =>
      key.Reasonable ∧ value.Reasonable ∧ tail.Reasonable

/-- A relation describing the domain of deterministic definite-length
encoding, before committing to a byte-level encoder. -/
def DeterministicallyEncodable (value : Cbor) : Prop := value.Reasonable

theorem deterministicallyEncodable_of_reasonable {value : Cbor}
    (h : value.Reasonable) : DeterministicallyEncodable value := h

end CborSyn

end Nucleus
