import Nucleus.Cbor.Basic

/-!
# General CBOR data model

Unlike JSON-shaped subsets, general CBOR has recursive map keys and semantic
tags.  The indexed grammar makes every recursion structural while representing
arrays and maps as finite sequences.  A parser can therefore preserve map
order and duplicate keys; semantic well-formedness is an explicit predicate.
-/

namespace Nucleus

/-- Sorts of the structurally recursive CBOR grammar. -/
inductive CborIx where | value | array | map
  deriving DecidableEq

/-- Non-container CBOR items. Float widths and bit payloads are retained. -/
inductive CborPrimitive where
  | integer (value : CborInteger)
  | bytes (value : Bytes)
  | text (value : String)
  | simple (value : UInt8)
  | float16 (bits : UInt16)
  | float32 (bits : UInt32)
  | float64 (bits : UInt64)
  deriving DecidableEq

/-- The complete structural CBOR data model, including tags and arbitrary
values as map keys. -/
inductive CborSyn : CborIx → Type where
  | primitive (value : CborPrimitive) : CborSyn .value
  | array (items : CborSyn .array) : CborSyn .value
  | map (entries : CborSyn .map) : CborSyn .value
  | tag (number : UInt64) (content : CborSyn .value) : CborSyn .value
  | arrayNil : CborSyn .array
  | arrayCons (head : CborSyn .value) (tail : CborSyn .array) : CborSyn .array
  | mapNil : CborSyn .map
  | mapCons (key value : CborSyn .value) (tail : CborSyn .map) : CborSyn .map
  deriving DecidableEq

/-- A complete CBOR value. -/
abbrev Cbor := CborSyn .value

namespace CborSyn

/-- Array contents in wire order. -/
def toArrayList : CborSyn .array → List Cbor
  | .arrayNil => []
  | .arrayCons head tail => head :: tail.toArrayList

/-- Map entries in wire order. -/
def toMapList : CborSyn .map → List (Cbor × Cbor)
  | .mapNil => []
  | .mapCons key value tail => (key, value) :: tail.toMapList

/-- Structural node count. -/
def size : {i : CborIx} → CborSyn i → Nat
  | _, .primitive _ => 1
  | _, .array items => 1 + items.size
  | _, .map entries => 1 + entries.size
  | _, .tag _ content => 1 + content.size
  | _, .arrayNil => 0
  | _, .arrayCons head tail => head.size + tail.size
  | _, .mapNil => 0
  | _, .mapCons key value tail => key.size + value.size + tail.size

/-- Number of direct items in an array tail. -/
def arrayLength : CborSyn .array → Nat
  | .arrayNil => 0
  | .arrayCons _ tail => tail.arrayLength + 1

/-- Number of direct entries in a map tail. -/
def mapLength : CborSyn .map → Nat
  | .mapNil => 0
  | .mapCons _ _ tail => tail.mapLength + 1

end CborSyn

namespace CborPrimitive

/-- CBOR `false`, simple value 20. -/
def false : CborPrimitive := .simple 20
/-- CBOR `true`, simple value 21. -/
def true : CborPrimitive := .simple 21
/-- CBOR `null`, simple value 22. -/
def null : CborPrimitive := .simple 22
/-- CBOR `undefined`, distinct from null and epistemic unknown. -/
def undefined : CborPrimitive := .simple 23

end CborPrimitive

end Nucleus
