import Nucleus.Cbor.General
import Nucleus.Json.Ordered
import Nucleus.Json.Validate

/-!
# CBOR subset embeddings

The small fixed-key APIs reuse `Json`; this module embeds them into general
CBOR. The converse recognizers will remain partial because arbitrary keys,
tags, simple values, and narrower float widths are outside those profiles.
-/

namespace Nucleus

namespace Cbor

private def primitiveOfScalar : StringKeyCborScalar → CborPrimitive
  | .null => .null
  | .bool false => .false
  | .bool true => .true
  | .integer value => .integer value
  | .float64 bits => .float64 bits
  | .text value => .text value
  | .bytes value => .bytes value

private def cborIxOf : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def rawOfStringKey : {i : JsonIx} →
    RawSyn String StringKeyCborScalar i → CborSyn (cborIxOf i)
  | _, .scalar scalar => .primitive (primitiveOfScalar scalar)
  | _, .list items => .array (rawOfStringKey items)
  | _, .map entries => .map (rawOfStringKey entries)
  | _, .nil => .arrayNil
  | _, .cons head tail => .arrayCons (rawOfStringKey head) (rawOfStringKey tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail => .mapCons (.primitive (.text key))
      (rawOfStringKey value) (rawOfStringKey tail)

/-- Total embedding of string-key CBOR into general CBOR. -/
noncomputable def ofStringKey : StringKeyCbor → Cbor
  | value => rawOfStringKey value.toRaw

private def scalarOfPrimitive? : CborPrimitive → Option StringKeyCborScalar
  | .integer value => some (.integer value)
  | .bytes value => some (.bytes value)
  | .text value => some (.text value)
  | .simple 20 => some (.bool false)
  | .simple 21 => some (.bool true)
  | .simple 22 => some .null
  | .float64 bits => some (.float64 bits)
  | _ => none

mutual

private def rawStringKeyValue? : Cbor → Option
    (RawSyn String StringKeyCborScalar .val)
  | .primitive primitive => .scalar <$> scalarOfPrimitive? primitive
  | .array items => .list <$> rawStringKeyArray? items
  | .map entries => .map <$> rawStringKeyMap? entries
  | .tag _ _ => none

private def rawStringKeyArray? : CborSyn .array → Option
    (RawSyn String StringKeyCborScalar .arr)
  | .arrayNil => some .nil
  | .arrayCons head tail =>
      .cons <$> rawStringKeyValue? head <*> rawStringKeyArray? tail

private def rawStringKeyMap? : CborSyn .map → Option
    (RawSyn String StringKeyCborScalar .obj)
  | .mapNil => some .objNil
  | .mapCons (.primitive (.text key)) value tail =>
      .objCons key <$> rawStringKeyValue? value <*> rawStringKeyMap? tail
  | .mapCons _ _ _ => none

end

/-- Partial projection from general CBOR to the string-key JSON-shaped
profile. It rejects tags, non-text keys, unsupported primitives, and duplicate
map keys rather than silently losing information. -/
def toStringKey? (value : Cbor) : Option StringKeyCbor := do
  let raw ← rawStringKeyValue? value
  match raw.validate with
  | .ok result => some result
  | .error _ => none

@[simp] theorem ofStringKey_scalar (scalar : StringKeyCborScalar) :
    ofStringKey (.scalar scalar) = .primitive (primitiveOfScalar scalar) := by
  rfl

end Cbor

end Nucleus
