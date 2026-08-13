import Nucleus.Cbor.General
import Nucleus.Json.Ordered

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

@[simp] theorem ofStringKey_scalar (scalar : StringKeyCborScalar) :
    ofStringKey (.scalar scalar) = .primitive (primitiveOfScalar scalar) := by
  rfl

end Cbor

end Nucleus
