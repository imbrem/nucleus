import Nucleus.Json.Raw
import Nucleus.Structured

/-!
# Raw JSON container instances

Raw JSON preserves array order, object order, and duplicate keys, so it has
the same lawful list views as general CBOR.  Extensional JSON uses finite maps
instead and intentionally does not implement this ordered-object interface.
-/

namespace Nucleus

universe u v

variable {Key : Type v} {Scalar : Type u}

instance : ArrayLike (KeyedRawJson Key Scalar) where
  array values := .list (RawSyn.ofList values)
  array?
    | .list values => some values.toList
    | _ => none
  array?_array values := by simp

instance : ObjectLike (KeyedRawJson Key Scalar) Key where
  object fields := .map (RawSyn.ofEntries fields)
  object?
    | .map fields => some fields.toEntries
    | _ => none
  object?_object fields := by simp

end Nucleus
