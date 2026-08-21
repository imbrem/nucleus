import Mathlib.Data.List.Basic

/-!
# List-view interfaces for structured values

These classes isolate the common array and ordered-object structure shared by
formats such as raw JSON and general CBOR.  Observers are partial because a
structured value may instead be a scalar or another container kind.
-/

namespace Nucleus

universe u v

variable {Value : Type u} {Key : Type v}

/-- A value format with arrays represented canonically by finite lists. -/
class ArrayLike (Value : Type u) where
  array : List Value → Value
  array? : Value → Option (List Value)
  array?_array : ∀ values, array? (array values) = some values

/-- A value format with ordered object entries.  Order and duplicate keys are
observable at this layer; profiles may impose stronger validity separately. -/
class ObjectLike (Value : Type u) (Key : Type v) where
  object : List (Key × Value) → Value
  object? : Value → Option (List (Key × Value))
  object?_object : ∀ fields, object? (object fields) = some fields

namespace ArrayLike

@[simp] theorem observe_construct [ArrayLike Value] (values : List Value) :
    ArrayLike.array? (ArrayLike.array values : Value) = some values :=
  ArrayLike.array?_array values

theorem array_injective [ArrayLike Value] :
    Function.Injective (ArrayLike.array : List Value → Value) := by
  intro left right equal
  have := congrArg ArrayLike.array? equal
  simpa using this

end ArrayLike

namespace ObjectLike

@[simp] theorem observe_construct [ObjectLike Value Key]
    (fields : List (Key × Value)) :
    ObjectLike.object? (ObjectLike.object fields : Value) = some fields :=
  ObjectLike.object?_object fields

theorem object_injective [ObjectLike Value Key] :
    Function.Injective (ObjectLike.object : List (Key × Value) → Value) := by
  intro left right equal
  have := congrArg
    (ObjectLike.object? (Value := Value) (Key := Key)) equal
  simpa using this

end ObjectLike

/- Generic operations on the ordered field list exposed by `ObjectLike`. -/
namespace Fields

def keys (fields : List (Key × Value)) : List Key := fields.map Prod.fst

def Unique [DecidableEq Key] (fields : List (Key × Value)) : Prop :=
  (keys fields).Nodup

instance [DecidableEq Key] (fields : List (Key × Value)) :
    Decidable (Unique fields) := by
  unfold Unique keys
  infer_instance

/-- First matching field.  Consumers that require dictionary semantics should
first establish `Unique`; raw formats intentionally preserve duplicates. -/
def lookup? [DecidableEq Key] (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (candidate, value) :: fields =>
      if candidate = key then some value else lookup? key fields

/-- Return a value exactly when the requested key occurs once. -/
def lookupUnique? [DecidableEq Key] (key : Key)
    (fields : List (Key × Value)) : Option Value :=
  match fields.filterMap fun (candidate, value) =>
      if candidate = key then some value else none with
  | [value] => some value
  | _ => none

@[simp] theorem lookup?_nil [DecidableEq Key] (key : Key) :
    lookup? (Value := Value) key [] = none := rfl

@[simp] theorem lookup?_cons_self [DecidableEq Key]
    (key : Key) (value : Value) (fields : List (Key × Value)) :
    lookup? key ((key, value) :: fields) = some value := by
  simp [lookup?]

@[simp] theorem lookup?_cons_of_ne [DecidableEq Key]
    {key candidate : Key} (different : candidate ≠ key)
    (value : Value) (fields : List (Key × Value)) :
    lookup? key ((candidate, value) :: fields) = lookup? key fields := by
  simp [lookup?, different]

end Fields

end Nucleus
