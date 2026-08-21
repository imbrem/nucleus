import Nucleus.Cbor.General
import Nucleus.Structured

/-!
# General CBOR containers

List construction and observation belong to the CBOR data model rather than
to any one object schema.  The instances also expose the same operations
through the format-independent `ArrayLike` and `ObjectLike` interfaces.
-/

namespace Nucleus

namespace CborSyn

/-- Build a CBOR array tail from its list view. -/
def arrayOfList : List Cbor → CborSyn .array
  | [] => .arrayNil
  | value :: values => .arrayCons value (arrayOfList values)

/-- Build an arbitrary-key CBOR map tail from its ordered entries. -/
def mapOfList : List (Cbor × Cbor) → CborSyn .map
  | [] => .mapNil
  | (key, value) :: fields => .mapCons key value (mapOfList fields)

/-- Build a text-key CBOR map tail from its ordered entries. -/
def textMapOfList : List (String × Cbor) → CborSyn .map
  | [] => .mapNil
  | (key, value) :: fields =>
      .mapCons (.primitive (.text key)) value (textMapOfList fields)

/-- Observe a map tail as text-key entries, rejecting any non-text key. -/
def textMapToList? : CborSyn .map → Option (List (String × Cbor))
  | .mapNil => some []
  | .mapCons (.primitive (.text key)) value fields =>
      return (key, value) :: (← textMapToList? fields)
  | .mapCons _ _ _ => none

@[simp] theorem arrayOfList_toArrayList (values : List Cbor) :
    (arrayOfList values).toArrayList = values := by
  induction values with
  | nil => simp [arrayOfList, CborSyn.toArrayList]
  | cons value values ih => simp [arrayOfList, CborSyn.toArrayList, ih]

@[simp] theorem mapOfList_toMapList (fields : List (Cbor × Cbor)) :
    (mapOfList fields).toMapList = fields := by
  induction fields with
  | nil => simp [mapOfList, CborSyn.toMapList]
  | cons field fields ih =>
      rcases field with ⟨key, value⟩
      simp [mapOfList, CborSyn.toMapList, ih]

@[simp] theorem textMapToList?_ofList
    (fields : List (String × Cbor)) :
    textMapToList? (textMapOfList fields) = some fields := by
  induction fields with
  | nil => simp [textMapOfList, textMapToList?]
  | cons field fields ih =>
      rcases field with ⟨key, value⟩
      simp [textMapOfList, textMapToList?, ih]

end CborSyn

instance : ArrayLike Cbor where
  array values := .array (CborSyn.arrayOfList values)
  array?
    | .array values => some values.toArrayList
    | _ => none
  array?_array values := by simp

instance : ObjectLike Cbor Cbor where
  object fields := .map (CborSyn.mapOfList fields)
  object?
    | .map fields => some fields.toMapList
    | _ => none
  object?_object fields := by simp

instance : ObjectLike Cbor String where
  object fields := .map (CborSyn.textMapOfList fields)
  object?
    | .map fields => CborSyn.textMapToList? fields
    | _ => none
  object?_object fields := by simp

namespace Cbor

def arrayOfList (values : List Cbor) : Cbor := ArrayLike.array values
def asArray? (value : Cbor) : Option (List Cbor) := ArrayLike.array? value

def mapOfList (fields : List (Cbor × Cbor)) : Cbor :=
  ObjectLike.object fields

def asMap? (value : Cbor) : Option (List (Cbor × Cbor)) :=
  ObjectLike.object? value

def textMapOfList (fields : List (String × Cbor)) : Cbor :=
  ObjectLike.object fields

def asTextMap? (value : Cbor) : Option (List (String × Cbor)) :=
  ObjectLike.object? value

@[simp] theorem asArray?_arrayOfList (values : List Cbor) :
    asArray? (arrayOfList values) = some values := ArrayLike.observe_construct values

@[simp] theorem asMap?_mapOfList (fields : List (Cbor × Cbor)) :
    asMap? (mapOfList fields) = some fields := ObjectLike.observe_construct fields

@[simp] theorem asTextMap?_textMapOfList (fields : List (String × Cbor)) :
    asTextMap? (textMapOfList fields) = some fields := ObjectLike.observe_construct fields

end Cbor

end Nucleus
