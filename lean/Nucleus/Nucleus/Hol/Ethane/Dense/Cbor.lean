import Nucleus.Cbor.Containers
import Nucleus.Hol.Ethane.Dense

/-!
# CBOR for signed dense Ethane arenas

The dictionaries and field names in this file are the exact Serde-facing
representation used by `crates/logic/hol`.
-/

namespace Nucleus.Hol.Ethane.Dense.Cbor

open Nucleus Nucleus.Hol.Ethane.Dense

private def text (value : String) : Nucleus.Cbor := .primitive (.text value)
private def null : Nucleus.Cbor := .primitive .null
private def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  Nucleus.Cbor.arrayOfList values
private def object (fields : List (String × Nucleus.Cbor)) : Nucleus.Cbor :=
  Nucleus.Cbor.textMapOfList fields

def encodeTag : Tag → Nucleus.Cbor
  | .pair => text "pair"
  | .kindStar => text "kind.star"
  | .kindArr => text "kind.arr"
  | .boolTy => text "ty.bool"
  | .arr => text "ty.arr"
  | .tyApp => text "ty.app"
  | .tyLam => text "ty.lam"
  | .tyFv => text "ty.fv"
  | .tyExists => text "tm.ty_exists"
  | .model => text "ty.model"
  | .primFam => text "fam.prim"
  | .primTm => text "tm.prim"
  | .tmFv => text "tm.fv"
  | .app => text "tm.app"
  | .lam => text "tm.lam"
  | .bool => text "tm.bool"
  | .eq => text "tm.eq"
  | .eps => text "tm.eps"

def decodeTag? (value : Nucleus.Cbor) : Option Tag :=
  if value = text "pair" then some .pair
  else if value = text "kind.star" then some .kindStar
  else if value = text "kind.arr" then some .kindArr
  else if value = text "ty.bool" then some .boolTy
  else if value = text "ty.arr" then some .arr
  else if value = text "ty.app" then some .tyApp
  else if value = text "ty.lam" then some .tyLam
  else if value = text "ty.fv" then some .tyFv
  else if value = text "tm.ty_exists" then some .tyExists
  else if value = text "ty.model" then some .model
  else if value = text "fam.prim" then some .primFam
  else if value = text "tm.prim" then some .primTm
  else if value = text "tm.fv" then some .tmFv
  else if value = text "tm.app" then some .app
  else if value = text "tm.lam" then some .lam
  else if value = text "tm.bool" then some .bool
  else if value = text "tm.eq" then some .eq
  else if value = text "tm.eps" then some .eps
  else none

@[simp] theorem decodeTag?_encodeTag (tag : Tag) :
    decodeTag? (encodeTag tag) = some tag := by
  cases tag <;> decide

def encodeUInt64 (value : UInt64) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned value))

def decodeUInt64? : Nucleus.Cbor → Option UInt64
  | .primitive (.integer (.unsigned value)) => some value
  | _ => none

@[simp] theorem decodeUInt64?_encodeUInt64 (value : UInt64) :
    decodeUInt64? (encodeUInt64 value) = some value := rfl

def encodeInt64 (value : Int64) : Nucleus.Cbor :=
  match value.toInt with
  | .ofNat value => .primitive (.integer (.unsigned (UInt64.ofNat value)))
  | .negSucc value => .primitive (.integer (.negative (UInt64.ofNat value)))

def decodeInt64? : Nucleus.Cbor → Option Int64
  | .primitive (.integer (.unsigned value)) =>
      if value.toNat < 2 ^ 63 then some (Int64.ofInt value.toNat) else none
  | .primitive (.integer (.negative value)) =>
      if value.toNat < 2 ^ 63 then some (Int64.ofInt (.negSucc value.toNat)) else none
  | _ => none

@[simp] theorem decodeInt64?_encodeInt64 (value : Int64) :
    decodeInt64? (encodeInt64 value) = some value := by
  have lower := Int64.le_toInt value
  have upper := Int64.toInt_lt value
  cases valueEq : value.toInt with
  | ofNat n =>
      have upper' := upper
      rw [valueEq] at upper'
      have upper'' : (n : Int) < ((2 ^ 63 : Nat) : Int) := by simpa using upper'
      have small : n < 2 ^ 63 := Int.ofNat_lt.mp upper''
      have fits : n < 2 ^ 64 :=
        lt_trans small (Nat.pow_lt_pow_right (by decide) (by decide))
      have converted : (UInt64.ofNat n).toNat = n := by
        change n % 2 ^ 64 = n
        exact Nat.mod_eq_of_lt fits
      rw [encodeInt64, valueEq]
      simp only [decodeInt64?, converted, small, ↓reduceIte]
      have intEq : (n : Int) = value.toInt := valueEq.symm
      rw [intEq, Int64.ofInt_toInt]
  | negSucc n =>
      have small : n < 2 ^ 63 := by omega
      have fits : n < 2 ^ 64 :=
        lt_trans small (Nat.pow_lt_pow_right (by decide) (by decide))
      have converted : (UInt64.ofNat n).toNat = n := by
        change n % 2 ^ 64 = n
        exact Nat.mod_eq_of_lt fits
      rw [encodeInt64, valueEq]
      simp only [decodeInt64?, converted, small, ↓reduceIte]
      have intEq : Int.negSucc n = value.toInt := valueEq.symm
      rw [intEq, Int64.ofInt_toInt]

def encodeScalar : Scalar → Nucleus.Cbor
  | .nat value => encodeUInt64 value
  | .bool false => .primitive .false
  | .bool true => .primitive .true

def decodeScalar? : Nucleus.Cbor → Option Scalar
  | .primitive (.integer (.unsigned value)) => some (.nat value)
  | .primitive (.simple 20) => some (.bool false)
  | .primitive (.simple 21) => some (.bool true)
  | _ => none

@[simp] theorem decodeScalar?_encodeScalar (value : Scalar) :
    decodeScalar? (encodeScalar value) = some value := by
  cases value with
  | nat => rfl
  | bool value => cases value <;> rfl

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

private theorem traverse_encode (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (inverse : ∀ value, decode (encode value) = some value) (values : List α) :
    traverse decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, inverse, ih]

private def optionalField (name : String) (value : Option Nucleus.Cbor) :
    List (String × Nucleus.Cbor) :=
  (value.map fun value => [(name, value)]).getD []

private def encodeSerdeRow (row : SerdeRow) : Nucleus.Cbor :=
  object <| [("tag", encodeTag row.tag),
      ("ixs", array (row.ixs.toList.map encodeInt64))] ++
    optionalField "val" (row.val.map encodeScalar) ++
    optionalField "eq" (row.eq.map encodeInt64) ++
    optionalField "sort" (row.sort.map encodeInt64)

private def allowedRowFields : List String := ["tag", "ixs", "val", "eq", "sort"]

private def decodeOptional (fields : List (String × Nucleus.Cbor))
    (name : String) (decode : Nucleus.Cbor → Option α) : Option (Option α) :=
  match Fields.lookup? name fields with
  | none => some none
  | some value => return some (← decode value)

private def decodeSerdeRow? (value : Nucleus.Cbor) : Option SerdeRow := do
  let fields ← Nucleus.Cbor.asTextMap? value
  if _ : ¬Fields.Unique fields then none else
  if _ : ¬∀ field ∈ fields, field.1 ∈ allowedRowFields then none else
  let tag ← decodeTag? (← Fields.lookup? "tag" fields)
  let indices ← traverse decodeInt64?
    (← Nucleus.Cbor.asArray? (← Fields.lookup? "ixs" fields))
  return {
    tag
    ixs := indices.toArray
    val := ← decodeOptional fields "val" decodeScalar?
    eq := ← decodeOptional fields "eq" decodeInt64?
    sort := ← decodeOptional fields "sort" decodeInt64?
  }

def encodeRow (row : Row) : Nucleus.Cbor := encodeSerdeRow row.toSerde

def decodeRow? (value : Nucleus.Cbor) : Option Row := do
  (← decodeSerdeRow? value).decode

private theorem decodeSerdeRow?_encode (row : SerdeRow) :
    decodeSerdeRow? (encodeSerdeRow row) = some row := by
  rcases row with ⟨tag, ixs, val, eq, sort⟩
  have indices := traverse_encode encodeInt64 decodeInt64?
    decodeInt64?_encodeInt64 ixs.toList
  cases val <;> cases eq <;> cases sort <;>
    simp [decodeSerdeRow?, encodeSerdeRow, optionalField, decodeOptional,
      allowedRowFields, Fields.Unique, Fields.keys, Fields.lookup?,
      decodeTag?_encodeTag, object, array, indices]

@[simp] theorem decodeRow?_encodeRow (row : Row) :
    decodeRow? (encodeRow row) = some row := by
  simp [decodeRow?, encodeRow, decodeSerdeRow?_encode]

private def encodeRows (rows : List Row) : Nucleus.Cbor :=
  array (rows.map encodeRow)

private def decodeRows? (value : Nucleus.Cbor) : Option (List Row) := do
  traverse decodeRow? (← Nucleus.Cbor.asArray? value)

private theorem decodeRows?_encodeRows (rows : List Row) :
    decodeRows? (encodeRows rows) = some rows := by
  have decoded := traverse_encode encodeRow decodeRow?
    decodeRow?_encodeRow rows
  simpa [decodeRows?, encodeRows, array] using decoded

/-- Exact CBOR dictionary emitted by Serde for a root dense arena. -/
def encode (arena : Arena) : Nucleus.Cbor :=
  object [("tag", text "arena.dense"), ("parent", null),
    ("offset", encodeInt64 arena.offset), ("defs", encodeRows arena.defs.toList)]

private def allowedArenaFields : List String := ["tag", "parent", "offset", "defs"]

def decode? (value : Nucleus.Cbor) : Option Arena := do
  let fields ← Nucleus.Cbor.asTextMap? value
  if _ : ¬Fields.Unique fields then none else
  if _ : ¬∀ field ∈ fields, field.1 ∈ allowedArenaFields then none else
  if (← Fields.lookup? "tag" fields) != text "arena.dense" then none else
  if (← Fields.lookup? "parent" fields) != null then none else
  let offset ← decodeInt64? (← Fields.lookup? "offset" fields)
  let defs ← decodeRows? (← Fields.lookup? "defs" fields)
  return ⟨none, offset, defs.toArray⟩

@[simp] theorem decode?_encode (arena : Arena) :
    decode? (encode arena) = some arena := by
  rcases arena with ⟨parent, offset, defs⟩
  cases parent with
  | none =>
      simp [decode?, encode, Fields.Unique, Fields.keys, Fields.lookup?,
        decodeRows?_encodeRows, object, allowedArenaFields]
  | some impossible => exact nomatch impossible

end Nucleus.Hol.Ethane.Dense.Cbor
