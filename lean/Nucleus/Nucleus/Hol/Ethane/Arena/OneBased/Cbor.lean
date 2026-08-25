import Nucleus.Cbor.Containers
import Nucleus.Hol.Ethane.Arena.OneBased

/-!
# Legacy CBOR oracle for the HOL proof core

The expression-row codec remains useful for golden tests. The arena codec in
this file describes the pre-column proof-core fixture only and is not the
current Rust wire contract. The authoritative current shape is
`OneBased.Layout`: `import` plus nested `amb`, `pred`, and `hol` sections, with
no separate proxy metadata arrays. New table or wire proofs must target that
layout.
-/

namespace Nucleus.Hol.Ethane.OneBased.Cbor

open Nucleus

private def text (value : String) : Nucleus.Cbor := .primitive (.text value)
private def unsigned (value : UInt64) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned value))
private def bool : Bool → Nucleus.Cbor
  | false => .primitive .false
  | true => .primitive .true
private def null : Nucleus.Cbor := .primitive .null
private def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  Nucleus.Cbor.arrayOfList values
private def object (fields : List (String × Nucleus.Cbor)) : Nucleus.Cbor :=
  Nucleus.Cbor.textMapOfList fields

@[simp] private theorem unsigned_ne_null (value : UInt64) :
    unsigned value ≠ null := by
  simp [unsigned, null, Nucleus.CborPrimitive.null]

@[simp] private theorem array_ne_null (values : List Nucleus.Cbor) :
    array values ≠ null := by
  simp [array, null, Nucleus.Cbor.arrayOfList, ArrayLike.array,
    Nucleus.CborPrimitive.null]

@[simp] private theorem bool_ne_null (value : Bool) : bool value ≠ null := by
  cases value <;>
    simp [bool, null, Nucleus.CborPrimitive.false, Nucleus.CborPrimitive.true,
      Nucleus.CborPrimitive.null]

@[simp] private theorem object_ne_null (fields : List (String × Nucleus.Cbor)) :
    object fields ≠ null := by
  simp [object, null, Nucleus.Cbor.textMapOfList, ObjectLike.object]

private def asText? : Nucleus.Cbor → Option String
  | .primitive (.text value) => some value
  | _ => none

private def asUnsigned? : Nucleus.Cbor → Option UInt64
  | .primitive (.integer (.unsigned value)) => some value
  | _ => none

private def asBool? : Nucleus.Cbor → Option Bool
  | .primitive (.simple 20) => some false
  | .primitive (.simple 21) => some true
  | _ => none

@[simp] private theorem asUnsigned?_unsigned (value : UInt64) :
    asUnsigned? (unsigned value) = some value := rfl

@[simp] private theorem asBool?_bool (value : Bool) : asBool? (bool value) = some value := by
  cases value <;> rfl

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

private theorem traverse_encode (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (values : List α) :
    traverse decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, roundtrip, ih]

private def encodeRef (reference : Ref) : Nucleus.Cbor := unsigned reference.value
private def decodeRef? (value : Nucleus.Cbor) : Option Ref := do
  Ref.ofUInt64? (← asUnsigned? value)
private def encodeImportId (source : ImportId) : Nucleus.Cbor := unsigned source.value
private def decodeImportId? (value : Nucleus.Cbor) : Option ImportId := do
  ImportId.ofUInt64? (← asUnsigned? value)
private def encodeSynFactId (id : SynFactId) : Nucleus.Cbor := unsigned id.value
private def decodeSynFactId? (value : Nucleus.Cbor) : Option SynFactId := do
  SynFactId.ofUInt64? (← asUnsigned? value)

@[simp] private theorem encodeRef_ne_null (reference : Ref) :
    encodeRef reference ≠ null := unsigned_ne_null _

@[simp] private theorem encodeImportId_ne_null (source : ImportId) :
    encodeImportId source ≠ null := unsigned_ne_null _

@[simp] private theorem encodeSynFactId_ne_null (id : SynFactId) :
    encodeSynFactId id ≠ null := unsigned_ne_null _

@[simp] private theorem decodeRef?_encode (reference : Ref) :
    decodeRef? (encodeRef reference) = some reference := by
  simp [decodeRef?, encodeRef, unsigned, asUnsigned?]

@[simp] private theorem decodeRef?_unsigned (reference : Ref) :
    decodeRef? (unsigned reference.value) = some reference := by
  simpa [encodeRef] using decodeRef?_encode reference

@[simp] private theorem decodeImportId?_encode (source : ImportId) :
    decodeImportId? (encodeImportId source) = some source := by
  simp [decodeImportId?, encodeImportId, unsigned, asUnsigned?]

@[simp] private theorem decodeImportId?_unsigned (source : ImportId) :
    decodeImportId? (unsigned source.value) = some source := by
  simpa [encodeImportId] using decodeImportId?_encode source

@[simp] private theorem decodeSynFactId?_encode (id : SynFactId) :
    decodeSynFactId? (encodeSynFactId id) = some id := by
  simp [decodeSynFactId?, encodeSynFactId, unsigned, asUnsigned?]

@[simp] private theorem decodeRef?_maxExclusive :
    decodeRef? (unsigned (UInt64.ofNat Ref.maxExclusive)) = none := by
  simp [decodeRef?, unsigned, asUnsigned?]

@[simp] private theorem decodeImportId?_aboveMax :
    decodeImportId? (unsigned (UInt64.ofNat (ImportId.maxInclusive + 1))) = none := by
  change ImportId.ofUInt64? (UInt64.ofNat (ImportId.maxInclusive + 1)) = none
  exact ImportId.ofUInt64?_aboveMax

@[simp] private theorem decodeSynFactId?_aboveMax :
    decodeSynFactId? (unsigned (UInt64.ofNat (SynFactId.maxInclusive + 1))) = none := by
  change SynFactId.ofUInt64? (UInt64.ofNat (SynFactId.maxInclusive + 1)) = none
  exact SynFactId.ofUInt64?_aboveMax

private def optional (name : String) : Option Nucleus.Cbor → List (String × Nucleus.Cbor)
  | none => []
  | some value => [(name, value)]

private def fields? (allowed : List String) (value : Nucleus.Cbor) :
    Option (List (String × Nucleus.Cbor)) := do
  let fields ← Nucleus.Cbor.asTextMap? value
  if (fields.map Prod.fst).Nodup then
    if fields.all fun field => allowed.contains field.1 then some fields else none
  else none

private def field? (name : String) (fields : List (String × Nucleus.Cbor)) :
    Option Nucleus.Cbor :=
  (fields.find? fun field => field.1 == name).map Prod.snd

private def required? (name : String) (fields : List (String × Nucleus.Cbor)) :
    Option Nucleus.Cbor := field? name fields

private def decodeOptional (decode : Nucleus.Cbor → Option α) :
    Option Nucleus.Cbor → Option (Option α)
  | none => some none
  | some value =>
      if value = null then some none
      else return some (← decode value)

@[simp] private theorem decodeOptional_none (decode : Nucleus.Cbor → Option α) :
    decodeOptional decode none = some none := rfl

@[simp] private theorem decodeOptional_encodeRef (reference : Ref) :
    decodeOptional decodeRef? (some (encodeRef reference)) = some (some reference) := by
  simp [decodeOptional]

@[simp] private theorem decodeOptional_encodeImportId (source : ImportId) :
    decodeOptional decodeImportId? (some (encodeImportId source)) = some (some source) := by
  simp [decodeOptional]

@[simp] private theorem decodeOptional_encodeSynFactId (id : SynFactId) :
    decodeOptional decodeSynFactId? (some (encodeSynFactId id)) = some (some id) := by
  simp [decodeOptional]

private def decodeNullable (decode : Nucleus.Cbor → Option α) :
    Nucleus.Cbor → Option (Option α)
  | .primitive .null => some none
  | value => return some (← decode value)

@[simp] private theorem decodeNullable_null (decode : Nucleus.Cbor → Option α) :
    decodeNullable decode null = some none := rfl

private def decodeList (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (List α) := do
  traverse decode (← Nucleus.Cbor.asArray? value)

@[simp] private theorem decodeOptional_encodedRefList (references : List Ref) :
    decodeOptional (decodeList decodeRef?)
      (some (array (references.map encodeRef))) = some (some references) := by
  have decoded :
      decodeList decodeRef? (array (references.map encodeRef)) = some references := by
    simp [decodeList, array,
      traverse_encode encodeRef decodeRef? decodeRef?_encode]
  simp [decodeOptional, decoded]

@[simp] private theorem decodeOptional_encodedRefSingleton (reference : Ref) :
    decodeOptional (decodeList decodeRef?) (some (array [encodeRef reference])) =
      some (some [reference]) := by
  simpa using decodeOptional_encodedRefList [reference]

@[simp] private theorem decodeOptional_encodedRefPair (left right : Ref) :
    decodeOptional (decodeList decodeRef?)
      (some (array [encodeRef left, encodeRef right])) = some (some [left, right]) := by
  simpa using decodeOptional_encodedRefList [left, right]

private def encodeSynRel : SynRel → Nucleus.Cbor
  | .syn => text "syn"
  | .alpha => text "alpha"
  | .conv => text "conv"

private def decodeSynRel? (value : Nucleus.Cbor) : Option SynRel := do
  match ← asText? value with
  | "syn" => some .syn
  | "alpha" => some .alpha
  | "conv" => some .conv
  | _ => none

@[simp] private theorem decodeSynRel?_encode (relation : SynRel) :
    decodeSynRel? (encodeSynRel relation) = some relation := by
  cases relation <;> rfl

private def encodeSynFact (fact : SynFact) : Nucleus.Cbor := object <|
  [("rel", encodeSynRel fact.rel)] ++
    optional "var" (fact.var.map encodeRef) ++
    optional "val" (fact.val.map encodeRef) ++
    [("in", encodeRef fact.input), ("out", encodeRef fact.output)]

private def decodeSynFact? (value : Nucleus.Cbor) : Option SynFact := do
  let fields ← fields? ["rel", "var", "val", "in", "out"] value
  let rel ← decodeSynRel? (← required? "rel" fields)
  let var ← decodeOptional decodeRef? (field? "var" fields)
  let val ← decodeOptional decodeRef? (field? "val" fields)
  let input ← decodeRef? (← required? "in" fields)
  let output ← decodeRef? (← required? "out" fields)
  return { rel, var, val, input, output }

private def encodeSynFree (free : SynFree) : Nucleus.Cbor :=
  object [("next", free.next.map encodeSynFactId |>.getD null)]

private def decodeSynFree? (value : Nucleus.Cbor) : Option SynFree := do
  let fields ← fields? ["next"] value
  let next ← match field? "next" fields with
    | none => some none
    | some value => decodeNullable decodeSynFactId? value
  return ⟨next⟩

/-- Rust uses an untagged enum: fact decoding is attempted before the free
payload.  Required fact fields make the two object shapes disjoint. -/
def encodeSynSlot : SynSlot → Nucleus.Cbor
  | .fact fact => encodeSynFact fact
  | .free free => encodeSynFree free

def decodeSynSlot? (value : Nucleus.Cbor) : Option SynSlot :=
  match decodeSynFact? value with
  | some fact => some (.fact fact)
  | none => return .free (← decodeSynFree? value)

@[simp] private theorem decodeNullable_encodeSynFactId (id : SynFactId) :
    decodeNullable decodeSynFactId? (encodeSynFactId id) = some (some id) := by
  simp [decodeNullable, encodeSynFactId, unsigned, decodeSynFactId?, asUnsigned?]

@[simp] private theorem decodeSynFact?_encode (fact : SynFact) :
    decodeSynFact? (encodeSynFact fact) = some fact := by
  cases fact with
  | mk rel var val input output =>
      cases rel <;> cases var <;> cases val <;>
        simp [decodeSynFact?, encodeSynFact, fields?, field?, required?,
          optional, object]

@[simp] private theorem decodeSynFree?_encode (free : SynFree) :
    decodeSynFree? (encodeSynFree free) = some free := by
  cases free with
  | mk free =>
      cases free <;>
        simp [decodeSynFree?, encodeSynFree, fields?, field?, object]

@[simp] private theorem decodeSynFact?_encodeSynFree (free : SynFree) :
    decodeSynFact? (encodeSynFree free) = none := by
  cases free with
  | mk free =>
      cases free <;>
        simp [decodeSynFact?, encodeSynFree, fields?, field?, required?,
          decodeOptional, object, null]

@[simp] theorem decodeSynSlot?_encode (slot : SynSlot) :
    decodeSynSlot? (encodeSynSlot slot) = some slot := by
  cases slot <;> simp [decodeSynSlot?, encodeSynSlot]

@[simp] private theorem traverse_encodeSynSlots (slots : List SynSlot) :
    traverse decodeSynSlot? (slots.map encodeSynSlot) = some slots :=
  traverse_encode encodeSynSlot decodeSynSlot? decodeSynSlot?_encode slots

@[simp] private theorem traverse_encodeSynSlots_cons (slot : SynSlot)
    (slots : List SynSlot) :
    traverse decodeSynSlot? (encodeSynSlot slot :: slots.map encodeSynSlot) =
      some (slot :: slots) := by
  simpa using traverse_encodeSynSlots (slot :: slots)

@[simp] private theorem decodeList_encodeSynSlots (slots : List SynSlot) :
    decodeList decodeSynSlot? (array (slots.map encodeSynSlot)) = some slots := by
  simp [decodeList, array]

private def encodeValue : detail.Value → Nucleus.Cbor
  | .nat value => unsigned value
  | .bool value => bool value

private def decodeValue? (tag : Tag) (value : Nucleus.Cbor) : Option detail.Value :=
  match tag with
  | .tm .bool => return .bool (← asBool? value)
  | .ty .fv | .ty .model | .tm .tyExists | .tm .fv | .tm .op1 | .tm .op2 =>
      return .nat (← asUnsigned? value)
  | _ => none

@[simp] private theorem decodeOptional_tyFvValue (value : UInt64) :
    decodeOptional (decodeValue? (.ty .fv)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

@[simp] private theorem decodeOptional_modelValue (value : UInt64) :
    decodeOptional (decodeValue? (.ty .model)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

@[simp] private theorem decodeOptional_tyExistsValue (value : UInt64) :
    decodeOptional (decodeValue? (.tm .tyExists)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

@[simp] private theorem decodeOptional_tmFvValue (value : UInt64) :
    decodeOptional (decodeValue? (.tm .fv)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

@[simp] private theorem decodeOptional_boolValue (value : Bool) :
    decodeOptional (decodeValue? (.tm .bool)) (some (bool value)) =
      some (some (.bool value)) := by
  cases value <;> simp [decodeOptional, decodeValue?, asBool?, bool, null,
    Nucleus.CborPrimitive.false, Nucleus.CborPrimitive.true, Nucleus.CborPrimitive.null]

@[simp] private theorem decodeOptional_op1Value (value : UInt64) :
    decodeOptional (decodeValue? (.tm .op1)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

@[simp] private theorem decodeOptional_op2Value (value : UInt64) :
    decodeOptional (decodeValue? (.tm .op2)) (some (unsigned value)) =
      some (some (.nat value)) := by
  simp [decodeOptional, decodeValue?]

private def encodeTag (tag : Tag) : Nucleus.Cbor := text tag.name
private def decodeTag? (value : Nucleus.Cbor) : Option Tag := do
  Tag.ofName? (← asText? value)

@[simp] private theorem decodeTag?_encodeTag (tag : Tag) :
    decodeTag? (encodeTag tag) = some tag := by
  cases tag with
  | kind tag => cases tag <;> rfl
  | ty tag => cases tag <;> rfl
  | tm tag => cases tag <;> rfl

private def rowFields (view : detail.RowView) : List (String × Nucleus.Cbor) :=
  [("tag", encodeTag view.tag)] ++
    optional "ixs" (view.ixs.map fun values => array (values.map encodeRef)) ++
    optional "val" (view.val.map encodeValue) ++
    optional "src" (view.src.map encodeImportId) ++
    optional "ix" (view.ix.map encodeRef) ++
    optional "eq" (view.eq.map encodeRef) ++
    optional "sort" (view.sort.map encodeRef)

def encodeRow (row : detail.Row) : Nucleus.Cbor := object (rowFields row.toView)

private def decodeRowView? (value : Nucleus.Cbor) : Option detail.RowView := do
  let fields ← fields? ["tag", "ixs", "val", "src", "ix", "eq", "sort"] value
  let tag ← decodeTag? (← required? "tag" fields)
  let ixs ← decodeOptional (decodeList decodeRef?) (field? "ixs" fields)
  let val ← decodeOptional (decodeValue? tag) (field? "val" fields)
  let src ← decodeOptional decodeImportId? (field? "src" fields)
  let ix ← decodeOptional decodeRef? (field? "ix" fields)
  let eq ← decodeOptional decodeRef? (field? "eq" fields)
  let sort ← decodeOptional decodeRef? (field? "sort" fields)
  return { tag, ixs, val, src, ix, eq, sort }

def decodeRow? (value : Nucleus.Cbor) : Option detail.Row := do
  detail.Row.ofView? (← decodeRowView? value)

private def encodeMeta : Meta → Nucleus.Cbor
  | .valid source => object [
      ("tag", text "meta.valid"),
      ("src", encodeImportId source)]
  | .wf source foreign sort => object [
      ("tag", text "meta.wf"),
      ("src", encodeImportId source),
      ("ix", encodeRef foreign),
      ("sort", encodeRef sort)]

private def decodeMeta? (value : Nucleus.Cbor) : Option Meta := do
  let fields ← fields? ["tag", "src", "ix", "sort"] value
  match ← asText? (← required? "tag" fields) with
  | "meta.valid" =>
      if field? "ix" fields = none ∧ field? "sort" fields = none then
        return .valid (← decodeImportId? (← required? "src" fields))
      else none
  | "meta.wf" =>
      return .wf
        (← decodeImportId? (← required? "src" fields))
        (← decodeRef? (← required? "ix" fields))
        (← decodeRef? (← required? "sort" fields))
  | _ => none

@[simp] theorem decodeMeta?_encodeMeta (record : Meta) :
    decodeMeta? (encodeMeta record) = some record := by
  cases record <;>
    simp [decodeMeta?, encodeMeta, fields?, field?, required?, object, text, asText?]

private def bytesOfO256 (value : O256) : Bytes := ⟨value.bytes.toByteArray⟩
private def o256OfBytes? (value : Bytes) : Option O256 :=
  O256.ofList? value.data.data.toList

private def encodeLink (link : Link) : Nucleus.Cbor := object [
  ("tag", text "link"),
  ("format", text "cbor"),
  ("blake3", .primitive (.bytes (bytesOfO256 link.blake3)))]

private def decodeLink? (value : Nucleus.Cbor) : Option Link := do
  let fields ← fields? ["tag", "format", "blake3"] value
  if (← asText? (← required? "tag" fields)) != "link" then none else pure ()
  if (← asText? (← required? "format" fields)) != "cbor" then none else pure ()
  let bytes ← match ← required? "blake3" fields with
    | .primitive (.bytes bytes) => some bytes
    | _ => none
  return { blake3 := ← o256OfBytes? bytes }

@[simp] private theorem o256OfBytes?_bytesOfO256 (value : O256) :
    o256OfBytes? (bytesOfO256 value) = some value := by
  simp [o256OfBytes?, bytesOfO256]

@[simp] theorem decodeLink?_encodeLink (link : Link) :
    decodeLink? (encodeLink link) = some link := by
  cases link
  simp [decodeLink?, encodeLink, fields?, field?, required?, object, text, asText?]

set_option maxHeartbeats 1000000 in
-- The exhaustive proof normalizes the strict field parser once for every row shape.
private theorem decodeRowView?_encodeRow (row : detail.Row) :
    decodeRowView? (encodeRow row) = some row.toView := by
  cases row with
  | mk expr eq sort =>
      cases expr <;> cases eq <;> cases sort <;>
        simp [encodeRow, decodeRowView?, rowFields, detail.Row.toView, fields?, field?,
          required?, encodeValue, optional, object]

@[simp] theorem decodeRow?_encodeRow (row : detail.Row) :
    decodeRow? (encodeRow row) = some row := by
  simp [decodeRow?, decodeRowView?_encodeRow, detail.Row.ofView?_toView]

mutual

def encodeImport : Import → Nucleus.Cbor
  | .null => null
  | .literal arena => encodeArena arena
  | .link link => encodeLink link

def encodeArena : Arena → Nucleus.Cbor
  | .mk imports axs defs synFacts synFree ctx assume assert => object <| [
      ("tag", text "arena"),
      ("imports", array (encodeImports imports)),
      ("axs", array ((axs.sort (· ≤ ·)).map text)),
      ("defs", array (defs.map encodeRow))] ++
      optional "syn_facts" (if synFacts.isEmpty then none
        else some (array (synFacts.map encodeSynSlot))) ++
      optional "syn_free" (synFree.map encodeSynFactId) ++ [
      ("ctx", array ((ctx.sort (· ≤ ·)).map encodeRef)),
      ("assume", array (assume.map encodeMeta)),
      ("assert", array (assert.map encodeMeta))]

def encodeImports : List Import → List Nucleus.Cbor
  | [] => []
  | entry :: entries => encodeImport entry :: encodeImports entries

end

private def decodeArenaUsing? (decodeImport : Nucleus.Cbor → Option Import)
    (value : Nucleus.Cbor) : Option Arena := do
  let fields ← fields? ["tag", "imports", "axs", "defs", "syn_facts", "syn_free",
    "ctx", "assume", "assert"] value
  if (← asText? (← required? "tag" fields)) != "arena" then none else pure ()
  let imports ← decodeList decodeImport (← required? "imports" fields)
  let axs ← decodeList asText? (← required? "axs" fields)
  let defs ← decodeList decodeRow? (← required? "defs" fields)
  let synFacts ← match field? "syn_facts" fields with
    | none => some []
    | some facts => decodeList decodeSynSlot? facts
  let synFree ← decodeOptional decodeSynFactId? (field? "syn_free" fields)
  let ctx ← decodeList decodeRef? (← required? "ctx" fields)
  let assume ← decodeList decodeMeta? (← required? "assume" fields)
  let assert ← decodeList decodeMeta? (← required? "assert" fields)
  return View.normalize { imports, axs, defs, synFacts, synFree, ctx, assume, assert }

def decodeImportWithFuel? : Nat → Nucleus.Cbor → Option Import
  | 0, _ => none
  | fuel + 1, value => do
      if value = null then some .null
      else match field? "tag" (← Nucleus.Cbor.asTextMap? value) with
        | some (.primitive (.text "link")) => return .link (← decodeLink? value)
        | some (.primitive (.text "arena")) =>
            return .literal (← decodeArenaUsing? (decodeImportWithFuel? fuel) value)
        | _ => none

/-- Decode an arena with a bound on nested literal imports. -/
def decodeArenaWithFuel? (fuel : Nat) (value : Nucleus.Cbor) : Option Arena :=
  decodeArenaUsing? (decodeImportWithFuel? fuel) value

private theorem size_array (values : List Nucleus.Cbor) :
    (array values).size = 1 + (values.map Nucleus.CborSyn.size).sum := by
  simp only [array, Nucleus.Cbor.arrayOfList, ArrayLike.array, Nucleus.CborSyn.size,
    Nat.add_left_cancel_iff]
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [Nucleus.CborSyn.arrayOfList, Nucleus.CborSyn.size, ih]

private theorem size_object (fields : List (String × Nucleus.Cbor)) :
    (object fields).size =
      1 + (fields.map fun field => 1 + field.2.size).sum := by
  simp only [object, Nucleus.Cbor.textMapOfList, ObjectLike.object,
    Nucleus.CborSyn.size, Nat.add_left_cancel_iff]
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rcases field with ⟨key, value⟩
      simp [Nucleus.CborSyn.textMapOfList, Nucleus.CborSyn.size, ih,
        Nat.add_assoc, Nat.add_left_comm]

mutual

private def importFuel : Import → Nat
  | .null => 1
  | .literal arena => arenaFuel arena + 1
  | .link _ => 1

private def arenaFuel : Arena → Nat
  | .mk imports _ _ _ _ _ _ _ => importsFuel imports

private def importsFuel : List Import → Nat
  | [] => 0
  | entry :: entries => max (importFuel entry) (importsFuel entries)

end

private def ImportSizeBound (entry : Import) : Prop :=
  importFuel entry ≤ (encodeImport entry).size

private def ArenaSizeBound (arena : Arena) : Prop :=
  arenaFuel arena + 1 ≤ (encodeArena arena).size

private def ImportsSizeBound (entries : List Import) : Prop :=
  importsFuel entries ≤
    (List.map Nucleus.CborSyn.size (encodeImports entries)).sum

private theorem nullSizeBound : ImportSizeBound .null := by
  simp [ImportSizeBound, importFuel, encodeImport, null, Nucleus.CborSyn.size]

private theorem literalSizeBound (arena : Arena) (ih : ArenaSizeBound arena) :
    ImportSizeBound (.literal arena) := by
  simpa [ImportSizeBound, ArenaSizeBound, importFuel, encodeImport] using ih

private theorem linkSizeBound (link : Link) : ImportSizeBound (.link link) := by
  simp [ImportSizeBound, importFuel, encodeImport, encodeLink, size_object]

private theorem nilSizeBound : ImportsSizeBound [] := by
  simp [ImportsSizeBound, importsFuel, encodeImports]

private theorem consSizeBound (head : Import) (tail : List Import)
    (headIH : ImportSizeBound head) (tailIH : ImportsSizeBound tail) :
    ImportsSizeBound (head :: tail) := by
  change importFuel head ≤ (encodeImport head).size at headIH
  change importsFuel tail ≤
    (List.map Nucleus.CborSyn.size (encodeImports tail)).sum at tailIH
  change max (importFuel head) (importsFuel tail) ≤
    (encodeImport head).size +
      (List.map Nucleus.CborSyn.size (encodeImports tail)).sum
  rw [Nat.max_le]
  constructor
  · omega
  · omega

private theorem arenaSizeBound (imports : List Import) (axs : Finset String)
    (defs : List detail.Row) (synFacts : List SynSlot) (synFree : Option SynFactId)
    (ctx : Finset Ref) (assume assert : List Meta)
    (importsIH : ImportsSizeBound imports) :
    ArenaSizeBound (.mk imports axs defs synFacts synFree ctx assume assert) := by
  have importArrayBound : importsFuel imports ≤ (array (encodeImports imports)).size := by
    rw [size_array]
    exact Nat.le_add_left_of_le importsIH
  cases synFacts <;> cases synFree <;>
    simp [ArenaSizeBound, arenaFuel, encodeArena, size_object, optional] <;> omega

private theorem arenaFuel_lt_size (arena : Arena) :
    arenaFuel arena < (encodeArena arena).size := by
  have bound : ArenaSizeBound arena := by
    exact Arena.rec
      (motive_1 := ImportSizeBound)
      (motive_2 := ArenaSizeBound)
      (motive_3 := ImportsSizeBound)
      nullSizeBound literalSizeBound linkSizeBound arenaSizeBound
      nilSizeBound consSizeBound arena
  exact bound

private theorem importFuel_le_size (entry : Import) :
    importFuel entry ≤ (encodeImport entry).size := by
  exact Import.rec
    (motive_1 := ImportSizeBound)
    (motive_2 := ArenaSizeBound)
    (motive_3 := ImportsSizeBound)
    nullSizeBound literalSizeBound linkSizeBound arenaSizeBound
    nilSizeBound consSizeBound entry

/-- Decode a raw import. The structural CBOR size bounds literal nesting. -/
def decodeImport? (value : Nucleus.Cbor) : Option Import :=
  decodeImportWithFuel? value.size value

/-- Decode a raw arena. The structural CBOR size bounds literal nesting. -/
def decodeArena? (value : Nucleus.Cbor) : Option Arena :=
  decodeArenaWithFuel? value.size value


private def ImportRoundtrip (entry : Import) : Prop :=
  ∀ fuel, importFuel entry ≤ fuel →
    decodeImportWithFuel? fuel (encodeImport entry) = some entry

private def ArenaRoundtrip (arena : Arena) : Prop :=
  ∀ fuel, arenaFuel arena ≤ fuel →
    decodeArenaWithFuel? fuel (encodeArena arena) = some arena

private def ImportsRoundtrip (entries : List Import) : Prop :=
  ∀ fuel, importsFuel entries ≤ fuel →
    traverse (decodeImportWithFuel? fuel) (encodeImports entries) = some entries

private theorem nullRoundtrip : ImportRoundtrip .null := by
  intro fuel sufficient
  cases fuel with
  | zero => simp [importFuel] at sufficient
  | succ fuel => simp [decodeImportWithFuel?, encodeImport, null]

private theorem literalRoundtrip (arena : Arena) (ih : ArenaRoundtrip arena) :
    ImportRoundtrip (.literal arena) := by
  rcases arena with ⟨imports, axs, defs, synFacts, synFree, ctx, assume, assert⟩
  intro fuel sufficient
  cases fuel with
  | zero => simp [importFuel] at sufficient
  | succ fuel =>
      have arenaSufficient :
          arenaFuel (.mk imports axs defs synFacts synFree ctx assume assert) ≤ fuel := by
        simpa [importFuel, Nat.add_le_add_iff_right] using sufficient
      have encodedNotNull :
          encodeImport (.literal
            (.mk imports axs defs synFacts synFree ctx assume assert)) ≠ null := by
        simp [encodeImport, encodeArena]
      simp only [decodeImportWithFuel?]
      rw [if_neg encodedNotNull]
      simp only [encodeImport]
      have decoded : decodeArenaUsing? (decodeImportWithFuel? fuel)
          (encodeArena (.mk imports axs defs synFacts synFree ctx assume assert)) =
          some (.mk imports axs defs synFacts synFree ctx assume assert) :=
        ih fuel arenaSufficient
      simpa [encodeArena, object, field?, text] using
        congrArg (fun value => value.bind (fun imported => some (Import.literal imported)))
          decoded

private theorem linkRoundtrip (link : Link) : ImportRoundtrip (.link link) := by
  rcases link with ⟨blake3⟩
  intro fuel sufficient
  cases fuel with
  | zero => simp [importFuel] at sufficient
  | succ fuel =>
      have encodedNotNull : encodeImport (.link { blake3 }) ≠ null := by
        simp [encodeImport, encodeLink]
      simp only [decodeImportWithFuel?]
      rw [if_neg encodedNotNull]
      simp only [encodeImport]
      simpa [encodeLink, object, field?, text] using
        congrArg (fun value => value.bind (fun link => some (Import.link link)))
          (decodeLink?_encodeLink { blake3 })

private theorem nilRoundtrip : ImportsRoundtrip [] := by
  intro _ _
  rfl

private theorem consRoundtrip (head : Import) (tail : List Import)
    (headIH : ImportRoundtrip head) (tailIH : ImportsRoundtrip tail) :
    ImportsRoundtrip (head :: tail) := by
  intro fuel sufficient
  have headSufficient : importFuel head ≤ fuel :=
    le_trans (Nat.le_max_left _ _) sufficient
  have tailSufficient : importsFuel tail ≤ fuel :=
    le_trans (Nat.le_max_right _ _) sufficient
  simp [encodeImports, traverse, headIH fuel headSufficient, tailIH fuel tailSufficient]

set_option maxHeartbeats 2000000 in
-- The arena proof expands the strict parser for all four cache-field cases.
private theorem arenaRoundtrip (imports : List Import) (axs : Finset String)
    (defs : List detail.Row) (synFacts : List SynSlot) (synFree : Option SynFactId)
    (ctx : Finset Ref) (assume assert : List Meta)
    (importsIH : ImportsRoundtrip imports) :
    ArenaRoundtrip (.mk imports axs defs synFacts synFree ctx assume assert) := by
  intro fuel sufficient
  have axsDecoded :
      traverse asText? ((axs.sort (· ≤ ·)).map text) = some (axs.sort (· ≤ ·)) :=
    traverse_encode text asText? (fun _ => rfl) _
  cases synFacts <;> cases synFree <;>
    simp (config := { maxSteps := 1000000 })
      [decodeArenaWithFuel?, decodeArenaUsing?, encodeArena, fields?, field?, required?,
      object, text, asText?, array, decodeList, importsIH fuel sufficient, traverse_encode,
      axsDecoded, View.normalize, Finset.sort_toFinset, optional]

@[simp] theorem decodeImportWithFuel?_encodeImport (entry : Import) (fuel : Nat)
    (sufficient : importFuel entry ≤ fuel) :
    decodeImportWithFuel? fuel (encodeImport entry) = some entry := by
  exact Import.rec
    (motive_1 := ImportRoundtrip)
    (motive_2 := ArenaRoundtrip)
    (motive_3 := ImportsRoundtrip)
    nullRoundtrip literalRoundtrip linkRoundtrip arenaRoundtrip
    nilRoundtrip consRoundtrip entry fuel sufficient

@[simp] theorem decodeArenaWithFuel?_encodeArena (arena : Arena) (fuel : Nat)
    (sufficient : arenaFuel arena ≤ fuel) :
    decodeArenaWithFuel? fuel (encodeArena arena) = some arena := by
  exact Arena.rec
    (motive_1 := ImportRoundtrip)
    (motive_2 := ArenaRoundtrip)
    (motive_3 := ImportsRoundtrip)
    nullRoundtrip literalRoundtrip linkRoundtrip arenaRoundtrip
    nilRoundtrip consRoundtrip arena fuel sufficient

@[simp] theorem decodeImport?_encodeImport (entry : Import) :
    decodeImport? (encodeImport entry) = some entry := by
  apply decodeImportWithFuel?_encodeImport
  exact importFuel_le_size entry

@[simp] theorem decodeArena?_encodeArena (arena : Arena) :
    decodeArena? (encodeArena arena) = some arena := by
  apply decodeArenaWithFuel?_encodeArena
  exact Nat.le_of_lt (arenaFuel_lt_size arena)

end Nucleus.Hol.Ethane.OneBased.Cbor
