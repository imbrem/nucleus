import Nucleus.Cbor.Containers
import Nucleus.Hol.Ethane.Arena.OneBased

/-!
# CBOR for one-based dense Ethane arenas

The codec mirrors the private Rust Serde views.  Maps are decoded by field
name, so their order is irrelevant; duplicate, unknown, missing, and
constructor-inappropriate fields are rejected.
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

private def encodeRef (reference : Ref) : Nucleus.Cbor := unsigned reference.value
private def decodeRef? (value : Nucleus.Cbor) : Option Ref := do
  Ref.ofUInt64? (← asUnsigned? value)
private def encodeImportId (source : ImportId) : Nucleus.Cbor := unsigned source.value
private def decodeImportId? (value : Nucleus.Cbor) : Option ImportId := do
  ImportId.ofUInt64? (← asUnsigned? value)

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
  | some value => return some (← decode value)

private def decodeList (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (List α) := do
  traverse decode (← Nucleus.Cbor.asArray? value)

private def encodeValue : detail.Value → Nucleus.Cbor
  | .nat value => unsigned value
  | .bool value => bool value

private def decodeValue? (tag : Tag) (value : Nucleus.Cbor) : Option detail.Value :=
  match tag with
  | .tm .bool => return .bool (← asBool? value)
  | .ty .fv | .ty .model | .tm .tyExists | .tm .fv =>
      return .nat (← asUnsigned? value)
  | _ => none

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

private instance : Inhabited Nucleus.Cbor := ⟨null⟩

mutual

partial def encodeImport : Import → Nucleus.Cbor
  | .null => null
  | .literal arena => encodeArena arena
  | .link link => encodeLink link

partial def encodeArena (arena : Arena) : Nucleus.Cbor :=
  let view := arena.toView
  object [
    ("tag", text "arena"),
    ("imports", array (view.imports.map encodeImport)),
    ("axs", array (view.axs.map text)),
    ("defs", array (view.defs.map encodeRow)),
    ("ctx", array (view.ctx.map encodeRef)),
    ("assume", array (view.assume.map encodeMeta)),
    ("assert", array (view.assert.map encodeMeta))]

end

mutual

partial def decodeImport? (value : Nucleus.Cbor) : Option Import := do
  if value = null then some .null
  else match field? "tag" (← Nucleus.Cbor.asTextMap? value) with
    | some (.primitive (.text "link")) => return .link (← decodeLink? value)
    | some (.primitive (.text "arena")) => return .literal (← decodeArena? value)
    | _ => none

partial def decodeArena? (value : Nucleus.Cbor) : Option Arena := do
  let fields ← fields? ["tag", "imports", "axs", "defs", "ctx", "assume", "assert"] value
  if (← asText? (← required? "tag" fields)) != "arena" then none else pure ()
  let imports ← decodeList decodeImport? (← required? "imports" fields)
  let axs ← decodeList asText? (← required? "axs" fields)
  let defs ← decodeList decodeRow? (← required? "defs" fields)
  let ctx ← decodeList decodeRef? (← required? "ctx" fields)
  let assume ← decodeList decodeMeta? (← required? "assume" fields)
  let assert ← decodeList decodeMeta? (← required? "assert" fields)
  return View.normalize { imports, axs, defs, ctx, assume, assert }

end

set_option maxHeartbeats 1000000 in
-- The exhaustive proof normalizes the strict field parser once for every row shape.
private theorem decodeRowView?_encodeRow (row : detail.Row) :
    decodeRowView? (encodeRow row) = some row.toView := by
  cases row with
  | mk expr eq sort =>
      cases expr <;> cases eq <;> cases sort <;>
        simp [encodeRow, decodeRowView?, rowFields, detail.Row.toView, fields?, field?,
          required?, decodeOptional, decodeList,
          traverse, encodeValue, decodeValue?, optional, object, array]

@[simp] theorem decodeRow?_encodeRow (row : detail.Row) :
    decodeRow? (encodeRow row) = some row := by
  simp [decodeRow?, decodeRowView?_encodeRow, detail.Row.ofView?_toView]

end Nucleus.Hol.Ethane.OneBased.Cbor
