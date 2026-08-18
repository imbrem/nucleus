import Nucleus.Cbor.Integers
import Nucleus.Cbor.Wire
import Nucleus.HolSurface

/-!
# CBOR values for indexed HolE objects

These definitions specify the CBOR values encoded and accepted by the Rust
implementation. Maps may occur in any order, but each recognized field must
occur exactly once. Different encodings may therefore decode to the same
object.
-/

namespace Nucleus.HolSurface.Cbor

open Nucleus

noncomputable section

private def arrayItems : List Nucleus.Cbor → CborSyn .array
  | [] => .arrayNil
  | value :: values => .arrayCons value (arrayItems values)

private def mapItems : List (Nucleus.Cbor × Nucleus.Cbor) → CborSyn .map
  | [] => .mapNil
  | (key, value) :: entries => .mapCons key value (mapItems entries)

def array (values : List Nucleus.Cbor) : Nucleus.Cbor := .array (arrayItems values)

def map (entries : List (String × Nucleus.Cbor)) : Nucleus.Cbor :=
  .map (mapItems (entries.map fun (key, value) => (.primitive (.text key), value)))

def unsigned (value : Nat) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned (UInt64.ofNat value)))

def null : Nucleus.Cbor := .primitive .null

def bytes (value : ByteArray) : Nucleus.Cbor := .primitive (.bytes ⟨value⟩)

private def asArray? : Nucleus.Cbor → Option (List Nucleus.Cbor)
  | .array values => some values.toArrayList
  | _ => none

private def asMap? : Nucleus.Cbor → Option (List (Nucleus.Cbor × Nucleus.Cbor))
  | .map entries => some entries.toMapList
  | _ => none

private def asNat? : Nucleus.Cbor → Option Nat
  | .primitive (.integer (.unsigned value)) => some value.toNat
  | _ => none

private def asUInt32? (value : Nucleus.Cbor) : Option UInt32 := do
  let value ← asNat? value
  if value ≤ UInt32.size - 1 then some (UInt32.ofNat value) else none

private def asInt? : Nucleus.Cbor → Option Int
  | .primitive (.integer (.unsigned value)) => some value.toNat
  | .primitive (.integer (.negative value)) => some (.negSucc value.toNat)
  | _ => none

private def asInt32? (value : Nucleus.Cbor) : Option Int32 := do
  let value ← asInt? value
  if Int32.minValue.toInt ≤ value ∧ value ≤ Int32.maxValue.toInt then
    some (Int32.ofInt value)
  else none

private def valuesFor (name : String) :
    List (Nucleus.Cbor × Nucleus.Cbor) → List Nucleus.Cbor
  | [] => []
  | (.primitive (.text key), value) :: rest =>
      if key = name then value :: valuesFor name rest else valuesFor name rest
  | _ :: rest => valuesFor name rest

/-- Serde rejects duplicate known fields but ignores unknown fields. -/
private def field? (entries : List (Nucleus.Cbor × Nucleus.Cbor))
    (name : String) : Option Nucleus.Cbor :=
  match valuesFor name entries with
  | [value] => some value
  | _ => none

/-- Serde's optional-field behavior: absence is distinct from a duplicate,
which remains a decoding error. -/
private def optionalField? (entries : List (Nucleus.Cbor × Nucleus.Cbor))
    (name : String) : Option (Option Nucleus.Cbor) :=
  match valuesFor name entries with
  | [] => some none
  | [value] => some (some value)
  | _ => none

private def traverse {α : Type} (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

def encodeFormat (format : Format) : Nucleus.Cbor := unsigned format.tag

def decodeFormat? (value : Nucleus.Cbor) : Option Format := do
  match ← asNat? value with
  | 0 => some .blob
  | 1 => some .cborDense
  | 2 => some .cborSparse
  | _ => none

def encodeObjectKind (kind : ObjectKind) : Nucleus.Cbor := unsigned kind.tag

def decodeObjectKind? (value : Nucleus.Cbor) : Option ObjectKind := do
  match ← asNat? value with
  | 0 => some .bytes
  | 1 => some .importTable
  | 2 => some .arena
  | 3 => some .sequent
  | _ => none

def encodeO256 (hash : O256) : Nucleus.Cbor :=
  .primitive (.bytes (Hash32.bytes hash).1)

def decodeO256? : Nucleus.Cbor → Option O256
  | .primitive (.bytes value) =>
      if length : value.length = 32 then some (Hash32.bytes.symm ⟨value, length⟩) else none
  | _ => none

def encodeLink (link : Link) : Nucleus.Cbor := map [
  ("addr", encodeO256 link.addr),
  ("format", encodeFormat link.format),
  ("kind", encodeObjectKind link.kind)]

def decodeLink? (value : Nucleus.Cbor) : Option Link := do
  let entries ← asMap? value
  let addr ← decodeO256? (← field? entries "addr")
  let format ← decodeFormat? (← field? entries "format")
  let kind ← decodeObjectKind? (← field? entries "kind")
  some ⟨addr, format, kind⟩

def encodeLinkRef (link : LinkRef) : Nucleus.Cbor := map [
  ("import", unsigned link.importId.toNat),
  ("format", encodeFormat link.format),
  ("kind", encodeObjectKind link.kind)]

def decodeLinkRef? (value : Nucleus.Cbor) : Option LinkRef := do
  let entries ← asMap? value
  let importId ← asUInt32? (← field? entries "import")
  let format ← decodeFormat? (← field? entries "format")
  let kind ← decodeObjectKind? (← field? entries "kind")
  some ⟨importId, format, kind⟩

private def encodeOptional {α : Type} (encode : α → Nucleus.Cbor) :
    Option α → Nucleus.Cbor
  | none => null
  | some value => encode value

private def decodeOptional {α : Type} (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (Option α) :=
  if value = null then some none else some <$> decode value

def encodeImportTable (table : ImportTable) : Nucleus.Cbor :=
  array (table.map encodeO256)

def decodeImportTable? (value : Nucleus.Cbor) : Option ImportTable := do
  traverse decodeO256? (← asArray? value)

def encodeRef (ref : Ref) : Nucleus.Cbor := unsigned ref.value

def decodeRef? (value : Nucleus.Cbor) : Option Ref := do
  Ref.ofNat? (← asNat? value)

private def exprMap (tag : String) (children : List Ref) (var : Option UInt32 := none)
    (value : Option Bool := none) :
    Nucleus.Cbor :=
  map <| [("tag", .primitive (.text tag)), ("ix", array (children.map encodeRef))] ++
    var.toList.map (fun index => ("var", unsigned index.toNat)) ++
    value.toList.map (fun value => ("value", .primitive (if value then .true else .false)))

def encodeExpr : Expr → Nucleus.Cbor
  | .kindStar => exprMap "KIND_STAR" []
  | .kindArr domain codomain => exprMap "KIND_ARR" [domain, codomain]
  | .tyBool => exprMap "TY_BOOL" []
  | .tyArr domain codomain => exprMap "TY_ARR" [domain, codomain]
  | .tyApp function argument => exprMap "TY_APP" [function, argument]
  | .tyLam domain body => exprMap "TY_LAM" [domain, body]
  | .tyBv index => exprMap "TY_BV" [] (some index)
  | .tySub carrier predicate => exprMap "TY_SUB" [carrier, predicate]
  | .tyExists predicate => exprMap "TY_EXISTS" [predicate]
  | .tyModel predicate => exprMap "TY_MODEL" [predicate]
  | .tmBv index => exprMap "TM_BV" [] (some index)
  | .tmFv name type => exprMap "TM_FV" [type] (some name)
  | .tmApp function argument => exprMap "TM_APP" [function, argument]
  | .tmLam domain body => exprMap "TM_LAM" [domain, body]
  | .tmBool value => exprMap "TM_BOOL" [] none (some value)
  | .tmEq type left right => exprMap "TM_EQ" [type, left, right]
  | .tmEps type predicate => exprMap "TM_EPS" [type, predicate]
  | .tmAbs carrier predicate value => exprMap "TM_ABS" [carrier, predicate, value]
  | .tmRep carrier predicate value => exprMap "TM_REP" [carrier, predicate, value]
  | .tmCast term target => exprMap "TM_CAST" [term, target]

def decodeExpr? (value : Nucleus.Cbor) : Option Expr := do
  let entries ← asMap? value
  let children ← traverse decodeRef? (← asArray? (← field? entries "ix"))
  let var ← optionalField? entries "var"
  let scalar ← optionalField? entries "value"
  match ← field? entries "tag", children, var, scalar with
  | .primitive (.text "KIND_STAR"), [], none, none => some .kindStar
  | .primitive (.text "KIND_ARR"), [domain, codomain], none, none =>
      some (.kindArr domain codomain)
  | .primitive (.text "TY_BOOL"), [], none, none => some .tyBool
  | .primitive (.text "TY_ARR"), [domain, codomain], none, none =>
      some (.tyArr domain codomain)
  | .primitive (.text "TY_APP"), [function, argument], none, none =>
      some (.tyApp function argument)
  | .primitive (.text "TY_LAM"), [domain, body], none, none => some (.tyLam domain body)
  | .primitive (.text "TY_BV"), [], some var, none => some (.tyBv (← asUInt32? var))
  | .primitive (.text "TY_SUB"), [carrier, predicate], none, none =>
      some (.tySub carrier predicate)
  | .primitive (.text "TY_EXISTS"), [predicate], none, none => some (.tyExists predicate)
  | .primitive (.text "TY_MODEL"), [predicate], none, none => some (.tyModel predicate)
  | .primitive (.text "TM_BV"), [], some var, none => some (.tmBv (← asUInt32? var))
  | .primitive (.text "TM_FV"), [type], some var, none =>
      some (.tmFv (← asUInt32? var) type)
  | .primitive (.text "TM_APP"), [function, argument], none, none =>
      some (.tmApp function argument)
  | .primitive (.text "TM_LAM"), [domain, body], none, none => some (.tmLam domain body)
  | .primitive (.text "TM_BOOL"), [], none, some (.primitive (.simple 20)) =>
      some (.tmBool false)
  | .primitive (.text "TM_BOOL"), [], none, some (.primitive (.simple 21)) =>
      some (.tmBool true)
  | .primitive (.text "TM_EQ"), [type, left, right], none, none =>
      some (.tmEq type left right)
  | .primitive (.text "TM_EPS"), [type, predicate], none, none =>
      some (.tmEps type predicate)
  | .primitive (.text "TM_ABS"), [carrier, predicate, value], none, none =>
      some (.tmAbs carrier predicate value)
  | .primitive (.text "TM_REP"), [carrier, predicate, value], none, none =>
      some (.tmRep carrier predicate value)
  | .primitive (.text "TM_CAST"), [term, target], none, none => some (.tmCast term target)
  | _, _, _, _ => none

def encodeSegment (segment : Segment) : Nucleus.Cbor := map [
  ("start", encodeRef segment.start),
  ("end", encodeRef segment.end),
  ("link", encodeLinkRef segment.link),
  ("source_start", encodeRef segment.sourceStart)]

def decodeSegment? (value : Nucleus.Cbor) : Option Segment := do
  let entries ← asMap? value
  let start ← decodeRef? (← field? entries "start")
  let «end» ← decodeRef? (← field? entries "end")
  let link ← decodeLinkRef? (← field? entries "link")
  let sourceStart ← decodeRef? (← field? entries "source_start")
  if nonempty : start.value < «end».value then
    if arenaKind : link.kind = .arena then
      if sourceBound : sourceStart.value + («end».value - start.value - 1) ≤ maxRef then
        some ⟨start, «end», link, sourceStart, nonempty, arenaKind, sourceBound⟩
      else none
    else none
  else none

def encodeArena {V : Type → Type} [TrustedVec V] (arena : Arena V) : Nucleus.Cbor := map [
  ("imports", encodeOptional encodeO256 arena.imports),
  ("segments", array ((TrustedVec.toList arena.segments).map encodeSegment)),
  ("local_base", unsigned arena.localBase.toNat),
  ("defs", array ((TrustedVec.toList arena.defs).map encodeExpr))]

def decodeArena? (value : Nucleus.Cbor) : Option Arena := do
  let entries ← asMap? value
  let imports ← decodeOptional decodeO256? (← field? entries "imports")
  let segments ← traverse decodeSegment? (← asArray? (← field? entries "segments"))
  let localBase ← asUInt32? (← field? entries "local_base")
  let defs ← traverse decodeExpr? (← asArray? (← field? entries "defs"))
  some ⟨imports, segments, localBase, defs⟩

/-- Static and owned arenas share one wire shape. -/
def encodeStaticArena (arena : StaticArena) : Nucleus.Cbor :=
  encodeArena arena

def encodeRelation (relation : Relation) : Nucleus.Cbor := unsigned relation.tag

def decodeRelation? (value : Nucleus.Cbor) : Option Relation := do
  match ← asNat? value with
  | 0 => some .synEq | 1 => some .convEq | 2 => some .tyEq | 3 => some .hasTy
  | 4 => some .imp | 5 => some .eq | 6 => some .hasKind | 7 => some .ne
  | _ => none

private def encodeSRef (ref : SRef) : Nucleus.Cbor :=
  match ref.raw.toInt with
  | .ofNat value => unsigned value
  | .negSucc value => .primitive (.integer (.negative (UInt64.ofNat value)))

private def decodeSRef? (value : Nucleus.Cbor) : Option SRef := do
  let raw ← asInt32? value
  if valid : raw ≠ Int32.minValue then some ⟨raw, valid⟩ else none

private def encodePair (pair : SRef × SRef) : Nucleus.Cbor :=
  array [encodeSRef pair.1, encodeSRef pair.2]

private def decodePair? (value : Nucleus.Cbor) : Option (SRef × SRef) := do
  match ← asArray? value with
  | [left, right] => some (← decodeSRef? left, ← decodeSRef? right)
  | _ => none

private def relationMapItems : RelationTable → List (Nucleus.Cbor × Nucleus.Cbor)
  | [] => []
  | (relation, pairs) :: rest =>
      (encodeRelation relation, array (pairs.map encodePair)) :: relationMapItems rest

def encodeRelationTable (table : RelationTable) : Nucleus.Cbor :=
  .map (mapItems (relationMapItems table))

private def decodeRelationEntries? :
    List (Nucleus.Cbor × Nucleus.Cbor) → Option RelationTable
  | [] => some []
  | (key, value) :: rest => do
      let relation ← decodeRelation? key
      let pairs ← traverse decodePair? (← asArray? value)
      let rest ← decodeRelationEntries? rest
      some ((relation, pairs) :: rest)

def decodeRelationTable? (value : Nucleus.Cbor) : Option RelationTable := do
  decodeRelationEntries? (← asMap? value)

def encodeCtxBody (body : Nucleus.HolSurface.CtxBody) : Nucleus.Cbor := map [
  ("sequents", array (body.sequents.map encodeLinkRef)),
  ("relations", encodeRelationTable body.relations)]

def decodeCtxBody? (value : Nucleus.Cbor) : Option Nucleus.HolSurface.CtxBody := do
  let entries ← asMap? value
  let sequents ← traverse decodeLinkRef? (← asArray? (← field? entries "sequents"))
  let relations ← decodeRelationTable? (← field? entries "relations")
  some ⟨sequents, relations⟩

def encodeCtx (ctx : Nucleus.HolSurface.Ctx) : Nucleus.Cbor := map [
  ("arena", encodeOptional encodeLinkRef ctx.arena),
  ("imports", encodeOptional encodeO256 ctx.imports),
  ("body", encodeCtxBody ctx.body)]

def decodeCtx? (value : Nucleus.Cbor) : Option Nucleus.HolSurface.Ctx := do
  let entries ← asMap? value
  let arena ← decodeOptional decodeLinkRef? (← field? entries "arena")
  let imports ← decodeOptional decodeO256? (← field? entries "imports")
  let body ← decodeCtxBody? (← field? entries "body")
  some ⟨arena, imports, body⟩

def encodeSeq (seq : Nucleus.HolSurface.Seq) : Nucleus.Cbor := map [
  ("arena", encodeOptional encodeLinkRef seq.arena),
  ("imports", encodeOptional encodeO256 seq.imports),
  ("premises", encodeCtxBody seq.premises),
  ("conclusion", encodeCtxBody seq.conclusion)]

def decodeSeq? (value : Nucleus.Cbor) : Option Nucleus.HolSurface.Seq := do
  let entries ← asMap? value
  let arena ← decodeOptional decodeLinkRef? (← field? entries "arena")
  let imports ← decodeOptional decodeO256? (← field? entries "imports")
  let premises ← decodeCtxBody? (← field? entries "premises")
  let conclusion ← decodeCtxBody? (← field? entries "conclusion")
  some ⟨arena, imports, premises, conclusion⟩

/-- An address is correct when it hashes a complete CBOR encoding of the
value. The encoded bytes are a logical witness and are not retained by the
cached wrapper. -/
def HasAddress (value : Nucleus.Cbor) (address : O256) : Prop :=
  ∃ encoded, Nucleus.CborWire.parse? encoded = some value ∧
    Hash32.hash encoded = address

structure CachedArena where
  arena : Arena
  address : O256
  correct : HasAddress (encodeArena arena) address

namespace CachedArena

def link (cached : CachedArena) : Link :=
  ⟨cached.address, .cborDense, .arena⟩

@[simp] theorem link_address (cached : CachedArena) : cached.link.addr = cached.address := rfl

end CachedArena

structure CachedImportTable where
  table : ImportTable
  address : O256
  correct : HasAddress (encodeImportTable table) address

namespace CachedImportTable

/-- Import-table references are bare `O256` values. -/
def link (cached : CachedImportTable) : O256 := cached.address

@[simp] theorem link_eq (cached : CachedImportTable) : cached.link = cached.address := rfl

end CachedImportTable

structure CachedSeq where
  seq : Nucleus.HolSurface.Seq
  address : O256
  correct : HasAddress (encodeSeq seq) address

namespace CachedSeq

def link (cached : CachedSeq) : Link :=
  ⟨cached.address, .cborSparse, .sequent⟩

@[simp] theorem link_address (cached : CachedSeq) : cached.link.addr = cached.address := rfl

end CachedSeq

/-! ## Preferred-encoding round trips -/

@[simp] private theorem arrayItems_toArrayList (values : List Nucleus.Cbor) :
    (arrayItems values).toArrayList = values := by
  induction values with
  | nil => simp [arrayItems, CborSyn.toArrayList]
  | cons value values ih => simp [arrayItems, CborSyn.toArrayList, ih]

@[simp] private theorem mapItems_toMapList
    (entries : List (Nucleus.Cbor × Nucleus.Cbor)) :
    (mapItems entries).toMapList = entries := by
  induction entries with
  | nil => simp [mapItems, CborSyn.toMapList]
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      simp [mapItems, CborSyn.toMapList, ih]

@[simp] private theorem asArray?_array (values : List Nucleus.Cbor) :
    asArray? (array values) = some values := by
  simp [array, asArray?]

@[simp] private theorem asArray?_raw (values : List Nucleus.Cbor) :
    asArray? (.array (arrayItems values)) = some values := by
  simp [asArray?]

@[simp] private theorem asMap?_map (entries : List (String × Nucleus.Cbor)) :
    asMap? (map entries) = some
      (entries.map fun (key, value) => (.primitive (.text key), value)) := by
  simp [map, asMap?]

@[simp] private theorem asMap?_raw (entries : List (Nucleus.Cbor × Nucleus.Cbor)) :
    asMap? (.map (mapItems entries)) = some entries := by
  simp [asMap?]

private theorem traverse_map_roundtrip {α : Type} (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value) (values : List α) :
    traverse decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, roundtrip, ih]

@[simp] theorem decodeFormat?_encode (format : Format) :
    decodeFormat? (encodeFormat format) = some format := by cases format <;> rfl

@[simp] theorem decodeObjectKind?_encode (kind : ObjectKind) :
    decodeObjectKind? (encodeObjectKind kind) = some kind := by cases kind <;> rfl

@[simp] theorem decodeO256?_encode (hash : O256) :
    decodeO256? (encodeO256 hash) = some hash := by
  simp [encodeO256, decodeO256?, (Hash32.bytes hash).2]

@[simp] theorem decodeLink?_encode (link : Link) :
    decodeLink? (encodeLink link) = some link := by
  rcases link with ⟨addr, format, kind⟩
  simp [encodeLink, decodeLink?, field?, valuesFor]

private theorem uint64_uint32 (value : UInt32) :
    (UInt64.ofNat value.toNat).toNat = value.toNat := by
  change value.toNat % 2 ^ 64 = value.toNat
  apply Nat.mod_eq_of_lt
  exact lt_trans value.toNat_lt_size (by decide)

@[simp] private theorem asUInt32?_encoded (value : UInt32) :
    asUInt32? (unsigned value.toNat) = some value := by
  unfold asUInt32?
  have bound : value.toNat ≤ UInt32.size - 1 := Nat.le_pred_of_lt value.toNat_lt_size
  have bound' : value.toNat ≤ 4294967295 := by simpa [UInt32.size] using bound
  simp [asNat?, unsigned, bound', UInt32.ofNat_toNat]

@[simp] theorem decodeLinkRef?_encode (link : LinkRef) :
    decodeLinkRef? (encodeLinkRef link) = some link := by
  rcases link with ⟨importId, format, kind⟩
  simp [encodeLinkRef, decodeLinkRef?, field?, valuesFor]

@[simp] private theorem decodeOptional_encode {α : Type} (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α) (roundtrip : ∀ value, decode (encode value) = some value)
    (notNull : ∀ value, encode value ≠ null) (value : Option α) :
    decodeOptional decode (encodeOptional encode value) = some value := by
  cases value with
  | none => simp [encodeOptional, decodeOptional, null]
  | some value => simp [encodeOptional, decodeOptional, notNull value, roundtrip]

private theorem encodeO256_ne_null (hash : O256) : encodeO256 hash ≠ null := by
  intro equality
  cases equality

private theorem encodeLinkRef_ne_null (link : LinkRef) : encodeLinkRef link ≠ null := by
  simp [encodeLinkRef, map, mapItems, null]

@[simp] private theorem decodeOptionalO256_encode (value : Option O256) :
    decodeOptional decodeO256? (encodeOptional encodeO256 value) = some value :=
  decodeOptional_encode encodeO256 decodeO256? decodeO256?_encode encodeO256_ne_null value

@[simp] private theorem decodeOptionalLinkRef_encode (value : Option LinkRef) :
    decodeOptional decodeLinkRef? (encodeOptional encodeLinkRef value) = some value :=
  decodeOptional_encode encodeLinkRef decodeLinkRef? decodeLinkRef?_encode
    encodeLinkRef_ne_null value

@[simp] theorem decodeImportTable?_encode (table : ImportTable) :
    decodeImportTable? (encodeImportTable table) = some table := by
  simp [encodeImportTable, decodeImportTable?,
    traverse_map_roundtrip encodeO256 decodeO256? decodeO256?_encode]

private theorem uint64_ref (ref : Ref) :
    (UInt64.ofNat ref.value).toNat = ref.value := by
  change ref.value % 2 ^ 64 = ref.value
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt ref.bounded (by decide)

@[simp] theorem decodeRef?_encode (ref : Ref) :
    decodeRef? (encodeRef ref) = some ref := by
  change Ref.ofNat? ((UInt64.ofNat ref.value).toNat) = some ref
  rw [uint64_ref]
  exact Ref.ofNat?_value ref

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
-- Expanding the generic map decoder once per expression constructor is costly.
@[simp] theorem decodeExpr?_encode (expr : Expr) :
    decodeExpr? (encodeExpr expr) = some expr := by
  cases expr
  case tmBool value =>
    cases value <;>
      simp [encodeExpr, exprMap, decodeExpr?, field?, optionalField?, valuesFor, traverse,
        CborPrimitive.false, CborPrimitive.true]
  all_goals
    simp [encodeExpr, exprMap, decodeExpr?, field?, optionalField?, valuesFor, traverse]

@[simp] theorem decodeSegment?_encode (segment : Segment) :
    decodeSegment? (encodeSegment segment) = some segment := by
  rcases segment with ⟨start, end_, link, sourceStart, nonempty, arenaKind, sourceBound⟩
  simp [encodeSegment, decodeSegment?, field?, valuesFor, nonempty, arenaKind, sourceBound]

@[simp] theorem decodeArena?_encode {V : Type → Type} [TrustedVec V] (arena : Arena V) :
    decodeArena? (encodeArena arena) = some arena.toOwned := by
  rcases arena with ⟨imports, segments, localBase, defs⟩
  simp [encodeArena, decodeArena?, Arena.toOwned, field?, valuesFor,
    traverse_map_roundtrip encodeSegment decodeSegment? decodeSegment?_encode,
    traverse_map_roundtrip encodeExpr decodeExpr? decodeExpr?_encode]

@[simp] theorem decodeArena?_encodeStatic (arena : StaticArena) :
    decodeArena? (encodeStaticArena arena) = some arena.toOwned :=
  decodeArena?_encode arena

@[simp] theorem decodeRelation?_encode (relation : Relation) :
    decodeRelation? (encodeRelation relation) = some relation := by cases relation <;> rfl

private theorem asInt?_encodeSRef (ref : SRef) :
    asInt? (encodeSRef ref) = some ref.raw.toInt := by
  have lower := Int32.le_toInt ref.raw
  have upper := Int32.toInt_le ref.raw
  cases representation : ref.raw.toInt with
  | ofNat value =>
      have upper' : (value : Int) ≤ 2 ^ 31 - 1 := by
        simpa [representation, Int32.toInt_maxValue] using upper
      have fits : value < 2 ^ 64 := by
        omega
      have converted : (UInt64.ofNat value).toNat = value := by
        change value % 2 ^ 64 = value
        exact Nat.mod_eq_of_lt fits
      simp [encodeSRef, representation, asInt?, unsigned, converted]
  | negSucc value =>
      have lower' : -(2 : Int) ^ 31 ≤ .negSucc value := by
        simpa [representation] using lower
      have fits : value < 2 ^ 64 := by
        omega
      have converted : (UInt64.ofNat value).toNat = value := by
        change value % 2 ^ 64 = value
        exact Nat.mod_eq_of_lt fits
      simp [encodeSRef, representation, asInt?, converted]

@[simp] private theorem asInt32?_encodeSRef (ref : SRef) :
    asInt32? (encodeSRef ref) = some ref.raw := by
  have lower := Int32.le_toInt ref.raw
  change (-2147483648 : Int) ≤ ref.raw.toInt at lower
  have bounds : Int32.minValue.toInt ≤ ref.raw.toInt ∧
      ref.raw.toInt ≤ Int32.maxValue.toInt := by
    constructor
    · rw [Int32.toInt_minValue]
      exact lower
    · exact Int32.toInt_le ref.raw
  unfold asInt32?
  rw [asInt?_encodeSRef]
  change (if Int32.minValue.toInt ≤ ref.raw.toInt ∧
      ref.raw.toInt ≤ Int32.maxValue.toInt then
    some (Int32.ofInt ref.raw.toInt) else none) = some ref.raw
  rw [if_pos bounds, Int32.ofInt_toInt]

@[simp] private theorem decodeSRef?_encode (ref : SRef) :
    decodeSRef? (encodeSRef ref) = some ref := by
  simp [decodeSRef?, ref.valid]

@[simp] private theorem decodePair?_encode (pair : SRef × SRef) :
    decodePair? (encodePair pair) = some pair := by
  rcases pair with ⟨left, right⟩
  simp [decodePair?, encodePair]

private theorem decodeRelationEntries?_map (table : RelationTable) :
    decodeRelationEntries? (relationMapItems table) = some table := by
  induction table with
  | nil => rfl
  | cons entry table ih =>
      rcases entry with ⟨relation, pairs⟩
      simp [relationMapItems, decodeRelationEntries?, ih,
        traverse_map_roundtrip encodePair decodePair? decodePair?_encode]

@[simp] theorem decodeRelationTable?_encode (table : RelationTable) :
    decodeRelationTable? (encodeRelationTable table) = some table := by
  simp [encodeRelationTable, decodeRelationTable?, decodeRelationEntries?_map]

@[simp] theorem decodeCtx?_encode (ctx : Nucleus.HolSurface.Ctx) :
    decodeCtx? (encodeCtx ctx) = some ctx := by
  rcases ctx with ⟨arena, imports, body⟩
  simp [encodeCtx, decodeCtx?, encodeCtxBody, decodeCtxBody?, field?, valuesFor,
    traverse_map_roundtrip encodeLinkRef decodeLinkRef? decodeLinkRef?_encode]

@[simp] theorem decodeSeq?_encode (seq : Nucleus.HolSurface.Seq) :
    decodeSeq? (encodeSeq seq) = some seq := by
  rcases seq with ⟨arena, imports, premises, conclusion⟩
  simp [encodeSeq, decodeSeq?, encodeCtxBody, decodeCtxBody?, field?, valuesFor,
    traverse_map_roundtrip encodeLinkRef decodeLinkRef? decodeLinkRef?_encode]

end

end Nucleus.HolSurface.Cbor
