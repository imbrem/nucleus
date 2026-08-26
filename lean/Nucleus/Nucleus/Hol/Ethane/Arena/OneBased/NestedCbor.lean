import Nucleus.Cbor.Containers
import Nucleus.Cbor.Wire
import Nucleus.Hol.Ethane.Arena.OneBased.Cbor
import Nucleus.Hol.Ethane.Arena.OneBased.Layout

/-!
# CBOR contract for the nested HOL arena

This is the authoritative structural codec for the `arena` wire introduced by
the ambient/column refactor.  Unlike the legacy oracle in `Cbor.lean`, it
models the exact nested Serde maps and their strict field discipline.  Codecs
for already-formalized leaf payloads are reused directly; the nesting,
optional column defaults, ambient predicate representation, and arena
normalization are fixed here.

The boundary of this file is one already-parsed `CborSyn.value`. Rust's
`wire::deserialize` additionally owns the byte-reader boundary and rejects any
byte after the one decoded CBOR item (including a second valid item). Trailing
bytes do not exist in `CborSyn`, so that whole-reader property is intentionally
not restated as a theorem about values here; it is enforced and regression
tested in `crates/logic/hol/src/wire.rs` and `tests/wire_robustness.rs`.
-/

namespace Nucleus.Hol.Ethane.OneBased.NestedCbor

open Nucleus
open Nucleus.Hol.Ethane
open Nucleus.Hol.Ethane.OneBased
open Nucleus.Hol.Ethane.OneBased.Layout

private def text (value : String) : Nucleus.Cbor := .primitive (.text value)
private def unsigned (value : UInt64) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned value))
private def null : Nucleus.Cbor := .primitive (.simple 22)
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

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

private theorem optionBindSome (value : α) (next : α → Option β) :
    (some value).bind next = next value := rfl

private theorem optionDoSome (value : α) (next : α → Option β) :
    (do let result ← (some value : Option α); next result) = next value := rfl

private theorem traverse_encode (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value) (values : List α) :
    traverse decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, roundtrip, ih]

@[simp] private theorem traverse_text (values : List String) :
    traverse asText? (values.map text) = some values := by
  exact traverse_encode text asText? (fun _ => rfl) values

private def decodeList (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (List α) := do
  traverse decode (← Nucleus.Cbor.asArray? value)

@[simp] private theorem decodeList_text (values : List String) :
    decodeList asText? (array (values.map text)) = some values := by
  simp [decodeList, array, traverse_text]

@[simp] private theorem decodeList_map (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (values : List α) :
    decodeList decode (array (values.map encode)) = some values := by
  simp [decodeList, array, traverse_encode encode decode roundtrip]

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

private def optional (name : String) : Option Nucleus.Cbor →
    List (String × Nucleus.Cbor)
  | none => []
  | some value => [(name, value)]

private def encodeRef (reference : Ref) : Nucleus.Cbor := unsigned reference.value
private def decodeRef? (value : Nucleus.Cbor) : Option Ref := do
  Ref.ofUInt64? (← asUnsigned? value)
private def encodeImportId (source : ImportId) : Nucleus.Cbor := unsigned source.value
private def decodeImportId? (value : Nucleus.Cbor) : Option ImportId := do
  ImportId.ofUInt64? (← asUnsigned? value)
private def encodeSynFactId (id : SynFactId) : Nucleus.Cbor := unsigned id.value
private def decodeSynFactId? (value : Nucleus.Cbor) : Option SynFactId := do
  SynFactId.ofUInt64? (← asUnsigned? value)

@[simp] private theorem decodeRef?_encode (reference : Ref) :
    decodeRef? (encodeRef reference) = some reference := by
  simp [decodeRef?, encodeRef, unsigned, asUnsigned?]

@[simp] private theorem decodeImportId?_encode (source : ImportId) :
    decodeImportId? (encodeImportId source) = some source := by
  simp [decodeImportId?, encodeImportId, unsigned, asUnsigned?]

@[simp] private theorem decodeSynFactId?_encode (id : SynFactId) :
    decodeSynFactId? (encodeSynFactId id) = some id := by
  simp [decodeSynFactId?, encodeSynFactId, unsigned, asUnsigned?]

private def encodeNullableRef : Option Ref → Nucleus.Cbor
  | none => null
  | some reference => encodeRef reference

private def decodeNullableRef? : Nucleus.Cbor → Option (Option Ref)
  | .primitive .null => some none
  | value => return some (← decodeRef? value)

@[simp] private theorem decodeNullableRef?_encode (value : Option Ref) :
    decodeNullableRef? (encodeNullableRef value) = some value := by
  cases value with
  | none =>
      simp [decodeNullableRef?, encodeNullableRef, null]
  | some reference =>
      simp [decodeNullableRef?, encodeNullableRef, encodeRef, decodeRef?, unsigned,
        asUnsigned?]

private def encodeColumn (column : Columns.Column Ref) : Nucleus.Cbor :=
  array (column.map encodeNullableRef)
private def decodeColumn? (value : Nucleus.Cbor) : Option (Columns.Column Ref) :=
  decodeList decodeNullableRef? value

@[simp] private theorem decodeColumn?_encode (column : Columns.Column Ref) :
    decodeColumn? (encodeColumn column) = some column := by
  simp [decodeColumn?, encodeColumn, decodeList, array,
    traverse_encode encodeNullableRef decodeNullableRef? decodeNullableRef?_encode]

@[simp] private theorem decodeList_encodeColumn (column : Columns.Column Ref) :
    decodeList decodeNullableRef? (encodeColumn column) = some column :=
  decodeColumn?_encode column

private def decodeDefaultList (decode : Nucleus.Cbor → Option α) :
    Option Nucleus.Cbor → Option (List α)
  | none => some []
  | some value => decodeList decode value

@[simp] private theorem decodeDefaultList_none (decode : Nucleus.Cbor → Option α) :
    decodeDefaultList decode none = some [] := rfl

@[simp] private theorem decodeDefaultList_column_cons (head : Option Ref)
    (tail : List (Option Ref)) :
    decodeDefaultList decodeNullableRef? (some (encodeColumn (head :: tail))) =
      some (head :: tail) := by
  exact decodeColumn?_encode (head :: tail)

private def decodeOptional (decode : Nucleus.Cbor → Option α) :
    Option Nucleus.Cbor → Option (Option α)
  | none => some none
  | some (.primitive .null) => some none
  | some value => return some (← decode value)

@[simp] private theorem decodeOptional_none (decode : Nucleus.Cbor → Option α) :
    decodeOptional decode none = some none := rfl

@[simp] private theorem decodeOptional_encodeSynFactId (id : SynFactId) :
    decodeOptional decodeSynFactId? (some (encodeSynFactId id)) = some (some id) := by
  simp [decodeOptional, encodeSynFactId, decodeSynFactId?, unsigned, asUnsigned?]

private def encodeExpr (expr : detail.Expr) : Nucleus.Cbor :=
  OneBased.Cbor.encodeExpr expr

private def decodeExpr? (value : Nucleus.Cbor) : Option detail.Expr := do
  OneBased.Cbor.decodeExpr? value

@[simp] private theorem decodeExpr?_encode (expr : detail.Expr) :
    decodeExpr? (encodeExpr expr) = some expr := by
  simp [decodeExpr?, encodeExpr]

private def encodeLit (literal : ClassicalMatrix.Lit Ref) : Nucleus.Cbor :=
  match literal.2 with
  | true => unsigned literal.1.value
  | false => .primitive (.integer (.negative
      (UInt64.ofNat (literal.1.value.toNat - 1))))

private def decodeLit? : Nucleus.Cbor → Option (ClassicalMatrix.Lit Ref)
  | .primitive (.integer (.unsigned value)) =>
      return (← Ref.ofUInt64? value, true)
  | .primitive (.integer (.negative argument)) =>
      return (← Ref.ofUInt64? (UInt64.ofNat (argument.toNat + 1)), false)
  | _ => none

@[simp] private theorem decodeLit?_encode (literal : ClassicalMatrix.Lit Ref) :
    decodeLit? (encodeLit literal) = some literal := by
  rcases literal with ⟨reference, polarity⟩
  cases polarity
  · have positive : 0 < reference.value.toNat := by
      have := reference.property.1
      exact UInt64.pos_iff_ne_zero.mpr this
    have upper : reference.value.toNat < 2_147_483_647 := by
      simpa [Ref.value, Ref.maxExclusive] using reference.property.2
    have small : reference.value.toNat - 1 < 2 ^ 64 := by
      omega
    have encodedToNat :
        (UInt64.ofNat (reference.value.toNat - 1)).toNat =
          reference.value.toNat - 1 := by
      exact UInt64.toNat_ofNat'.trans (Nat.mod_eq_of_lt small)
    have restored : UInt64.ofNat
        ((UInt64.ofNat (reference.value.toNat - 1)).toNat + 1) = reference.value := by
      rw [← UInt64.toNat_inj]
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      rw [encodedToNat, Nat.sub_add_cancel (by omega)]
    simp only [encodeLit, decodeLit?]
    rw [restored, Ref.ofUInt64?_value]
    rfl
  · simp [encodeLit, decodeLit?, unsigned]

private def encodeClause (clause : ClassicalMatrix.Clause Ref) : Nucleus.Cbor :=
  array (clause.literals.map encodeLit)
private def decodeClause? (value : Nucleus.Cbor) : Option (ClassicalMatrix.Clause Ref) :=
  return ⟨← decodeList decodeLit? value⟩

@[simp] private theorem encodeClause_ne_null (clause : ClassicalMatrix.Clause Ref) :
    encodeClause clause ≠ null := by
  simp [encodeClause, array, null, Nucleus.Cbor.arrayOfList, ArrayLike.array]

@[simp] private theorem decodeClause?_encode (clause : ClassicalMatrix.Clause Ref) :
    decodeClause? (encodeClause clause) = some clause := by
  cases clause
  simp [decodeClause?, encodeClause, decodeList, array,
    traverse_encode encodeLit decodeLit? decodeLit?_encode]

private def encodeRow (encode : α → Nucleus.Cbor) : Option α → Nucleus.Cbor
  | none => null
  | some row => encode row

private def decodeRow (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (Option α) :=
  if value = null then some none else (decode value).map some

private def decodeRows (decode : Nucleus.Cbor → Option α)
    (value : Nucleus.Cbor) : Option (List (Option α)) := do
  traverse (decodeRow decode) (← Nucleus.Cbor.asArray? value)

private theorem decodeRow_encode (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (notNull : ∀ row, encode row ≠ null)
    (roundtrip : ∀ row, decode (encode row) = some row) (row : Option α) :
    decodeRow decode (encodeRow encode row) = some row := by
  cases row with
  | none => simp [decodeRow, encodeRow]
  | some row => simp [decodeRow, encodeRow, notNull row, roundtrip row]

private theorem decodeRows_encode (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (notNull : ∀ row, encode row ≠ null)
    (roundtrip : ∀ row, decode (encode row) = some row)
    (rows : List (Option α)) :
    decodeRows decode (array (rows.map (encodeRow encode))) = some rows := by
  exact decodeList_map (encodeRow encode) (decodeRow decode)
    (decodeRow_encode encode decode notNull roundtrip) rows

private def encodeCnf (cnf : Layout.WireCnf) : Nucleus.Cbor :=
  array (cnf.rows.map (encodeRow encodeClause))
private def decodeCnf? (value : Nucleus.Cbor) : Option Layout.WireCnf :=
  return ⟨← decodeRows decodeClause? value⟩

@[simp] private theorem decodeCnf?_encode (cnf : Layout.WireCnf) :
    decodeCnf? (encodeCnf cnf) = some cnf := by
  cases cnf
  simp [decodeCnf?, encodeCnf,
    decodeRows_encode encodeClause decodeClause? encodeClause_ne_null decodeClause?_encode]

private def encodeCube (cube : ClassicalMatrix.Cube Ref) : Nucleus.Cbor :=
  array (cube.literals.map encodeLit)
private def decodeCube? (value : Nucleus.Cbor) : Option (ClassicalMatrix.Cube Ref) :=
  return ⟨← decodeList decodeLit? value⟩

@[simp] private theorem encodeCube_ne_null (cube : ClassicalMatrix.Cube Ref) :
    encodeCube cube ≠ null := by
  simp [encodeCube, array, null, Nucleus.Cbor.arrayOfList, ArrayLike.array]

@[simp] private theorem decodeCube?_encode (cube : ClassicalMatrix.Cube Ref) :
    decodeCube? (encodeCube cube) = some cube := by
  cases cube
  simp [decodeCube?, encodeCube, decodeList, array,
    traverse_encode encodeLit decodeLit? decodeLit?_encode]

private def encodeDnf (dnf : Layout.WireDnf) : Nucleus.Cbor :=
  array (dnf.rows.map (encodeRow encodeCube))
private def decodeDnf? (value : Nucleus.Cbor) : Option Layout.WireDnf :=
  return ⟨← decodeRows decodeCube? value⟩

@[simp] private theorem decodeDnf?_encode (dnf : Layout.WireDnf) :
    decodeDnf? (encodeDnf dnf) = some dnf := by
  cases dnf
  simp [decodeDnf?, encodeDnf,
    decodeRows_encode encodeCube decodeCube? encodeCube_ne_null decodeCube?_encode]

private def encodeSequent (fact : Layout.WireSequent) : Nucleus.Cbor :=
  array [encodeCnf fact.left, encodeDnf fact.right]
private def decodeSequent? (value : Nucleus.Cbor) : Option Layout.WireSequent := do
  let [left, right] ← Nucleus.Cbor.asArray? value | none
  return ⟨← decodeCnf? left, ← decodeDnf? right⟩

@[simp] private theorem decodeSequent?_encode (fact : Layout.WireSequent) :
    decodeSequent? (encodeSequent fact) = some fact := by
  cases fact
  simp [decodeSequent?, encodeSequent, array]

@[simp] private theorem decodeList_expr (values : List detail.Expr) :
    decodeList decodeExpr? (array (values.map encodeExpr)) = some values :=
  decodeList_map encodeExpr decodeExpr? decodeExpr?_encode values

@[simp] private theorem decodeList_ref (values : List Ref) :
    decodeList decodeRef? (array (values.map encodeRef)) = some values :=
  decodeList_map encodeRef decodeRef? decodeRef?_encode values

@[simp] private theorem decodeList_sequent
    (values : List Layout.WireSequent) :
    decodeList decodeSequent? (array (values.map encodeSequent)) = some values :=
  decodeList_map encodeSequent decodeSequent? decodeSequent?_encode values

private def encodeAmbPred : Layout.Pred → Nucleus.Cbor
  | .arenaOk source => object [
      ("src", encodeImportId source), ("tag", text "arena.ok")]
  | .holSort source ix sort => object [
      ("ix", encodeRef ix), ("src", encodeImportId source),
      ("tag", text "hol.sort"), ("sort", encodeRef sort)]

private def decodeAmbPred? (value : Nucleus.Cbor) : Option Layout.Pred := do
  let fields ← fields? ["tag", "src", "ix", "sort"] value
  match ← asText? (← required? "tag" fields) with
  | "arena.ok" =>
      if field? "ix" fields = none ∧ field? "sort" fields = none then
        return .arenaOk (← decodeImportId? (← required? "src" fields))
      else none
  | "hol.sort" =>
      return .holSort
        (← decodeImportId? (← required? "src" fields))
        (← decodeRef? (← required? "ix" fields))
        (← decodeRef? (← required? "sort" fields))
  | _ => none

@[simp] theorem decodeAmbPred?_encode (predicate : Layout.Pred) :
    decodeAmbPred? (encodeAmbPred predicate) = some predicate := by
  cases predicate <;>
    simp [decodeAmbPred?, encodeAmbPred, fields?, field?, required?, object, text,
      asText?]

private def encodeAmb (amb : AmbView) : Nucleus.Cbor := object [
  ("ax", array (amb.ax.map text)),
  ("ctx", encodeCnf amb.ctx),
  ("thm", array (amb.thm.map encodeSequent)),
  ("pred", array (amb.pred.map encodeAmbPred))]

private def decodeAmb? (value : Nucleus.Cbor) : Option AmbView := do
  let fields ← fields? ["pred", "ax", "ctx", "thm"] value
  return {
    pred := ← decodeList decodeAmbPred? (← required? "pred" fields)
    ax := ← decodeList asText? (← required? "ax" fields)
    ctx := ← decodeCnf? (← required? "ctx" fields)
    thm := ← decodeList decodeSequent? (← required? "thm" fields)
  }

private def encodePred (pred : PredSection) : Nucleus.Cbor :=
  object [("syl", array (pred.syl.map encodeSequent))]

private def decodePred? (value : Nucleus.Cbor) : Option PredSection := do
  let fields ← fields? ["syl"] value
  return { syl := ← decodeList decodeSequent? (← required? "syl" fields) }

private def encodeSyn (syn : SynView) : Nucleus.Cbor := object <|
  optional "eq" (if syn.eq.isEmpty then none else some (encodeColumn syn.eq)) ++
  optional "conv" (if syn.conv.isEmpty then none else some (encodeColumn syn.conv)) ++
  optional "subst1" (if syn.subst1.isEmpty then none
    else some (array (syn.subst1.map OneBased.Cbor.encodeSynSlot))) ++
  optional "subst1_free" (syn.subst1Free.map encodeSynFactId)

private def decodeSyn? (value : Nucleus.Cbor) : Option SynView := do
  let fields ← fields? ["subst1", "subst1_free", "eq", "conv"] value
  return {
    subst1 := ← decodeDefaultList OneBased.Cbor.decodeSynSlot? (field? "subst1" fields)
    subst1Free := ← decodeOptional decodeSynFactId? (field? "subst1_free" fields)
    eq := ← decodeDefaultList decodeNullableRef? (field? "eq" fields)
    conv := ← decodeDefaultList decodeNullableRef? (field? "conv" fields)
  }

@[simp] private theorem traverse_synSlots (slots : List SynSlot) :
    traverse OneBased.Cbor.decodeSynSlot?
      (slots.map OneBased.Cbor.encodeSynSlot) = some slots := by
  exact traverse_encode OneBased.Cbor.encodeSynSlot OneBased.Cbor.decodeSynSlot?
    OneBased.Cbor.decodeSynSlot?_encode slots

@[simp] private theorem decodeList_synSlots (slots : List SynSlot) :
    decodeList OneBased.Cbor.decodeSynSlot?
      (array (slots.map OneBased.Cbor.encodeSynSlot)) = some slots :=
  decodeList_map OneBased.Cbor.encodeSynSlot OneBased.Cbor.decodeSynSlot?
    OneBased.Cbor.decodeSynSlot?_encode slots

@[simp] private theorem decodeList_synSlots_cons (head : SynSlot) (tail : List SynSlot) :
    decodeList OneBased.Cbor.decodeSynSlot?
      (array (OneBased.Cbor.encodeSynSlot head ::
        tail.map OneBased.Cbor.encodeSynSlot)) = some (head :: tail) := by
  simpa using decodeList_synSlots (head :: tail)

private def encodeHol (hol : HolView) : Nucleus.Cbor := object <|
  [("ax", array (hol.ax.map text))] ++
  optional "eq" (if hol.eq.isEmpty then none else some (encodeColumn hol.eq)) ++
  [("ctx", array (hol.ctx.map encodeRef)),
   ("syn", encodeSyn hol.syn),
   ("thm", array (hol.thm.map encodeSequent)),
   ("defs", array (hol.defs.map encodeExpr))]

private def decodeHol? (value : Nucleus.Cbor) : Option HolView := do
  let fields ← fields? ["defs", "ax", "ctx", "thm", "eq", "syn"] value
  return {
    defs := ← decodeList decodeExpr? (← required? "defs" fields)
    ax := ← decodeList asText? (← required? "ax" fields)
    ctx := ← decodeList decodeRef? (← required? "ctx" fields)
    thm := ← decodeList decodeSequent? (← required? "thm" fields)
    eq := ← decodeDefaultList decodeNullableRef? (field? "eq" fields)
    syn := ← decodeSyn? (← required? "syn" fields)
  }

private def bytesOfO256 (value : O256) : Bytes := ⟨value.bytes.toByteArray⟩
private def o256OfBytes? (value : Bytes) : Option O256 :=
  O256.ofList? value.data.data.toList

private def encodeLink (link : OneBased.Link) : Nucleus.Cbor := object [
  ("tag", text "link"),
  ("blake3", .primitive (.bytes (bytesOfO256 link.blake3))),
  ("format", text "cbor")]

private def decodeLink? (value : Nucleus.Cbor) : Option OneBased.Link := do
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

@[simp] private theorem decodeLink?_encode (link : OneBased.Link) :
    decodeLink? (encodeLink link) = some link := by
  cases link
  simp [decodeLink?, encodeLink, fields?, field?, required?, object, text, asText?]

@[simp] private theorem encodeLink_ne_null (link : OneBased.Link) :
    encodeLink link ≠ null := by
  simp [encodeLink, object, null, Nucleus.Cbor.textMapOfList, ObjectLike.object]

private def encodeViewWithImports (view : Layout.View)
    (imports : List Nucleus.Cbor) : Nucleus.Cbor := object [
  ("amb", encodeAmb view.amb),
  ("hol", encodeHol view.hol),
  ("tag", text "arena"),
  ("pred", encodePred view.pred),
  ("import", array imports)]

mutual

/-- Encode one import using Rust's untagged null/literal/link representation. -/
def encodeImport : Layout.Import → Nucleus.Cbor
  | .null => null
  | .literal arena => encodeArena arena
  | .link link => encodeLink link

/-- Encode a normalized arena, recursively encoding literal imports. -/
def encodeArena : Layout.Arena → Nucleus.Cbor
  | .mk imports amb pred hol =>
      encodeViewWithImports (Layout.Arena.toView (.mk imports amb pred hol))
        (encodeImports imports)

def encodeImports : List Layout.Import → List Nucleus.Cbor
  | [] => []
  | entry :: entries => encodeImport entry :: encodeImports entries

end

@[simp] private theorem encodeImport_null : encodeImport .null = null := rfl
@[simp] private theorem encodeImport_link (link : OneBased.Link) :
    encodeImport (.link link) = encodeLink link := rfl
@[simp] private theorem encodeImport_literal (arena : Layout.Arena) :
    encodeImport (.literal arena) = encodeArena arena := rfl

@[simp] private theorem encodeArena_ne_null (arena : Layout.Arena) :
    encodeArena arena ≠ null := by
  cases arena
  simp [encodeArena, encodeViewWithImports, object, null,
    Nucleus.Cbor.textMapOfList, ObjectLike.object]

mutual

private theorem importDepth_le_encodeSize (entry : Layout.Import) :
    entry.literalDepth ≤ (encodeImport entry).size := by
  cases entry with
  | null => simp [Layout.Import.literalDepth, encodeImport, null, CborSyn.size]
  | link link => simp [Layout.Import.literalDepth]
  | literal arena =>
      simpa [Layout.Import.literalDepth, encodeImport] using arenaDepth_lt_encodeSize arena

private theorem arenaDepth_lt_encodeSize (arena : Layout.Arena) :
    arena.literalDepth < (encodeArena arena).size := by
  cases arena with
  | mk imports amb pred hol =>
      have importsBound := importsDepth_le_encodeSize imports
      apply lt_of_le_of_lt importsBound
      simp [encodeArena, encodeViewWithImports, object, array,
        Nucleus.Cbor.textMapOfList, Nucleus.Cbor.arrayOfList,
        ObjectLike.object, ArrayLike.array, CborSyn.size, CborSyn.textMapOfList]
      omega

private theorem importsDepth_le_encodeSize (imports : List Layout.Import) :
    Layout.Imports.literalDepth imports ≤
      (CborSyn.arrayOfList (encodeImports imports)).size := by
  cases imports with
  | nil => simp [Layout.Imports.literalDepth, encodeImports, CborSyn.arrayOfList, CborSyn.size]
  | cons entry entries =>
      have entryBound := importDepth_le_encodeSize entry
      have entriesBound := importsDepth_le_encodeSize entries
      simp only [Layout.Imports.literalDepth, encodeImports, CborSyn.arrayOfList, CborSyn.size]
      omega

end

/-- Strict structural decoding. `fields?` rejects duplicate and unknown keys;
every non-optional field is fetched with `required?`. -/
private def decodeViewUsing? (decodeImport : Nucleus.Cbor → Option Layout.Import)
    (value : Nucleus.Cbor) : Option Layout.View := do
  let fields ← fields? ["tag", "import", "amb", "pred", "hol"] value
  if (← asText? (← required? "tag" fields)) != "arena" then none else pure ()
  return {
    tag := .arena
    «import» := ← decodeList decodeImport (← required? "import" fields)
    amb := ← decodeAmb? (← required? "amb" fields)
    pred := ← decodePred? (← required? "pred" fields)
    hol := ← decodeHol? (← required? "hol" fields)
  }

mutual

def decodeImportWithFuel? : Nat → Nucleus.Cbor → Option Layout.Import
  | 0, _ => none
  | fuel + 1, value => do
      if value = null then some .null
      else match field? "tag" (← Nucleus.Cbor.asTextMap? value) with
        | some (.primitive (.text "arena")) =>
            return .literal (← (← decodeViewUsing? (decodeImportWithFuel? fuel) value).normalize?)
        | some (.primitive (.text "link")) => return .link (← decodeLink? value)
        | _ => none

def decodeViewWithFuel? (fuel : Nat) (value : Nucleus.Cbor) : Option Layout.View :=
  decodeViewUsing? (decodeImportWithFuel? fuel) value

end

/-- Decode a structural view with CBOR size as a conservative nesting bound. -/
def decodeView? (value : Nucleus.Cbor) : Option Layout.View :=
  decodeViewWithFuel? value.size value

/-- Decode and apply the exact Rust normalization/residency gate. -/
def decodeArena? (value : Nucleus.Cbor) :
    Option Layout.Arena := do
  (← decodeView? value).normalize?

private theorem decodeAmb?_encode (amb : AmbView) :
    decodeAmb? (encodeAmb amb) = some amb := by
  simp [decodeAmb?, encodeAmb, fields?, field?, required?, object, array, decodeList,
    traverse_encode, decodeCnf?_encode, decodeSequent?_encode]

private theorem decodePred?_encode (pred : PredSection) :
    decodePred? (encodePred pred) = some pred := by
  cases pred
  simp [decodePred?, encodePred, fields?, field?, required?, object, array, decodeList,
    traverse_encode]

private theorem decodeSyn?_encode (syn : SynView) :
    decodeSyn? (encodeSyn syn) = some syn := by
  cases syn with
  | mk subst1 subst1Free eq conv =>
      cases subst1 <;> cases subst1Free <;> cases eq <;> cases conv <;>
        simp [decodeSyn?, encodeSyn, fields?, field?, optional, object,
          decodeDefaultList]

private theorem decodeHol?_encode (hol : HolView) :
    decodeHol? (encodeHol hol) = some hol := by
  cases hol with
  | mk defs ax ctx thm eq syn =>
      cases eq <;>
        simp [decodeHol?, encodeHol, fields?, field?, required?, optional, object,
          decodeDefaultList, decodeSyn?_encode]

private theorem decodeViewUsing?_encode (decodeImport : Nucleus.Cbor → Option Layout.Import)
    (view : Layout.View)
    (encodedImports : List Nucleus.Cbor)
    (imports : traverse decodeImport encodedImports = some view.import) :
    decodeViewUsing? decodeImport (encodeViewWithImports view encodedImports) = some view := by
  cases view
  simp [decodeViewUsing?, encodeViewWithImports, fields?, field?, required?, object, text, asText?,
    array, decodeList, imports, decodeAmb?_encode, decodePred?_encode,
    decodeHol?_encode]

/-- Structural decoding followed by Rust's residency/normalization gate is a
round trip whenever the recursively encoded import vector is decoded by the
supplied import decoder. -/
theorem decodeNormalizedUsing?_encode {arena : Layout.Arena}
    (decodeImport : Nucleus.Cbor → Option Layout.Import)
    (encodedImports : List Nucleus.Cbor)
    (imports : traverse decodeImport encodedImports = some arena.imports)
    (wireValid : arena.ColumnsWireValid)
    (classicalValid : arena.ClassicalWireValid)
    (normalized : arena.ColumnsNormalized) :
    (decodeViewUsing? decodeImport
      (encodeViewWithImports arena.toView encodedImports)).bind
        Layout.View.normalize? = some arena := by
  rw [decodeViewUsing?_encode decodeImport arena.toView encodedImports imports]
  exact arena.normalize?_toView wireValid classicalValid normalized

/-! ## Recursive import round trip

These three mutually proved statements follow the mutually recursive arena,
import, and import-list syntax.  The fuel hypothesis is expressed using only
literal-import depth; no reference bound truncates the semantic object.  They
describe the already-parsed `CborSyn` decoder, which has no artificial depth
cutoff.  `Arena.ByteWireCanonical` separately records the concrete Rust byte
decoder's 126-level limit. -/

mutual

theorem decodeImportWithFuel?_encode (entry : Layout.Import)
    (canonical : entry.WireCanonical) (fuel : Nat)
    (enough : entry.literalDepth < fuel) :
    decodeImportWithFuel? fuel (encodeImport entry) = some entry := by
  cases entry with
  | null =>
      cases fuel with
      | zero => simp [Layout.Import.literalDepth] at enough
      | succ fuel => simp [decodeImportWithFuel?, encodeImport, null]
  | link link =>
      cases fuel with
      | zero => simp [Layout.Import.literalDepth] at enough
      | succ fuel =>
          rw [encodeImport_link]
          simp only [decodeImportWithFuel?]
          simp only [if_neg (encodeLink_ne_null link)]
          rw [show (encodeLink link).asTextMap? = some
            [("tag", text "link"),
              ("blake3", .primitive (.bytes (bytesOfO256 link.blake3))),
              ("format", text "cbor")] by
            simp [encodeLink, object]]
          rw [optionDoSome]
          rw [show field? "tag"
            [("tag", text "link"),
              ("blake3", .primitive (.bytes (bytesOfO256 link.blake3))),
              ("format", text "cbor")] =
              some (text "link") by rfl]
          rw [decodeLink?_encode]
          rfl
  | literal arena =>
      cases fuel with
      | zero => simp [Layout.Import.literalDepth] at enough
      | succ fuel =>
          have nestedEnough : arena.literalDepth < fuel := by
            simpa [Layout.Import.literalDepth] using enough
          have decoded := decodeArenaViewWithFuel?_encode arena canonical fuel nestedEnough
          change arena.WireCanonical at canonical
          cases arena with
          | mk imports amb pred hol =>
            change Layout.Imports.WireCanonical imports ∧
              (Layout.Arena.mk imports amb pred hol).ColumnsWireValid ∧
              (Layout.Arena.mk imports amb pred hol).ClassicalWireValid ∧
              (Layout.Arena.mk imports amb pred hol).ColumnsNormalized at canonical
            rcases canonical with ⟨_, columns, classical, normalized⟩
            rw [encodeImport_literal]
            simp only [decodeImportWithFuel?]
            simp only [if_neg (encodeArena_ne_null _)]
            let fields :=
              [("amb", encodeAmb (Layout.Arena.mk imports amb pred hol).toView.amb),
                ("hol", encodeHol (Layout.Arena.mk imports amb pred hol).toView.hol),
                ("tag", text "arena"),
                ("pred", encodePred (Layout.Arena.mk imports amb pred hol).toView.pred),
                ("import", array (encodeImports imports))]
            rw [show (encodeArena (Layout.Arena.mk imports amb pred hol)).asTextMap? =
              some fields by simp [fields, encodeArena, encodeViewWithImports, object]]
            rw [optionDoSome]
            rw [show field? "tag" fields = some (text "arena") by rfl]
            change (do
              let view ← decodeViewUsing? (decodeImportWithFuel? fuel)
                (encodeArena (Layout.Arena.mk imports amb pred hol))
              let decodedArena ← view.normalize?
              pure (Layout.Import.literal decodedArena)) = _
            change decodeViewUsing? (decodeImportWithFuel? fuel)
              (encodeArena (Layout.Arena.mk imports amb pred hol)) =
                some (Layout.Arena.mk imports amb pred hol).toView at decoded
            rw [decoded]
            rw [optionDoSome]
            rw [(Layout.Arena.mk imports amb pred hol).normalize?_toView
              columns classical normalized]
            rfl

theorem decodeArenaViewWithFuel?_encode (arena : Layout.Arena)
    (canonical : arena.WireCanonical) (fuel : Nat)
    (enough : arena.literalDepth < fuel) :
    decodeViewWithFuel? fuel (encodeArena arena) = some arena.toView := by
  cases arena with
  | mk imports amb pred hol =>
      rcases canonical with ⟨importsCanonical, _, _, _⟩
      have decodedImports := decodeImportsWithFuel?_encode imports importsCanonical fuel enough
      unfold decodeViewWithFuel? encodeArena
      exact decodeViewUsing?_encode _ _ _ decodedImports

theorem decodeImportsWithFuel?_encode (imports : List Layout.Import)
    (canonical : Layout.Imports.WireCanonical imports) (fuel : Nat)
    (enough : Layout.Imports.literalDepth imports < fuel) :
    traverse (decodeImportWithFuel? fuel) (encodeImports imports) = some imports := by
  cases imports with
  | nil => rfl
  | cons entry entries =>
      rcases canonical with ⟨entryCanonical, entriesCanonical⟩
      have entryEnough : entry.literalDepth < fuel :=
        lt_of_le_of_lt (Nat.le_max_left _ _) enough
      have entriesEnough : Layout.Imports.literalDepth entries < fuel :=
        lt_of_le_of_lt (Nat.le_max_right _ _) enough
      rw [encodeImports, traverse,
        decodeImportWithFuel?_encode entry entryCanonical fuel entryEnough,
        decodeImportsWithFuel?_encode entries entriesCanonical fuel entriesEnough]
      rfl

end

/-- The parsed-value decoder round-trips every recursively canonical arena.
Its concrete `Cbor.size` fuel is proved sufficient from the encoding tree
itself; no external import-decoder premise or artificial depth cutoff remains. -/
theorem decodeArena?_encode (arena : Layout.Arena)
    (canonical : arena.WireCanonical) :
    decodeArena? (encodeArena arena) = some arena := by
  have enough := arenaDepth_lt_encodeSize arena
  have decoded := decodeArenaViewWithFuel?_encode arena canonical
    (encodeArena arena).size enough
  cases arena with
  | mk imports amb pred hol =>
      change Layout.Imports.WireCanonical imports ∧
        (Layout.Arena.mk imports amb pred hol).ColumnsWireValid ∧
        (Layout.Arena.mk imports amb pred hol).ClassicalWireValid ∧
        (Layout.Arena.mk imports amb pred hol).ColumnsNormalized at canonical
      rcases canonical with ⟨_, columns, classical, normalized⟩
      unfold decodeArena? decodeView?
      rw [decoded]
      exact (Layout.Arena.mk imports amb pred hol).normalize?_toView
        columns classical normalized

/-- The same parsed-value roundtrip specialized to arenas accepted by the
current Rust byte decoder.  The byte parser itself is outside `CborSyn`; its
126-level precondition is retained explicitly rather than redefining semantic
canonicity. -/
theorem decodeArena?_encode_byteWire (arena : Layout.Arena)
    (supported : arena.ByteWireCanonical) :
    decodeArena? (encodeArena arena) = some arena :=
  decodeArena?_encode arena supported.1

/-- Parsed-CBOR model of the executable byte decoder's literal-import budget.
The actual byte parser enforces the same bound through its container recursion
limit; keeping this check explicit separates that resource policy from the
unbounded semantic decoder above. -/
def decodeArenaByte? (value : Nucleus.Cbor) : Option Layout.Arena := do
  let arena ← decodeArena? value
  if arena.literalDepth ≤ Layout.maxLiteralImportDepth then some arena else none

theorem decodeArenaByte?_encode (arena : Layout.Arena)
    (supported : arena.ByteWireCanonical) :
    decodeArenaByte? (encodeArena arena) = some arena := by
  simp [decodeArenaByte?, decodeArena?_encode arena supported.1, supported.2]

/-- Byte-level deterministic CBOR parsing composes with the checked nested
arena decoder whenever the structural encoding fits the definite-length wire
domain. `encodeArena` emits every fixed field map in deterministic key order;
the explicit evidence remains necessary because semantic arenas contain
mathematically unbounded lists and strings. -/
theorem decodeArenaByte?_parse_deterministic_wireNormal (arena : Layout.Arena)
    (supported : arena.ByteWireCanonical)
    (normal : CborWire.WireNormal (encodeArena arena)) :
    (CborWire.parse?
      (CborWire.deterministic ⟨encodeArena arena, normal.reasonable⟩)).bind
        decodeArenaByte? = some arena := by
  rw [CborWire.parse?_deterministic_wireNormal (encodeArena arena) normal]
  exact decodeArenaByte?_encode arena supported

theorem decodeArenaByte?_encode_reject_depth (arena : Layout.Arena)
    (canonical : arena.WireCanonical)
    (tooDeep : Layout.maxLiteralImportDepth < arena.literalDepth) :
    decodeArenaByte? (encodeArena arena) = none := by
  simp [decodeArenaByte?, decodeArena?_encode arena canonical,
    Nat.not_le.mpr tooDeep]

/-- A serialized CNF tombstone is retained at its exact row position. -/
theorem decodeCnf?_leadingNull (cnf : Layout.WireCnf) :
    decodeCnf? (encodeCnf ⟨none :: cnf.rows⟩) = some ⟨none :: cnf.rows⟩ :=
  decodeCnf?_encode _

/-- The DNF half retains the identical positional tombstone. -/
theorem decodeDnf?_leadingNull (dnf : Layout.WireDnf) :
    decodeDnf? (encodeDnf ⟨none :: dnf.rows⟩) = some ⟨none :: dnf.rows⟩ :=
  decodeDnf?_encode _

end Nucleus.Hol.Ethane.OneBased.NestedCbor
