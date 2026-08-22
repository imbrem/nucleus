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
          required?, decodeOptional, decodeList,
          traverse, encodeValue, decodeValue?, optional, object, array]

@[simp] theorem decodeRow?_encodeRow (row : detail.Row) :
    decodeRow? (encodeRow row) = some row := by
  simp [decodeRow?, decodeRowView?_encodeRow, detail.Row.ofView?_toView]

mutual

def encodeImport : Import → Nucleus.Cbor
  | .null => null
  | .literal arena => encodeArena arena
  | .link link => encodeLink link

def encodeArena : Arena → Nucleus.Cbor
  | .mk imports axs defs ctx assume assert => object [
      ("tag", text "arena"),
      ("imports", array (encodeImports imports)),
      ("axs", array ((axs.sort (· ≤ ·)).map text)),
      ("defs", array (defs.map encodeRow)),
      ("ctx", array ((ctx.sort (· ≤ ·)).map encodeRef)),
      ("assume", array (assume.map encodeMeta)),
      ("assert", array (assert.map encodeMeta))]

def encodeImports : List Import → List Nucleus.Cbor
  | [] => []
  | entry :: entries => encodeImport entry :: encodeImports entries

end

private def decodeArenaUsing? (decodeImport : Nucleus.Cbor → Option Import)
    (value : Nucleus.Cbor) : Option Arena := do
  let fields ← fields? ["tag", "imports", "axs", "defs", "ctx", "assume", "assert"] value
  if (← asText? (← required? "tag" fields)) != "arena" then none else pure ()
  let imports ← decodeList decodeImport (← required? "imports" fields)
  let axs ← decodeList asText? (← required? "axs" fields)
  let defs ← decodeList decodeRow? (← required? "defs" fields)
  let ctx ← decodeList decodeRef? (← required? "ctx" fields)
  let assume ← decodeList decodeMeta? (← required? "assume" fields)
  let assert ← decodeList decodeMeta? (← required? "assert" fields)
  return View.normalize { imports, axs, defs, ctx, assume, assert }

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
  | .mk imports _ _ _ _ _ => importsFuel imports

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
    (defs : List detail.Row) (ctx : Finset Ref) (assume assert : List Meta)
    (importsIH : ImportsSizeBound imports) :
    ArenaSizeBound (.mk imports axs defs ctx assume assert) := by
  have importArrayBound : importsFuel imports ≤ (array (encodeImports imports)).size := by
    rw [size_array]
    exact Nat.le_add_left_of_le importsIH
  simp only [ArenaSizeBound, arenaFuel, encodeArena, size_object, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil]
  omega

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
  rcases arena with ⟨imports, axs, defs, ctx, assume, assert⟩
  intro fuel sufficient
  cases fuel with
  | zero => simp [importFuel] at sufficient
  | succ fuel =>
      have arenaSufficient :
          arenaFuel (.mk imports axs defs ctx assume assert) ≤ fuel := by
        simpa [importFuel, Nat.add_le_add_iff_right] using sufficient
      have encodedNotNull :
          encodeImport (.literal (.mk imports axs defs ctx assume assert)) ≠ null := by
        simp [encodeImport, encodeArena]
      simp only [decodeImportWithFuel?]
      rw [if_neg encodedNotNull]
      simp only [encodeImport]
      have decoded : decodeArenaUsing? (decodeImportWithFuel? fuel)
          (encodeArena (.mk imports axs defs ctx assume assert)) =
          some (.mk imports axs defs ctx assume assert) :=
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

private theorem arenaRoundtrip (imports : List Import) (axs : Finset String)
    (defs : List detail.Row) (ctx : Finset Ref) (assume assert : List Meta)
    (importsIH : ImportsRoundtrip imports) :
    ArenaRoundtrip (.mk imports axs defs ctx assume assert) := by
  intro fuel sufficient
  have axsDecoded :
      traverse asText? ((axs.sort (· ≤ ·)).map text) = some (axs.sort (· ≤ ·)) :=
    traverse_encode text asText? (fun _ => rfl) _
  simp [decodeArenaWithFuel?, decodeArenaUsing?, encodeArena, fields?, field?, required?,
    object, text, asText?, array, decodeList, importsIH fuel sufficient, traverse_encode,
    axsDecoded, View.normalize, Finset.sort_toFinset]

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
