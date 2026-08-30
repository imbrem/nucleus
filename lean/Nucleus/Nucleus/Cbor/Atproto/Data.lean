import Nucleus.Cbor.Atproto.Cid
import Nucleus.Cbor.Drisl
import Nucleus.Json.Equiv
import Nucleus.Json.Validate
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex

/-!
# Extensional AT Protocol data model

The semantic model is extensional: arrays are finite indexed families and
objects are finite maps, so object member order is unobservable and duplicate
keys are unrepresentable.  DRISL encoding chooses one raw representative by
ordering object keys by their complete length-first CBOR text encoding.

The CID policy is a parameter.  `Value Cid.Policy.atproto` is exactly the
AT Protocol model; `Value Cid.Policy.nucleus` adds BLAKE3 links while retaining
the same data and wire rules.
-/

namespace Nucleus.Atproto

/-- A text value which fits one definite CBOR text-string item. -/
@[ext]
structure Text where
  value : String
  fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength

deriving instance DecidableEq for Text

/-- A byte value which fits one definite CBOR byte-string item. -/
@[ext]
structure ByteString where
  value : Bytes
  fits : value.length ≤ Bytes.maxDefiniteLength

deriving instance DecidableEq for ByteString

/-- Signed 64-bit membership expressed in CBOR's two argument polarities. -/
def Integer.Valid : CborInteger → Prop
  | .unsigned argument | .negative argument =>
      argument ≤ Nucleus.Cbor.Drisl.int64ArgumentMax

instance (value : CborInteger) : Decidable (Integer.Valid value) := by
  cases value <;> unfold Integer.Valid <;> infer_instance

/-- An exact signed 64-bit integer in CBOR argument form. -/
@[ext]
structure Integer where
  value : CborInteger
  valid : Integer.Valid value

deriving instance DecidableEq for Integer

/-- A CID already checked against the selected data-model policy. -/
abbrev Link (policy : Cid.Policy) :=
  {cid : Cid // policy.accepts cid = true}

/-- Scalar leaves of the AT Protocol data model.  Floats are absent by type. -/
inductive Scalar (policy : Cid.Policy) where
  | null
  | bool (value : Bool)
  | integer (value : Integer)
  | text (value : Text)
  | bytes (value : ByteString)
  | link (value : Link policy)
  deriving DecidableEq

/-- Length-first deterministic key-order code. -/
private instance : LinearOrder UInt8 :=
  LinearOrder.lift' UInt8.toFin fun _ _ => UInt8.eq_of_toFin_eq

def Text.orderCode (text : Text) : Nat ×ₗ List UInt8 :=
  let bytes := CborWire.canonicalTextKeyBytes text.value
  toLex (bytes.length, bytes)

theorem Text.orderCode_injective : Function.Injective Text.orderCode := by
  intro left right equal
  apply Text.ext
  apply CborWire.canonicalTextKeyBytes_injective left.fits right.fits
  exact congrArg (fun code => (ofLex code).2) equal

/-- Object keys use the historical length-first CBOR text-key order, not
Lean's ordinary `String` order. -/
instance : LinearOrder Text :=
  LinearOrder.lift' Text.orderCode Text.orderCode_injective

theorem Text.lt_iff_deterministicTextKeyLt (left right : Text) :
    left < right ↔ CborWire.DeterministicTextKeyLt left.value right.value := by
  rw [CborWire.deterministicTextKeyLt_iff]
  change Text.orderCode left < Text.orderCode right ↔ _
  simp only [Text.orderCode, Prod.Lex.toLex_lt_toLex]

private theorem textValues_inDeterministicOrder :
    ∀ (keys : List Text), keys.Pairwise (fun left right => left < right) →
      CborWire.TextKeysInDeterministicOrder (keys.map Text.value)
  | [], _ => trivial
  | [_], _ => trivial
  | left :: right :: rest, sorted => by
      have parts := List.pairwise_cons.mp sorted
      rw [CborWire.TextKeysInDeterministicOrder.eq_def]
      exact ⟨Text.lt_iff_deterministicTextKeyLt left right |>.mp
          (parts.1 right (by simp)),
        textValues_inDeterministicOrder (right :: rest) parts.2⟩

private theorem textValues_distinct (keys : List Text) (distinct : keys.Nodup) :
    CborWire.TextKeysDistinct (keys.map Text.value) := by
  unfold CborWire.TextKeysDistinct
  rw [List.map_map]
  exact distinct.map fun left right equal => by
    apply Text.ext
    exact CborWire.canonicalTextKeyBytes_injective left.fits right.fits equal

/-- Extensional arrays and maps over AT Protocol scalars. -/
abbrev Value (policy : Cid.Policy) := Json (Scalar policy) Text

/-- Strict AT Protocol values. -/
abbrev BlessedValue := Value Cid.Policy.atproto

/-- Migration values admitting the explicit BLAKE3 CID extension. -/
abbrev NucleusValue := Value Cid.Policy.nucleus

namespace Value

private def scalarToCbor {policy : Cid.Policy} : Scalar policy → Cbor
  | .null => .primitive .null
  | .bool false => .primitive .false
  | .bool true => .primitive .true
  | .integer value => .primitive (.integer value.value)
  | .text value => .primitive (.text value.value)
  | .bytes value => .primitive (.bytes value.value)
  | .link value => .tag 42 (.primitive (.bytes value.1.tag42Payload))

private abbrev cborIx : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def rawToCbor {policy : Cid.Policy} : {i : JsonIx} →
    RawSyn Text (Scalar policy) i → CborSyn (cborIx i)
  | _, .scalar value => scalarToCbor value
  | _, .list values => .array (rawToCbor values)
  | _, .map entries => .map (rawToCbor entries)
  | _, .nil => .arrayNil
  | _, .cons head tail => .arrayCons (rawToCbor head) (rawToCbor tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail =>
      .mapCons (.primitive (.text key.value)) (rawToCbor value)
        (rawToCbor tail)

/-- Canonical CBOR tree representative of one extensional value.  Object
members are enumerated using `Text`'s length-first key order. -/
noncomputable def toCbor {policy : Cid.Policy} (value : Value policy) : Cbor :=
  rawToCbor value.toRaw

@[simp] private theorem rawToCbor_ofList {policy : Cid.Policy}
    (values : List (KeyedRawJson Text (Scalar policy))) :
    rawToCbor (RawSyn.ofList values) =
      CborSyn.arrayOfList (values.map rawToCbor) := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [RawSyn.ofList, rawToCbor, CborSyn.arrayOfList, ih]

@[simp] private theorem rawToCbor_ofEntries {policy : Cid.Policy}
    (entries : List (Text × KeyedRawJson Text (Scalar policy))) :
    rawToCbor (RawSyn.ofEntries entries) =
      CborSyn.textMapOfList
        (entries.map fun entry =>
          (entry.1.value, @rawToCbor policy .val entry.2)) := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨key, value⟩
      simp [RawSyn.ofEntries, rawToCbor, CborSyn.textMapOfList, ih]

@[simp] theorem toCbor_list {policy : Cid.Policy} (n : Nat)
    (elems : Fin n → Value policy) :
    toCbor (.list n elems) =
      .array (CborSyn.arrayOfList (List.ofFn fun i => toCbor (elems i))) := by
  unfold toCbor
  rw [Json.toRaw_list]
  simp only [rawToCbor]
  rw [rawToCbor_ofList, List.map_ofFn]
  rfl

@[simp] theorem toCbor_map {policy : Cid.Policy} (keys : Finset Text)
    (vals : {key // key ∈ keys} → Value policy) :
    toCbor (.map keys vals) =
      .map (CborSyn.textMapOfList
        ((keys.sort (fun left right => left ≤ right)).attach.map fun key =>
          (key.1.value,
            toCbor (vals ⟨key.1, (Finset.mem_sort _).mp key.2⟩)))) := by
  unfold toCbor
  rw [Json.toRaw_map]
  simp only [rawToCbor]
  rw [rawToCbor_ofEntries]
  simp [List.map_map, Function.comp_def]

private def text? (value : String) : Option Text :=
  if fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength then some ⟨value, fits⟩
  else none

private def bytes? (value : Bytes) : Option ByteString :=
  if fits : value.length ≤ Bytes.maxDefiniteLength then some ⟨value, fits⟩
  else none

private def integer? (value : CborInteger) : Option Integer :=
  if valid : Integer.Valid value then some ⟨value, valid⟩ else none

private def link? (policy : Cid.Policy) (value : Bytes) : Option (Link policy) := do
  let cid ← Cid.parseTag42Payload? value
  if accepted : policy.accepts cid = true then some ⟨cid, accepted⟩ else none

private def scalarFromCbor? (policy : Cid.Policy) : Cbor → Option (Scalar policy)
  | .primitive (.simple 22) => some .null
  | .primitive (.simple 20) => some (.bool false)
  | .primitive (.simple 21) => some (.bool true)
  | .primitive (.integer value) => .integer <$> integer? value
  | .primitive (.text value) => .text <$> text? value
  | .primitive (.bytes value) => .bytes <$> bytes? value
  | .tag 42 (.primitive (.bytes value)) => .link <$> link? policy value
  | _ => none

mutual
  /-- Recover raw AT Protocol syntax from a CBOR tree.  Duplicate-key rejection
  is deliberately left to `RawSyn.validate`, keeping parsing and map policy
  separate. -/
  def fromCbor? (policy : Cid.Policy) (value : Cbor) :
      Option (KeyedRawJson Text (Scalar policy)) :=
    match scalarFromCbor? policy value with
    | some scalar => some (.scalar scalar)
    | none =>
        match value with
        | .array items => .list <$> arrayFromCbor? policy items
        | .map entries => .map <$> mapFromCbor? policy entries
        | _ => none

  private def arrayFromCbor? (policy : Cid.Policy) : CborSyn .array →
      Option (RawSyn Text (Scalar policy) .arr)
    | .arrayNil => some .nil
    | .arrayCons head tail =>
        return .cons (← fromCbor? policy head) (← arrayFromCbor? policy tail)

  private def mapFromCbor? (policy : Cid.Policy) : CborSyn .map →
      Option (RawSyn Text (Scalar policy) .obj)
    | .mapNil => some .objNil
    | .mapCons (.primitive (.text key)) value tail =>
        return .objCons (← text? key) (← fromCbor? policy value)
          (← mapFromCbor? policy tail)
    | .mapCons _ _ _ => none
end

@[simp] private theorem text?_value (value : Text) : text? value.value = some value := by
  rcases value with ⟨value, fits⟩
  simp only [text?, dif_pos fits]

@[simp] private theorem bytes?_value (value : ByteString) :
    bytes? value.value = some value := by
  rcases value with ⟨value, fits⟩
  simp only [bytes?, dif_pos fits]

@[simp] private theorem integer?_value (value : Integer) :
    integer? value.value = some value := by
  rcases value with ⟨value, valid⟩
  simp only [integer?, dif_pos valid]

@[simp] private theorem link?_tag42Payload
    (policy : Cid.Policy) (value : Link policy) :
    link? policy value.1.tag42Payload = some value := by
  rcases value with ⟨cid, accepted⟩
  simp [link?, accepted]

@[simp] private theorem scalarFromCbor?_scalarToCbor
    {policy : Cid.Policy} (value : Scalar policy) :
    scalarFromCbor? policy (scalarToCbor value) = some value := by
  cases value with
  | null => rfl
  | bool value => cases value <;> rfl
  | integer value => simp [scalarToCbor, scalarFromCbor?]
  | text value => simp [scalarToCbor, scalarFromCbor?]
  | bytes value => simp [scalarToCbor, scalarFromCbor?]
  | link value => simp [scalarToCbor, scalarFromCbor?]

@[simp] private theorem fromCbor?_scalarToCbor
    {policy : Cid.Policy} (value : Scalar policy) :
    fromCbor? policy (scalarToCbor value) = some (RawSyn.scalar value) := by
  cases value <;> unfold fromCbor? <;>
    rw [scalarFromCbor?_scalarToCbor]

private def parsedRaw? (policy : Cid.Policy) : {i : JsonIx} →
    CborSyn (cborIx i) → Option (RawSyn Text (Scalar policy) i)
  | .val, value => fromCbor? policy value
  | .arr, values => arrayFromCbor? policy values
  | .obj, entries => mapFromCbor? policy entries

@[simp] private theorem parsedRaw?_rawToCbor {policy : Cid.Policy} :
    ∀ {i : JsonIx} (value : RawSyn Text (Scalar policy) i),
      parsedRaw? policy (rawToCbor value) = some value
  | _, .scalar value => fromCbor?_scalarToCbor value
  | _, .list values => by
      have ih := parsedRaw?_rawToCbor values
      change arrayFromCbor? policy (rawToCbor values) = some values at ih
      change fromCbor? policy (.array (rawToCbor values)) = some (.list values)
      unfold fromCbor?
      rw [show scalarFromCbor? policy (.array (rawToCbor values)) = none by rfl]
      simp only [ih]
      rfl
  | _, .map entries => by
      have ih := parsedRaw?_rawToCbor entries
      change mapFromCbor? policy (rawToCbor entries) = some entries at ih
      change fromCbor? policy (.map (rawToCbor entries)) = some (.map entries)
      unfold fromCbor?
      rw [show scalarFromCbor? policy (.map (rawToCbor entries)) = none by rfl]
      simp only [ih]
      rfl
  | _, .nil => by simp [parsedRaw?, rawToCbor, arrayFromCbor?]
  | _, .cons head tail => by
      have headIH := parsedRaw?_rawToCbor head
      change fromCbor? policy (rawToCbor head) = some head at headIH
      have tailIH := parsedRaw?_rawToCbor tail
      change arrayFromCbor? policy (rawToCbor tail) = some tail at tailIH
      simp only [parsedRaw?, rawToCbor, arrayFromCbor?]
      change (fromCbor? policy (rawToCbor head)).bind (fun decodedHead =>
        (arrayFromCbor? policy (rawToCbor tail)).bind (fun decodedTail =>
          some (RawSyn.cons decodedHead decodedTail))) = _
      rw [headIH, tailIH]
      rfl
  | _, .objNil => by simp [parsedRaw?, rawToCbor, mapFromCbor?]
  | _, .objCons key value tail => by
      have valueIH := parsedRaw?_rawToCbor value
      change fromCbor? policy (rawToCbor value) = some value at valueIH
      have tailIH := parsedRaw?_rawToCbor tail
      change mapFromCbor? policy (rawToCbor tail) = some tail at tailIH
      simp only [parsedRaw?, rawToCbor, mapFromCbor?]
      change (text? key.value).bind (fun decodedKey =>
        (fromCbor? policy (rawToCbor value)).bind (fun decodedValue =>
          (mapFromCbor? policy (rawToCbor tail)).bind (fun decodedTail =>
            some (RawSyn.objCons decodedKey decodedValue decodedTail)))) = _
      rw [text?_value, valueIH, tailIH]
      rfl

@[simp] private theorem fromCbor?_rawToCbor {policy : Cid.Policy}
    (value : KeyedRawJson Text (Scalar policy)) :
    fromCbor? policy (rawToCbor value) = some value := by
  simpa [parsedRaw?] using parsedRaw?_rawToCbor value

/-- The CBOR tree representative faithfully embeds extensional values. -/
theorem toCbor_injective (policy : Cid.Policy) :
    Function.Injective (toCbor (policy := policy)) := by
  intro left right equal
  apply Json.toRaw_injective
  have recovered := congrArg (fromCbor? policy) equal
  simpa [toCbor] using recovered

/-- Full normality predicate for an extensional value under its CID policy. -/
def Normal (policy : Cid.Policy) (value : Value policy) : Prop :=
  Cbor.Drisl.Normal policy.acceptTag42Payload (toCbor value)

/-- Structural container bounds not already carried by scalar refinements.
This is the only remaining admission condition for an extensional value. -/
def Fits {policy : Cid.Policy} : Value policy → Prop
  | .scalar _ => True
  | .list n elems =>
      n ≤ Bytes.maxDefiniteLength ∧ ∀ i, Fits (elems i)
  | .map keys vals =>
      keys.card ≤ Bytes.maxDefiniteLength ∧ ∀ key, Fits (vals key)

noncomputable instance {policy : Cid.Policy} (value : Value policy) :
    Decidable (Fits value) := Classical.propDecidable _

private theorem scalarNormal {policy : Cid.Policy} (value : Scalar policy) :
    Cbor.Drisl.Normal policy.acceptTag42Payload (scalarToCbor value) := by
  cases value with
  | null =>
      change Cbor.Drisl.Normal policy.acceptTag42Payload
        (.primitive (.simple 22))
      exact Cbor.Drisl.Normal.null _
  | bool value =>
      cases value with
      | false =>
          change Cbor.Drisl.Normal policy.acceptTag42Payload
            (.primitive (.simple 20))
          exact ⟨by simp [Cbor.Drisl.Profile, Cbor.Drisl.profile?],
            by simp [CborWire.Canonical], .simple 20⟩
      | true =>
          change Cbor.Drisl.Normal policy.acceptTag42Payload
            (.primitive (.simple 21))
          exact ⟨by simp [Cbor.Drisl.Profile, Cbor.Drisl.profile?],
            by simp [CborWire.Canonical], .simple 21⟩
  | integer value =>
      rcases value with ⟨integer, valid⟩
      cases integer with
      | unsigned argument => exact Cbor.Drisl.Normal.unsigned _ argument valid
      | negative argument => exact Cbor.Drisl.Normal.negative _ argument valid
  | text value => exact Cbor.Drisl.Normal.text _ value.value value.fits
  | bytes value => exact Cbor.Drisl.Normal.bytes _ value.value value.fits
  | link value =>
      rcases value with ⟨cid, accepted⟩
      apply Cbor.Drisl.Normal.link _ cid.tag42Payload
      · simpa using (show 37 ≤ Bytes.maxDefiniteLength by decide)
      · simpa using accepted

/-- Every structurally bounded extensional value has a normal deterministic
DRISL representation.  Scalar widths and CID policy were enforced when their
refined values were constructed. -/
theorem normal_of_fits {policy : Cid.Policy} (value : Value policy) :
    Fits value → Normal policy value := by
  intro fits
  induction value with
  | scalar value => exact scalarNormal value
  | list n elems ih =>
      unfold Normal
      rw [toCbor_list]
      apply Cbor.Drisl.Normal.arrayOfList
      · simpa using fits.1
      · intro child present
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
        exact ih i (fits.2 i)
  | map keys vals ih =>
      let orderedKeys := keys.sort (fun left right => left ≤ right)
      let fields := orderedKeys.attach.map fun key =>
        (key.1.value,
          toCbor (vals ⟨key.1, (Finset.mem_sort _).mp key.2⟩))
      unfold Normal
      rw [toCbor_map]
      change Cbor.Drisl.Normal policy.acceptTag42Payload
        (.map (CborSyn.textMapOfList fields))
      apply Cbor.Drisl.Normal.textMapOfList
      · simpa [fields, orderedKeys] using fits.1
      · intro field present
        obtain ⟨key, _, rfl⟩ := List.mem_map.mp present
        exact key.1.fits
      · apply CborWire.DistinctCanonicalMapKeys.textMapOfList
        simpa [fields, orderedKeys, List.map_map, Function.comp_def] using
          textValues_distinct orderedKeys
            (Finset.sortedLT_sort keys).pairwise.nodup
      · apply CborWire.MapInDeterministicOrder.textMapOfList
        simpa [fields, orderedKeys, List.map_map, Function.comp_def] using
          textValues_inDeterministicOrder orderedKeys
            (Finset.sortedLT_sort keys).pairwise
      · intro field present
        obtain ⟨key, _, rfl⟩ := List.mem_map.mp present
        exact ih ⟨key.1, (Finset.mem_sort _).mp key.2⟩
          (fits.2 ⟨key.1, (Finset.mem_sort _).mp key.2⟩)

noncomputable instance (policy : Cid.Policy) (value : Value policy) :
    Decidable (Normal policy value) := by
  unfold Normal
  infer_instance

/-- Deterministic DRISL bytes for a normal extensional value. -/
private noncomputable def asNormalCbor {policy : Cid.Policy}
    (value : {value : Value policy // Normal policy value}) :
    {value : Cbor // Cbor.Drisl.Normal policy.acceptTag42Payload value} :=
  ⟨toCbor value.1, by simpa [Normal] using value.2⟩

@[simp] private theorem asNormalCbor_value {policy : Cid.Policy}
    (value : {value : Value policy // Normal policy value}) :
    (asNormalCbor value).1 = toCbor value.1 := rfl

noncomputable def encode {policy : Cid.Policy}
    (value : {value : Value policy // Normal policy value}) : Bytes :=
  Cbor.Drisl.deterministic (asNormalCbor value)

@[simp] private theorem parseNormal?_encode {policy : Cid.Policy}
    (value : {value : Value policy // Normal policy value}) :
    Cbor.Drisl.parseNormal? policy.acceptTag42Payload (encode value) =
      some (asNormalCbor value) := by
  exact Cbor.Drisl.parseNormal?_deterministic (asNormalCbor value)

/-- Recover one extensional value from a normal CBOR tree.  The final equality
check is the explicit bridge from ordered raw maps back to the extensional
representative; it also keeps decoder soundness independent of ordering proof
internals. -/
private noncomputable def decodeTree? (policy : Cid.Policy)
    (normal : {value : Cbor // Cbor.Drisl.Normal policy.acceptTag42Payload value}) :
    Option (Value policy) := do
  let raw ← fromCbor? policy normal.1
  match raw.validate with
  | .ok value =>
      if toCbor value = normal.1 then some value else none
  | .error _ => none

private theorem decodeTree?_sound {policy : Cid.Policy}
    {normal : {value : Cbor // Cbor.Drisl.Normal policy.acceptTag42Payload value}}
    {value : Value policy} (accepted : decodeTree? policy normal = some value) :
    toCbor value = normal.1 := by
  unfold decodeTree? at accepted
  cases parsed : fromCbor? policy normal.1 with
  | none => simp [parsed] at accepted
  | some raw =>
      simp only [parsed] at accepted
      change (match raw.validate with
        | .ok decoded =>
            if toCbor decoded = normal.1 then some decoded else none
        | .error _ => none) = some value at accepted
      cases validated : raw.validate with
      | error failure => simp [validated] at accepted
      | ok decoded =>
          rw [validated] at accepted
          change (if toCbor decoded = normal.1 then some decoded else none) =
            some value at accepted
          split at accepted
          · rename_i sameTree
            have sameValue := Option.some.inj accepted
            rw [← sameValue]
            exact sameTree
          · simp at accepted

/-- Parse one canonical DRISL item and recover its extensional object-model
meaning, rejecting duplicate keys and non-canonical representatives. -/
noncomputable def decode? (policy : Cid.Policy) (bytes : Bytes) :
    Option (Value policy) := do
  let normal ← Cbor.Drisl.parseNormal? policy.acceptTag42Payload bytes
  decodeTree? policy normal

@[simp] theorem decode?_encode {policy : Cid.Policy}
    (value : {value : Value policy // Normal policy value}) :
    decode? policy (encode value) = some value.1 := by
  unfold decode?
  rw [parseNormal?_encode]
  unfold decodeTree?
  change ((fromCbor? policy (toCbor value.1)).bind fun raw =>
    match raw.validate with
    | .ok decoded =>
        if toCbor decoded = toCbor value.1 then some decoded else none
    | .error _ => none) = some value.1
  rw [show fromCbor? policy (toCbor value.1) = some value.1.toRaw by
    simp [toCbor]]
  simp only [Option.bind_some]
  rw [RawSyn.validate_ok_of_wellFormed value.1.toRaw_sortedKeys.wellFormed]
  simp [Json.toJson_toRaw]

/-- DRISL is canonical with respect to the extensional AT Protocol object
model: equal bytes emitted for two normal values imply equal semantic values. -/
theorem encode_injective {policy : Cid.Policy}
    {left right : {value : Value policy // Normal policy value}}
    (equal : encode left = encode right) : left = right := by
  apply Subtype.ext
  have leftDecoded := decode?_encode left
  have rightDecoded := decode?_encode right
  rw [equal] at leftDecoded
  exact Option.some.inj (leftDecoded.symm.trans rightDecoded)

/-- Relational normal encoding of an extensional value. -/
def Encoding (policy : Cid.Policy) (value : Value policy) (bytes : Bytes) : Prop :=
  ∃ normal : Normal policy value, bytes = encode ⟨value, normal⟩

/-- Every accepted byte string is the normal encoding of the returned
extensional value. -/
theorem decode?_sound {policy : Cid.Policy} {bytes : Bytes}
    {value : Value policy} (accepted : decode? policy bytes = some value) :
    Encoding policy value bytes := by
  unfold decode? at accepted
  cases parsed : Cbor.Drisl.parseNormal? policy.acceptTag42Payload bytes with
  | none => simp [parsed] at accepted
  | some normal =>
    have decoded : decodeTree? policy normal = some value := by
      simpa [parsed] using accepted
    have sameTree := decodeTree?_sound decoded
    have normalValue : Normal policy value := by
      unfold Normal
      rw [sameTree]
      exact normal.2
    refine ⟨normalValue, ?_⟩
    have sameBytes := Cbor.Drisl.parseNormal?_sound parsed
    rw [← sameBytes]
    unfold encode
    apply congrArg Cbor.Drisl.deterministic
    apply Subtype.ext
    exact sameTree.symm

/-- Checked decoding and the relational normal encoding coincide exactly. -/
theorem decode?_eq_some_iff {policy : Cid.Policy} {bytes : Bytes}
    {value : Value policy} :
    decode? policy bytes = some value ↔ Encoding policy value bytes := by
  constructor
  · exact decode?_sound
  · rintro ⟨normal, rfl⟩
    exact decode?_encode ⟨value, normal⟩

/-- One semantic value has at most one normal DRISL representation. -/
theorem encoding_unique {policy : Cid.Policy} {value : Value policy}
    {left right : Bytes} (leftEncoding : Encoding policy value left)
    (rightEncoding : Encoding policy value right) : left = right := by
  rcases leftEncoding with ⟨_, rfl⟩
  rcases rightEncoding with ⟨_, rfl⟩
  rfl

/-- One normal DRISL byte string has at most one extensional meaning. -/
theorem encoding_injective {policy : Cid.Policy} {left right : Value policy}
    {bytes : Bytes} (leftEncoding : Encoding policy left bytes)
    (rightEncoding : Encoding policy right bytes) : left = right := by
  rcases leftEncoding with ⟨leftNormal, rfl⟩
  rcases rightEncoding with ⟨rightNormal, equal⟩
  exact congrArg Subtype.val (encode_injective equal)

end Value

end Nucleus.Atproto
