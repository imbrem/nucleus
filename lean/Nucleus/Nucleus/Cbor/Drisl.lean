import Nucleus.Cbor.Wire

/-!
# AT Protocol data profile

This module refines general CBOR syntax to the DRISL data model used for Nucleus
objects: signed 64-bit integers,
byte and text strings, arrays, text-keyed maps, `null` and booleans, and CID
links encoded as tag 42 around a byte string.  The CID payload predicate is a
parameter so hash and multicodec policy remains outside the CBOR grammar.

`Normal` is intentionally stronger than the structural profile.  It also
requires the generic canonical artifact constraints and exact deterministic
map order.  The checked decoder compares the input with deterministic output;
the general CBOR parser deliberately accepts non-canonical wire spellings.
-/

namespace Nucleus.Cbor.Drisl

open Nucleus

/-- Largest CBOR argument used by either polarity of a signed 64-bit integer.
For a negative integer CBOR stores `-1 - n`, so the same bound includes
`Int64.min`. -/
def int64ArgumentMax : UInt64 := 0x7fff_ffff_ffff_ffff

mutual
  /-- Executable structural membership test. `acceptCid` receives the complete
  tag-42 byte-string payload, including any CID framing required by policy. -/
  def profile? (acceptCid : Bytes → Bool) : Cbor → Bool
    | .primitive (.integer (.unsigned argument)) =>
        decide (argument ≤ int64ArgumentMax)
    | .primitive (.integer (.negative argument)) =>
        decide (argument ≤ int64ArgumentMax)
    | .primitive (.bytes _) => true
    | .primitive (.text _) => true
    | .primitive (.simple value) =>
        value == 20 || value == 21 || value == 22
    | .primitive (.float16 _) => false
    | .primitive (.float32 _) => false
    | .primitive (.float64 _) => false
    | .array items => arrayProfile? acceptCid items
    | .map entries => mapProfile? acceptCid entries
    | .tag number content =>
        number == 42 && match content with
          | .primitive (.bytes cid) => acceptCid cid
          | _ => false

  /-- Recursive profile check for array elements. -/
  def arrayProfile? (acceptCid : Bytes → Bool) : CborSyn .array → Bool
    | .arrayNil => true
    | .arrayCons head tail =>
        profile? acceptCid head && arrayProfile? acceptCid tail

  /-- Recursive profile check for text-keyed map entries. -/
  def mapProfile? (acceptCid : Bytes → Bool) : CborSyn .map → Bool
    | .mapNil => true
    | .mapCons (.primitive (.text _)) value tail =>
        profile? acceptCid value && mapProfile? acceptCid tail
    | .mapCons _ _ _ => false
end

/-- Semantic membership in the data profile selected by `acceptCid`. -/
def Profile (acceptCid : Bytes → Bool) (value : Cbor) : Prop :=
  profile? acceptCid value = true

instance (acceptCid : Bytes → Bool) (value : Cbor) :
    Decidable (Profile acceptCid value) := by
  unfold Profile
  infer_instance

/-- A canonical content-addressed object in this profile. `WireNormal` records
the exact deterministic map order; `Canonical` supplies finite lengths and
duplicate-key rejection. -/
def Normal (acceptCid : Bytes → Bool) (value : Cbor) : Prop :=
  Profile acceptCid value ∧ CborWire.Canonical value ∧ CborWire.WireNormal value

instance (acceptCid : Bytes → Bool) (value : Cbor) :
    Decidable (Normal acceptCid value) := by
  unfold Normal
  infer_instance

namespace Normal

/-- Normal objects lie in the generic deterministic encoder's domain. -/
theorem reasonable {acceptCid : Bytes → Bool} {value : Cbor}
    (normal : Normal acceptCid value) : value.Reasonable :=
  normal.2.2.reasonable

/-- A bounded byte string is normal in every CID policy. -/
theorem bytes (acceptCid : Bytes → Bool) (value : Bytes)
    (fits : value.length ≤ Bytes.maxDefiniteLength) :
    Normal acceptCid (.primitive (.bytes value)) := by
  exact ⟨by simp [Profile, profile?], by simp [CborWire.Canonical, fits],
    .bytes value fits⟩

/-- A bounded text string is normal in every CID policy. -/
theorem text (acceptCid : Bytes → Bool) (value : String)
    (fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength) :
    Normal acceptCid (.primitive (.text value)) := by
  have utf8Fits : value.utf8ByteSize ≤ Bytes.maxDefiniteLength := by
    simpa only [String.toUTF8_eq_toByteArray, String.size_toByteArray] using fits
  exact ⟨by simp [Profile, profile?], by simpa [CborWire.Canonical] using utf8Fits,
    .text value fits⟩

private theorem arrayProfileOfList (acceptCid : Bytes → Bool)
    (values : List Cbor) (normal : ∀ value ∈ values, Normal acceptCid value) :
    arrayProfile? acceptCid (CborSyn.arrayOfList values) = true := by
  induction values with
  | nil => simp [CborSyn.arrayOfList, arrayProfile?]
  | cons value values ih =>
      simp only [CborSyn.arrayOfList, arrayProfile?, Bool.and_eq_true]
      exact ⟨(normal value (by simp)).1,
        ih fun member present => normal member (by simp [present])⟩

/-- Compose a normal array from normal values and its finite-length bound. -/
theorem arrayOfList (acceptCid : Bytes → Bool) (values : List Cbor)
    (fits : values.length ≤ Bytes.maxDefiniteLength)
    (normal : ∀ value ∈ values, Normal acceptCid value) :
    Normal acceptCid (.array (CborSyn.arrayOfList values)) := by
  have profile : Profile acceptCid (.array (CborSyn.arrayOfList values)) := by
    simpa [Profile, profile?] using arrayProfileOfList acceptCid values normal
  refine ⟨profile, ?_, ?_⟩
  · exact CborWire.Canonical.arrayOfList values fits fun value present =>
      (normal value present).2.1
  · exact CborWire.WireNormal.arrayOfList values fits fun value present =>
      (normal value present).2.2

private theorem mapProfileTextMapOfList (acceptCid : Bytes → Bool)
    (fields : List (String × Cbor))
    (normal : ∀ field ∈ fields, Normal acceptCid field.2) :
    mapProfile? acceptCid (CborSyn.textMapOfList fields) = true := by
  induction fields with
  | nil => simp [CborSyn.textMapOfList, mapProfile?]
  | cons field fields ih =>
      rcases field with ⟨key, value⟩
      simp only [CborSyn.textMapOfList, mapProfile?, Bool.and_eq_true]
      exact ⟨(normal (key, value) (by simp)).1,
        ih fun member present => normal member (by simp [present])⟩

/-- Compose a normal text-key map. The hypotheses separate the finite-length,
key uniqueness, and deterministic-order commitments made by a schema. -/
theorem textMapOfList (acceptCid : Bytes → Bool)
    (fields : List (String × Cbor))
    (fits : fields.length ≤ Bytes.maxDefiniteLength)
    (keyFits : ∀ field ∈ fields,
      field.1.toUTF8.size ≤ Bytes.maxDefiniteLength)
    (distinct : CborWire.DistinctCanonicalMapKeys
      (CborSyn.textMapOfList fields))
    (ordered : CborWire.MapInDeterministicOrder
      (CborSyn.textMapOfList fields))
    (normal : ∀ field ∈ fields, Normal acceptCid field.2) :
    Normal acceptCid (.map (CborSyn.textMapOfList fields)) := by
  have profile : Profile acceptCid (.map (CborSyn.textMapOfList fields)) := by
    simpa [Profile, profile?] using mapProfileTextMapOfList acceptCid fields normal
  refine ⟨profile, ?_, ?_⟩
  · apply CborWire.Canonical.textMapOfList fields fits distinct
    intro field present
    have utf8Fits : field.1.utf8ByteSize ≤ Bytes.maxDefiniteLength := by
      simpa only [String.toUTF8_eq_toByteArray, String.size_toByteArray] using
        keyFits field present
    exact ⟨by simpa [CborWire.Canonical] using utf8Fits,
      (normal field present).2.1⟩
  · apply CborWire.WireNormal.textMapOfList fields fits ordered
    intro field present
    exact ⟨.text field.1 (keyFits field present), (normal field present).2.2⟩

end Normal

/-- Deterministic serialization of a normal profile object. -/
def deterministic {acceptCid : Bytes → Bool}
    (value : {value : Cbor // Normal acceptCid value}) : Bytes :=
  CborWire.deterministic ⟨value.1, value.2.reasonable⟩

/-- Normal deterministic serialization is recovered exactly by the generic
CBOR parser. -/
@[simp] theorem parse?_deterministic {acceptCid : Bytes → Bool}
    (value : {value : Cbor // Normal acceptCid value}) :
    CborWire.parse? (deterministic value) = some value.1 :=
  CborWire.parse?_deterministic_wireNormal value.1 value.2.2.2

/-- Deterministic serialization is injective on normal profile objects. -/
theorem deterministic_injective {acceptCid : Bytes → Bool}
    {left right : {value : Cbor // Normal acceptCid value}}
    (equal : deterministic left = deterministic right) : left = right := by
  apply Subtype.ext
  have leftParsed := parse?_deterministic left
  have rightParsed := parse?_deterministic right
  rw [equal] at leftParsed
  exact Option.some.inj (leftParsed.symm.trans rightParsed)

/-- Parse one normal object, rejecting both values outside the profile and
non-deterministic encodings of an otherwise normal syntax tree. -/
def parseNormal? (acceptCid : Bytes → Bool) (bytes : Bytes) :
    Option {value : Cbor // Normal acceptCid value} := do
  let value ← CborWire.parse? bytes
  if normal : Normal acceptCid value then
    let checked : {value : Cbor // Normal acceptCid value} := ⟨value, normal⟩
    if deterministic checked = bytes then some checked else none
  else
    none

/-- The checked decoder accepts every normal deterministic serialization. -/
@[simp] theorem parseNormal?_deterministic {acceptCid : Bytes → Bool}
    (value : {value : Cbor // Normal acceptCid value}) :
    parseNormal? acceptCid (deterministic value) = some value := by
  simp [parseNormal?, value.2]

/-- Relational presentation of normal serialization. -/
def Encoding (acceptCid : Bytes → Bool) (value : Cbor) (bytes : Bytes) : Prop :=
  ∃ normal : Normal acceptCid value,
    bytes = deterministic ⟨value, normal⟩

/-- A normal value has at most one deterministic byte representation. -/
theorem encoding_unique {acceptCid : Bytes → Bool} {value : Cbor}
    {left right : Bytes} (leftEncoding : Encoding acceptCid value left)
    (rightEncoding : Encoding acceptCid value right) : left = right := by
  rcases leftEncoding with ⟨_, rfl⟩
  rcases rightEncoding with ⟨_, rfl⟩
  rfl

/-- A normal deterministic byte representation denotes at most one syntax
tree. -/
theorem encoding_injective {acceptCid : Bytes → Bool} {left right : Cbor}
    {bytes : Bytes} (leftEncoding : Encoding acceptCid left bytes)
    (rightEncoding : Encoding acceptCid right bytes) : left = right := by
  rcases leftEncoding with ⟨leftNormal, rfl⟩
  rcases rightEncoding with ⟨rightNormal, equal⟩
  have same :
      deterministic ⟨left, leftNormal⟩ =
        deterministic ⟨right, rightNormal⟩ := equal
  exact congrArg Subtype.val (deterministic_injective same)

end Nucleus.Cbor.Drisl
