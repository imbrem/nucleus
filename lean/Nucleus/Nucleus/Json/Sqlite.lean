import Nucleus.Json.CasMap
import Nucleus.Json.Ipld
import Nucleus.Json.RfcParser

/-!
# SQLite values and JSON conversion boundaries

This module models SQLite's four non-null storage classes.  SQL `NULL` is
represented separately by `Option`, so it cannot be confused with failure to
decode a value.  A failed or not-yet-known conversion is represented by
`WithBot`: its bottom element carries the information-order meaning “no result
is known”, while `some none` remains an ordinary, known SQL/JSON null.

The RFC-JSON and IPLD-JSON scalar types deliberately remain parameters here.
`PartialScalarCodec` is the integration seam: their modules can supply codecs
without introducing an import cycle.
-/

namespace Nucleus

universe u

/-- A non-null SQLite value. `blob` is an uninterpreted sequence of bytes and
`real` has SQLite's binary64 representation. -/
inductive SqliteValue where
  | text (value : String)
  | blob (value : ByteArray)
  | integer (value : Int64)
  | real (value : Float)

/-- SQLite values including SQL `NULL`. -/
abbrev NullableSqliteValue := Option SqliteValue

/-- JSON whose scalar leaves are nullable SQLite values.  In particular,
`.scalar none` is a known null, not an unknown subtree. -/
abbrev SqliteJson := Json NullableSqliteValue

/-- A result ordered by information, with `⊥` meaning that conversion is
invalid or its answer is not known.  This is intentionally distinct from
`Option`, which represents SQL/JSON null inside a successful result. -/
abbrev Partial (α : Type u) := WithBot α

namespace Json

/-- Partially map scalar leaves. Conversion fails for the entire tree when a
single scalar is rejected; object keys and container structure are preserved. -/
def mapScalar? {Key : Type} {S T : Type u} (f : S → Option T) :
    Json S Key → Option (Json T Key)
  | .scalar value => (f value).map .scalar
  | .list n elems =>
      if h : ∀ i, (mapScalar? f (elems i)).isSome then
        some (.list n fun i => (mapScalar? f (elems i)).get (h i))
      else none
  | .map keys vals =>
      if h : ∀ k, (mapScalar? f (vals k)).isSome then
        some (.map keys fun k => (mapScalar? f (vals k)).get (h k))
      else none

@[simp] theorem mapScalar?_some {Key : Type} {S T : Type u}
    (f : S → T) (j : Json S Key) :
    j.mapScalar? (some ∘ f) = some (j.mapScalar f) := by
  induction j with
  | scalar value => rfl
  | list n elems ih =>
      unfold mapScalar?
      have h : ∀ i, (mapScalar? (some ∘ f) (elems i)).isSome := by
        intro i
        rw [ih i]
        rfl
      rw [dif_pos h]
      congr 2
      funext i
      apply Option.some.inj
      rw [Option.some_get, ih i]
  | map keys vals ih =>
      unfold mapScalar?
      have h : ∀ k, (mapScalar? (some ∘ f) (vals k)).isSome := by
        intro k
        rw [ih k]
        rfl
      rw [dif_pos h]
      congr 2
      funext k
      apply Option.some.inj
      rw [Option.some_get, ih k]

@[simp] theorem mapScalar?_pure {Key : Type} {S : Type u} (j : Json S Key) :
    j.mapScalar? some = some j := by
  simpa using mapScalar?_some (f := id) j

end Json

/-- Lift all-or-nothing scalar conversion into the flat information domain. -/
def partialMapJson {Key : Type} {S T : Type u}
    (f : S → Option T) (j : Json S Key) : Partial (Json T Key) :=
  match j.mapScalar? f with
  | none => ⊥
  | some result => ↑result

@[simp] theorem partialMapJson_some {Key : Type} {S T : Type u}
    (f : S → T) (j : Json S Key) :
    partialMapJson (some ∘ f) j = ↑(j.mapScalar f) := by
  simp [partialMapJson]

@[simp] theorem partialMapJson_pure {Key : Type} {S : Type u} (j : Json S Key) :
    partialMapJson some j = ↑j := by
  simpa using partialMapJson_some (f := id) j

/-- Partial scalar interconversion.  The laws state round trips only when the
forward conversion succeeds; invalid inputs simply produce no information. -/
structure PartialScalarCodec (Source Target : Type u) where
  encode : Source → Option Target
  decode : Target → Option Source
  decode_encode : ∀ {source target}, encode source = some target →
    decode target = some source
  encode_decode : ∀ {target source}, decode target = some source →
    encode source = some target

namespace PartialScalarCodec

/-- Apply the forward half of a scalar codec to a complete JSON tree. -/
def encodeJson {Source Target : Type u} (codec : PartialScalarCodec Source Target)
    {Key : Type} (json : Json Source Key) : Partial (Json Target Key) :=
  partialMapJson codec.encode json

/-- Apply the reverse half of a scalar codec to a complete JSON tree. -/
def decodeJson {Source Target : Type u} (codec : PartialScalarCodec Source Target)
    {Key : Type} (json : Json Target Key) : Partial (Json Source Key) :=
  partialMapJson codec.decode json

theorem encodeJson_scalar {Source Target : Type u} (codec : PartialScalarCodec Source Target)
    {Key : Type} {source : Source} {target : Target} (h : codec.encode source = some target) :
    codec.encodeJson (Key := Key) (.scalar source) =
      ↑(Json.scalar target : Json Target Key) := by
  simp [encodeJson, partialMapJson, Json.mapScalar?, h]

theorem decodeJson_scalar {Source Target : Type u} (codec : PartialScalarCodec Source Target)
    {Key : Type} {source : Source} {target : Target} (h : codec.decode target = some source) :
    codec.decodeJson (Key := Key) (.scalar target) =
      ↑(Json.scalar source : Json Source Key) := by
  simp [decodeJson, partialMapJson, Json.mapScalar?, h]

/-- A successful scalar encoding can be decoded back exactly. -/
theorem scalar_roundtrip {Source Target : Type u} (codec : PartialScalarCodec Source Target)
    {Key : Type} {source : Source} {target : Target} (h : codec.encode source = some target) :
    codec.decodeJson (Key := Key) (.scalar target) =
      ↑(Json.scalar source : Json Source Key) :=
  codec.decodeJson_scalar (codec.decode_encode h)

/-- Integration hook for the anticipated RFC JSON scalar type. -/
abbrev SqliteRfcCodec (RfcScalar : Type) :=
  PartialScalarCodec NullableSqliteValue RfcScalar

/-- Integration hook for the anticipated link-free IPLD JSON scalar type. -/
abbrev SqliteIpldCodec (IpldScalar : Type) :=
  PartialScalarCodec NullableSqliteValue IpldScalar

end PartialScalarCodec

/-! ## Concrete RFC and IPLD conversions -/

/-- Partially encode a nullable SQLite value as an RFC JSON scalar. Blobs and
binary64 reals are left unknown; integers retain exact decimal notation. -/
def sqliteToRfcScalar? : NullableSqliteValue → Option RfcJsonScalar
  | none => some none
  | some (.text value) => some (.string value)
  | some (.integer value) => some (.number (toString value.toInt))
  | some (.blob _) | some (.real _) => none

/-- Partially decode an RFC scalar as a nullable SQLite value. Booleans use
SQLite's conventional integer representation and numeric literals must fit
exactly in `Int64`. -/
def sqliteOfRfcScalar? : RfcJsonScalar → Option NullableSqliteValue
  | none => some none
  | some (.bool false) => some (some (.integer 0))
  | some (.bool true) => some (some (.integer 1))
  | some (.string value) => some (some (.text value))
  | some (.number literal) =>
      (IpldJson.parseInt64? literal).map fun value => some (.integer value)

/-- Partially encode a nullable SQLite value in the integer-only IPLD profile. -/
def sqliteToIpldScalar? : NullableSqliteValue → Option IpldJsonScalar
  | none => some none
  | some (.text value) => some (some (.string value))
  | some (.integer value) => some (some (.int value))
  | some (.blob _) | some (.real _) => none

/-- Partially decode an integer-only IPLD scalar as a SQLite value. -/
def sqliteOfIpldScalar? : IpldJsonScalar → Option NullableSqliteValue
  | none => some none
  | some (.bool false) => some (some (.integer 0))
  | some (.bool true) => some (some (.integer 1))
  | some (.string value) => some (some (.text value))
  | some (.int value) => some (some (.integer value))

@[simp] theorem sqliteToRfcScalar?_null : sqliteToRfcScalar? none = some none := rfl
@[simp] theorem sqliteOfRfcScalar?_null : sqliteOfRfcScalar? none = some none := rfl
@[simp] theorem sqliteToIpldScalar?_null : sqliteToIpldScalar? none = some none := rfl
@[simp] theorem sqliteOfIpldScalar?_null : sqliteOfIpldScalar? none = some none := rfl

@[simp] theorem sqlite_rfc_text_roundtrip (value : String) :
    sqliteOfRfcScalar? (some (.string value)) = some (some (.text value)) := rfl

@[simp] theorem sqlite_ipld_integer_roundtrip (value : Int64) :
    sqliteOfIpldScalar? (some (.int value)) = some (some (.integer value)) := rfl

/-- Lift an `Option`-returning parser into epistemic unknown information. -/
def Unknown.ofOption {α : Type u} : Option α → Unknown α
  | none => .unknown
  | some value => .known value

namespace JsonCas

variable {Name : Type} [DecidableEq Name]

/-- Interpret a CAS of RFC scalars as integer-only IPLD JSON at a fixed gas
level. Invalid profile values yield epistemic unknown, not JSON null. -/
def fetchIpld (cas : JsonCas RfcJsonScalar Name) (gas : Nat) (name : Name) :
    Unknown IpldJson :=
  cas.mapFetch (Unknown.ofOption ∘ IpldJson.ofRfcScalar?) gas name

/-- Parse a fetched scalar text as one complete RFC JSON document and then as
linked integer-only IPLD data. A non-scalar CAS output, malformed RFC text,
non-Int64 number, or invalid link name is simply unknown. -/
noncomputable def parseLinkedIpldDocument (parseName : String → Option Name) :
    Json String → Unknown (IpldLinkedJson Name)
  | .scalar text =>
      match RfcJson.parse? text with
      | none => .unknown
      | some rfc => Unknown.ofOption (IpldLinkedJson.ofRfc? parseName rfc)
  | _ => .unknown

/-- Gas-bounded extraction of linked IPLD JSON from a CAS whose stored scalar
payloads are serialized RFC JSON documents. -/
noncomputable def fetchLinkedIpld (cas : JsonCas String Name)
    (parseName : String → Option Name) (gas : Nat) (name : Name) :
    Unknown (IpldLinkedJson Name) :=
  cas.mapOutput (parseLinkedIpldDocument parseName) gas name

/-- The name-indexed linked-data view induced by a real CAS and gas level. -/
noncomputable def linkedIpldFunction (cas : JsonCas String Name)
    (parseName : String → Option Name) (gas : Nat) :
    Name → Unknown (IpldLinkedJson Name) :=
  cas.mappedFunction (parseLinkedIpldDocument parseName) gas

end JsonCas

end Nucleus
