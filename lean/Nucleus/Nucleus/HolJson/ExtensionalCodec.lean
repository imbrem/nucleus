import Nucleus.HolJson.Codec
import Nucleus.Json.Extensional

/-!
# Extensional HOL JSON decoding

RFC 8259 objects are unordered.  This module is the semantic decoding boundary:
it checks the exact key set for every node, but looks fields up by name rather
than depending on their serialized order.  `AtomProfile` also isolates the
representation of scalar leaves, including the representation of free names.
-/

namespace Nucleus.HolJson

/-- Scalar projections needed by the HOL JSON profile. -/
structure AtomProfile (Atom Free : Type) where
  string? : Atom -> Option String
  uint? : Atom -> Option UInt64
  bool? : Atom -> Option Bool
  free? : Atom -> Option Free

namespace ExtensionalCodec

variable {Atom Free Value : Type}

private def hasKeys (json : Nucleus.Json Atom)
    (expected : List String) : Bool :=
  match json with
  | .map keys _ => keys = expected.toFinset
  | _ => false

private def field? (json : Nucleus.Json Atom) (key : String) : Option (Nucleus.Json Atom) :=
  json.get? [.key key]

private def scalar? (project : Atom -> Option Value) : Nucleus.Json Atom -> Option Value
  | .scalar atom => project atom
  | _ => none

private def decodeFuel (schema : Schema) (profile : AtomProfile Atom Free) :
    Nat -> Nucleus.Json Atom -> Option (Syntax String Free)
  | 0, _ => none
  | fuel + 1, json => do
      let tag <- scalar? profile.string? (← field? json schema.tagField)
      if tag = schema.tyBaseTag then
        if hasKeys json [schema.tagField, schema.nameField] then
          return .base (← scalar? profile.string? (← field? json schema.nameField))
        else none
      else if tag = schema.tyBoolTag then
        if hasKeys json [schema.tagField] then some .boolTy else none
      else if tag = schema.tyIndTag then
        if hasKeys json [schema.tagField] then some .indTy else none
      else if tag = schema.tyArrTag then
        if hasKeys json [schema.tagField, schema.domainField, schema.codomainField] then
          return .arr (← decodeFuel schema profile fuel (← field? json schema.domainField))
            (← decodeFuel schema profile fuel (← field? json schema.codomainField))
        else none
      else if tag = schema.tySubTag then
        if hasKeys json [schema.tagField, schema.carrierField, schema.predicateField] then
          return .sub (← decodeFuel schema profile fuel (← field? json schema.carrierField))
            (← decodeFuel schema profile fuel (← field? json schema.predicateField))
        else none
      else if tag = schema.tmBoundTag then
        if hasKeys json [schema.tagField, schema.indexField] then
          return .bound (← scalar? profile.uint? (← field? json schema.indexField))
        else none
      else if tag = schema.tmFreeTag then
        if hasKeys json [schema.tagField, schema.nameField] then
          return .free (← scalar? profile.free? (← field? json schema.nameField))
        else none
      else if tag = schema.tmAppTag then
        if hasKeys json [schema.tagField, schema.functionField, schema.argumentField] then
          return .app (← decodeFuel schema profile fuel (← field? json schema.functionField))
            (← decodeFuel schema profile fuel (← field? json schema.argumentField))
        else none
      else if tag = schema.tmLamTag then
        if hasKeys json [schema.tagField, schema.domainField, schema.bodyField] then
          return .lam (← decodeFuel schema profile fuel (← field? json schema.domainField))
            (← decodeFuel schema profile fuel (← field? json schema.bodyField))
        else none
      else if tag = schema.tmBoolTag then
        if hasKeys json [schema.tagField, schema.valueField] then
          return .bool (← scalar? profile.bool? (← field? json schema.valueField))
        else none
      else if tag = schema.tmZeroTag then
        if hasKeys json [schema.tagField] then some .zero else none
      else if tag = schema.tmSuccTag then
        if hasKeys json [schema.tagField, schema.valueField] then
          return .succ (← decodeFuel schema profile fuel (← field? json schema.valueField))
        else none
      else if tag = schema.tmEqTag then
        if hasKeys json
            [schema.tagField, schema.typeField, schema.leftField, schema.rightField] then
          return .eqn (← decodeFuel schema profile fuel (← field? json schema.typeField))
            (← decodeFuel schema profile fuel (← field? json schema.leftField))
            (← decodeFuel schema profile fuel (← field? json schema.rightField))
        else none
      else if tag = schema.tmEpsTag then
        if hasKeys json [schema.tagField, schema.typeField, schema.predicateField] then
          return .eps (← decodeFuel schema profile fuel (← field? json schema.typeField))
            (← decodeFuel schema profile fuel (← field? json schema.predicateField))
        else none
      else if tag = schema.tmAbsTag then
        if hasKeys json [schema.tagField, schema.carrierField, schema.predicateField,
            schema.valueField] then
          return .abs (← decodeFuel schema profile fuel (← field? json schema.carrierField))
            (← decodeFuel schema profile fuel (← field? json schema.predicateField))
            (← decodeFuel schema profile fuel
              (← field? (Atom := Atom) json schema.valueField))
        else none
      else if tag = schema.tmRepTag then
        if hasKeys json [schema.tagField, schema.carrierField, schema.predicateField,
            schema.valueField] then
          return .rep (← decodeFuel schema profile fuel (← field? json schema.carrierField))
            (← decodeFuel schema profile fuel (← field? json schema.predicateField))
            (← decodeFuel schema profile fuel
              (← field? (Atom := Atom) json schema.valueField))
        else none
      else none

/-- Decode duplicate-free, extensional JSON.  The input depth supplies a total
recursion bound; malformed or exhausted input returns `none`. -/
def decodeWith (schema : Schema) (profile : AtomProfile Atom Free)
    (json : Nucleus.Json Atom) : Option (Syntax String Free) :=
  decodeFuel schema profile (json.depth + 1) json

/-- Decode using the inspectable v0 vocabulary. -/
def decode (profile : AtomProfile Atom Free)
    (json : Nucleus.Json Atom) : Option (Syntax String Free) :=
  decodeWith Schema.v0 profile json

/-- Decode using an implicitly supplied vocabulary. -/
def decodeProvided [SchemaProvider] (profile : AtomProfile Atom Free)
    (json : Nucleus.Json Atom) : Option (Syntax String Free) :=
  decodeWith providedSchema profile json

/-- The ordinary v0 scalar profile. -/
def wireProfile : AtomProfile Scalar UInt64 where
  string?
    | .string value => some value
    | _ => none
  uint?
    | .uint value => some value
    | _ => none
  bool?
    | .bool value => some value
    | _ => none
  free?
    | .uint value => some value
    | _ => none

/-- Decode the ordinary v0 profile after raw duplicate-key validation. -/
def decodeWire (json : Nucleus.Json Scalar) : Option WireSyntax :=
  decode wireProfile json

/-- A linked profile keeps original free names on the left and turns a link
scalar in free-name position into a right-hand free name. -/
def linkedProfile (Name : Type) : AtomProfile (Scalar ⊕ Name) (UInt64 ⊕ Name) where
  string?
    | .inl (.string value) => some value
    | _ => none
  uint?
    | .inl (.uint value) => some value
    | _ => none
  bool?
    | .inl (.bool value) => some value
    | _ => none
  free?
    | .inl (.uint value) => some (.inl value)
    | .inr name => some (.inr name)
    | _ => none

/-- Decode a linked HOL JSON tree with an explicit vocabulary, without erasing
the provenance of free names. -/
def decodeLinkedWith {Name : Type} (schema : Schema)
    (json : Nucleus.Json (Scalar ⊕ Name)) :
    Option (Syntax String (UInt64 ⊕ Name)) :=
  decodeWith schema (linkedProfile Name) json

/-- Decode a linked HOL JSON tree using the v0 vocabulary. -/
def decodeLinked {Name : Type} (json : Nucleus.Json (Scalar ⊕ Name)) :
    Option (Syntax String (UInt64 ⊕ Name)) :=
  decodeLinkedWith Schema.v0 json

/-- The semantic JSON node used when a linked HOL subtree stays opaque. -/
def linkedFreeJsonWith {Name : Type} (schema : Schema)
    (tag_ne_name : schema.tagField ≠ schema.nameField) (name : Name) :
    Nucleus.Json (Scalar ⊕ Name) :=
  Nucleus.Json.ofEntries
    [(schema.tagField, .scalar (.inl (.string schema.tmFreeTag))),
      (schema.nameField, .scalar (.inr name))]
    (by simpa using tag_ne_name)

/-- The v0 opaque linked-free node. -/
def linkedFreeJson {Name : Type} (name : Name) : Nucleus.Json (Scalar ⊕ Name) :=
  linkedFreeJsonWith Schema.v0 (by decide) name

@[simp] theorem decodeLinked_linkedFreeJson {Name : Type} (name : Name) :
    decodeLinked (linkedFreeJson name) = some (.free (.inr name)) := by
  have hkeys :
      (⟨(["tag", "name"] : List String), by simp⟩ : Finset String) = {"tag", "name"} := by
    ext key
    simp
  simp [decodeLinked, decodeLinkedWith, decodeWith, decodeFuel, linkedFreeJson,
    linkedFreeJsonWith, field?, scalar?, hasKeys, linkedProfile, Nucleus.Json.ofEntries,
    Nucleus.Json.get?, Schema.v0, hkeys]

end ExtensionalCodec

end Nucleus.HolJson
