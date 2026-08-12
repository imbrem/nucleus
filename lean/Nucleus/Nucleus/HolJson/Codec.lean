import Nucleus.HolJson.Schema
import Nucleus.Json.Raw

/-!
# The v0 HOL JSON tree codec

This module formalizes the initial Rust/Serde representation.  Every node is
an object whose first member is `"tag"`; remaining members are the fields of
the fixed struct wrapped by that enum variant.  Children are nested JSON
trees.  The decoder is intentionally strict about member order, spelling,
arity, and scalar kinds, matching the canonical output produced by Serde.

Strict raw decoding gives a small, auditable canonical-output language.  It is
not the semantic JSON boundary: ordinary JSON objects are unordered, so the
extensional codec layered above this module accepts member permutations after
duplicate-key validation.
-/

namespace Nucleus.HolJson

/-- Scalar kinds used by the v0 HOL JSON profile. -/
inductive Scalar where
  | string (value : String)
  | uint (value : UInt64)
  | bool (value : Bool)
  deriving DecidableEq, Repr

abbrev Json := RawJson Scalar

namespace Codec

private def string (value : String) : Json := .scalar (.string value)
private def uint (value : UInt64) : Json := .scalar (.uint value)
private def bool (value : Bool) : Json := .scalar (.bool value)

private def field (key : String) (value : Json) (tail : RawSyn String Scalar JsonIx.obj) :
    RawSyn String Scalar JsonIx.obj := .objCons key value tail

private def tagged (schema : Schema) (tag : String)
    (fields : RawSyn String Scalar JsonIx.obj := .objNil) : Json :=
  .map (.objCons schema.tagField (string tag) fields)

/-- Serialize a raw HOL tree with an explicit tagged-object vocabulary. -/
def encodeWith (schema : Schema) : WireSyntax -> Json
  | .base name => tagged schema schema.tyBaseTag
      (field schema.nameField (string name) .objNil)
  | .boolTy => tagged schema schema.tyBoolTag
  | .indTy => tagged schema schema.tyIndTag
  | .arr domain codomain =>
      tagged schema schema.tyArrTag (field schema.domainField (encodeWith schema domain)
        (field schema.codomainField (encodeWith schema codomain) .objNil))
  | .sub carrier predicate =>
      tagged schema schema.tySubTag (field schema.carrierField (encodeWith schema carrier)
        (field schema.predicateField (encodeWith schema predicate) .objNil))
  | .bound index => tagged schema schema.tmBoundTag
      (field schema.indexField (uint index) .objNil)
  | .free name => tagged schema schema.tmFreeTag
      (field schema.nameField (uint name) .objNil)
  | .app function argument =>
      tagged schema schema.tmAppTag (field schema.functionField (encodeWith schema function)
        (field schema.argumentField (encodeWith schema argument) .objNil))
  | .lam domain body =>
      tagged schema schema.tmLamTag (field schema.domainField (encodeWith schema domain)
        (field schema.bodyField (encodeWith schema body) .objNil))
  | .bool value => tagged schema schema.tmBoolTag
      (field schema.valueField (bool value) .objNil)
  | .zero => tagged schema schema.tmZeroTag
  | .succ value => tagged schema schema.tmSuccTag
      (field schema.valueField (encodeWith schema value) .objNil)
  | .eqn type left right =>
      tagged schema schema.tmEqTag (field schema.typeField (encodeWith schema type)
        (field schema.leftField (encodeWith schema left)
          (field schema.rightField (encodeWith schema right) .objNil)))
  | .eps type predicate =>
      tagged schema schema.tmEpsTag (field schema.typeField (encodeWith schema type)
        (field schema.predicateField (encodeWith schema predicate) .objNil))
  | .abs carrier predicate value =>
      tagged schema schema.tmAbsTag (field schema.carrierField (encodeWith schema carrier)
        (field schema.predicateField (encodeWith schema predicate)
          (field schema.valueField (encodeWith schema value) .objNil)))
  | .rep carrier predicate value =>
      tagged schema schema.tmRepTag (field schema.carrierField (encodeWith schema carrier)
        (field schema.predicateField (encodeWith schema predicate)
          (field schema.valueField (encodeWith schema value) .objNil)))

/-- Serialize with the inspectable v0 vocabulary. -/
def encode : WireSyntax -> Json := encodeWith Schema.v0

/-- Serialize using an implicitly supplied schema. -/
def encodeProvided [SchemaProvider] : WireSyntax -> Json := encodeWith providedSchema

private def decodeFuel (schema : Schema) : Nat -> Json -> Option WireSyntax
  | 0, _ => none
  | fuel + 1, .map (.objCons key (.scalar (.string tag)) fields) =>
      if key != schema.tagField then none
      else
      if tag = schema.tyBaseTag then
        match fields with
        | .objCons key (.scalar (.string name)) .objNil =>
            if key = schema.nameField then some (.base name) else none
        | _ => none
      else if tag = schema.tyBoolTag then
        match fields with | .objNil => some .boolTy | _ => none
      else if tag = schema.tyIndTag then
        match fields with | .objNil => some .indTy | _ => none
      else if tag = schema.tyArrTag then
        match fields with
        | .objCons first domain (.objCons second codomain .objNil) =>
            if first = schema.domainField ∧ second = schema.codomainField then
              return .arr (← decodeFuel schema fuel domain)
                (← decodeFuel schema fuel codomain)
            else none
        | _ => none
      else if tag = schema.tySubTag then
        match fields with
        | .objCons first carrier (.objCons second predicate .objNil) =>
            if first = schema.carrierField ∧ second = schema.predicateField then
              return .sub (← decodeFuel schema fuel carrier)
                (← decodeFuel schema fuel predicate)
            else none
        | _ => none
      else if tag = schema.tmBoundTag then
        match fields with
        | .objCons key (.scalar (.uint index)) .objNil =>
            if key = schema.indexField then some (.bound index) else none
        | _ => none
      else if tag = schema.tmFreeTag then
        match fields with
        | .objCons key (.scalar (.uint name)) .objNil =>
            if key = schema.nameField then some (.free name) else none
        | _ => none
      else if tag = schema.tmAppTag then
        match fields with
        | .objCons first function (.objCons second argument .objNil) =>
            if first = schema.functionField ∧ second = schema.argumentField then
              return .app (← decodeFuel schema fuel function)
                (← decodeFuel schema fuel argument)
            else none
        | _ => none
      else if tag = schema.tmLamTag then
        match fields with
        | .objCons first domain (.objCons second body .objNil) =>
            if first = schema.domainField ∧ second = schema.bodyField then
              return .lam (← decodeFuel schema fuel domain) (← decodeFuel schema fuel body)
            else none
        | _ => none
      else if tag = schema.tmBoolTag then
        match fields with
        | .objCons key (.scalar (.bool value)) .objNil =>
            if key = schema.valueField then some (.bool value) else none
        | _ => none
      else if tag = schema.tmZeroTag then
        match fields with | .objNil => some .zero | _ => none
      else if tag = schema.tmSuccTag then
        match fields with
        | .objCons key value .objNil =>
            if key = schema.valueField then
              return .succ (← decodeFuel schema fuel value)
            else none
        | _ => none
      else if tag = schema.tmEqTag then
        match fields with
        | .objCons first type (.objCons second left (.objCons third right .objNil)) =>
            if first = schema.typeField ∧ second = schema.leftField ∧
                third = schema.rightField then
              return .eqn (← decodeFuel schema fuel type) (← decodeFuel schema fuel left)
                (← decodeFuel schema fuel right)
            else none
        | _ => none
      else if tag = schema.tmEpsTag then
        match fields with
        | .objCons first type (.objCons second predicate .objNil) =>
            if first = schema.typeField ∧ second = schema.predicateField then
              return .eps (← decodeFuel schema fuel type)
                (← decodeFuel schema fuel predicate)
            else none
        | _ => none
      else if tag = schema.tmAbsTag then
        match fields with
        | .objCons first carrier
            (.objCons second predicate (.objCons third value .objNil)) =>
            if first = schema.carrierField ∧ second = schema.predicateField ∧
                third = schema.valueField then
              return .abs (← decodeFuel schema fuel carrier)
                (← decodeFuel schema fuel predicate) (← decodeFuel schema fuel value)
            else none
        | _ => none
      else if tag = schema.tmRepTag then
        match fields with
        | .objCons first carrier
            (.objCons second predicate (.objCons third value .objNil)) =>
            if first = schema.carrierField ∧ second = schema.predicateField ∧
                third = schema.valueField then
              return .rep (← decodeFuel schema fuel carrier)
                (← decodeFuel schema fuel predicate) (← decodeFuel schema fuel value)
            else none
        | _ => none
      else none
  | _ + 1, _ => none

private def height : WireSyntax -> Nat
  | .base _ | .boolTy | .indTy | .bound _ | .free _ | .bool _ | .zero => 0
  | .arr a b | .sub a b | .app a b | .lam a b | .eps a b =>
      1 + max (height a) (height b)
  | .succ value => 1 + height value
  | .eqn a b c | .abs a b c | .rep a b c =>
      1 + max (height a) (max (height b) (height c))

private theorem succ_lt_succ_iff' (a n : Nat) : 1 + a < n + 1 ↔ a < n := by
  omega

/-- Parse one exact v0 nested HOL JSON tree.  Fuel is derived from the input's
JSON depth, so decoding is total even for adversarial trees. -/
def decodeWith (schema : Schema) (json : Json) : Option WireSyntax :=
  decodeFuel schema (json.depth + 1) json

/-- Parse the exact v0 nested HOL JSON tree. -/
def decode (json : Json) : Option WireSyntax := decodeWith Schema.v0 json

/-- Decode using an implicitly supplied schema. -/
def decodeProvided [SchemaProvider] (json : Json) : Option WireSyntax :=
  decodeWith providedSchema json

private theorem decodeFuel_encode (term : WireSyntax) (fuel : Nat)
    (enough : height term < fuel) :
    decodeFuel Schema.v0 fuel (encode term) = some term := by
  induction term generalizing fuel <;> cases fuel <;>
    simp_all [height, encode, encodeWith, tagged, field, string, uint, bool, decodeFuel,
      Schema.v0, succ_lt_succ_iff', Nat.max_lt]

private theorem height_lt_encode_depth (term : WireSyntax) :
    height term < (encode term).depth + 1 := by
  induction term <;>
    simp_all [height, encode, encodeWith, tagged, field, string, uint, bool, RawSyn.depth,
      Schema.v0] <;> omega

/-- Serialization followed by deserialization is the identity on every raw
HOL tree. -/
@[simp] theorem decode_encode (term : WireSyntax) : decode (encode term) = some term := by
  exact decodeFuel_encode term ((encode term).depth + 1) (height_lt_encode_depth term)

/-- The v0 serializer is injective, as an immediate consequence of the
verified decoder. -/
theorem encode_injective : Function.Injective encode :=
  fun {left right} equality => Option.some.inj (by
    rw [← decode_encode left, ← decode_encode right, equality])

end Codec

end Nucleus.HolJson
