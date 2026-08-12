import Nucleus.HolLN.Syntax
import Nucleus.Json.Raw

/-!
# JSON trees for locally nameless HOL

This module serializes the actual intrinsically scoped `HolLN.Hol` family,
rather than introducing a second untyped HOL syntax.  Decoding is indexed by
the expected HOL sort and binder depth; in particular, a bound-variable index
is accepted only when it constructs a `Fin depth`.

The scalar vocabulary remains generic in base symbols and represents natural
numbers directly.  This follows the generic-scalar JSON foundation and keeps
the choice of an RFC numeral/base-symbol profile separate from the logical
codec.
-/

namespace Nucleus.HolLN.Json

universe u v

/-- Object member names used by a HOL JSON dialect. -/
structure Fields where
  tag : String
  name : String
  domain : String
  codomain : String
  carrier : String
  predicate : String
  index : String
  function : String
  argument : String
  body : String
  value : String
  type : String
  left : String
  right : String
  deriving DecidableEq, Repr

/-- Constructor names used by a HOL JSON dialect. -/
structure Tags where
  tyBase : String
  tyBool : String
  tyInd : String
  tyArr : String
  tySub : String
  tmBound : String
  tmFree : String
  tmApp : String
  tmLam : String
  tmBool : String
  tmZero : String
  tmSucc : String
  tmEq : String
  tmEps : String
  tmAbs : String
  tmRep : String
  deriving DecidableEq, Repr

/-- The complete inspectable vocabulary of one HOL JSON dialect. -/
structure Schema where
  fields : Fields
  tags : Tags
  deriving DecidableEq, Repr

/-- Initial nested-object HOL JSON vocabulary. -/
def Schema.v0 : Schema where
  fields := {
    tag := "tag", name := "name", domain := "domain", codomain := "codomain",
    carrier := "carrier", predicate := "predicate", index := "index",
    function := "function", argument := "argument", body := "body", value := "value",
    type := "type", left := "left", right := "right" }
  tags := {
    tyBase := "ty.base", tyBool := "ty.bool", tyInd := "ty.ind", tyArr := "ty.arr",
    tySub := "ty.sub", tmBound := "tm.bound", tmFree := "tm.free", tmApp := "tm.app",
    tmLam := "tm.lam", tmBool := "tm.bool", tmZero := "tm.zero", tmSucc := "tm.succ",
    tmEq := "tm.eq", tmEps := "tm.eps", tmAbs := "tm.abs", tmRep := "tm.rep" }

/-- Field names in a stable inspection order. -/
def Fields.names (fields : Fields) : List String :=
  [fields.tag, fields.name, fields.domain, fields.codomain, fields.carrier,
    fields.predicate, fields.index, fields.function, fields.argument, fields.body,
    fields.value, fields.type, fields.left, fields.right]

/-- Constructor tags in `Hol` constructor order. -/
def Tags.names (tags : Tags) : List String :=
  [tags.tyBase, tags.tyBool, tags.tyInd, tags.tyArr, tags.tySub, tags.tmBound,
    tags.tmFree, tags.tmApp, tags.tmLam, tags.tmBool, tags.tmZero, tags.tmSucc,
    tags.tmEq, tags.tmEps, tags.tmAbs, tags.tmRep]

/-- Tags must be distinct. Field names need not all be distinct because some
positions intentionally share names, but the tag member must be distinguishable
from every payload member. -/
def Schema.WellFormed (schema : Schema) : Prop :=
  schema.tags.names.Nodup ∧
    schema.fields.tag ∉ schema.fields.names.tail

@[simp] theorem Schema.v0_wellFormed : Schema.v0.WellFormed := by
  unfold Schema.WellFormed Schema.v0 Fields.names Tags.names
  decide

/-- Optional implicit selection for applications with one preferred dialect.
Core operations also expose explicit-schema variants so several dialects may
coexist in one process. -/
class SchemaProvider where
  schema : Schema := Schema.v0

/-- Scalar leaves required by the logical HOL codec. -/
inductive Scalar (Base : Type u) (Free : Type v) where
  | string (value : String)
  | index (value : Nat)
  | free (value : Free)
  | bool (value : Bool)
  | base (value : Base)
  deriving Repr

abbrev TreeF (Base : Type u) (Free : Type v) := RawJson (Scalar Base Free)
abbrev Tree (Base : Type u) := TreeF Base Nat

namespace Codec

variable {Base : Type u} {Free : Type v} {sort : HolSort} {depth : Nat}

private def string (value : String) : TreeF Base Free := .scalar (.string value)
private def indexScalar (value : Nat) : TreeF Base Free := .scalar (.index value)
private def free (value : Free) : TreeF Base Free := .scalar (.free value)
private def bool (value : Bool) : TreeF Base Free := .scalar (.bool value)
private def base (value : Base) : TreeF Base Free := .scalar (.base value)

private def field (key : String) (value : TreeF Base Free)
    (tail : RawSyn String (Scalar Base Free) .obj) : RawSyn String (Scalar Base Free) .obj :=
  .objCons key value tail

private def tagged (schema : Schema) (tag : String)
    (fields : RawSyn String (Scalar Base Free) .obj := .objNil) : TreeF Base Free :=
  .map (.objCons schema.fields.tag (string tag) fields)

/-- Serialize an intrinsically scoped HOL type or term as a nested JSON tree. -/
def encodeWith (schema : Schema) : {sort : HolSort} → {depth : Nat} →
    HolF Base Free sort depth → TreeF Base Free
  | _, _, .base name =>
      tagged schema schema.tags.tyBase
        (field schema.fields.name (base name) .objNil)
  | _, _, .boolTy => tagged schema schema.tags.tyBool
  | _, _, .natTy => tagged schema schema.tags.tyInd
  | _, _, .arr domain codomain =>
      tagged schema schema.tags.tyArr
        (field schema.fields.domain (encodeWith schema domain)
          (field schema.fields.codomain (encodeWith schema codomain) .objNil))
  | _, _, .sub carrier predicate =>
      tagged schema schema.tags.tySub
        (field schema.fields.carrier (encodeWith schema carrier)
          (field schema.fields.predicate (encodeWith schema predicate) .objNil))
  | _, _, .bound index =>
      tagged schema schema.tags.tmBound
        (field schema.fields.index (indexScalar index) .objNil)
  | _, _, .free name =>
      tagged schema schema.tags.tmFree
        (field schema.fields.name (free name) .objNil)
  | _, _, .app function argument =>
      tagged schema schema.tags.tmApp
        (field schema.fields.function (encodeWith schema function)
          (field schema.fields.argument (encodeWith schema argument) .objNil))
  | _, _, .lam domain body =>
      tagged schema schema.tags.tmLam
        (field schema.fields.domain (encodeWith schema domain)
          (field schema.fields.body (encodeWith schema body) .objNil))
  | _, _, .bool value =>
      tagged schema schema.tags.tmBool
        (field schema.fields.value (bool value) .objNil)
  | _, _, .zero => tagged schema schema.tags.tmZero
  | _, _, .succ value =>
      tagged schema schema.tags.tmSucc
        (field schema.fields.value (encodeWith schema value) .objNil)
  | _, _, .eq type left right =>
      tagged schema schema.tags.tmEq
        (field schema.fields.type (encodeWith schema type)
          (field schema.fields.left (encodeWith schema left)
            (field schema.fields.right (encodeWith schema right) .objNil)))
  | _, _, .eps type predicate =>
      tagged schema schema.tags.tmEps
        (field schema.fields.type (encodeWith schema type)
          (field schema.fields.predicate (encodeWith schema predicate) .objNil))
  | _, _, .abs carrier predicate value =>
      tagged schema schema.tags.tmAbs
        (field schema.fields.carrier (encodeWith schema carrier)
          (field schema.fields.predicate (encodeWith schema predicate)
            (field schema.fields.value (encodeWith schema value) .objNil)))
  | _, _, .rep carrier predicate value =>
      tagged schema schema.tags.tmRep
        (field schema.fields.carrier (encodeWith schema carrier)
          (field schema.fields.predicate (encodeWith schema predicate)
            (field schema.fields.value (encodeWith schema value) .objNil)))

/-- Serialize with the initial vocabulary. -/
def encode (term : Hol Base sort depth) : Tree Base := encodeWith Schema.v0 term

/-- Decode at the expected HOL sort and binder depth. Recursion follows strict
JSON subtrees, so no operational fuel or artificial size limit is exposed. -/
def decodeOpenWith (schema : Schema) (sort : HolSort) (depth : Nat) :
    TreeF Base Free → Option (HolF Base Free sort depth)
  | .map (.objCons key (.scalar (.string tag)) fields) =>
      if key != schema.fields.tag then none
      else match sort, depth with
      | .ty, 0 =>
        if tag = schema.tags.tyBase then
          match fields with
          | .objCons key (.scalar (.base name)) .objNil =>
              if key = schema.fields.name then some (.base name) else none
          | _ => none
        else if tag = schema.tags.tyBool then
          match fields with | .objNil => some .boolTy | _ => none
        else if tag = schema.tags.tyInd then
          match fields with | .objNil => some .natTy | _ => none
        else if tag = schema.tags.tyArr then
          match fields with
          | .objCons first domain (.objCons second codomain .objNil) =>
              if first = schema.fields.domain ∧ second = schema.fields.codomain then
                return .arr (← decodeOpenWith schema .ty 0 domain)
                  (← decodeOpenWith schema .ty 0 codomain)
              else none
          | _ => none
        else if tag = schema.tags.tySub then
          match fields with
          | .objCons first carrier (.objCons second predicate .objNil) =>
              if first = schema.fields.carrier ∧ second = schema.fields.predicate then
                return .sub (← decodeOpenWith schema .ty 0 carrier)
                  (← decodeOpenWith schema .tm 1 predicate)
              else none
          | _ => none
        else none
      | .ty, _ + 1 => none
      | .tm, depth =>
        if tag = schema.tags.tmBound then
          match fields with
          | .objCons key (.scalar (.index index)) .objNil =>
              if key = schema.fields.index then
                if h : index < depth then some (.bound ⟨index, h⟩) else none
              else none
          | _ => none
        else if tag = schema.tags.tmFree then
          match fields with
          | .objCons key (.scalar (.free name)) .objNil =>
              if key = schema.fields.name then some (.free name) else none
          | _ => none
        else if tag = schema.tags.tmApp then
          match fields with
          | .objCons first function (.objCons second argument .objNil) =>
              if first = schema.fields.function ∧ second = schema.fields.argument then
                return .app (← decodeOpenWith schema .tm depth function)
                  (← decodeOpenWith schema .tm depth argument)
              else none
          | _ => none
        else if tag = schema.tags.tmLam then
          match fields with
          | .objCons first domain (.objCons second body .objNil) =>
              if first = schema.fields.domain ∧ second = schema.fields.body then
                return .lam (← decodeOpenWith schema .ty 0 domain)
                  (← decodeOpenWith schema .tm (depth + 1) body)
              else none
          | _ => none
        else if tag = schema.tags.tmBool then
          match fields with
          | .objCons key (.scalar (.bool value)) .objNil =>
              if key = schema.fields.value then some (.bool value) else none
          | _ => none
        else if tag = schema.tags.tmZero then
          match fields with | .objNil => some .zero | _ => none
        else if tag = schema.tags.tmSucc then
          match fields with
          | .objCons key value .objNil =>
              if key = schema.fields.value then
                match decodeOpenWith schema .tm depth value with
                | some decoded => some (.succ decoded)
                | none => none
              else none
          | _ => none
        else if tag = schema.tags.tmEq then
          match fields with
          | .objCons first type (.objCons second left (.objCons third right .objNil)) =>
              if first = schema.fields.type ∧ second = schema.fields.left ∧
                  third = schema.fields.right then
                return .eq (← decodeOpenWith schema .ty 0 type)
                  (← decodeOpenWith schema .tm depth left)
                  (← decodeOpenWith schema .tm depth right)
              else none
          | _ => none
        else if tag = schema.tags.tmEps then
          match fields with
          | .objCons first type (.objCons second predicate .objNil) =>
              if first = schema.fields.type ∧ second = schema.fields.predicate then
                return .eps (← decodeOpenWith schema .ty 0 type)
                  (← decodeOpenWith schema .tm depth predicate)
              else none
          | _ => none
        else if tag = schema.tags.tmAbs then
          match fields with
          | .objCons first carrier
              (.objCons second predicate (.objCons third value .objNil)) =>
              if first = schema.fields.carrier ∧ second = schema.fields.predicate ∧
                  third = schema.fields.value then
                return .abs (← decodeOpenWith schema .ty 0 carrier)
                  (← decodeOpenWith schema .tm 1 predicate)
                  (← decodeOpenWith schema .tm depth value)
              else none
          | _ => none
        else if tag = schema.tags.tmRep then
          match fields with
          | .objCons first carrier
              (.objCons second predicate (.objCons third value .objNil)) =>
              if first = schema.fields.carrier ∧ second = schema.fields.predicate ∧
                  third = schema.fields.value then
                return .rep (← decodeOpenWith schema .ty 0 carrier)
                  (← decodeOpenWith schema .tm 1 predicate)
                  (← decodeOpenWith schema .tm depth value)
              else none
          | _ => none
        else none
  | _ => none

/-- Decode an intrinsically open type or term with the initial vocabulary.
Most callers should use `decodeTy` or `decodeTm`, which return closed values. -/
def decodeOpen (sort : HolSort) (depth : Nat) (json : Tree Base) :
    Option (Hol Base sort depth) :=
  decodeOpenWith (Base := Base) (Free := Nat) Schema.v0 sort depth json

/-- Decode a closed HOL type with an explicitly selected vocabulary. -/
def decodeTyWith (schema : Schema) (json : Tree Base) : Option (Ty Base) :=
  decodeOpenWith (Base := Base) (Free := Nat) schema .ty 0 json

/-- Decode a closed HOL term with an explicitly selected vocabulary. -/
def decodeTmWith (schema : Schema) (json : Tree Base) : Option (ClosedTm Base) :=
  decodeOpenWith (Base := Base) (Free := Nat) schema .tm 0 json

/-- Decode a closed HOL type with the initial vocabulary. -/
def decodeTy (json : Tree Base) : Option (Ty Base) := decodeTyWith Schema.v0 json

/-- Decode a closed HOL term with the initial vocabulary. -/
def decodeTm (json : Tree Base) : Option (ClosedTm Base) := decodeTmWith Schema.v0 json

/-- Open round trip for the initial vocabulary. -/
@[simp] theorem decodeOpen_encode (term : Hol Base sort depth) :
    decodeOpen sort depth (encode term) = some term := by
  induction term
  case succ openDepth value ih =>
    simp only [decodeOpen, encode, Schema.v0, encodeWith, tagged, field, string]
    unfold decodeOpenWith
    dsimp only [Schema.v0]
    have hkey : ("tag" != "tag") ≠ true := by decide
    have hbound : "tm.succ" ≠ "tm.bound" := by decide
    have hfree : "tm.succ" ≠ "tm.free" := by decide
    have happ : "tm.succ" ≠ "tm.app" := by decide
    have hlam : "tm.succ" ≠ "tm.lam" := by decide
    have hbool : "tm.succ" ≠ "tm.bool" := by decide
    have hzero : "tm.succ" ≠ "tm.zero" := by decide
    rw [if_neg hkey, if_neg hbound, if_neg hfree, if_neg happ, if_neg hlam,
      if_neg hbool, if_neg hzero, if_pos rfl]
    simp only [decodeOpen, encode, Schema.v0] at ih
    rw [ih]
    rw [if_pos rfl]
  all_goals
    simp_all [decodeOpen, encode, Schema.v0, encodeWith, tagged, field, string, indexScalar,
      free, bool, base, decodeOpenWith]

/-- Closed-type round trip for the initial vocabulary. -/
@[simp] theorem decodeTy_encode (type : Ty Base) : decodeTy (encode type) = some type :=
  decodeOpen_encode type

/-- Closed-term round trip for the initial vocabulary. -/
@[simp] theorem decodeTm_encode (term : ClosedTm Base) : decodeTm (encode term) = some term :=
  decodeOpen_encode term

/-- The initial serializer is injective at each intrinsic sort and depth. -/
theorem encode_injective : Function.Injective (encode : Hol Base sort depth → Tree Base) :=
  fun {left right} equality => Option.some.inj (by
    rw [← decodeOpen_encode left, ← decodeOpen_encode right, equality])

end Codec

end Nucleus.HolLN.Json
