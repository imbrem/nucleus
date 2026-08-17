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

universe u

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
  kind : String
  deriving DecidableEq, Repr

/-- Constructor names used by a HOL JSON dialect. -/
structure Tags where
  tyBase : String
  tyBool : String
  tyInd : String
  tyArr : String
  tyApp : String
  tySub : String
  tmBv : String
  tmFv : String
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
    type := "type", left := "left", right := "right", kind := "kind" }
  tags := {
    tyBase := "ty.base", tyBool := "ty.bool", tyInd := "ty.ind",
    tyArr := "ty.arr", tyApp := "ty.app",
    tySub := "ty.sub", tmBv := "tm.bv", tmFv := "tm.fv", tmApp := "tm.app",
    tmLam := "tm.lam", tmBool := "tm.bool", tmZero := "tm.zero", tmSucc := "tm.succ",
    tmEq := "tm.eq", tmEps := "tm.eps", tmAbs := "tm.abs", tmRep := "tm.rep" }

/-- Field names in a stable inspection order. -/
def Fields.names (fields : Fields) : List String :=
  [fields.tag, fields.name, fields.domain, fields.codomain, fields.carrier,
    fields.predicate, fields.index, fields.function, fields.argument, fields.body,
    fields.value, fields.type, fields.left, fields.right, fields.kind]

/-- Constructor tags in `Hol` constructor order. -/
def Tags.names (tags : Tags) : List String :=
  [tags.tyBase, tags.tyBool, tags.tyInd, tags.tyArr, tags.tyApp, tags.tySub, tags.tmBv,
    tags.tmFv, tags.tmApp, tags.tmLam, tags.tmBool, tags.tmZero, tags.tmSucc,
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
inductive Scalar (Base : Type u) where
  | string (value : String)
  | nat (value : Nat)
  | bool (value : Bool)
  | base (value : Base)
  | kind (value : Kind)
  deriving Repr

abbrev Tree (Base : Type u) := RawJson (Scalar Base)

namespace Codec

variable {Base : Type u} {sort : HolSort} {depth : Nat}

private def string (value : String) : Tree Base := .scalar (.string value)
private def nat (value : Nat) : Tree Base := .scalar (.nat value)
private def bool (value : Bool) : Tree Base := .scalar (.bool value)
private def base (value : Base) : Tree Base := .scalar (.base value)
private def kindScalar (value : Kind) : Tree Base := .scalar (.kind value)

private def field (key : String) (value : Tree Base) (tail : RawSyn String (Scalar Base) .obj) :
    RawSyn String (Scalar Base) .obj := .objCons key value tail

private def tagged (schema : Schema) (tag : String)
    (fields : RawSyn String (Scalar Base) .obj := .objNil) : Tree Base :=
  .map (.objCons schema.fields.tag (string tag) fields)

/-- Serialize an intrinsically scoped HOL type or term as a nested JSON tree. -/
def encodeWith (schema : Schema) : {sort : HolSort} → {depth : Nat} →
    Hol Base sort depth → Tree Base
  | .kind kind, _, .base name =>
      tagged schema schema.tags.tyBase
        (field schema.fields.name (base name)
          (field schema.fields.kind (kindScalar kind) .objNil))
  | _, _, .boolTy => tagged schema schema.tags.tyBool
  | _, _, .natTy => tagged schema schema.tags.tyInd
  | _, _, .arr domain codomain =>
      tagged schema schema.tags.tyArr
        (field schema.fields.domain (encodeWith schema domain)
          (field schema.fields.codomain (encodeWith schema codomain) .objNil))
  | .kind _, _, @Hol.tyApp _ domain _ function argument =>
      tagged schema schema.tags.tyApp
        (field schema.fields.kind (kindScalar domain)
          (field schema.fields.function (encodeWith schema function)
            (field schema.fields.argument (encodeWith schema argument) .objNil)))
  | _, _, .sub carrier predicate =>
      tagged schema schema.tags.tySub
        (field schema.fields.carrier (encodeWith schema carrier)
          (field schema.fields.predicate (encodeWith schema predicate) .objNil))
  | _, _, .bv index =>
      tagged schema schema.tags.tmBv
        (field schema.fields.index (nat index) .objNil)
  | _, _, .fv name type =>
      tagged schema schema.tags.tmFv
        (field schema.fields.name (nat name)
          (field schema.fields.type (encodeWith schema type) .objNil))
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
    Tree Base → Option (Hol Base sort depth)
  | .map (.objCons key (.scalar (.string tag)) fields) =>
      if key != schema.fields.tag then none
      else match sort, depth with
      | .kind expected, 0 =>
        if tag = schema.tags.tyBase then
          match fields with
          | .objCons first (.scalar (.base name))
              (.objCons second (.scalar (.kind actual)) .objNil) =>
              if first = schema.fields.name ∧ second = schema.fields.kind then
                if h : actual = expected then by
                  subst actual; exact some (.base name)
                else none
              else none
          | _ => none
        else if tag = schema.tags.tyBool then
          if h : expected = .star then by
            subst expected; exact match fields with | .objNil => some .boolTy | _ => none
          else none
        else if tag = schema.tags.tyInd then
          if h : expected = .star then by
            subst expected; exact match fields with | .objNil => some .natTy | _ => none
          else none
        else if tag = schema.tags.tyArr then
          match fields with
          | .objCons first domain (.objCons second codomain .objNil) =>
              if first = schema.fields.domain ∧ second = schema.fields.codomain then
                if h : expected = .star then by
                  subst expected
                  exact do
                    let A ← decodeOpenWith schema (.kind .star) 0 domain
                    let B ← decodeOpenWith schema (.kind .star) 0 codomain
                    return .arr A B
                else none
              else none
          | _ => none
        else if tag = schema.tags.tyApp then
          match fields with
          | .objCons first (.scalar (.kind domain))
              (.objCons second function (.objCons third argument .objNil)) =>
              if first = schema.fields.kind ∧ second = schema.fields.function ∧
                  third = schema.fields.argument then
                do
                  let F ← decodeOpenWith schema (.kind (.arr domain expected)) 0 function
                  let A ← decodeOpenWith schema (.kind domain) 0 argument
                  return .tyApp F A
              else none
          | _ => none
        else if tag = schema.tags.tySub then
          match fields with
          | .objCons first carrier (.objCons second predicate .objNil) =>
              if first = schema.fields.carrier ∧ second = schema.fields.predicate then
                if h : expected = .star then by
                  subst expected
                  exact do
                    let A ← decodeOpenWith schema (.kind .star) 0 carrier
                    let p ← decodeOpenWith schema .tm 1 predicate
                    return .sub A p
                else none
              else none
          | _ => none
        else none
      | .kind _, _ + 1 => none
      | .tm, depth =>
        if tag = schema.tags.tmBv then
          match fields with
          | .objCons key (.scalar (.nat index)) .objNil =>
              if key = schema.fields.index then
                if h : index < depth then some (.bv ⟨index, h⟩) else none
              else none
          | _ => none
        else if tag = schema.tags.tmFv then
          match fields with
          | .objCons first (.scalar (.nat name)) (.objCons second type .objNil) =>
              if first = schema.fields.name ∧ second = schema.fields.type then
                return .fv name (← decodeOpenWith schema (.kind .star) 0 type)
              else none
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
                return .lam (← decodeOpenWith schema (.kind .star) 0 domain)
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
                return .eq (← decodeOpenWith schema (.kind .star) 0 type)
                  (← decodeOpenWith schema .tm depth left)
                  (← decodeOpenWith schema .tm depth right)
              else none
          | _ => none
        else if tag = schema.tags.tmEps then
          match fields with
          | .objCons first type (.objCons second predicate .objNil) =>
              if first = schema.fields.type ∧ second = schema.fields.predicate then
                return .eps (← decodeOpenWith schema (.kind .star) 0 type)
                  (← decodeOpenWith schema .tm depth predicate)
              else none
          | _ => none
        else if tag = schema.tags.tmAbs then
          match fields with
          | .objCons first carrier
              (.objCons second predicate (.objCons third value .objNil)) =>
              if first = schema.fields.carrier ∧ second = schema.fields.predicate ∧
                  third = schema.fields.value then
                return .abs (← decodeOpenWith schema (.kind .star) 0 carrier)
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
                return .rep (← decodeOpenWith schema (.kind .star) 0 carrier)
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
  decodeOpenWith Schema.v0 sort depth json

/-- Decode a closed HOL type with an explicitly selected vocabulary. -/
def decodeTyWith (schema : Schema) (json : Tree Base) : Option (Ty Base) :=
  decodeOpenWith schema (.kind .star) 0 json

/-- Decode a closed HOL term with an explicitly selected vocabulary. -/
def decodeTmWith (schema : Schema) (json : Tree Base) : Option (ClosedTm Base) :=
  decodeOpenWith schema .tm 0 json

/-- Decode a closed HOL type with the initial vocabulary. -/
def decodeTy (json : Tree Base) : Option (Ty Base) := decodeTyWith Schema.v0 json

/-- Decode a closed HOL term with the initial vocabulary. -/
def decodeTm (json : Tree Base) : Option (ClosedTm Base) := decodeTmWith Schema.v0 json

/-- Open round trip for the initial vocabulary. -/
@[simp] theorem decodeOpen_encode (term : Hol Base sort depth) :
    decodeOpen sort depth (encode term) = some term := by
  induction term
  case base kind name =>
    simp only [decodeOpen, encode, encodeWith, tagged, field, string, base, kindScalar]
    unfold decodeOpenWith
    simp [Schema.v0]
  case tyApp domain codomain function argument function_ih argument_ih =>
    simp only [decodeOpen, encode, Schema.v0] at function_ih argument_ih
    simp only [decodeOpen, encode, encodeWith, tagged, field, string, kindScalar]
    unfold decodeOpenWith
    simp [Schema.v0, function_ih, argument_ih]
  all_goals
    simp only [decodeOpen, encode, Schema.v0, encodeWith, tagged, field, string,
      nat, bool] at *
    unfold decodeOpenWith
    simp_all [Option.bind]

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
