import Nucleus.HolJson.Syntax

/-!
# Inspectable HOL JSON vocabulary

Every externally visible tag and field name lives in `Schema`.  Codecs take a
schema explicitly so several versions can coexist; `SchemaProvider` is an
optional typeclass facade for applications that want an implicit choice.
-/

namespace Nucleus.HolJson

/-- Names used by one tagged-object HOL JSON dialect. -/
structure Schema where
  tagField : String
  nameField : String
  domainField : String
  codomainField : String
  carrierField : String
  predicateField : String
  indexField : String
  functionField : String
  argumentField : String
  bodyField : String
  valueField : String
  typeField : String
  leftField : String
  rightField : String
  tyBaseTag : String
  tyBoolTag : String
  tyIndTag : String
  tyArrTag : String
  tySubTag : String
  tmBoundTag : String
  tmFreeTag : String
  tmAppTag : String
  tmLamTag : String
  tmBoolTag : String
  tmZeroTag : String
  tmSuccTag : String
  tmEqTag : String
  tmEpsTag : String
  tmAbsTag : String
  tmRepTag : String
  deriving DecidableEq, Repr

/-- The initial Rust/Serde vocabulary. -/
def Schema.v0 : Schema where
  tagField := "tag"
  nameField := "name"
  domainField := "domain"
  codomainField := "codomain"
  carrierField := "carrier"
  predicateField := "predicate"
  indexField := "index"
  functionField := "function"
  argumentField := "argument"
  bodyField := "body"
  valueField := "value"
  typeField := "type"
  leftField := "left"
  rightField := "right"
  tyBaseTag := "ty.base"
  tyBoolTag := "ty.bool"
  tyIndTag := "ty.ind"
  tyArrTag := "ty.arr"
  tySubTag := "ty.sub"
  tmBoundTag := "tm.bound"
  tmFreeTag := "tm.free"
  tmAppTag := "tm.app"
  tmLamTag := "tm.lam"
  tmBoolTag := "tm.bool"
  tmZeroTag := "tm.zero"
  tmSuccTag := "tm.succ"
  tmEqTag := "tm.eq"
  tmEpsTag := "tm.eps"
  tmAbsTag := "tm.abs"
  tmRepTag := "tm.rep"

/-- All field names, in a stable inspection order. -/
def Schema.fields (schema : Schema) : List String :=
  [schema.tagField, schema.nameField, schema.domainField, schema.codomainField,
    schema.carrierField, schema.predicateField, schema.indexField, schema.functionField,
    schema.argumentField, schema.bodyField, schema.valueField, schema.typeField,
    schema.leftField, schema.rightField]

/-- All constructor tags, in syntax-constructor order. -/
def Schema.tags (schema : Schema) : List String :=
  [schema.tyBaseTag, schema.tyBoolTag, schema.tyIndTag, schema.tyArrTag, schema.tySubTag,
    schema.tmBoundTag, schema.tmFreeTag, schema.tmAppTag, schema.tmLamTag, schema.tmBoolTag,
    schema.tmZeroTag, schema.tmSuccTag, schema.tmEqTag, schema.tmEpsTag, schema.tmAbsTag,
    schema.tmRepTag]

/-- A schema is unambiguous when field names and constructor tags are each
duplicate-free. -/
def Schema.WellFormed (schema : Schema) : Prop :=
  schema.fields.Nodup ∧ schema.tags.Nodup

@[simp] theorem Schema.v0_wellFormed : Schema.v0.WellFormed := by
  unfold Schema.WellFormed Schema.fields Schema.tags Schema.v0
  decide

/-- Optional implicit configuration for higher-level applications. Core codecs
prefer an explicit `Schema` argument. -/
class SchemaProvider where
  schema : Schema

/-- Retrieve the schema chosen by an implicit provider. -/
def providedSchema [provider : SchemaProvider] : Schema := provider.schema

end Nucleus.HolJson
