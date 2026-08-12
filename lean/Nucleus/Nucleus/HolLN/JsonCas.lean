import Nucleus.HolLN.Json
import Nucleus.Json.Cas

/-!
# Gas-bounded linked HOL JSON

Following a store entry consumes one unit of gas. A missing entry or exhausted
budget becomes the closed HOL term `.free (.inr name)`. Original numeric free
names remain in the left summand, so no hashing or sentinel convention is
involved.
-/

namespace Nucleus.HolLN.Json.Cas

universe u

open Nucleus

variable {Base : Type u} {Name : Type}
variable {Atom : Type u}

abbrev Store (Base : Type u) (Name : Type) := JsonCas (Scalar Base Nat) Name
abbrev ImportedName (Name : Type) := Nat ⊕ Name
abbrev ImportedTm (Base : Type u) (Name : Type) := ClosedTmF Base (ImportedName Name)

private def importScalar : Scalar Base Nat → Scalar Base (ImportedName Name)
  | .string value => .string value
  | .index value => .index value
  | .free name => .free (.inl name)
  | .bool value => .bool value
  | .base value => .base value

/-- An unresolved import is represented by the ordinary free-variable node,
with its link name in the right summand. -/
def unresolvedWith (schema : Schema) (hschema : schema.WellFormed) (name : Name) :
    Nucleus.Json (Scalar Base (ImportedName Name)) :=
  Nucleus.Json.ofEntries
    [(schema.fields.tag, .scalar (.string schema.tags.tmFree)),
      (schema.fields.name, .scalar (.free (.inr name)))]
    (by
      have htag : schema.fields.tag ≠ schema.fields.name := by
        intro equality
        apply hschema.2
        simp [Fields.names, equality]
      simpa using htag)

def unresolved (name : Name) : Nucleus.Json (Scalar Base (ImportedName Name)) :=
  unresolvedWith Schema.v0 Schema.v0_wellFormed name

/-- Replace links using `resolve`, while preserving original free-name
provenance in the left summand. -/
def derefOrWith (resolve : Name → Nucleus.Json (Scalar Base (ImportedName Name))) :
    Nucleus.Json (Link (Scalar Base Nat) Name) →
      Nucleus.Json (Scalar Base (ImportedName Name))
  | .scalar (.inl scalar) => .scalar (importScalar scalar)
  | .scalar (.inr name) => resolve name
  | .list n elems => .list n fun i => derefOrWith resolve (elems i)
  | .map keys vals => .map keys fun key => derefOrWith resolve (vals key)

/-- Follow at most `gas` store entries. Exhausted gas and missing entries use
the fallback for the exact unresolved name. -/
def fetchOr [DecidableEq Name] (store : Store Base Name)
    (fallback : Name → Nucleus.Json (Scalar Base (ImportedName Name))) :
    Nat → Name → Nucleus.Json (Scalar Base (ImportedName Name))
  | 0, name => fallback name
  | gas + 1, name =>
      match store.get? name with
      | Unknown.unknown => fallback name
      | Unknown.known json => derefOrWith (fetchOr store fallback gas) json

def resolveWith [DecidableEq Name] (schema : Schema) (hschema : schema.WellFormed)
    (store : Store Base Name)
    (gas : Nat) (name : Name) : Nucleus.Json (Scalar Base (ImportedName Name)) :=
  fetchOr store (unresolvedWith schema hschema) gas name

def resolve [DecidableEq Name] (store : Store Base Name) (gas : Nat) (name : Name) :
    Nucleus.Json (Scalar Base (ImportedName Name)) :=
  resolveWith Schema.v0 Schema.v0_wellFormed store gas name

private def orderEntries (schema : Schema)
    (entries : List (String × RawJson Atom)) : List (String × RawJson Atom) :=
  let known := schema.fields.names.filterMap fun key =>
    entries.find? fun entry => decide (entry.1 = key)
  let other := entries.filter fun entry => decide (entry.1 ∉ schema.fields.names)
  known ++ other

/-- Choose the raw member order consumed by the strict tree decoder. The
input is extensional and therefore duplicate-free; unknown fields are retained
at the end so malformed nodes remain malformed rather than being normalized
away. -/
private def orderedRaw (schema : Schema) : {ix : JsonIx} → RawSyn String Atom ix →
    RawSyn String Atom ix
  | _, .scalar value => .scalar value
  | _, .list elems => .list (orderedRaw schema elems)
  | _, .map entries =>
      let normalized := orderedRaw schema entries
      .map (RawSyn.ofEntries (orderEntries schema normalized.toEntries))
  | _, .nil => .nil
  | _, .cons head tail => .cons (orderedRaw schema head) (orderedRaw schema tail)
  | _, .objNil => .objNil
  | _, .objCons key value tail =>
      .objCons key (orderedRaw schema value) (orderedRaw schema tail)

private def toDecoderTree (schema : Schema)
    (json : Nucleus.Json Atom) : RawJson Atom :=
  orderedRaw schema json.toRaw

/-- Decode an imported value at an explicit intrinsic sort and binder depth. -/
def decodeOpenWith [DecidableEq Name] (schema : Schema) (hschema : schema.WellFormed)
    (store : Store Base Name)
    (gas : Nat) (name : Name) (sort : HolSort) (depth : Nat) :
    Option (HolF Base (ImportedName Name) sort depth) :=
  Codec.decodeOpenWith (Base := Base) (Free := ImportedName Name) schema sort depth
    (toDecoderTree schema
      (resolveWith (Base := Base) (Name := Name) schema hschema store gas name))

def decodeOpen [DecidableEq Name] (store : Store Base Name) (gas : Nat) (name : Name)
    (sort : HolSort) (depth : Nat) : Option (HolF Base (ImportedName Name) sort depth) :=
  decodeOpenWith Schema.v0 Schema.v0_wellFormed store gas name sort depth

/-- Decode a linked entry as a closed HOL type. -/
def decodeTy [DecidableEq Name] (store : Store Base Name) (gas : Nat) (name : Name) :
    Option (TyF Base (ImportedName Name)) :=
  decodeOpen store gas name .ty 0

/-- Decode a linked entry as a closed HOL term. -/
def decodeTm [DecidableEq Name] (store : Store Base Name) (gas : Nat) (name : Name) :
    Option (ImportedTm Base Name) := match gas with
  | 0 => some (.free (.inr name))
  | gas + 1 => decodeOpen store (gas + 1) name .tm 0

@[simp] theorem fetchOr_zero [DecidableEq Name] (store : Store Base Name)
    (fallback : Name → Nucleus.Json (Scalar Base (ImportedName Name))) (name : Name) :
    fetchOr store fallback 0 name = fallback name := rfl

@[simp] theorem resolve_zero [DecidableEq Name] (store : Store Base Name) (name : Name) :
    resolve store 0 name = unresolved name := rfl

/-- Exhausting the budget at the root produces the exact unresolved link name
as a closed free term. -/
@[simp] theorem decodeTm_zero [DecidableEq Name] (store : Store Base Name) (name : Name) :
    decodeTm store 0 name = some (.free (.inr name)) := rfl

end Nucleus.HolLN.Json.Cas
