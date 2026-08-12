import Nucleus.HolJson.ExtensionalCodec
import Nucleus.Json.Cas

/-!
# Gas-bounded HOL imports

Unlike generic all-or-nothing CAS fetching, HOL import decoding has a useful
total fallback: an unresolved import is an opaque free variable named by the
link.  This preserves the distinction between original numeric free names and
import names as `UInt64 ⊕ Name`.
-/

namespace Nucleus.HolJson.LinkedCas

open Nucleus

variable {Name : Type}

private def freeJson (name : Name) : Nucleus.Json (Scalar ⊕ Name) :=
  ExtensionalCodec.linkedFreeJson name

/-- Replace links using `resolve`, while embedding ordinary scalars on the
left. Container shape and object keys are unchanged. -/
def derefOrWith (resolve : Name -> Nucleus.Json (Scalar ⊕ Name)) :
    Nucleus.Json (Link Scalar Name) -> Nucleus.Json (Scalar ⊕ Name)
  | .scalar (.inl scalar) => .scalar (.inl scalar)
  | .scalar (.inr name) => resolve name
  | .list n elems => .list n fun i => derefOrWith resolve (elems i)
  | .map keys vals => .map keys fun key => derefOrWith resolve (vals key)

/-- Follow at most `gas` store entries. Running out of gas, or encountering a
missing name, returns the caller-supplied opaque fallback for that exact name. -/
def fetchOr [DecidableEq Name] (cas : JsonCas Scalar Name)
    (fallback : Name -> Nucleus.Json (Scalar ⊕ Name)) :
    Nat -> Name -> Nucleus.Json (Scalar ⊕ Name)
  | 0, name => fallback name
  | gas + 1, name =>
      match cas.get? name with
      | .unknown => fallback name
      | .known json => derefOrWith (fetchOr cas fallback gas) json

@[simp] theorem fetchOr_zero [DecidableEq Name] (cas : JsonCas Scalar Name)
    (fallback : Name -> Nucleus.Json (Scalar ⊕ Name)) (name : Name) :
    fetchOr cas fallback 0 name = fallback name := rfl

/-- Resolve imports with an explicit HOL vocabulary and its required distinct
tag/name fields. -/
def resolveWith [DecidableEq Name] (schema : Schema)
    (tag_ne_name : schema.tagField ≠ schema.nameField) (cas : JsonCas Scalar Name)
    (gas : Nat) (name : Name) : Nucleus.Json (Scalar ⊕ Name) :=
  fetchOr cas (ExtensionalCodec.linkedFreeJsonWith schema tag_ne_name) gas name

/-- Resolve imports with the v0 opaque-free-variable fallback. -/
def resolve [DecidableEq Name] (cas : JsonCas Scalar Name) (gas : Nat) (name : Name) :
    Nucleus.Json (Scalar ⊕ Name) :=
  resolveWith Schema.v0 (by decide) cas gas name

@[simp] theorem resolve_zero [DecidableEq Name] (cas : JsonCas Scalar Name) (name : Name) :
    resolve cas 0 name = freeJson name := rfl

/-- Resolve and decode with an explicit vocabulary. -/
def decodeWith [DecidableEq Name] (schema : Schema)
    (tag_ne_name : schema.tagField ≠ schema.nameField) (cas : JsonCas Scalar Name)
    (gas : Nat) (name : Name) : Option (Syntax String (UInt64 ⊕ Name)) :=
  ExtensionalCodec.decodeLinkedWith schema
    (resolveWith schema tag_ne_name cas gas name)

/-- Resolve a named JSON value and decode it as raw v0 HOL syntax. Original
free names inhabit the left summand; unresolved imports inhabit the right. -/
def decode [DecidableEq Name] (cas : JsonCas Scalar Name) (gas : Nat) (name : Name) :
    Option (Syntax String (UInt64 ⊕ Name)) :=
  decodeWith Schema.v0 (by decide) cas gas name

@[simp] theorem decode_zero [DecidableEq Name] (cas : JsonCas Scalar Name) (name : Name) :
    decode cas 0 name = some (.free (.inr name)) := by
  simp only [decode, decodeWith, resolveWith, fetchOr]
  change ExtensionalCodec.decodeLinked (ExtensionalCodec.linkedFreeJson name) =
    some (.free (.inr name))
  exact ExtensionalCodec.decodeLinked_linkedFreeJson name

end Nucleus.HolJson.LinkedCas
