import Mathlib.Data.List.InsertIdx
import Nucleus.Json.Path

/-!
# JSON Patch

An extensional, key-parametric model of the six RFC 6902 operations. Paths are
the singular object/index paths from `Nucleus.Json.Path`. Applying a list is
transactional in the usual pure sense: the first failing operation returns
`none`, so no partially updated document is observable.
-/

namespace Nucleus

universe u

/-- The six JSON Patch operation forms. -/
inductive JsonPatchOp (Scalar : Type u) (Key : Type := String) where
  | add (path : KeyedJsonPath Key) (value : Json Scalar Key)
  | remove (path : KeyedJsonPath Key)
  | replace (path : KeyedJsonPath Key) (value : Json Scalar Key)
  | move (source path : KeyedJsonPath Key)
  | copy (source path : KeyedJsonPath Key)
  | test (path : KeyedJsonPath Key) (value : Json Scalar Key)

abbrev JsonPatch (Scalar : Type u) (Key : Type := String) := List (JsonPatchOp Scalar Key)

namespace Json

variable {Key : Type} {Scalar : Type u} [DecidableEq Key]

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

private def ofList (values : List (Json Scalar Key)) : Json Scalar Key :=
  .list values.length values.get

/-- Remove one immediate child selected by a final path step. -/
def removeChild? : Json Scalar Key → KeyedJsonStep Key → Option (Json Scalar Key)
  | .list n elems, .index i =>
      if _hi : i < n then some (ofList ((List.ofFn elems).eraseIdx i)) else none
  | .map keys vals, .key key =>
      if _hk : key ∈ keys then
        some (.map (keys.erase key) fun k => vals ⟨k.1, Finset.mem_of_mem_erase k.2⟩)
      else none
  | _, _ => none

/-- Remove a non-root location. Removing the document root has no JSON-valued
result and therefore fails. -/
def remove? (json : Json Scalar Key) (path : KeyedJsonPath Key) : Option (Json Scalar Key) :=
  match path.getLast? with
  | none => none
  | some step => json.modify? path.dropLast (fun parent => parent.removeChild? step)

/-- Add or overwrite one immediate child. Array index `n` appends; indices
greater than `n` fail. Object members are inserted or replaced. -/
def addChild? : Json Scalar Key → KeyedJsonStep Key → Json Scalar Key → Option (Json Scalar Key)
  | .list n elems, .index i, value =>
      if hi : i ≤ n then some (ofList ((List.ofFn elems).insertIdx i value)) else none
  | .map keys vals, .key key, value =>
      some (.map (insert key keys) fun k =>
        if heq : k.1 = key then value
        else vals ⟨k.1, by
          rcases Finset.mem_insert.mp k.2 with h | h
          · exact False.elim (heq h)
          · exact h⟩)
  | _, _, _ => none

/-- RFC-style add. Adding at the empty path replaces the whole document. -/
def add? (json : Json Scalar Key) (path : KeyedJsonPath Key)
    (value : Json Scalar Key) : Option (Json Scalar Key) :=
  match path.getLast? with
  | none => some value
  | some step => json.modify? path.dropLast (fun parent => parent.addChild? step value)

/-- Apply one JSON Patch operation. Equality for `test` is extensional JSON
equality; it is propositionally decidable here rather than adding an artificial
computable equality instance to function-backed JSON containers. -/
noncomputable def applyPatchOp (json : Json Scalar Key) :
    JsonPatchOp Scalar Key → Option (Json Scalar Key)
  | .add path value => json.add? path value
  | .remove path => json.remove? path
  | .replace path value => json.replace? path value
  | .copy source path => do
      let value ← json.get? source
      json.add? path value
  | .move source path => do
      let value ← json.get? source
      let removed ← json.remove? source
      removed.add? path value
  | .test path expected => do
      let actual ← json.get? path
      if actual = expected then some json else none

/-- Apply a patch sequence from left to right, stopping at its first failure. -/
noncomputable def applyPatch : Json Scalar Key → JsonPatch Scalar Key → Option (Json Scalar Key)
  | json, [] => some json
  | json, op :: ops => (json.applyPatchOp op).bind fun updated => updated.applyPatch ops

@[simp] theorem applyPatch_nil (json : Json Scalar Key) : json.applyPatch [] = some json := rfl

/-- Patch concatenation is Kleisli composition. -/
theorem applyPatch_append (json : Json Scalar Key)
    (first second : JsonPatch Scalar Key) :
    json.applyPatch (first ++ second) =
      (json.applyPatch first).bind fun updated => updated.applyPatch second := by
  induction first generalizing json with
  | nil => rfl
  | cons op rest ih => simp [applyPatch, ih, Option.bind_assoc]

/-- Successful replacement has the advertised lookup semantics. -/
theorem get?_applyPatchOp_replace {json updated value : Json Scalar Key}
    {path : KeyedJsonPath Key}
    (h : json.applyPatchOp (.replace path value) = some updated) :
    updated.get? path = some value :=
  get?_replace? h

@[simp] theorem applyPatchOp_test_self (json : Json Scalar Key) (path : KeyedJsonPath Key)
    (h : json.get? path = some json) :
    json.applyPatchOp (.test path json) = some json := by
  simp [applyPatchOp, h]

/-- A singleton patch is exactly its operation semantics. -/
@[simp] theorem applyPatch_singleton (json : Json Scalar Key) (op : JsonPatchOp Scalar Key) :
    json.applyPatch [op] = json.applyPatchOp op := by
  simp [applyPatch]

end

end Json

end Nucleus
