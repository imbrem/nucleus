import Nucleus.Json.Extensional

/-!
# Singular JSON paths

This module develops the update theory of the singular path language already
used by `Json.get?`: object-name and array-index steps rooted at a JSON value.
These are the deterministic paths needed by JSON Patch and by holes.  Query
features such as wildcards and filters are deliberately a separate concern:
their result is a node list, whereas a singular path identifies at most one
location.
-/

namespace Nucleus

universe u

namespace Json

variable {Key : Type} {Scalar : Type u} [DecidableEq Key]

/-- Replace the value at a singular path. Failure means that some step has the
wrong container kind, an array index is out of range, or an object key is
absent. -/
def replace? : Json Scalar Key → KeyedJsonPath Key → Json Scalar Key → Option (Json Scalar Key)
  | _, [], replacement => some replacement
  | .list n elems, .index i :: rest, replacement =>
      if hi : i < n then do
        let child ← replace? (elems ⟨i, hi⟩) rest replacement
        some (.list n fun k => if k.1 = i then child else elems k)
      else none
  | .map keys vals, .key key :: rest, replacement =>
      if hk : key ∈ keys then do
        let child ← replace? (vals ⟨key, hk⟩) rest replacement
        some (.map keys fun k => if k.1 = key then child else vals k)
      else none
  | _, _, _ => none

/-- Modify the value selected by a path, when both lookup and the user
transformation succeed. -/
def modify? (json : Json Scalar Key) (path : KeyedJsonPath Key)
    (f : Json Scalar Key → Option (Json Scalar Key)) : Option (Json Scalar Key) := do
  let old ← json.get? path
  let replacement ← f old
  json.replace? path replacement

@[simp] theorem replace?_nil (json replacement : Json Scalar Key) :
    json.replace? [] replacement = some replacement := by simp [replace?]

/-- Replacing a reachable path and looking it up returns exactly the new
value. -/
theorem get?_replace? : ∀ {json updated replacement : Json Scalar Key}
    {path : KeyedJsonPath Key},
    json.replace? path replacement = some updated →
      updated.get? path = some replacement := by
  intro json updated replacement path hreplace
  induction path generalizing json updated with
  | nil =>
      simp at hreplace
      subst updated
      simp [get?]
  | cons step rest ih =>
      cases json with
      | scalar value => cases step <;> simp [replace?] at hreplace
      | list n elems =>
          cases step with
          | key key => simp [replace?] at hreplace
          | index i =>
              simp only [replace?] at hreplace
              split at hreplace <;> rename_i hi
              · simp only [Option.bind_eq_bind] at hreplace
                rw [Option.bind_eq_some_iff] at hreplace
                obtain ⟨child, hchild, hupdated⟩ := hreplace
                simp only [Option.some.injEq] at hupdated
                subst updated
                simp [get?, hi, ih hchild]
              · simp at hreplace
      | map keys vals =>
          cases step with
          | index i => simp [replace?] at hreplace
          | key key =>
              simp only [replace?] at hreplace
              split at hreplace <;> rename_i hk
              · simp only [Option.bind_eq_bind] at hreplace
                rw [Option.bind_eq_some_iff] at hreplace
                obtain ⟨child, hchild, hupdated⟩ := hreplace
                simp only [Option.some.injEq] at hupdated
                subst updated
                simp [get?, hk, ih hchild]
              · simp at hreplace

/-- Replacement succeeds exactly on paths that are reachable. -/
theorem replace?_isSome_iff_get?_isSome
    (json replacement : Json Scalar Key) (path : KeyedJsonPath Key) :
    (json.replace? path replacement).isSome = (json.get? path).isSome := by
  induction path generalizing json with
  | nil => simp [get?]
  | cons step rest ih =>
      cases json with
      | scalar value => cases step <;> rfl
      | list n elems =>
          cases step with
          | key key => rfl
          | index i =>
              by_cases hi : i < n
              · simp [replace?, get?, hi, Option.isSome_bind, ih]
              · simp [replace?, get?, hi]
      | map keys vals =>
          cases step with
          | index i => rfl
          | key key =>
              by_cases hk : key ∈ keys
              · simp [replace?, get?, hk, Option.isSome_bind, ih]
              · simp [replace?, get?, hk]

/-- Modifying the root is just applying the transformation. -/
@[simp] theorem modify?_nil (json : Json Scalar Key)
    (f : Json Scalar Key → Option (Json Scalar Key)) :
    json.modify? [] f = f json := by simp [modify?, get?]

/-- Concatenated path lookup is sequential lookup. -/
theorem get?_append (json : Json Scalar Key) (p q : KeyedJsonPath Key) :
    json.get? (p ++ q) = (json.get? p).bind (fun child => child.get? q) := by
  induction p generalizing json with
  | nil => simp [get?]
  | cons step rest ih =>
      cases json with
      | scalar value => cases step <;> rfl
      | list n elems =>
          cases step with
          | key key => rfl
          | index i =>
              by_cases hi : i < n <;> simp [get?, hi, ih]
      | map keys vals =>
          cases step with
          | index i => rfl
          | key key =>
              by_cases hk : key ∈ keys <;> simp [get?, hk, ih]

end Json

end Nucleus
