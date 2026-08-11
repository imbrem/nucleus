import Nucleus.Json.Ordered

/-!
# Validation of raw JSON trees

`RawJson.validate` converts a raw tree to its extensional `Json` value, rejecting any
tree that contains a duplicated object key.  Duplicate handling is an explicit,
versioned policy decision: this library never collapses duplicates implicitly (neither
first-wins nor last-wins), and the only policy currently provided is rejection, with
the offending key reported via `JsonError.duplicateKey`.

The kernel of the validator is `RawJson.dupWitness?`, which finds the first duplicated
object key anywhere in the tree; `RawJson.dupWitness?_eq_none` identifies its success
exactly with `RawJson.WellFormed`, giving the specification lemmas for `validate`.
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

/-- Structured validation errors; currently only duplicate object keys.  Duplicate
handling is an explicit, versioned policy decision — `RawJson.validate` rejects. -/
inductive JsonError where
  /-- The key `key` occurs more than once in a single object. -/
  | duplicateKey (key : String)
  deriving DecidableEq, Repr

/-- The first element of the list that also occurs later in the list, if any. -/
def firstDup? {α : Type*} [DecidableEq α] : List α → Option α
  | [] => none
  | a :: rest => if a ∈ rest then some a else firstDup? rest

/-- `firstDup?` finds nothing exactly when the list is duplicate-free. -/
theorem firstDup?_eq_none {α : Type*} [DecidableEq α] {l : List α} :
    firstDup? l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [firstDup?]
  | cons a rest ih =>
    rw [firstDup?]
    by_cases h : a ∈ rest <;> simp [h, ih, List.nodup_cons]

namespace RawJson

/-- The first duplicated object key found anywhere in the tree, if any.  Used only for
error reporting by `RawJson.validate`; the specification is
`RawJson.dupWitness?_eq_none`. -/
def dupWitness? : RawJson Scalar → Option String
  | .scalar _ => none
  | .list elems => (elems.map fun e => e.dupWitness?).findSome? id
  | .map entries =>
      (firstDup? (entries.map Prod.fst)).orElse fun _ =>
        (entries.map fun e => e.2.dupWitness?).findSome? id
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- `dupWitness?` finds nothing exactly when the tree is well-formed. -/
theorem dupWitness?_eq_none {r : RawJson Scalar} : r.dupWitness? = none ↔ r.WellFormed := by
  induction r with
  | scalar v =>
    rw [dupWitness?]
    exact ⟨fun _ => .scalar v, fun _ => rfl⟩
  | list elems ih =>
    rw [dupWitness?, List.findSome?_eq_none_iff]
    constructor
    · intro h
      exact .list fun e he => (ih e he).mp (h _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    · intro h o ho
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      exact (ih e he).mpr (h.list_elem e he)
  | map entries ih =>
    rw [dupWitness?, Option.orElse_eq_or, Option.or_eq_none_iff, firstDup?_eq_none,
      List.findSome?_eq_none_iff]
    constructor
    · rintro ⟨hnd, hall⟩
      exact .map hnd fun e he => (ih e he).mp (hall _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    · intro h
      refine ⟨h.map_nodup, fun o ho => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      exact (ih e he).mpr (h.map_elem e he)

/-- Explicit duplicate-key policy: reject.  Convert a raw tree to its extensional
value, or report the first duplicated key.  Neither first-wins nor last-wins
collapsing is performed implicitly anywhere in this library. -/
def validate (r : RawJson Scalar) : Except JsonError (Json Scalar) :=
  match h : r.dupWitness? with
  | some k => .error (.duplicateKey k)
  | none => .ok (r.toJson (dupWitness?_eq_none.mp h))

/-- `validate` succeeds with `j` exactly when the tree is well-formed and `j` is its
extensional value. -/
theorem validate_eq_ok_iff {r : RawJson Scalar} {j : Json Scalar} :
    r.validate = .ok j ↔ ∃ h : r.WellFormed, r.toJson h = j := by
  unfold validate
  split
  · next k hk =>
    constructor
    · intro h
      simp at h
    · rintro ⟨hwf, -⟩
      rw [dupWitness?_eq_none.mpr hwf] at hk
      simp at hk
  · next hnone =>
    constructor
    · intro h
      exact ⟨dupWitness?_eq_none.mp hnone, Except.ok.inj h⟩
    · rintro ⟨hwf, rfl⟩
      rfl

/-- `validate` fails exactly when the tree is not well-formed. -/
theorem validate_eq_error_iff {r : RawJson Scalar} :
    (∃ e, r.validate = .error e) ↔ ¬ r.WellFormed := by
  unfold validate
  split
  · next k hk =>
    constructor
    · intro _ hwf
      rw [dupWitness?_eq_none.mpr hwf] at hk
      simp at hk
    · intro _
      exact ⟨.duplicateKey k, rfl⟩
  · next hnone =>
    constructor
    · rintro ⟨e, he⟩
      simp at he
    · intro hn
      exact absurd (dupWitness?_eq_none.mp hnone) hn

/-- On a well-formed tree, `validate` succeeds with the extensional value. -/
theorem validate_ok_of_wellFormed {r : RawJson Scalar} (h : r.WellFormed) :
    r.validate = .ok (r.toJson h) :=
  validate_eq_ok_iff.mpr ⟨h, rfl⟩

end RawJson

end Nucleus
