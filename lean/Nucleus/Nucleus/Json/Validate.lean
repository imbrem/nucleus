import Nucleus.Json.Ordered

/-!
# Validation of raw JSON trees

`RawSyn.validate` converts a raw tree to its extensional `Json` value, rejecting any
tree that contains a duplicated object key.  Duplicate handling is an explicit,
versioned policy decision: this library never collapses duplicates implicitly (neither
first-wins nor last-wins), and the only policy currently provided is rejection, with
the offending key reported via `JsonError.duplicateKey`.

The kernel of the validator is `RawSyn.dupWitness?`, which finds the first duplicated
object key anywhere in the tree; `RawSyn.dupWitness?_eq_none` identifies its success
exactly with `RawSyn.WellFormed`, giving the specification lemmas for `validate`.
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

/-- Structured validation errors; currently only duplicate object keys.  Duplicate
handling is an explicit, versioned policy decision — `RawSyn.validate` rejects. -/
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

namespace RawSyn

/-- The first duplicated object key found anywhere in the tree, if any.  Used only for
error reporting by `RawSyn.validate`; the specification is
`RawSyn.dupWitness?_eq_none`.  Recurses structurally over all three sorts. -/
def dupWitness? : ∀ {i : JsonIx}, RawSyn Scalar i → Option String
  | _, .scalar _ => none
  | _, .list elems => elems.dupWitness?
  | _, .map entries => (firstDup? entries.keys).orElse fun _ => entries.dupWitness?
  | _, .nil => none
  | _, .cons head tail => (head.dupWitness?).orElse fun _ => tail.dupWitness?
  | _, .objNil => none
  | _, .objCons _ value tail => (value.dupWitness?).orElse fun _ => tail.dupWitness?

/-- `dupWitness?` finds nothing exactly when the tree is well-formed. -/
theorem dupWitness?_eq_none {i : JsonIx} {r : RawSyn Scalar i} :
    r.dupWitness? = none ↔ r.WellFormed := by
  induction r with
  | scalar value => simp [dupWitness?]
  | list elems ih => simp [dupWitness?, ih]
  | map entries ih =>
    simp [dupWitness?, Option.orElse_eq_or, Option.or_eq_none_iff, firstDup?_eq_none, ih]
  | nil => simp [dupWitness?]
  | cons head tail ih ih' =>
    simp [dupWitness?, Option.orElse_eq_or, Option.or_eq_none_iff, ih, ih']
  | objNil => simp [dupWitness?]
  | objCons key value tail ih ih' =>
    simp [dupWitness?, Option.orElse_eq_or, Option.or_eq_none_iff, ih, ih']

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

end RawSyn

end Nucleus
