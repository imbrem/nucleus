import Mathlib.Tactic
import Nucleus.Hol.Ethane.Amber.Row

/-!
# Dense overlay forests

An Amber dense forest is a finite suffix over either the empty forest or one
CAS-addressed parent prefix.  References are absolute natural numbers.  A
parent link carries its denoted size, so local backward-edge validation never
needs to fetch the parent.

Resolving a parent is a separate semantic operation.  The resolver must return
exactly the declared prefix length; missing or mismatched parents make the
overlay unavailable rather than changing the meaning of its local rows.
-/

namespace Nucleus.Hol.Ethane.Amber

universe u v w x y
set_option relaxedAutoImplicit true

/-- A row interpreter.  Forest shape remains governed only by `Row`; this
second class is needed only when a client asks for denoted values. -/
class Elaborates (R : Type u) (Value : Type v) where
  elaborate : (Nat → Option Value) → R → Option Value

/-- A CAS parent and the exact number of values it contributes. -/
structure Parent (Key : Type u) where
  key : Key
  size : Nat
  deriving DecidableEq

/-- A dense suffix whose absolute indices begin immediately after its parent. -/
structure Dense (Key : Type u) (R : Type v) where
  parent : Option (Parent Key)
  rows : List R
  deriving DecidableEq

namespace Dense

/-- The first absolute index occupied by a local row. -/
def offset (forest : Dense Key R) : Nat :=
  forest.parent.map Parent.size |>.getD 0

/-- The first unallocated absolute index. -/
def next (forest : Dense Key R) : Nat := forest.offset + forest.rows.length

/-- A row may only reference the parent or earlier local rows. -/
def RowValid [Row R Tag Nat Extra] (next : Nat) (row : R) : Prop :=
  ∀ child ∈ Row.children row, child < next

/-- Left-to-right structural validity.  Tags and extra fields do not
participate in this predicate. -/
def RowsValid [Row R Tag Nat Extra] : Nat → List R → Prop
  | _, [] => True
  | next, row :: rows => RowValid next row ∧ RowsValid (next + 1) rows

/-- Every local edge points strictly backward in the overlaid index space. -/
def Valid [Row R Tag Nat Extra] (forest : Dense Key R) : Prop :=
  RowsValid forest.offset forest.rows

/-- Whether one row can be appended without introducing a forward edge. -/
def CanPush [Row R Tag Nat Extra] (forest : Dense Key R) (row : R) : Prop :=
  RowValid forest.next row

/-- Append one row.  The operation is deliberately pure; callers that accept
untrusted input use `push?` below. -/
def push (forest : Dense Key R) (row : R) : Dense Key R :=
  ⟨forest.parent, forest.rows ++ [row]⟩

/-- Validate and append one row, matching a small Rust mutation boundary. -/
noncomputable def push? [Row R Tag Nat Extra] (forest : Dense Key R) (row : R) :
    Option (Dense Key R) := by
  classical
  exact if CanPush forest row then some (forest.push row) else none

/-- A CAS resolver returns the already interpreted values of a parent forest. -/
abbrev Resolver (Key : Type u) (Value : Type v) := Key → Option (List Value)

/-- Resolve and length-check the parent prefix. -/
def resolveParent? (resolve : Resolver Key Value) (forest : Dense Key R) :
    Option (List Value) :=
  match forest.parent with
  | none => some []
  | some parent => do
      let values ← resolve parent.key
      if values.length = parent.size then some values else none

/-- Lookup in a resolved prefix followed by partially elaborated local rows. -/
def lookup (base : List Value) (values : List (Option Value))
    (index : Nat) : Option Value :=
  if index < base.length then
    base[index]?
  else
    (values[index - base.length]?).join

/-- Elaborate rows while retaining an explicit local accumulator. -/
def elaborateRows [Elaborates R Value] (base : List Value) :
    List (Option Value) → List R → List (Option Value)
  | values, [] => values
  | values, row :: rows =>
      let value := Elaborates.elaborate (lookup base values) row
      elaborateRows base (values ++ [value]) rows

/-- Elaborate a complete local suffix. -/
def elaborateLocal [Elaborates R Value] (base : List Value)
    (rows : List R) : List (Option Value) :=
  elaborateRows base [] rows

/-- The resolved denotation of a dense overlay. -/
structure Denotation (Value : Type u) where
  base : List Value
  suffix : List (Option Value)
  deriving DecidableEq

namespace Denotation

/-- Total number of addressable slots, including invalid local rows. -/
def size (forest : Denotation Value) : Nat :=
  forest.base.length + forest.suffix.length

/-- Partial lookup in the overlaid denotation. -/
def get (forest : Denotation Value) (index : Nat) : Option Value :=
  lookup forest.base forest.suffix index

/-- All local rows elaborated successfully. -/
def Complete (forest : Denotation Value) : Prop :=
  ∀ value ∈ forest.suffix, value.isSome

end Denotation

/-- Resolve the parent and elaborate every local row. -/
def denote? [Elaborates R Value] (resolve : Resolver Key Value)
    (forest : Dense Key R) : Option (Denotation Value) := do
  let base ← forest.resolveParent? resolve
  return ⟨base, elaborateLocal base forest.rows⟩

@[simp] theorem offset_root (rows : List R) :
    (Dense.mk (Key := Key) none rows).offset = 0 := rfl

@[simp] theorem offset_parent (parent : Parent Key) (rows : List R) :
    (Dense.mk (some parent) rows).offset = parent.size := rfl

@[simp] theorem next_push (forest : Dense Key R) (row : R) :
    (forest.push row).next = forest.next + 1 := by
  change forest.offset + (forest.rows ++ [row]).length =
    forest.offset + forest.rows.length + 1
  simp [Nat.add_assoc]

theorem rowsValid_append [Row R Tag Nat Extra] (next : Nat)
    (left right : List R) :
    RowsValid next (left ++ right) ↔
      RowsValid next left ∧ RowsValid (next + left.length) right := by
  induction left generalizing next with
  | nil => simp [RowsValid]
  | cons row left ih =>
      simp only [List.cons_append, RowsValid, List.length_cons]
      rw [ih (next + 1)]
      constructor
      · rintro ⟨rowValid, leftValid, rightValid⟩
        refine ⟨⟨rowValid, leftValid⟩, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightValid
      · rintro ⟨⟨rowValid, leftValid⟩, rightValid⟩
        refine ⟨rowValid, leftValid, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightValid

@[simp] theorem valid_push_iff [Row R Tag Nat Extra]
    (forest : Dense Key R) (row : R) :
    Valid (forest.push row) ↔ Valid forest ∧ CanPush forest row := by
  change RowsValid forest.offset (forest.rows ++ [row]) ↔
    RowsValid forest.offset forest.rows ∧ RowValid forest.next row
  rw [rowsValid_append]
  simp [next, RowsValid]

theorem Valid.push [Row R Tag Nat Extra] {forest : Dense Key R}
    (forestValid : forest.Valid) {row : R} (rowValid : forest.CanPush row) :
    (forest.push row).Valid :=
  (valid_push_iff forest row).2 ⟨forestValid, rowValid⟩

@[simp] theorem push?_eq_some [Row R Tag Nat Extra]
    (forest : Dense Key R) (row : R) :
    forest.push? row = some (forest.push row) ↔ forest.CanPush row := by
  classical
  unfold push?
  constructor
  · intro pushed
    by_contra invalid
    rw [if_neg invalid] at pushed
    contradiction
  · intro valid
    rw [if_pos valid]

theorem push?_valid [Row R Tag Nat Extra] {forest next : Dense Key R}
    (forestValid : forest.Valid) {row : R} (pushed : forest.push? row = some next) :
    next.Valid := by
  simp only [push?] at pushed
  split at pushed
  next rowValid =>
    cases pushed
    exact forestValid.push rowValid
  next _ => contradiction

@[simp] theorem resolveParent?_root (resolve : Resolver Key Value)
    (rows : List R) :
    resolveParent? resolve (Dense.mk (Key := Key) none rows) = some [] := rfl

theorem resolveParent?_parent {resolve : Resolver Key Value}
    {parent : Parent Key} {rows : List R} {values : List Value}
    (resolved : resolve parent.key = some values)
    (length_eq : values.length = parent.size) :
    resolveParent? resolve (Dense.mk (some parent) rows) = some values := by
  simp [resolveParent?, resolved, length_eq]

@[simp] theorem lookup_base {base : List Value} {values : List (Option Value)}
    {index : Nat} (below : index < base.length) :
    lookup base values index = base[index]? := by
  simp [lookup, below]

@[simp] theorem lookup_suffix {base : List Value} {values : List (Option Value)}
    {index : Nat} (above : base.length ≤ index) :
    lookup base values index = (values[index - base.length]?).join := by
  simp [lookup, Nat.not_lt.mpr above]

@[simp] theorem elaborateRows_length [Elaborates R Value]
    (base : List Value) (values : List (Option Value)) (rows : List R) :
    (elaborateRows base values rows).length = values.length + rows.length := by
  induction rows generalizing values with
  | nil => simp [elaborateRows]
  | cons row rows ih =>
      simp only [elaborateRows, ih, List.length_append, List.length_cons,
        List.length_nil]
      omega

@[simp] theorem elaborateLocal_length [Elaborates R Value]
    (base : List Value) (rows : List R) :
    (elaborateLocal base rows).length = rows.length := by
  simp [elaborateLocal]

theorem elaborateRows_append [Elaborates R Value]
    (base : List Value) (values : List (Option Value)) (left right : List R) :
    elaborateRows base values (left ++ right) =
      elaborateRows base (elaborateRows base values left) right := by
  induction left generalizing values with
  | nil => rfl
  | cons row left ih =>
      simp only [List.cons_append, elaborateRows]
      exact ih (values ++ [Elaborates.elaborate (lookup base values) row])

theorem elaborateLocal_push [Elaborates R Value]
    (base : List Value) (rows : List R) (row : R) :
    elaborateLocal base (rows ++ [row]) =
      elaborateRows base (elaborateLocal base rows) [row] := by
  exact elaborateRows_append base [] rows [row]

theorem denote?_size [Elaborates R Value] {resolve : Resolver Key Value}
    {forest : Dense Key R} {denotation : Denotation Value}
    (denotes : forest.denote? resolve = some denotation) :
    denotation.size = forest.next := by
  have resolvedLength : ∀ {base : List Value},
      forest.resolveParent? resolve = some base → base.length = forest.offset := by
    intro base resolvedParent
    cases parentEq : forest.parent with
    | none =>
        simp only [resolveParent?, parentEq] at resolvedParent
        change some [] = some base at resolvedParent
        injection resolvedParent with baseEq
        subst base
        simp [offset, parentEq]
    | some parent =>
        simp only [resolveParent?, parentEq] at resolvedParent
        cases resolveEq : resolve parent.key with
        | none =>
            rw [resolveEq] at resolvedParent
            change none = some base at resolvedParent
            contradiction
        | some values =>
            rw [resolveEq] at resolvedParent
            change (if values.length = parent.size then some values else none) =
              some base at resolvedParent
            by_cases lengthEq : values.length = parent.size
            · rw [if_pos lengthEq] at resolvedParent
              injection resolvedParent with baseEq
              subst base
              simpa [offset, parentEq] using lengthEq
            · rw [if_neg lengthEq] at resolvedParent
              contradiction
  unfold denote? at denotes
  cases parentResolved : forest.resolveParent? resolve with
  | none =>
      rw [parentResolved] at denotes
      contradiction
  | some base =>
      rw [parentResolved] at denotes
      have denotationEq :
          Denotation.mk base (elaborateLocal base forest.rows) = denotation :=
        Option.some.inj denotes
      subst denotation
      change base.length + (elaborateLocal base forest.rows).length =
        forest.offset + forest.rows.length
      rw [elaborateLocal_length, resolvedLength parentResolved]

end Dense

end Nucleus.Hol.Ethane.Amber
