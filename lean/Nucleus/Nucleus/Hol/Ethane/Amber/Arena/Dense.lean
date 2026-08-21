import Nucleus.Hol.Ethane.Amber.Serialization
import Nucleus.Hol.Ethane.Amber.Syntax

/-!
# Dense Amber arenas

`Arena.Dense` is the implementation-facing representation: an optional parent
key, an explicit signed offset, and a growable array of definitions.  Its local
domain is `[offset, offset + defs.size)`.  Signed references are the default;
the representation intentionally assigns no meaning to negative indices.

The older list-backed natural-number forest remains available as an alternate
mathematical model.  This file specifies the shape and checked mutations that
map directly to a Rust arena.
-/

namespace Nucleus.Hol.Ethane.Amber.Arena

open Nucleus.Hol.Ethane Nucleus.Hol.Ethane.Amber
universe u v x
set_option relaxedAutoImplicit true

/-- A dense overlay with default signed indices.  `parent` fixes the logical
object class to an arena; the active serialization strategy fixes its format. -/
structure Dense (Key : Type u) (R : Type v) (Ix : Type := Int) where
  parent : Option Key
  offset : Ix
  defs : Array R
  deriving DecidableEq

namespace Dense

/-- An index representable by the Rust dense arena's signed `i64` boundary.
This is deliberately separate from the general CBOR integer codec: decoding
may produce a wider mathematical integer which the Rust-view validator then
rejects. -/
def I64Fits (index : Int) : Prop :=
  -(2 ^ 63 : Int) ≤ index ∧ index < (2 ^ 63 : Int)

/-- Every index stored by the modeled Rust dense representation fits `i64`.
`List.Forall` keeps the predicate decidable without requiring equality on row
payloads. -/
def I64Valid [Row R Tag Int Extra] (arena : Dense Key R Int) : Prop :=
  I64Fits arena.offset ∧
    arena.defs.toList.Forall fun row =>
      (Row.children row).Forall I64Fits

instance (index : Int) : Decidable (I64Fits index) := by
  unfold I64Fits
  infer_instance

instance [Row R Tag Int Extra] (arena : Dense Key R Int) :
    Decidable arena.I64Valid := by
  unfold I64Valid
  infer_instance

/-- The next absolute index assigned by `push`. -/
def next [AddMonoidWithOne Ix] (arena : Dense Key R Ix) : Ix :=
  arena.offset + (arena.defs.size : Ix)

/-- The half-open interval owned by the local definition array. -/
def Owns [AddMonoidWithOne Ix] [Preorder Ix]
    (arena : Dense Key R Ix) (index : Ix) : Prop :=
  arena.offset ≤ index ∧ index < arena.next

/-- One row may refer only to indices preceding its own position.  Negative
indices are permitted; an object kind may interpret them or leave them opaque. -/
def RowValid [LT Ix] [Row R Tag Ix Extra] (next : Ix) (row : R) : Prop :=
  ∀ child ∈ Row.children row, child < next

/-- Left-to-right validity for an implementation array, stated over its list
view to keep induction independent of the storage container. -/
def RowsValid [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra] :
    Ix → List R → Prop
  | _, [] => True
  | next, row :: rows => RowValid next row ∧ RowsValid (next + 1) rows

/-- Every local reference is backward in the signed overlay coordinate space. -/
def Valid [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    (arena : Dense Key R Ix) : Prop :=
  RowsValid arena.offset arena.defs.toList

/-- Checked precondition for one append. -/
def CanPush [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    (arena : Dense Key R Ix) (row : R) : Prop :=
  RowValid arena.next row

/-- Pure model of `Vec::push`. -/
def push (arena : Dense Key R Ix) (row : R) : Dense Key R Ix :=
  ⟨arena.parent, arena.offset, arena.defs.push row⟩

/-- Validate all child references before mutating. -/
noncomputable def push? [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    (arena : Dense Key R Ix) (row : R) : Option (Dense Key R Ix) := by
  classical
  exact if arena.CanPush row then some (arena.push row) else none

/-- Repeated checked append. -/
noncomputable def extend? [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra] :
    Dense Key R Ix → List R → Option (Dense Key R Ix)
  | arena, [] => some arena
  | arena, row :: rows => do
      let arena ← arena.push? row
      extend? arena rows

@[simp] theorem next_push [AddMonoidWithOne Ix]
    (arena : Dense Key R Ix) (row : R) :
    (arena.push row).next = arena.next + 1 := by
  simp [next, push, Nat.cast_add, add_assoc]

@[simp] theorem push?_eq_some [AddMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    (arena : Dense Key R Ix) (row : R) :
    arena.push? row = some (arena.push row) ↔ arena.CanPush row := by
  classical
  unfold push?
  constructor
  · intro pushed
    by_contra invalid
    rw [if_neg invalid] at pushed
    contradiction
  · intro valid
    rw [if_pos valid]

theorem rowsValid_append [AddCommMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    (next : Ix) (left right : List R) :
    RowsValid next (left ++ right) ↔
      RowsValid next left ∧ RowsValid (next + (left.length : Ix)) right := by
  induction left generalizing next with
  | nil => simp [RowsValid]
  | cons row left ih =>
      simp only [List.cons_append, RowsValid, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      rw [ih (next + 1)]
      simp only [and_assoc, add_comm, add_left_comm]

@[simp] theorem valid_push_iff [AddCommMonoidWithOne Ix] [LT Ix]
    [Row R Tag Ix Extra] (arena : Dense Key R Ix) (row : R) :
    (arena.push row).Valid ↔ arena.Valid ∧ arena.CanPush row := by
  unfold Valid CanPush
  change RowsValid arena.offset ((arena.defs.push row).toList) ↔
    RowsValid arena.offset arena.defs.toList ∧ RowValid arena.next row
  simp only [Array.toList_push]
  rw [rowsValid_append]
  simp [RowsValid, next]

theorem Valid.push [AddCommMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    {arena : Dense Key R Ix} (arenaValid : arena.Valid)
    {row : R} (rowValid : arena.CanPush row) : (arena.push row).Valid :=
  (valid_push_iff arena row).2 ⟨arenaValid, rowValid⟩

theorem push?_valid [AddCommMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    {arena next : Dense Key R Ix} (arenaValid : arena.Valid) {row : R}
    (pushed : arena.push? row = some next) : next.Valid := by
  unfold push? at pushed
  split at pushed
  next rowValid =>
    cases pushed
    exact arenaValid.push rowValid
  next _ => contradiction

theorem extend?_valid [AddCommMonoidWithOne Ix] [LT Ix] [Row R Tag Ix Extra]
    {arena next : Dense Key R Ix} (arenaValid : arena.Valid) {rows : List R}
    (extended : extend? arena rows = some next) : next.Valid := by
  induction rows generalizing arena with
  | nil =>
      change some arena = some next at extended
      injection extended with arenaEq
      subst next
      exact arenaValid
  | cons row rows ih =>
      simp only [extend?] at extended
      cases pushedEq : arena.push? row with
      | none => rw [pushedEq] at extended; contradiction
      | some pushed =>
          rw [pushedEq] at extended
          exact ih (push?_valid arenaValid pushedEq) extended

/-- Rust-facing Ethane syntax state. -/
abbrev Syntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat)
    (Ix : Type := Int) :=
  Dense Key (Nucleus.Hol.Ethane.Arena.Row Sig Name Ix) Ix

/-- Natural-indexed arenas remain available for inductive arguments and direct
comparison with the original Ethane encoder. -/
abbrev NatSyntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat) :=
  Syntax Key Sig Name Nat

end Dense

end Nucleus.Hol.Ethane.Amber.Arena
