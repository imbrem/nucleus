import Nucleus.Hol.Ethane.Amber.Syntax
import Nucleus.RangeMap

/-!
# Segment arenas

A segment arena imports a sorted, nonoverlapping range map and overlays local
definitions at an explicit signed offset. Each destination range names a CAS
object and a signed source offset in that object.

Local definitions own their whole interval and shadow imports there. Imports
may be gapped and may use negative indices.
-/

namespace Nucleus.Hol.Ethane.Amber

open Nucleus.Hol.Ethane
universe u v
set_option relaxedAutoImplicit true

namespace Arena

/-- A range-mapped import layer with local definitions overlaid at `offset`. -/
structure Segment (Key : Type u) (R : Type v) where
  imports : RangeMap Key
  offset : Int
  defs : List R

namespace Segment

/-- One ranged import from another arena. -/
abbrev Import (Key : Type u) := RangeMap.Single Key

namespace Import

/-- Change the CAS key without changing either coordinate interval. -/
def mapKey (f : Key → Key') (source : Import Key) : Import Key' :=
  { source with target := f source.target }

end Import

/-! ## Arena operations -/

/-- Map CAS keys through the range map's functor without changing its domain. -/
def mapKeys (f : Key → Key') (arena : Segment Key R) : Segment Key' R :=
  ⟨arena.imports.map f, arena.offset, arena.defs⟩

@[simp] theorem mapKeys_id (arena : Segment Key R) :
    arena.mapKeys id = arena := by
  cases arena
  simp [mapKeys]

@[simp] theorem mapKeys_comp (g : Key' → Key'') (f : Key → Key')
    (arena : Segment Key R) :
    (arena.mapKeys f).mapKeys g = arena.mapKeys (g ∘ f) := by
  cases arena
  simp [mapKeys, Function.comp_def]

/-- The ranged import and local offset containing a destination index. -/
def importAt? (arena : Segment Key R) (index : Int) :
    Option (RangeMap.Hit Key) :=
  arena.imports.lookup? index

/-- Natural-index view of `importAt?`. -/
def importAtNat? (arena : Segment Key R) (index : Nat) :
    Option (RangeMap.Hit Key) :=
  arena.importAt? (Int.ofNat index)

/-- Resolve a destination index to its source key and source index. -/
def sourceAt? (arena : Segment Key R) (index : Int) : Option (Key × Int) :=
  (arena.importAt? index).map fun hit => (hit.target, hit.sourceIndex)

/-- Natural-index view of `sourceAt?`. -/
def sourceAtNat? (arena : Segment Key R) (index : Nat) : Option (Key × Int) :=
  arena.sourceAt? (Int.ofNat index)

@[simp] theorem importAtNat?_eq (arena : Segment Key R) (index : Nat) :
    arena.importAtNat? index = arena.importAt? (Int.ofNat index) := rfl

@[simp] theorem sourceAtNat?_eq (arena : Segment Key R) (index : Nat) :
    arena.sourceAtNat? index = arena.sourceAt? (Int.ofNat index) := rfl

/-- First signed index after the local overlay. -/
def next (arena : Segment Key R) : Int :=
  arena.offset + Int.ofNat arena.defs.length

/-- Membership in the interval owned by local definitions. -/
def Owns (arena : Segment Key R) (index : Int) : Prop :=
  arena.offset ≤ index ∧ index < arena.next

instance (arena : Segment Key R) (index : Int) : Decidable (arena.Owns index) :=
  inferInstanceAs (Decidable (arena.offset ≤ index ∧ index < arena.next))

/-- The imported map does not contain any index shadowed by local definitions. -/
def Unshadowed (arena : Segment Key R) : Prop :=
  ∀ index, arena.Owns index → arena.imports.lookup? index = none

/-- A row may refer only to indices before its own index. -/
def RowValid [Row R Tag Int Extra] (next : Int) (row : R) : Prop :=
  ∀ child ∈ Row.children row, child < next

/-- Left-to-right validity of a signed local overlay. -/
def RowsValid [Row R Tag Int Extra] : Int → List R → Prop
  | _, [] => True
  | next, row :: rows => RowValid next row ∧ RowsValid (next + 1) rows

/-- Every local reference points before its row. -/
def Valid [Row R Tag Int Extra] (arena : Segment Key R) : Prop :=
  RowsValid arena.offset arena.defs

/-- Whether one row may be appended. -/
def CanPush [Row R Tag Int Extra] (arena : Segment Key R) (row : R) : Prop :=
  RowValid arena.next row

/-- Append one local definition without changing the imported ranges. -/
def push (arena : Segment Key R) (row : R) : Segment Key R :=
  { arena with defs := arena.defs ++ [row] }

@[simp] theorem next_push (arena : Segment Key R) (row : R) :
    (arena.push row).next = arena.next + 1 := by
  simp [push, next]
  omega

theorem rowsValid_append [Row R Tag Int Extra] (next : Int)
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
        simpa [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc, add_comm,
          add_left_comm] using rightValid
      · rintro ⟨⟨rowValid, leftValid⟩, rightValid⟩
        refine ⟨rowValid, leftValid, ?_⟩
        simpa [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc, add_comm,
          add_left_comm] using rightValid

@[simp] theorem valid_push_iff [Row R Tag Int Extra]
    (arena : Segment Key R) (row : R) :
    Valid (arena.push row) ↔ Valid arena ∧ CanPush arena row := by
  change RowsValid arena.offset (arena.defs ++ [row]) ↔
    RowsValid arena.offset arena.defs ∧ RowValid arena.next row
  rw [rowsValid_append]
  simp [next, RowsValid]

theorem Valid.push [Row R Tag Int Extra] {arena : Segment Key R}
    (arenaValid : arena.Valid) {row : R} (rowValid : arena.CanPush row) :
    (arena.push row).Valid :=
  (valid_push_iff arena row).2 ⟨arenaValid, rowValid⟩

/-- A resolver distinguishes an unavailable source from an available source
whose denotation is partial at a particular index. -/
abbrev Resolver (Key : Type u) (Value : Type v) :=
  Key → Option (Int → Option Value)

/-- Resolve one imported destination. The outer `Option` records source
availability; the inner one records whether the source denotes this index.
An unmapped destination is available with no value. -/
def resolveAt? (resolve : Resolver Key Value) (arena : Segment Key R)
    (index : Int) : Option (Option Value) :=
  match arena.sourceAt? index with
  | none => some none
  | some (key, sourceIndex) =>
      match resolve key with
      | none => none
      | some source => some (source sourceIndex)

@[simp] theorem resolveAt?_unmapped (resolve : Resolver Key Value)
    (arena : Segment Key R) {index : Int} (unmapped : arena.sourceAt? index = none) :
    arena.resolveAt? resolve index = some none := by
  simp [resolveAt?, unmapped]

@[simp] theorem resolveAt?_unavailable (resolve : Resolver Key Value)
    (arena : Segment Key R) {index sourceIndex : Int} {key : Key}
    (mapped : arena.sourceAt? index = some (key, sourceIndex))
    (unavailable : resolve key = none) :
    arena.resolveAt? resolve index = none := by
  simp [resolveAt?, mapped, unavailable]

@[simp] theorem resolveAt?_available (resolve : Resolver Key Value)
    (arena : Segment Key R) {index sourceIndex : Int} {key : Key}
    {source : Int → Option Value}
    (mapped : arena.sourceAt? index = some (key, sourceIndex))
    (available : resolve key = some source) :
    arena.resolveAt? resolve index = some (source sourceIndex) := by
  simp [resolveAt?, mapped, available]

/-- Flatten source unavailability and pointwise absence for elaboration. -/
def imported (resolve : Resolver Key Value) (arena : Segment Key R)
    (index : Int) : Option Value :=
  (arena.resolveAt? resolve index).join

/-- Lookup while elaborating a prefix of the local definitions. The entire
local domain shadows imports, including rows not elaborated yet. -/
def lookup (imports : Int → Option Value) (offset stop : Int)
    (values : List (Option Value)) (index : Int) : Option Value :=
  if _inside : offset ≤ index ∧ index < stop then
    (values[(index - offset).toNat]?).join
  else
    imports index

@[simp] theorem lookup_local (imports : Int → Option Value)
    (offset stop index : Int) (values : List (Option Value))
    (inside : offset ≤ index ∧ index < stop) :
    lookup imports offset stop values index =
      (values[(index - offset).toNat]?).join := by
  simp [lookup, inside]

@[simp] theorem lookup_imported (imports : Int → Option Value)
    (offset stop index : Int) (values : List (Option Value))
    (outside : ¬(offset ≤ index ∧ index < stop)) :
    lookup imports offset stop values index = imports index := by
  simp [lookup, outside]

/-- Elaborate local rows from left to right. -/
def elaborateRows [Elaborates R Value Int]
    (imports : Int → Option Value) (offset stop : Int) :
    List (Option Value) → List R → List (Option Value)
  | values, [] => values
  | values, row :: rows =>
      let value := Elaborates.elaborate (lookup imports offset stop values) row
      elaborateRows imports offset stop (values ++ [value]) rows

/-- A signed, partially interpreted segment arena. -/
structure Denotation (Value : Type u) where
  imported : Int → Option Value
  offset : Int
  suffix : List (Option Value)

namespace Denotation

/-- First signed index after the local overlay. -/
def next (denotation : Denotation Value) : Int :=
  denotation.offset + Int.ofNat denotation.suffix.length

/-- Local definitions take precedence over imported ranges. -/
def get (denotation : Denotation Value) (index : Int) : Option Value :=
  lookup denotation.imported denotation.offset denotation.next
    denotation.suffix index

@[simp] theorem get_local (denotation : Denotation Value) (index : Int)
    (inside : denotation.offset ≤ index ∧ index < denotation.next) :
    denotation.get index =
      (denotation.suffix[(index - denotation.offset).toNat]?).join := by
  exact lookup_local _ _ _ _ _ inside

@[simp] theorem get_imported (denotation : Denotation Value) (index : Int)
    (outside : ¬(denotation.offset ≤ index ∧ index < denotation.next)) :
    denotation.get index = denotation.imported index := by
  exact lookup_imported _ _ _ _ _ outside

/-- Every local row elaborated successfully. -/
def Complete (denotation : Denotation Value) : Prop :=
  ∀ value ∈ denotation.suffix, value.isSome

end Denotation

/-- Interpret imports lazily and elaborate the local overlay. -/
def denote [Elaborates R Value Int] (resolve : Resolver Key Value)
    (arena : Segment Key R) : Denotation Value :=
  let imports := arena.imported resolve
  ⟨imports, arena.offset,
    elaborateRows imports arena.offset arena.next [] arena.defs⟩

@[simp] theorem elaborateRows_length [Elaborates R Value Int]
    (imports : Int → Option Value) (offset stop : Int)
    (values : List (Option Value)) (rows : List R) :
    (elaborateRows imports offset stop values rows).length =
      values.length + rows.length := by
  induction rows generalizing values with
  | nil => simp [elaborateRows]
  | cons row rows ih =>
      simp only [elaborateRows, ih, List.length_append, List.length_cons,
        List.length_nil]
      omega

@[simp] theorem denote_next [Elaborates R Value Int]
    (resolve : Resolver Key Value) (arena : Segment Key R) :
    (arena.denote resolve).next = arena.next := by
  simp [denote, Denotation.next, next]

/-- Segment arena containing signed Ethane syntax references. -/
abbrev Syntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat) :=
  Segment Key (Nucleus.Hol.Ethane.Arena.Row Sig Name Int)

end Segment

end Arena

end Nucleus.Hol.Ethane.Amber
