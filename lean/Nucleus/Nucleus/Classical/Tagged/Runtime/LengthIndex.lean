import Nucleus.Classical.Tagged.Runtime.SharedRuntime

/-!
# Private length index

The runtime caches each live block's arity outside the word arena. This model
states the complete domain invariant: a slot has a length exactly when its
aligned address is a live node. The index is rebuilt by construction and is
absent from the wire and kernel interfaces.
-/

namespace Nucleus.Classical.Tagged.Runtime.LengthIndex

open Nucleus.Classical.Tagged.Runtime.Shared
open Nucleus.Classical.Tagged.Runtime.SharedRuntime

/-- Logical view of the dense side index. Rust stores these values in a vector
with one slot per four arena words. -/
abbrev Index := Nat → Option Nat

def address (slot : Nat) : Nat := 4 * slot

def liveLength? (arena : RawArena) (slot : Nat) : Option Nat :=
  (readNode? arena (address slot)).map fun node ↦ node.children.length

def Consistent (arena : RawArena) (index : Index) : Prop :=
  ∀ slot, index slot = liveLength? arena slot

/-- Validation reconstructs the private cache from live nodes only. -/
def rebuild (arena : RawArena) : Index := liveLength? arena

theorem rebuild_consistent (arena : RawArena) : Consistent arena (rebuild arena) := by
  intro slot
  rfl

theorem some_iff_live {arena : RawArena} {index : Index}
    (consistent : Consistent arena index) {slot length : Nat} :
    index slot = some length ↔
      ∃ node, readNode? arena (address slot) = some node ∧
        node.children.length = length := by
  rw [consistent slot]
  unfold liveLength?
  constructor
  · intro mapped
    cases read : readNode? arena (address slot) with
    | none => simp [read] at mapped
    | some node =>
        simp only [read, Option.map_some, Option.some.injEq] at mapped
        exact ⟨node, rfl, mapped⟩
  · rintro ⟨node, read, rfl⟩
    simp [read]

theorem none_iff_not_live {arena : RawArena} {index : Index}
    (consistent : Consistent arena index) {slot : Nat} :
    index slot = none ↔ readNode? arena (address slot) = none := by
  rw [consistent slot]
  unfold liveLength?
  cases readNode? arena (address slot) <;> simp

def set (index : Index) (slot length : Nat) : Index :=
  fun selected ↦ if selected = slot then some length else index selected

def clear (index : Index) (slot : Nat) : Index :=
  fun selected ↦ if selected = slot then none else index selected

@[simp] theorem set_eq (index : Index) (slot length : Nat) :
    set index slot length slot = some length := by simp [set]

@[simp] theorem set_ne (index : Index) {slot other length : Nat}
    (different : other ≠ slot) :
    set index slot length other = index other := by simp [set, different]

@[simp] theorem clear_eq (index : Index) (slot : Nat) :
    clear index slot slot = none := by simp [clear]

@[simp] theorem clear_ne (index : Index) {slot other : Nat}
    (different : other ≠ slot) :
    clear index slot other = index other := by simp [clear, different]

/-- Word edits replace one live block's children and leave every other live
node unchanged. This covers push, pop, permutation, deduplication, flattening,
and constructor-preserving path rewrites. -/
def ReplacesChildren (before after : RawArena) (slot length : Nat) : Prop :=
  liveLength? after slot = some length ∧
    ∀ other, other ≠ slot → liveLength? after other = liveLength? before other

theorem replaceChildren_preserves {before after : RawArena} {index : Index}
    {slot length : Nat} (consistent : Consistent before index)
    (changed : ReplacesChildren before after slot length) :
    Consistent after (set index slot length) := by
  intro selected
  by_cases equal : selected = slot
  · subst selected
    simpa using changed.1.symm
  · rw [set_ne index equal, consistent selected, changed.2 selected equal]

/-- Allocation creates exactly one new live-base entry. -/
abbrev Allocates := ReplacesChildren

theorem allocate_preserves {before after : RawArena} {index : Index}
    {slot length : Nat} (consistent : Consistent before index)
    (allocated : Allocates before after slot length) :
    Consistent after (set index slot length) :=
  replaceChildren_preserves consistent allocated

/-- Freeing removes one live-base entry and changes no other live node. -/
def Frees (before after : RawArena) (slot : Nat) : Prop :=
  liveLength? after slot = none ∧
    ∀ other, other ≠ slot → liveLength? after other = liveLength? before other

theorem free_preserves {before after : RawArena} {index : Index} {slot : Nat}
    (consistent : Consistent before index) (freed : Frees before after slot) :
    Consistent after (clear index slot) := by
  intro selected
  by_cases equal : selected = slot
  · subst selected
    simpa using freed.1.symm
  · rw [clear_ne index equal, consistent selected, freed.2 selected equal]

/-- Growth and copy-on-write move one logical node to a fresh block. -/
def Relocates (before after : RawArena) (old new length : Nat) : Prop :=
  old ≠ new ∧ liveLength? after old = none ∧
    liveLength? after new = some length ∧
    ∀ other, other ≠ old → other ≠ new →
      liveLength? after other = liveLength? before other

theorem relocate_preserves {before after : RawArena} {index : Index}
    {old new length : Nat} (consistent : Consistent before index)
    (moved : Relocates before after old new length) :
    Consistent after (set (clear index old) new length) := by
  intro selected
  by_cases atNew : selected = new
  · subst selected
    simpa using moved.2.2.1.symm
  · rw [set_ne _ atNew]
    by_cases atOld : selected = old
    · subst selected
      simpa using moved.2.1.symm
    · rw [clear_ne index atOld, consistent selected,
        moved.2.2.2 selected atOld atNew]

/-- A push increments the cached arity. -/
theorem pushedLength (length : Nat) : (length + 1) - 1 = length := by omega

/-- A pop decrements a nonempty cached arity. -/
theorem poppedLength {length : Nat} (nonempty : 0 < length) :
    length - 1 + 1 = length := by omega

end Nucleus.Classical.Tagged.Runtime.LengthIndex
