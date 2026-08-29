import Nucleus.Classical.Packed.Block
import Mathlib.Data.List.Sort

/-!
# Checked block mutations

These executable operations mutate the shared flat word array through strict
block decoding and canonical re-encoding.  They never trust a caller's sort
key or claimed permutation as logical evidence: the resulting references are
either constructed from the decoded block or checked for an actual
permutation before the write occurs.
-/

namespace Nucleus.Classical.Packed

variable {payloadWidth : Nat}

namespace Memory

/-- Append one reference when the block has spare capacity. -/
def push? (memory : Memory payloadWidth) (block : Block)
    (reference : Word.Ref payloadWidth) : Option (Memory payloadWidth) := do
  let references ← memory.read block
  memory.write? block (references ++ [reference])

theorem push?_read {memory after : Memory payloadWidth} {block : Block}
    {reference : Word.Ref payloadWidth}
    (pushed : memory.push? block reference = some after) :
    ∃ before, memory.read block = some before ∧
      after.read block = some (before ++ [reference]) := by
  unfold push? at pushed
  cases read : memory.read block with
  | none => simp [read] at pushed
  | some before =>
      rw [read] at pushed
      refine ⟨before, ?_, write?_read pushed⟩
      simp

/-- Accept a caller-proposed order only after checking it is a permutation of
the currently decoded references. -/
def reorder? (memory : Memory payloadWidth) (block : Block)
    (candidate : List (Word.Ref payloadWidth)) : Option (Memory payloadWidth) := do
  let current ← memory.read block
  if candidate.Perm current then memory.write? block candidate else none

theorem reorder?_read {memory after : Memory payloadWidth} {block : Block}
    {candidate : List (Word.Ref payloadWidth)}
    (reordered : memory.reorder? block candidate = some after) :
    ∃ current, memory.read block = some current ∧ candidate.Perm current ∧
      after.read block = some candidate := by
  unfold reorder? at reordered
  cases read : memory.read block with
  | none => simp [read] at reordered
  | some current =>
      rw [read] at reordered
      change (if candidate.Perm current then memory.write? block candidate else none) =
        some after at reordered
      by_cases permutation : candidate.Perm current
      · rw [if_pos permutation] at reordered
        refine ⟨current, ?_, permutation, write?_read reordered⟩
        simp
      · rw [if_neg permutation] at reordered
        contradiction

/-- Sort one decoded block by a caller-selected key.  The implementation, not
the key, constructs the permutation. -/
def sortByKey? (memory : Memory payloadWidth) (block : Block)
    (key : Word.Ref payloadWidth → Nat) : Option (Memory payloadWidth) := do
  let current ← memory.read block
  memory.write? block (current.mergeSort fun left right ↦ key left ≤ key right)

theorem sortByKey?_read {memory after : Memory payloadWidth} {block : Block}
    {key : Word.Ref payloadWidth → Nat}
    (sorted : memory.sortByKey? block key = some after) :
    ∃ current, memory.read block = some current ∧
      after.read block = some (current.mergeSort fun left right ↦ key left ≤ key right) ∧
      (current.mergeSort fun left right ↦ key left ≤ key right).Perm current := by
  unfold sortByKey? at sorted
  cases read : memory.read block with
  | none => simp [read] at sorted
  | some current =>
      rw [read] at sorted
      refine ⟨current, ?_, write?_read sorted, List.mergeSort_perm _ _⟩
      simp

/-- Remove syntactically duplicate references from one decoded block. -/
def dedupe? (memory : Memory payloadWidth) (block : Block) : Option (Memory payloadWidth) := do
  let current ← memory.read block
  memory.write? block current.dedup

theorem dedupe?_read {memory after : Memory payloadWidth} {block : Block}
    (deduped : memory.dedupe? block = some after) :
    ∃ current, memory.read block = some current ∧
      after.read block = some current.dedup := by
  unfold dedupe? at deduped
  cases read : memory.read block with
  | none => simp [read] at deduped
  | some current =>
      rw [read] at deduped
      refine ⟨current, ?_, write?_read deduped⟩
      simp

theorem release?_read {memory after : Memory payloadWidth} {block : Block}
    (released : memory.release? block = some after) :
    after.read block = some [] := by
  unfold release? at released
  cases cleared : memory.write? block [] with
  | none => simp [cleared] at released
  | some intermediate =>
      simp [cleared] at released
      subst after
      simpa [Memory.read] using write?_read cleared

/-- Move one decoded block to a larger free block.  The blocks must be
disjoint; the old block is zeroed and returned to the free list before the new
block receives the original references. -/
def reallocate? (memory : Memory payloadWidth) (old : Block) :
    Option (Block × Memory payloadWidth) := do
  let references ← memory.read old
  let (new, memory) ← memory.allocate? references.length
  if old.Disjoint new then
    let memory ← memory.release? old
    let memory ← memory.write? new references
    some (new, memory)
  else
    none

/-- A successful reallocation retains the exact decoded child list, has enough
capacity, zeroes the old block, and exchanges ownership in the free list. -/
theorem reallocate?_result {memory after : Memory payloadWidth}
    {old new : Block} (reallocated : memory.reallocate? old = some (new, after)) :
    ∃ references rest,
      memory.read old = some references ∧
      references.length < new.capacity ∧
      after.read new = some references ∧
      after.read old = some [] ∧
      memory.free.Perm (new :: rest) ∧
      after.free = old :: rest := by
  cases sourceRead : memory.read old with
  | none =>
      simp [reallocate?, sourceRead] at reallocated
  | some references =>
      have afterRead :
          (do
            let selected ← memory.allocate? references.length
            if old.Disjoint selected.1 then
              let released ← selected.2.release? old
              let written ← released.write? selected.1 references
              some (selected.1, written)
            else none) = some (new, after) := by
        simpa [reallocate?, sourceRead] using reallocated
      cases allocated : memory.allocate? references.length with
      | none =>
          simp [allocated] at afterRead
      | some pair =>
          rcases pair with ⟨selected, allocatedMemory⟩
          have afterAllocated :
              (if old.Disjoint selected then
                do
                  let released ← allocatedMemory.release? old
                  let written ← released.write? selected references
                  some (selected, written)
              else none) = some (new, after) := by
            simpa [allocated] using afterRead
          by_cases disjoint : old.Disjoint selected
          · have afterDisjoint :
                (do
                  let released ← allocatedMemory.release? old
                  let written ← released.write? selected references
                  some (selected, written)) = some (new, after) := by
              simpa [if_pos disjoint] using afterAllocated
            cases released : allocatedMemory.release? old with
            | none =>
                simp [released] at afterDisjoint
            | some releasedMemory =>
                have afterReleased :
                    (do
                      let written ← releasedMemory.write? selected references
                      some (selected, written)) = some (new, after) := by
                  simpa [released] using afterDisjoint
                cases written : releasedMemory.write? selected references with
                | none =>
                    simp [written] at afterReleased
                | some finalMemory =>
                    have pairEqual : (selected, finalMemory) = (new, after) := by
                      simpa [written] using afterReleased
                    have selectedEqual : selected = new := congrArg Prod.fst pairEqual
                    have finalEqual : finalMemory = after := congrArg Prod.snd pairEqual
                    subst new
                    subst after
                    refine ⟨references, allocatedMemory.free, by simp,
                      allocate?_capacity allocated, write?_read written, ?_,
                      allocate?_free_perm allocated, ?_⟩
                    · rw [write?_read_disjoint written disjoint.symm]
                      exact release?_read released
                    · rw [write?_free written, release?_free released]
          · simp [if_neg disjoint] at afterAllocated

end Memory
end Nucleus.Classical.Packed
