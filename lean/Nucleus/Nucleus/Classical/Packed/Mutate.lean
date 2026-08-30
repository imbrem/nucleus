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

/-- Split a nonempty list into its initial elements and last element.  The
result shape is convenient for mutations that transfer ownership of the last
child in an array. -/
def splitLast? : List α → Option (List α × α)
  | [] => none
  | [last] => some ([], last)
  | head :: next :: tail =>
      (fun (initial, last) ↦ (head :: initial, last)) <$> splitLast? (next :: tail)

theorem splitLast?_eq_some {values : List α} {initial : List α} {last : α}
    (split : splitLast? values = some (initial, last)) :
    values = initial ++ [last] := by
  induction values generalizing initial last with
  | nil => simp [splitLast?] at split
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [splitLast?, Option.some.injEq, Prod.mk.injEq] at split
          rcases split with ⟨rfl, rfl⟩
          rfl
      | cons next rest =>
          cases recursive : splitLast? (next :: rest) with
          | none => simp [splitLast?, recursive] at split
          | some result =>
              rcases result with ⟨recursiveInitial, recursiveLast⟩
              simp only [splitLast?, recursive] at split
              rcases split with ⟨rfl, rfl⟩
              rw [ih recursive]
              rfl

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

/-- Move the last reference from `source` to `target`, complementing its sign.
The blocks must be disjoint so the two writes are an ownership transfer rather
than an aliasing update.  Failure is transactional because the intermediate
memories are immutable values local to the option computation. -/
def cross? (memory : Memory payloadWidth) (source target : Block) :
    Option (Word.Ref payloadWidth × Memory payloadWidth) := do
  let sourceReferences ← memory.read source
  let (sourceInitial, moved) ← splitLast? sourceReferences
  if source.Disjoint target then
    let afterSource ← memory.write? source sourceInitial
    let targetReferences ← afterSource.read target
    let afterTarget ← afterSource.write? target (targetReferences ++ [moved.neg])
    some (moved, afterTarget)
  else
    none

/-- Successful crossing exposes both exact writes and the transferred
reference.  This is the mutation-level evidence used by whole-arena validity
and semantic proofs. -/
theorem cross?_steps {memory after : Memory payloadWidth} {source target : Block}
    {moved : Word.Ref payloadWidth}
    (crossed : memory.cross? source target = some (moved, after)) :
    ∃ sourceInitial afterSource targetReferences,
      memory.read source = some (sourceInitial ++ [moved]) ∧
      source.Disjoint target ∧
      memory.write? source sourceInitial = some afterSource ∧
      afterSource.read target = some targetReferences ∧
      afterSource.write? target (targetReferences ++ [moved.neg]) = some after := by
  unfold cross? at crossed
  cases sourceRead : memory.read source with
  | none => simp [sourceRead] at crossed
  | some sourceReferences =>
      cases split : splitLast? sourceReferences with
      | none => simp [sourceRead, split] at crossed
      | some result =>
          rcases result with ⟨sourceInitial, selected⟩
          by_cases disjoint : source.Disjoint target
          · cases sourceWritten : memory.write? source sourceInitial with
            | none => simp [sourceRead, split, disjoint, sourceWritten] at crossed
            | some afterSource =>
                cases targetRead : afterSource.read target with
                | none =>
                    simp [sourceRead, split, disjoint, sourceWritten, targetRead] at crossed
                | some targetReferences =>
                    cases targetWritten :
                        afterSource.write? target (targetReferences ++ [selected.neg]) with
                    | none =>
                        simp [sourceRead, split, disjoint, sourceWritten, targetRead,
                          targetWritten] at crossed
                    | some afterTarget =>
                        have pairEqual : (selected, afterTarget) = (moved, after) := by
                          simpa [sourceRead, split, disjoint, sourceWritten, targetRead,
                            targetWritten] using crossed
                        have selectedEqual : selected = moved := congrArg Prod.fst pairEqual
                        have afterEqual : afterTarget = after := congrArg Prod.snd pairEqual
                        subst selected
                        subst afterTarget
                        exact ⟨sourceInitial, afterSource, targetReferences,
                          congrArg some (splitLast?_eq_some split), disjoint,
                          sourceWritten, targetRead, targetWritten⟩
          · simp [sourceRead, disjoint] at crossed

/-- Crossing leaves the source without its last reference and appends the
complemented reference to the target. -/
theorem cross?_reads {memory after : Memory payloadWidth} {source target : Block}
    {moved : Word.Ref payloadWidth}
    (crossed : memory.cross? source target = some (moved, after)) :
    ∃ sourceInitial targetReferences,
      memory.read source = some (sourceInitial ++ [moved]) ∧
      memory.read target = some targetReferences ∧
      after.read source = some sourceInitial ∧
      after.read target = some (targetReferences ++ [moved.neg]) := by
  obtain ⟨sourceInitial, afterSource, targetReferences, sourceRead, disjoint,
    sourceWritten, targetRead, targetWritten⟩ := cross?_steps crossed
  have originalTarget : memory.read target = some targetReferences := by
    rw [← targetRead, write?_read_disjoint sourceWritten disjoint]
  have finalSource : after.read source = some sourceInitial := by
    rw [write?_read_disjoint targetWritten disjoint.symm]
    exact write?_read sourceWritten
  exact ⟨sourceInitial, targetReferences, sourceRead, originalTarget,
    finalSource, write?_read targetWritten⟩

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
