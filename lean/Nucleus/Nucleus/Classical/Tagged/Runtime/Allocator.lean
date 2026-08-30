import Nucleus.Classical.Tagged.Runtime.Equality

/-!
# Intrusive allocator operations for the tagged runtime

This module gives an executable reference implementation of the intrusive
free rings.  Free blocks are ordered by increasing size class; blocks of one
class form a circular doubly linked ring.  The first block of the largest
class is the single allocator root and stores heads for all smaller rings.

The reference operations rebuild the affected free-node metadata and then run
the ordinary intrusive decoder as a postcheck.  This is already a direct,
safe Rust algorithm.  An optimized in-place splice can later refine the same
functions without changing their checked contracts.
-/

namespace Nucleus.Classical.Tagged.Runtime.Allocator

open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged.Runtime

variable {payloadWidth : Nat}

/-- Encode an unsigned metadata word. -/
def natural? (payloadWidth value : Nat) : Option (Word payloadWidth) :=
  if bound : value < 2 ^ payloadWidth then
    some ⟨false, ⟨value, bound⟩⟩
  else
    none

/-- Encode a non-null aligned allocator pointer. -/
def pointer? (payloadWidth base : Nat) : Option (Word payloadWidth) :=
  Word.pointer? payloadWidth base 0 false

/-- Encode an optional allocator pointer using canonical zero for null. -/
def optionalPointer? (payloadWidth : Nat) : Option Nat → Option (Word payloadWidth)
  | none => some (Word.zero payloadWidth)
  | some base => pointer? payloadWidth base

/-- Replace one complete fitted block. -/
def writeBlock? (arena : Arena payloadWidth) (block : Block)
    (contents : List (Word payloadWidth)) : Option (Arena payloadWidth) :=
  if block.Fits arena.words.size ∧ contents.length = block.capacity then
    some { arena with words :=
      (replaceRange arena.words contents.toArray block.base block.capacity) }
  else
    none

/-- Encode an allocated live block with a size-class header and canonical
zero-terminated children. -/
def liveWords? (payloadWidth : Nat) (block : Block)
    (references : List (Word.Ref payloadWidth)) : Option (List (Word payloadWidth)) := do
  if block.sizeClass + 2 ≤ payloadWidth then pure () else none
  let header ← natural? payloadWidth block.sizeClass
  let children ← encodeWords payloadWidth (block.capacity - 1) references
  some (header :: children)

/-- Initialize one allocated block as an empty live array. -/
def initializeLive? (arena : Arena payloadWidth) (block : Block) :
    Option (Arena payloadWidth) := do
  let contents ← liveWords? payloadWidth block []
  let candidate ← writeBlock? arena block contents
  if candidate.readLive? block = some [] then some candidate else none

theorem initializeLive?_reads {arena after : Arena payloadWidth} {block : Block}
    (initialized : initializeLive? arena block = some after) :
    after.readLive? block = some [] := by
  unfold initializeLive? at initialized
  cases contentsEncoded : liveWords? payloadWidth block [] with
  | none => simp [contentsEncoded] at initialized
  | some contents =>
      cases written : writeBlock? arena block contents with
      | none => simp [contentsEncoded, written] at initialized
      | some candidate =>
          rw [contentsEncoded] at initialized
          change (do
            let candidate ← writeBlock? arena block contents
            if candidate.readLive? block = some [] then some candidate else none) =
              some after at initialized
          rw [written] at initialized
          change (if candidate.readLive? block = some [] then some candidate else none) =
            some after at initialized
          split at initialized
          · rename_i reads
            have equal := Option.some.inj initialized
            subst after
            exact reads
          · contradiction

/-- The blocks in one size-class ring, preserving list order. -/
def ring (free : List Block) (sizeClass : Nat) : List Block :=
  free.filter fun block ↦ block.sizeClass = sizeClass

/-- Circular neighbours of one block in its size-class ring. -/
def neighbours? (free : List Block) (block : Block) : Option (Block × Block) := do
  let members := ring free block.sizeClass
  let index ← members.findIdx? (· = block)
  let next := members.getD ((index + 1) % members.length) block
  let prev := members.getD ((index + members.length - 1) % members.length) block
  some (next, prev)

/-- First representative of a nonempty size-class ring. -/
def ringHead? (free : List Block) (sizeClass : Nat) : Option Block :=
  free.find? fun block ↦ block.sizeClass = sizeClass

/-- The first block of the largest size class. -/
def root? (free : List Block) : Option Block := do
  let last ← free.getLast?
  ringHead? free last.sizeClass

/-- Encode one free node.  Only the distinguished root carries the directory
of smaller ring heads. -/
def freeWords? (payloadWidth : Nat) (free : List Block) (root block : Block) :
    Option (List (Word payloadWidth)) := do
  let (next, prev) ← neighbours? free block
  let nextWord ← pointer? payloadWidth next.base
  let prevWord ← pointer? payloadWidth prev.base
  let classWord ← natural? payloadWidth block.sizeClass
  let spareCount := block.capacity - 4
  let spare ← if block = root then
      if block.sizeClass ≤ spareCount then
        let directory ← (List.range block.sizeClass).mapM fun sizeClass ↦
          optionalPointer? payloadWidth ((ringHead? free sizeClass).map Block.base)
        some (directory ++
          List.replicate (spareCount - block.sizeClass) (Word.zero payloadWidth))
      else
        none
    else
      some (List.replicate spareCount (Word.zero payloadWidth))
  some (Word.zero payloadWidth :: nextWord :: prevWord :: classWord :: spare)

/-- Write every intrusive node using one distinguished root. -/
def writeFreeNodes? (arena : Arena payloadWidth) (free : List Block)
    (root : Block) : Option (Arena payloadWidth) :=
  free.foldlM (init := arena) fun current block ↦ do
    let contents ← freeWords? payloadWidth free root block
    writeBlock? current block contents

/-- Build intrusive metadata from a class-ordered free-block list. -/
def encodeFreeRaw? (arena : Arena payloadWidth) (free : List Block) :
    Option (Arena payloadWidth) :=
  match root? free with
  | none => some { arena with freeRoot := Word.zero payloadWidth }
  | some root => do
      let written ← writeFreeNodes? arena free root
      let rootWord ← pointer? payloadWidth root.base
      some { written with freeRoot := rootWord }

/-- Build intrusive metadata and accept it only when the ordinary decoder
recovers exactly the proposed class/ring order. -/
def encodeFree? (arena : Arena payloadWidth) (free : List Block) :
    Option (Arena payloadWidth) := do
  let candidate ← encodeFreeRaw? arena free
  if candidate.decodeFree? = some free then some candidate else none

theorem encodeFree?_decodes {arena after : Arena payloadWidth}
    {free : List Block} (encoded : encodeFree? arena free = some after) :
    after.decodeFree? = some free := by
  unfold encodeFree? at encoded
  cases raw : encodeFreeRaw? arena free with
  | none => simp [raw] at encoded
  | some candidate =>
      rw [raw] at encoded
      change (if candidate.decodeFree? = some free then some candidate else none) =
        some after at encoded
      split at encoded
      · rename_i decoded
        have equal := Option.some.inj encoded
        subst after
        exact decoded
      · contradiction

/-- Select the first class-ordered block with room for the live header,
children, and terminator. -/
def take? (free : List Block) (children : Nat) : Option (Block × List Block) :=
  Memory.takeFree? free (children + 1)

theorem take?_capacity {free : List Block} {children : Nat}
    {block : Block} {rest : List Block}
    (taken : take? free children = some (block, rest)) :
    children + 1 < block.capacity :=
  Memory.takeFree?_capacity taken

theorem take?_perm {free : List Block} {children : Nat}
    {block : Block} {rest : List Block}
    (taken : take? free children = some (block, rest)) :
    free.Perm (block :: rest) :=
  Memory.takeFree?_perm taken

/-- Allocate and initialize one empty live block.  The caller must link and
fill the block before presenting the complete arena as a checked theorem
state. -/
def allocate? (arena : Arena payloadWidth) (children : Nat) :
    Option (Block × Arena payloadWidth) := do
  let free ← arena.decodeFree?
  let (block, rest) ← take? free children
  let initialized ← initializeLive? arena block
  let after ← encodeFree? initialized rest
  if after.readLive? block = some [] then some (block, after) else none

theorem allocate?_result {arena after : Arena payloadWidth} {children : Nat}
    {block : Block} (allocated : allocate? arena children = some (block, after)) :
    ∃ free rest,
      arena.decodeFree? = some free ∧
      take? free children = some (block, rest) ∧
      children + 1 < block.capacity ∧
      free.Perm (block :: rest) ∧
      after.decodeFree? = some rest ∧
      after.readLive? block = some [] := by
  unfold allocate? at allocated
  cases freeDecoded : arena.decodeFree? with
  | none => simp [freeDecoded] at allocated
  | some free =>
      cases taken : take? free children with
      | none => simp [freeDecoded, taken] at allocated
      | some selected =>
          rcases selected with ⟨chosen, rest⟩
          cases initialized : initializeLive? arena chosen with
          | none => simp [freeDecoded, taken, initialized] at allocated
          | some intermediate =>
              cases encoded : encodeFree? intermediate rest with
              | none => simp [freeDecoded, taken, initialized, encoded] at allocated
              | some final =>
                  by_cases live : final.readLive? chosen = some []
                  · have pairEqual : (chosen, final) = (block, after) := by
                      simpa [freeDecoded, taken, initialized, encoded, live] using allocated
                    have chosenEqual : chosen = block := congrArg Prod.fst pairEqual
                    have finalEqual : final = after := congrArg Prod.snd pairEqual
                    subst chosen
                    subst final
                    exact ⟨free, rest, rfl, taken, take?_capacity taken,
                      take?_perm taken, encodeFree?_decodes encoded, live⟩
                  · simp [freeDecoded, taken, initialized, encoded, live] at allocated

/-- Insert a block before the first strictly larger size class. -/
def insert (block : Block) : List Block → List Block
  | [] => [block]
  | head :: tail =>
      if block.sizeClass ≤ head.sizeClass then block :: head :: tail
      else head :: insert block tail

theorem insert_perm (block : Block) (free : List Block) :
    (insert block free).Perm (block :: free) := by
  induction free with
  | nil => simp [insert]
  | cons head tail ih =>
      unfold insert
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons head ih).trans (List.Perm.swap _ _ _)

/-- Release an unlinked live block into its class ring. -/
def release? (arena : Arena payloadWidth) (block : Block) :
    Option (Arena payloadWidth) := do
  let free ← arena.decodeFree?
  let decoded ← arena.readLive? block
  -- Release is only defined for an empty unlinked block.  Formula-tree
  -- mutations clear children before calling the allocator.
  if decoded.isEmpty then
    encodeFree? arena (insert block free)
  else
    none

theorem release?_result {arena after : Arena payloadWidth} {block : Block}
    (released : release? arena block = some after) :
    ∃ free,
      arena.decodeFree? = some free ∧
      arena.readLive? block = some [] ∧
      after.decodeFree? = some (insert block free) ∧
      (insert block free).Perm (block :: free) := by
  unfold release? at released
  cases freeDecoded : arena.decodeFree? with
  | none => simp [freeDecoded] at released
  | some free =>
      cases liveDecoded : arena.readLive? block with
      | none => simp [freeDecoded, liveDecoded] at released
      | some references =>
          cases references with
          | nil =>
            have encoded : encodeFree? arena (insert block free) = some after := by
              simpa [freeDecoded, liveDecoded] using released
            exact ⟨free, rfl, rfl, encodeFree?_decodes encoded,
              insert_perm block free⟩
          | cons head tail => simp [freeDecoded, liveDecoded] at released

end Nucleus.Classical.Tagged.Runtime.Allocator
