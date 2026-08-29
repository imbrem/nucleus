import Nucleus.Classical.Packed.Block

/-!
# Packed arenas and strict layout certificates

The packed arena contains one word array, a reusable free list, and a list of
sequent-root pairs.  Live block size classes are not recoverable from those
fields alone, so a complete candidate state also carries `Layout` and must
validate it.  A future semantic wire object need not serialize allocator state,
but decoding such an object must construct both fields together.

Decoders consume live blocks as they traverse roots.  Removing a block before
its children are visited rejects cycles, and requiring every block to be
consumed rejects garbage.  A second visit rejects aliases.  This is
load-bearing for the untagged alternating representation, whose array meaning
depends on its unique root path.
-/

namespace Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- Packed words, free blocks, and sequent roots.  This is not independently
checkable without its live-block layout. -/
structure Arena (payloadWidth : Nat) where
  memory : Memory payloadWidth
  roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)
  deriving DecidableEq, Repr

/-- In-memory metadata proposing live block sizes and ownership. -/
structure Layout where
  live : List Block
  deriving DecidableEq, Repr

/-- Package the complete candidate in-memory state.  `Layout.Valid` or a
design's `Represents` relation supplies the actual check. -/
structure State (payloadWidth : Nat) where
  arena : Arena payloadWidth
  layout : Layout
  deriving DecidableEq, Repr

namespace Layout

/-- Remove the first block at `base`, returning it and the unconsumed blocks. -/
def takeBase? : List Block → Nat → Option (Block × List Block)
  | [], _ => none
  | block :: blocks, base =>
      if block.base = base then some (block, blocks)
      else (fun (selected, rest) ↦ (selected, block :: rest)) <$> takeBase? blocks base

theorem takeBase?_selected {blocks : List Block} {base : Nat}
    {selected : Block} {rest : List Block}
    (taken : takeBase? blocks base = some (selected, rest)) :
    selected.base = base := by
  induction blocks generalizing selected rest with
  | nil => simp [takeBase?] at taken
  | cons head tail ih =>
      by_cases equal : head.base = base
      · rw [takeBase?, if_pos equal] at taken
        have pairEqual := Option.some.inj taken
        have selectedEqual : head = selected := congrArg Prod.fst pairEqual
        subst selected
        exact equal
      · cases recursive : takeBase? tail base with
        | none =>
            rw [takeBase?, if_neg equal, recursive] at taken
            contradiction
        | some pair =>
            rcases pair with ⟨chosen, chosenRest⟩
            rw [takeBase?, if_neg equal, recursive] at taken
            have pairEqual := Option.some.inj taken
            have selectedEqual : chosen = selected := congrArg Prod.fst pairEqual
            subst selected
            exact ih recursive

theorem takeBase?_perm {blocks : List Block} {base : Nat}
    {selected : Block} {rest : List Block}
    (taken : takeBase? blocks base = some (selected, rest)) :
    blocks.Perm (selected :: rest) := by
  induction blocks generalizing selected rest with
  | nil => simp [takeBase?] at taken
  | cons head tail ih =>
      by_cases equal : head.base = base
      · rw [takeBase?, if_pos equal] at taken
        have pairEqual := Option.some.inj taken
        have selectedEqual : head = selected := congrArg Prod.fst pairEqual
        have restEqual : tail = rest := congrArg Prod.snd pairEqual
        subst selected
        subst rest
        exact List.Perm.refl _
      · cases recursive : takeBase? tail base with
        | none =>
            rw [takeBase?, if_neg equal, recursive] at taken
            contradiction
        | some pair =>
            rcases pair with ⟨chosen, chosenRest⟩
            rw [takeBase?, if_neg equal, recursive] at taken
            have pairEqual := Option.some.inj taken
            have selectedEqual : chosen = selected := congrArg Prod.fst pairEqual
            have restEqual : head :: chosenRest = rest := congrArg Prod.snd pairEqual
            subst selected
            rw [← restEqual]
            exact (List.Perm.cons head (ih recursive)).trans (List.Perm.swap _ _ _)

/-- Every block in a list fits the word array. -/
def AllFit (blocks : List Block) (size : Nat) : Prop :=
  ∀ block ∈ blocks, block.Fits size

/-- Every free block is canonically zeroed. -/
def FreeZeroed (memory : Memory payloadWidth) : Prop :=
  ∀ block ∈ memory.free, memory.read block = some []

/-- Local allocator/layout invariants independent of expression tags. -/
structure Valid (arena : Arena payloadWidth) (layout : Layout) : Prop where
  allFit : AllFit (layout.live ++ arena.memory.free) arena.memory.words.size
  disjoint : (layout.live ++ arena.memory.free).Pairwise Block.Disjoint
  freeZeroed : FreeZeroed arena.memory

theorem Valid.live_fit {arena : Arena payloadWidth} {layout : Layout}
    (valid : Valid arena layout) {block : Block} (member : block ∈ layout.live) :
    block.Fits arena.memory.words.size := by
  exact valid.allFit block (List.mem_append_left _ member)

theorem Valid.free_fit {arena : Arena payloadWidth} {layout : Layout}
    (valid : Valid arena layout) {block : Block} (member : block ∈ arena.memory.free) :
    block.Fits arena.memory.words.size := by
  exact valid.allFit block (List.mem_append_right _ member)

end Layout
end Nucleus.Classical.Packed
