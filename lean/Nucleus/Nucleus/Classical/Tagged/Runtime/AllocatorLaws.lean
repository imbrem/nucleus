import Nucleus.Classical.Tagged.Runtime.Allocator

/-!
# Allocator laws

These are the storage contracts used by the mutable runtime. Blocks have
power-of-two size classes beginning at four words. A live block owns its whole
capacity, including zero tail words; those words cannot name other storage.
The free root belongs to the largest ring and its tail is the directory of
smaller rings.
-/

namespace Nucleus.Classical.Tagged.Runtime.AllocatorLaws

open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged.Runtime

variable {payloadWidth : Nat}

theorem minimumCapacity : (Block.capacity ⟨4, 0⟩) = 4 := by
  simp [Block.capacity]

theorem nextClassDoubles (base sizeClass : Nat) :
    (Block.capacity ⟨base, sizeClass + 1⟩) =
      2 * Block.capacity ⟨base, sizeClass⟩ := by
  simp [Block.capacity, pow_succ]
  omega

/-- Number of zero words following the live children. The first is the
terminator and the rest are reserved capacity owned by the same block. -/
def trailingZeros (block : Block) (children : Nat) : Nat :=
  block.capacity - 1 - children

def CanStore (block : Block) (children : Nat) : Prop :=
  children < block.capacity - 1

instance (block : Block) (children : Nat) : Decidable (CanStore block children) :=
  by unfold CanStore; infer_instance

theorem canStore_iff_hasTerminator {block : Block} {children : Nat} :
    CanStore block children ↔ 0 < trailingZeros block children := by
  simp [CanStore, trailingZeros]
  omega

theorem canPush_iff_twoTrailingZeros {block : Block} {children : Nat} :
    CanStore block (children + 1) ↔ 1 < trailingZeros block children := by
  simp [CanStore, trailingZeros]
  omega

theorem liveWords?_ownsTail {block : Block}
    {references : List (Word.Ref payloadWidth)}
    {contents : List (Word payloadWidth)}
    (encoded : Allocator.liveWords? payloadWidth block references = some contents) :
    contents.length = block.capacity ∧
      decodeWords contents.tail = some references := by
  obtain ⟨header, children, _, _, childrenEncoded, rfl⟩ :=
    Allocator.liveWords?_result encoded
  constructor
  · have capacity := Block.four_le_capacity block
    simp [encodeWords_length childrenEncoded]
    omega
  · simp [decodeWords_of_encodeWords childrenEncoded]

/-- Abstract contract checked by the intrusive decoder: the root represents
the largest ring and its directory has one entry for every smaller class. -/
structure RootDirectory (free : List Block) where
  root : Block
  rootMem : root ∈ free
  largest : ∀ block ∈ free, block.sizeClass ≤ root.sizeClass
  heads : Fin root.sizeClass → Option Block
  headClass : ∀ sizeClass head,
    heads sizeClass = some head →
      head ∈ free ∧ head.sizeClass = sizeClass

theorem directory_covers_smallerClasses {free : List Block}
    (directory : RootDirectory free)
    (sizeClass : Nat) (smaller : sizeClass < directory.root.sizeClass) :
    ∃ slot : Fin directory.root.sizeClass, slot.val = sizeClass :=
  ⟨⟨sizeClass, smaller⟩, rfl⟩

end Nucleus.Classical.Tagged.Runtime.AllocatorLaws
