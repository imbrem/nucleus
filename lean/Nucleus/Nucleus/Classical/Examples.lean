import Nucleus.Classical.ConcreteEmbedding
import Nucleus.Classical.Packed.Mutate
import Nucleus.Classical.Refutation

/-!
# Executable boundary examples

Small fixed-width examples exercise malformed ownership graphs and the low-bit
encoding.  These are deliberately ordinary Lean declarations, so the normal
Lean build evaluates every check.
-/

namespace Nucleus.Classical.Examples

open Nucleus.Classical.Packed

private def word8 (negative : Bool) (payload : Fin 256) : Word 8 :=
  ⟨negative, payload⟩

private def ref8 (negative : Bool) (payload : Fin 256)
    (nonzero : payload.val ≠ 0) : Word.Ref 8 :=
  ⟨word8 negative payload, nonzero⟩

private def zero8 : Word 8 := Word.zero 8

private def block4 : Block := ⟨4, 0⟩
private def block8 : Block := ⟨8, 0⟩
private def emptyLayout : Layout := ⟨[]⟩

example : (Word.literal? 8 7 true).isSome = true := by decide

example : (Word.pointer? 8 12 2 false).isSome = true := by decide

example : Word.pointer? 8 12 3 false = none := by decide

example : (word8 false ⟨13, by decide⟩).tag = 1 := by decide

example : (word8 true ⟨13, by decide⟩).tag = 1 := by decide

example : ¬(word8 true ⟨0, by decide⟩).CanonicalZero := by decide

example {Atom : Type} (known : Nucleus.Classical.PartialAssignment Atom) :
    Nucleus.Classical.Refines Nucleus.Classical.bottom known :=
  Nucleus.Classical.bottom_refines known

private def literal0 : Word.Ref 8 := ref8 false ⟨3, by decide⟩ (by decide)
private def literal1 : Word.Ref 8 := ref8 false ⟨7, by decide⟩ (by decide)
private def array4 : Word.Ref 8 := ref8 false ⟨4, by decide⟩ (by decide)
private def array8 : Word.Ref 8 := ref8 false ⟨8, by decide⟩ (by decide)

private def cycleArena : Arena 8 where
  memory := ⟨#[zero8, zero8, zero8, zero8,
    array4.word, zero8, zero8, zero8], []⟩
  roots := [(array4, literal0)]

private def cycleLayout : Layout := ⟨[block4]⟩

example : cycleLayout.Valid cycleArena := by
  constructor
  · intro block member
    change block ∈ [block4] at member
    have member := List.mem_singleton.mp member
    subst block
    decide
  · simp [cycleLayout, cycleArena, Block.Disjoint, Block.stop, Block.capacity]
  · intro block member
    simp [cycleArena] at member

/-- The decoder consumes `block4` before following its self-edge. -/
example : (Nucleus.Classical.Alternating.Packed.decode?
    cycleArena cycleLayout).isNone = true := by
  simp [Nucleus.Classical.Alternating.Packed.decode?,
    Nucleus.Classical.Alternating.Packed.decodeRoots,
    Nucleus.Classical.Alternating.Packed.decodeRef, cycleArena, cycleLayout,
    array4, literal0, ref8, word8, block4, Memory.read, Block.Fits,
    Block.Aligned, Block.stop, Block.capacity, Layout.takeBase?, decodeWords,
    zero8, Word.zero, Word.tag, Word.base, Word.CanonicalZero, Word.IsRef]

private def aliasArena : Arena 8 where
  memory := ⟨#[zero8, zero8, zero8, zero8,
    array8.word, array8.word, zero8, zero8,
    zero8, zero8, zero8, zero8], []⟩
  roots := [(array4, literal0)]

private def aliasLayout : Layout := ⟨[block4, block8]⟩

example : aliasLayout.Valid aliasArena := by
  constructor
  · intro block member
    change block ∈ [block4, block8] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · simp [aliasLayout, aliasArena, block4, block8, Block.Disjoint, Block.stop,
      Block.capacity]
  · intro block member
    simp [aliasArena] at member

/-- Two paths cannot own the same child block. -/
example : (Nucleus.Classical.Alternating.Packed.decode?
    aliasArena aliasLayout).isNone = true := by
  simp [Nucleus.Classical.Alternating.Packed.decode?,
    Nucleus.Classical.Alternating.Packed.decodeRoots,
    Nucleus.Classical.Alternating.Packed.decodeRef, aliasArena, aliasLayout,
    array4, array8, literal0, ref8, word8, block4, block8, Memory.read,
    Block.Fits, Block.Aligned, Block.stop, Block.capacity, Layout.takeBase?,
    decodeWords, zero8, Word.zero, Word.tag, Word.base, Word.CanonicalZero,
    Word.IsRef]

private def garbageArena : Arena 8 where
  memory := ⟨#[zero8, zero8, zero8, zero8,
    zero8, zero8, zero8, zero8], []⟩
  roots := [(literal0, literal1)]

example : cycleLayout.Valid garbageArena := by
  constructor
  · intro block member
    change block ∈ [block4] at member
    have member := List.mem_singleton.mp member
    subst block
    decide
  · simp [cycleLayout, garbageArena, Block.Disjoint, Block.stop, Block.capacity]
  · intro block member
    simp [garbageArena] at member

/-- A certified live block which no root reaches is rejected. -/
example : (Nucleus.Classical.Tagged.Packed.decode?
    garbageArena cycleLayout).isNone = true := by
  simp [Nucleus.Classical.Tagged.Packed.decode?,
    Nucleus.Classical.Tagged.Packed.decodeRoots,
    Nucleus.Classical.Tagged.Packed.decodeRef, garbageArena, cycleLayout,
    literal0, literal1, ref8, word8, block4, zero8, Word.zero, Word.tag,
    Word.base]

private def danglingArena : Arena 8 where
  memory := ⟨#[], []⟩
  roots := [(array4, literal0)]

example : emptyLayout.Valid danglingArena := by
  constructor <;> simp [emptyLayout, danglingArena, Layout.AllFit,
    Layout.FreeZeroed]

example : (Nucleus.Classical.Alternating.Packed.decode?
    danglingArena emptyLayout).isNone = true := by
  simp [Nucleus.Classical.Alternating.Packed.decode?,
    Nucleus.Classical.Alternating.Packed.decodeRoots,
    Nucleus.Classical.Alternating.Packed.decodeRef, danglingArena, emptyLayout,
    array4, literal0, ref8, word8, Layout.takeBase?, Word.tag, Word.base]

private def freeEdgeArena : Arena 8 where
  memory := ⟨#[zero8, zero8, zero8, zero8,
    zero8, zero8, zero8, zero8], [block4]⟩
  roots := [(array4, literal0)]

example : emptyLayout.Valid freeEdgeArena := by
  constructor
  · intro block member
    change block ∈ [block4] at member
    have member := List.mem_singleton.mp member
    subst block
    decide
  · simp [emptyLayout, freeEdgeArena, Block.Disjoint]
  · intro block member
    change block ∈ [block4] at member
    have member := List.mem_singleton.mp member
    subst block
    simp [Memory.read, block4, Block.Fits, Block.Aligned, Block.stop,
      Block.capacity, freeEdgeArena, decodeWords, zero8, Word.zero,
      Word.CanonicalZero]

/-- A root may not acquire ownership by pointing into the free list. -/
example : (Nucleus.Classical.Tagged.Packed.decode?
    freeEdgeArena emptyLayout).isNone = true := by
  simp [Nucleus.Classical.Tagged.Packed.decode?,
    Nucleus.Classical.Tagged.Packed.decodeRoots,
    Nucleus.Classical.Tagged.Packed.decodeRef, freeEdgeArena, emptyLayout,
    array4, literal0, ref8, word8, Layout.takeBase?, Word.tag, Word.base]

private def literalArena : Arena 8 where
  memory := ⟨#[], []⟩
  roots := [(literal0, literal1)]

/-- Literal-only arenas need no retagging and exercise the concrete converter. -/
example : Nucleus.Classical.Embedding.AlternatingToTagged.Packed.retag?
    literalArena emptyLayout = some literalArena := by
  simp [Nucleus.Classical.Embedding.AlternatingToTagged.Packed.retag?,
    Nucleus.Classical.Embedding.AlternatingToTagged.Packed.retagRoots,
    Nucleus.Classical.Embedding.AlternatingToTagged.Packed.retagRef,
    literalArena, emptyLayout, literal0, literal1, ref8, word8, Word.tag]

end Nucleus.Classical.Examples
