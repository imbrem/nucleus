import Nucleus.Classical.Packed.Intrusive
import Nucleus.Classical.Tagged.Equality
import Nucleus.Classical.Tagged.Packed

/-!
# Self-describing tagged classical runtime

This is the selected packed representation for a Rust implementation.  The
low two pointer bits remain `AND`, `OR`, `SAT`, and literal tags.  A live array
starts with one unsigned size-class word followed by its zero-terminated child
references.  A free array uses the intrusive four-word header from
`Packed.Intrusive` instead.

No external live-block layout is trusted.  Decoding discovers live blocks from
the sequent roots, discovers free blocks from the single intrusive root, and
requires the two disjoint sets to cover all storage after four reserved words.
Consequently cycles, aliases, dangling pointers, overlapping allocation, and
unowned storage are rejected by one executable check.
-/

namespace Nucleus.Classical.Tagged.Runtime

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- The runtime arena uses one flat word array and one intrusive free root. -/
abbrev Arena := Packed.Intrusive.Arena

/-- The ownership and syntax recovered by the total runtime validator. -/
structure Decoded where
  sequents : List (Tagged.Sequent Nat)
  live : List Block
  free : List Block

namespace Arena

/-- Decode the size-class header of a live block. -/
def liveBlock? (arena : Arena payloadWidth) (base : Nat) : Option Block := do
  let classWord ← arena.word? base
  let sizeClass ← Packed.Intrusive.Arena.natural? classWord
  -- Besides bounding hostile exponentiation, this ensures the complete block
  -- capacity is representable by the fixed-width address space.
  if sizeClass + 2 ≤ payloadWidth then
    let block : Block := ⟨base, sizeClass⟩
    if block.Fits arena.words.size then some block else none
  else
    none

/-- Strictly read the children of a live block, including canonical padding.
The first word is metadata, so a class-zero block has room for at most two
children plus its terminator. -/
def readLive? (arena : Arena payloadWidth) (block : Block) :
    Option (List (Word.Ref payloadWidth)) := do
  let decoded ← arena.liveBlock? block.base
  if decoded = block then
    decodeWords
      ((arena.words.toList.drop (block.base + 1)).take (block.capacity - 1))
  else
    none

/-- One block is disjoint from every block already owned by the decoder. -/
def disjointFrom (block : Block) (owned : List Block) : Bool :=
  owned.all fun other ↦ decide (block.Disjoint other)

/-- The decoded allocation covers every word after the reserved prefix. -/
def coversStorage (blocks : List Block) (size : Nat) : Bool :=
  (List.range (size - 4)).all fun offset ↦
    blocks.any fun block ↦
      decide (block.base ≤ 4 + offset) && decide (4 + offset < block.stop)

/-- Decode one uniquely owned formula.  `free` is fixed allocator ownership;
`live` accumulates blocks reached through formula pointers. -/
def decodeRef (arena : Arena payloadWidth) (free : List Block) :
    Nat → List Block → Word.Ref payloadWidth →
      Option (Tagged.Formula Nat × List Block)
  | 0, _, _ => none
  | fuel + 1, live, reference =>
      let word := reference.word
      if literal : word.tag = 3 then
        some (.literal ⟨word.base / 4, word.negative⟩, live)
      else do
        let block ← arena.liveBlock? word.base
        if disjointFrom block (live ++ free) then pure () else none
        let children ← arena.readLive? block
        let (decoded, live) ← children.foldlM (init := ([], block :: live))
          fun (decoded, live) child => do
            let (formula, live) ← decodeRef arena free fuel live child
            some (formula :: decoded, live)
        let formula ← Tagged.Packed.node word.tag word.negative decoded.reverse
        some (formula, live)
  termination_by fuel _ _ => fuel

/-- Decode every sequent root while accumulating unique live ownership. -/
def decodeRoots (arena : Arena payloadWidth) (free : List Block) (fuel : Nat) :
    List Block → List (Word.Ref payloadWidth × Word.Ref payloadWidth) →
      Option (List (Tagged.Sequent Nat) × List Block)
  | live, [] => some ([], live)
  | live, (premise, conclusion) :: roots => do
      let (premise, live) ← arena.decodeRef free fuel live premise
      let (conclusion, live) ← arena.decodeRef free fuel live conclusion
      let (roots, live) ← arena.decodeRoots free fuel live roots
      some (⟨premise, conclusion⟩ :: roots, live)

/-- Decode the complete self-describing runtime state, retaining the recovered
allocation partition for checked mutations. -/
def decodeState? (arena : Arena payloadWidth) : Option Decoded := do
  if arena.zeroRange 0 4 then pure () else none
  let free ← arena.decodeFree?
  let (sequents, live) ←
    arena.decodeRoots free (arena.words.size + 1) [] arena.roots
  if coversStorage (live ++ free) arena.words.size then
    some ⟨sequents, live, free⟩
  else
    none

/-- Decode only the logical contents of a validated runtime arena. -/
def decode? (arena : Arena payloadWidth) : Option (List (Tagged.Sequent Nat)) :=
  Decoded.sequents <$> arena.decodeState?

end Arena

/-- Exact interpretation of a self-describing tagged runtime arena. -/
def Represents (arena : Arena payloadWidth)
    (sequents : List (Tagged.Sequent Nat)) : Prop :=
  arena.decode? = some sequents

namespace Represents

theorem functional {arena : Arena payloadWidth}
    {left right : List (Tagged.Sequent Nat)}
    (leftRepresents : Represents arena left)
    (rightRepresents : Represents arena right) : left = right := by
  exact Option.some.inj (leftRepresents.symm.trans rightRepresents)

end Represents

/-- Successful runtime decoding certifies the fixed-width address bound. -/
theorem Arena.decode?_addressable {arena : Arena payloadWidth}
    {sequents : List (Tagged.Sequent Nat)}
    (decoded : arena.decode? = some sequents) :
    arena.words.size ≤ 2 ^ payloadWidth := by
  unfold Arena.decode? at decoded
  cases stateDecoded : arena.decodeState? with
  | none => simp [stateDecoded] at decoded
  | some state =>
      unfold Arena.decodeState? at stateDecoded
      split at stateDecoded
      · cases freeDecoded : arena.decodeFree? with
        | none => simp [freeDecoded] at stateDecoded
        | some free =>
            exact Packed.Intrusive.Arena.decodeFree?_addressable freeDecoded
      · contradiction

end Nucleus.Classical.Tagged.Runtime
