import Nucleus.Classical.Alternating.Abstract
import Nucleus.Classical.Packed.Layout

/-!
# Packed untagged alternating classical expressions

Payload tag `0` denotes an untagged array and payload tag `3` denotes a
literal.  An array's connective is supplied by its root position and flips at
every array edge: left roots start in `Mode.all`, while right roots start in
`Mode.any`.  Polarity remains the independent sign bit from `Packed.Word`.

Decoding consumes each certified live block exactly once.  Consequently a
cycle, an aliased array, or a dangling pointer makes decoding fail; strict
top-level decoding also rejects certified live blocks not reached from a root.
This ownership check is load-bearing because an untagged array has no meaning
independent of its unique root path.
-/

namespace Nucleus.Classical.Alternating.Packed

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- Decode one expression at its path-determined mode while consuming its
uniquely owned live blocks.  The mode affects only descendants: the abstract
syntax records no connective tag. -/
def decodeRef (memory : Memory payloadWidth) :
    Nat → Mode → List Block → Word.Ref payloadWidth →
      Option (Expr Nat × List Block)
  | 0, _, _, _ => none
  | fuel + 1, mode, blocks, reference =>
      let word := reference.word
      if literal : word.tag = 3 then
        some (.literal ⟨word.base / 4, word.negative⟩, blocks)
      else if _array : word.tag = 0 then do
        let (block, remaining) ← Layout.takeBase? blocks word.base
        let children ← memory.read block
        let (decoded, remaining) ← children.foldlM (init := ([], remaining))
          fun (decoded, remaining) child => do
            let (expr, remaining) ←
              decodeRef memory fuel mode.flip remaining child
            some (expr :: decoded, remaining)
        some (.array word.negative decoded.reverse, remaining)
      else
        none
  termination_by fuel _ _ _ => fuel

/-- Decode all sequent roots, threading the live-block ownership state. -/
def decodeRoots (memory : Memory payloadWidth) (fuel : Nat) :
    List Block → List (Word.Ref payloadWidth × Word.Ref payloadWidth) →
      Option (List (Sequent Nat) × List Block)
  | blocks, [] => some ([], blocks)
  | blocks, (left, right) :: roots => do
      let (left, blocks) ← decodeRef memory fuel .all blocks left
      let (right, blocks) ← decodeRef memory fuel .any blocks right
      let (roots, blocks) ← decodeRoots memory fuel blocks roots
      some (⟨left, right⟩ :: roots, blocks)

/-- Strict decoding succeeds only if every certified live block is reached
exactly once from the sequent roots. -/
def decode? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (Arena Nat) := do
  let (sequents, remaining) ←
    decodeRoots arena.memory (layout.live.length + 1) layout.live arena.roots
  if remaining.isEmpty then some sequents else none

/-- The exact relation between packed storage and an abstract alternating
arena.  Allocator validity and strict syntactic decoding are both explicit. -/
def Represents (arena : Classical.Packed.Arena payloadWidth) (layout : Layout)
    (sequents : Arena Nat) : Prop :=
  layout.Valid arena ∧ decode? arena layout = some sequents

theorem Represents.functional {arena : Classical.Packed.Arena payloadWidth}
    {layout : Layout} {left right : Arena Nat}
    (leftRep : Represents arena layout left) (rightRep : Represents arena layout right) :
    left = right := by
  exact Option.some.inj (leftRep.2.symm.trans rightRep.2)

/-- A packed alternating arena is well formed when it has a valid allocator
layout and strict decoding succeeds. -/
def WellFormed (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) : Prop :=
  layout.Valid arena ∧ ∃ sequents, decode? arena layout = some sequents

theorem Represents.wellFormed {arena : Classical.Packed.Arena payloadWidth}
    {layout : Layout} {sequents : Arena Nat}
    (represents : Represents arena layout sequents) : WellFormed arena layout :=
  ⟨represents.1, sequents, represents.2⟩

end Nucleus.Classical.Alternating.Packed
