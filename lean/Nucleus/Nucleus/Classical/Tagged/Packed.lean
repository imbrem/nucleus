import Nucleus.Classical.Packed.Layout
import Nucleus.Classical.Tagged.Abstract

/-!
# Packed tagged classical formulas

Payload tags are `0 = AND`, `1 = OR`, `2 = SAT`, and `3 = literal`.
Polarity is the independent sign bit from `Packed.Word`.  Decoding consumes
each live block exactly once, so cycles, aliases, dangling pointers, and live
garbage are rejected rather than assigned a default meaning.
-/

namespace Nucleus.Classical.Tagged.Packed

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- Interpret one decoded connective tag. -/
def node (tag : Nat) (negative : Bool)
    (children : List (Formula Nat)) : Option (Formula Nat) :=
  match tag with
  | 0 => some (.and negative children)
  | 1 => some (.or negative children)
  | 2 => some (.sat negative children)
  | _ => none

/-- Decode one expression while consuming its uniquely owned live blocks. -/
def decodeRef (memory : Memory payloadWidth) :
    Nat → List Block → Word.Ref payloadWidth →
      Option (Formula Nat × List Block)
  | 0, _, _ => none
  | fuel + 1, blocks, reference =>
      let word := reference.word
      if literal : word.tag = 3 then
        some (.literal ⟨word.base / 4, word.negative⟩, blocks)
      else do
        let (block, remaining) ← Layout.takeBase? blocks word.base
        let children ← memory.read block
        let (decoded, remaining) ← children.foldlM (init := ([], remaining))
          fun (decoded, remaining) child => do
            let (formula, remaining) ← decodeRef memory fuel remaining child
            some (formula :: decoded, remaining)
        let formula ← node word.tag word.negative decoded.reverse
        some (formula, remaining)
  termination_by fuel _ _ => fuel

/-- Decode all sequent roots, threading the ownership state. -/
def decodeRoots (memory : Memory payloadWidth) (fuel : Nat) :
    List Block → List (Word.Ref payloadWidth × Word.Ref payloadWidth) →
      Option (List (Sequent Nat) × List Block)
  | blocks, [] => some ([], blocks)
  | blocks, (premise, conclusion) :: roots => do
      let (premise, blocks) ← decodeRef memory fuel blocks premise
      let (conclusion, blocks) ← decodeRef memory fuel blocks conclusion
      let (roots, blocks) ← decodeRoots memory fuel blocks roots
      some (⟨premise, conclusion⟩ :: roots, blocks)

/-- Strict decoding succeeds only when every certified live block is consumed. -/
def decode? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (List (Sequent Nat)) := do
  let (sequents, remaining) ←
    decodeRoots arena.memory (layout.live.length + 1) layout.live arena.roots
  if remaining.isEmpty then some sequents else none

/-- The exact relation between packed bytes/roots and the abstract tagged list. -/
def Represents (arena : Classical.Packed.Arena payloadWidth) (layout : Layout)
    (sequents : List (Sequent Nat)) : Prop :=
  layout.Valid arena ∧ decode? arena layout = some sequents

theorem Represents.functional {arena : Classical.Packed.Arena payloadWidth}
    {layout : Layout} {left right : List (Sequent Nat)}
    (leftRep : Represents arena layout left) (rightRep : Represents arena layout right) :
    left = right := by
  exact Option.some.inj (leftRep.2.symm.trans rightRep.2)

/-- A packed arena is well formed when strict decoding succeeds under a valid
local allocator layout. -/
def WellFormed (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) : Prop :=
  layout.Valid arena ∧ ∃ sequents, decode? arena layout = some sequents

theorem Represents.wellFormed {arena : Classical.Packed.Arena payloadWidth}
    {layout : Layout} {sequents : List (Sequent Nat)}
    (represents : Represents arena layout sequents) : WellFormed arena layout :=
  ⟨represents.1, sequents, represents.2⟩

end Nucleus.Classical.Tagged.Packed
