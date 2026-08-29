import Nucleus.Classical.Alternating.Packed
import Nucleus.Classical.Embedding
import Nucleus.Classical.Tagged.Packed

/-!
# Checked packed embedding

The untagged representation determines every array connective from its unique
root path.  `retag?` follows those paths, consumes the certified live blocks,
and records the recovered connective in each pointer.  It preserves literal
words, signs, block addresses, capacities, the free list, and the word-array
length.

`embed?` is a proof-level checked syntax boundary.  It uses classical equality
for the nested abstract syntax, so it is not the executable implementation;
`retag?` is the executable candidate generator.  The checker decodes both
sides and checks the abstract commuting square, so its theorem does not trust
that generator as logical evidence.  Allocator validity remains an explicit
premise of the representation theorem.
-/

namespace Nucleus.Classical.Embedding.AlternatingToTagged.Packed

open Nucleus.Classical
open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

private def nodeTag : Alternating.Mode → Nat
  | .all => 0
  | .any => 1

private def pointerRef? (payloadWidth base tag : Nat) (negative : Bool) :
    Option (Word.Ref payloadWidth) :=
  match encoded : Word.pointer? payloadWidth base tag negative with
  | none => none
  | some word => some ⟨word, Word.pointer?_isRef encoded⟩

/-- Retag one owned expression, threading both rewritten memory and the set of
live blocks which have not yet been consumed. -/
def retagRef : Nat → Alternating.Mode → Memory payloadWidth → List Block →
    Word.Ref payloadWidth →
      Option (Word.Ref payloadWidth × Memory payloadWidth × List Block)
  | 0, _, _, _, _ => none
  | fuel + 1, mode, memory, blocks, reference =>
      let word := reference.word
      if _literal : word.tag = 3 then
        some (reference, memory, blocks)
      else if _array : word.tag = 0 then do
        let (block, remaining) ← Layout.takeBase? blocks word.base
        let children ← memory.read block
        let (rewritten, memory, remaining) ←
          children.foldlM (init := ([], memory, remaining))
            fun (rewritten, memory, remaining) child => do
              let (child, memory, remaining) ←
                retagRef fuel mode.flip memory remaining child
              some (child :: rewritten, memory, remaining)
        let memory ← memory.write? block rewritten.reverse
        let reference ← pointerRef? payloadWidth word.base (nodeTag mode) word.negative
        some (reference, memory, remaining)
      else
        none
  termination_by fuel _ _ _ _ => fuel

/-- Retag sequent roots.  Premises begin in conjunction mode and conclusions
begin in disjunction mode. -/
def retagRoots (fuel : Nat) : Memory payloadWidth → List Block →
    List (Word.Ref payloadWidth × Word.Ref payloadWidth) →
      Option (List (Word.Ref payloadWidth × Word.Ref payloadWidth) ×
        Memory payloadWidth × List Block)
  | memory, blocks, [] => some ([], memory, blocks)
  | memory, blocks, (left, right) :: roots => do
      let (left, memory, blocks) ← retagRef fuel .all memory blocks left
      let (right, memory, blocks) ← retagRef fuel .any memory blocks right
      let (roots, memory, blocks) ← retagRoots fuel memory blocks roots
      some ((left, right) :: roots, memory, blocks)

/-- Perform the structural packed-to-packed retagging. -/
def retag? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (Classical.Packed.Arena payloadWidth) := do
  let (roots, memory, remaining) ←
    retagRoots (layout.live.length + 1) arena.memory layout.live arena.roots
  if remaining.isEmpty then some ⟨memory, roots⟩ else none

/-- Proof-level checked concrete embedding.  The final abstract equality is
the authority boundary; the executable retagging algorithm remains untrusted. -/
noncomputable def embed? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (Classical.Packed.Arena payloadWidth) := by
  classical
  exact do
    let source ← Alternating.Packed.decode? arena layout
    let target ← retag? arena layout
    if Tagged.Packed.decode? target layout = some (AlternatingToTagged.arena source) then
      some target
    else
      none

/-- Every successful concrete embedding has a source abstract arena and a
target representation of its abstract embedding.  This is the commuting
square, stated using the exact representation relations on both sides. -/
theorem embed?_commutes {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target) :
    ∃ abstract,
      Alternating.Packed.decode? source layout = some abstract ∧
      Tagged.Packed.decode? target layout =
        some (AlternatingToTagged.arena abstract) := by
  classical
  unfold embed? at embedded
  cases decoded : Alternating.Packed.decode? source layout with
  | none => simp [decoded] at embedded
  | some abstract =>
      rw [decoded] at embedded
      cases retagged : retag? source layout with
      | none => simp [retagged] at embedded
      | some candidate =>
          rw [retagged] at embedded
          change (if Tagged.Packed.decode? candidate layout =
              some (AlternatingToTagged.arena abstract) then some candidate else none) =
            some target at embedded
          split at embedded
          · rename_i targetDecoded
            have targetEqual := Option.some.inj embedded
            subst target
            exact ⟨abstract, by simp, targetDecoded⟩
          · contradiction

/-- Adding allocator-validity evidence upgrades the syntactic square to the
exact representation relations used by both concrete designs. -/
theorem embed?_represents {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target)
    (sourceValid : layout.Valid source) (targetValid : layout.Valid target) :
    ∃ abstract,
      Alternating.Packed.Represents source layout abstract ∧
      Tagged.Packed.Represents target layout (AlternatingToTagged.arena abstract) := by
  obtain ⟨abstract, sourceDecoded, targetDecoded⟩ := embed?_commutes embedded
  exact ⟨abstract, ⟨sourceValid, sourceDecoded⟩, ⟨targetValid, targetDecoded⟩⟩

/-- The concrete embedding also preserves semantics at every partial
assignment, not only at the null assignment. -/
theorem embed?_entailsAt_iff {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target)
    (sourceValid : layout.Valid source) (targetValid : layout.Valid target)
    (known : PartialAssignment Nat) :
    ∃ abstract tagged,
      Alternating.Packed.Represents source layout abstract ∧
      Tagged.Packed.Represents target layout tagged ∧
      (Tagged.EntailsAt known tagged ↔ abstract.EntailsAt known) := by
  obtain ⟨abstract, sourceRepresents, targetRepresents⟩ :=
    embed?_represents embedded sourceValid targetValid
  exact ⟨abstract, AlternatingToTagged.arena abstract, sourceRepresents,
    targetRepresents, AlternatingToTagged.arena_entailsAt_iff known abstract⟩

end Nucleus.Classical.Embedding.AlternatingToTagged.Packed
