import Nucleus.Classical.Mutation.Operations
import Nucleus.Classical.Tagged.Runtime.Allocator

/-!
# Checked mutations for the self-describing tagged runtime

This is the Rust-facing mutation design.  Raw functions edit the flat word
array directly through live-block headers.  Public functions run the ordinary
whole-arena validator and then check the exact one-sequent abstract edit.  A
successful result therefore carries both allocation safety and the logical
rule it implements.

The implementation deliberately keeps the raw word operation, structural
postcheck, and semantic theorem as separate layers.  Rust can translate the
raw operations one for one and retain the same checked boundary.
-/

namespace Nucleus.Classical.Tagged.Runtime.Mutate

open Nucleus.Classical
open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged.Runtime

namespace Operations
export Nucleus.Classical.Mutation.Operations (Side editAt EditedAt editAt_eq_true)
end Operations

namespace Abstract
export Nucleus.Classical.Mutation.Operations.Tagged
  (permutesRoot dedupesRoot pushesRoot crossesRoot
    permutesRoot_eq_true dedupesRoot_eq_true pushesRoot_eq_true
    crossesRoot_eq_true)
end Abstract

variable {payloadWidth : Nat}

/-- Write canonical children to one live block and independently read them
back before returning. -/
def writeLive? (arena : Arena payloadWidth) (block : Block)
    (references : List (Word.Ref payloadWidth)) : Option (Arena payloadWidth) := do
  let contents ← Allocator.liveWords? payloadWidth block references
  let candidate ← Allocator.writeBlock? arena block contents
  if candidate.readLive? block = some references then some candidate else none

theorem writeLive?_reads {arena after : Arena payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : writeLive? arena block references = some after) :
    after.readLive? block = some references := by
  unfold writeLive? at written
  cases contentsEncoded : Allocator.liveWords? payloadWidth block references with
  | none => simp [contentsEncoded] at written
  | some contents =>
      cases blockWritten : Allocator.writeBlock? arena block contents with
      | none => simp [contentsEncoded, blockWritten] at written
      | some candidate =>
          by_cases reads : candidate.readLive? block = some references
          · have equal : candidate = after := by
              simpa [contentsEncoded, blockWritten, reads] using written
            subst candidate
            exact reads
          · simp [contentsEncoded, blockWritten, reads] at written

/-- Find the allocated block named by one selected non-literal root. -/
def rootBlock? (arena : Arena payloadWidth) (index : Nat)
    (side : Operations.Side) : Option Block := do
  let roots ← arena.roots[index]?
  let reference := side.select roots
  if reference.word.tag = 3 then none
  else arena.liveBlock? reference.word.base

namespace Raw

/-- Apply a caller-proposed permutation to one selected root block. -/
def reorderRoot? (arena : Arena payloadWidth) (index : Nat)
    (side : Operations.Side) (candidate : List (Word.Ref payloadWidth)) :
    Option (Arena payloadWidth) := do
  let block ← rootBlock? arena index side
  let current ← arena.readLive? block
  if candidate.Perm current then writeLive? arena block candidate else none

/-- Sort a selected root block by an implementation-supplied key. -/
def sortRootByKey? (arena : Arena payloadWidth) (index : Nat)
    (side : Operations.Side) (key : Word.Ref payloadWidth → Nat) :
    Option (Arena payloadWidth) := do
  let block ← rootBlock? arena index side
  let current ← arena.readLive? block
  writeLive? arena block
    (current.mergeSort fun left right ↦ key left ≤ key right)

/-- Remove syntactically duplicate references from a selected root block. -/
def dedupeRoot? (arena : Arena payloadWidth) (index : Nat)
    (side : Operations.Side) : Option (Arena payloadWidth) := do
  let block ← rootBlock? arena index side
  let current ← arena.readLive? block
  writeLive? arena block current.dedup

/-- Append one literal.  Array references are rejected because borrowing one
would violate unique subtree ownership. -/
def pushRootLiteral? (arena : Arena payloadWidth) (index : Nat)
    (side : Operations.Side) (reference : Word.Ref payloadWidth) :
    Option (Arena payloadWidth) := do
  if reference.word.tag = 3 then pure () else none
  let block ← rootBlock? arena index side
  let current ← arena.readLive? block
  writeLive? arena block (current ++ [reference])

/-- Transfer the last owned child to the opposite root and complement it.
The intermediate source write is not exposed; the final whole-arena check is
transactional. -/
def crossRoot? (arena : Arena payloadWidth) (index : Nat)
    (sourceSide : Operations.Side) : Option (Arena payloadWidth) := do
  let source ← rootBlock? arena index sourceSide
  let target ← rootBlock? arena index sourceSide.flip
  let sourceReferences ← arena.readLive? source
  let (initial, moved) ← splitLast? sourceReferences
  if source.Disjoint target then pure () else none
  let afterSource ← writeLive? arena source initial
  let targetReferences ← afterSource.readLive? target
  writeLive? afterSource target (targetReferences ++ [moved.neg])

end Raw

/-- Validate a raw arena and accept it only when its decoded syntax is one
exact abstract edit of the checked source. -/
def checked? (check : Tagged.Sequent Nat → Tagged.Sequent Nat → Bool)
    (index : Nat) (before : Checked payloadWidth)
    (raw : Option (Arena payloadWidth)) : Option (Checked payloadWidth) := do
  let candidate ← raw
  let after ← Runtime.check? candidate
  if Operations.editAt check index before.decoded.sequents
      after.decoded.sequents then
    some after
  else
    none

theorem checked?_result
    {check : Tagged.Sequent Nat → Tagged.Sequent Nat → Bool}
    {index : Nat} {before after : Checked payloadWidth}
    {raw : Option (Arena payloadWidth)}
    (ran : checked? check index before raw = some after) :
    ∃ candidate,
      raw = some candidate ∧ Runtime.check? candidate = some after ∧
      Operations.editAt check index before.decoded.sequents
        after.decoded.sequents = true := by
  cases rawResult : raw with
  | none => simp [checked?, rawResult] at ran
  | some candidate =>
      cases validated : Runtime.check? candidate with
      | none => simp [checked?, rawResult, validated] at ran
      | some result =>
          cases edited : Operations.editAt check index before.decoded.sequents
              result.decoded.sequents with
          | false => simp [checked?, rawResult, validated, edited] at ran
          | true =>
              have equal : result = after := by
                simpa [checked?, rawResult, validated, edited] using ran
              subst result
              exact ⟨candidate, rfl, validated, edited⟩

/-- Success exposes the exact source and target syntax plus the checked edit
relation. -/
theorem checked?_decoded
    {check : Tagged.Sequent Nat → Tagged.Sequent Nat → Bool}
    {relation : Tagged.Sequent Nat → Tagged.Sequent Nat → Prop}
    (reflects : ∀ before after, check before after = true ↔
      relation before after)
    {index : Nat} {before after : Checked payloadWidth}
    {raw : Option (Arena payloadWidth)}
    (ran : checked? check index before raw = some after) :
    Operations.EditedAt relation index before.decoded.sequents
      after.decoded.sequents := by
  obtain ⟨_, _, _, edited⟩ := checked?_result ran
  exact (Operations.editAt_eq_true reflects _ _ _).mp edited

def reorderRoot? (before : Checked payloadWidth) (index : Nat)
    (side : Operations.Side) (candidate : List (Word.Ref payloadWidth)) :
    Option (Checked payloadWidth) :=
  checked? (Abstract.permutesRoot side) index before
    (Raw.reorderRoot? before.arena index side candidate)

def sortRootByKey? (before : Checked payloadWidth) (index : Nat)
    (side : Operations.Side) (key : Word.Ref payloadWidth → Nat) :
    Option (Checked payloadWidth) :=
  checked? (Abstract.permutesRoot side) index before
    (Raw.sortRootByKey? before.arena index side key)

def dedupeRoot? (before : Checked payloadWidth) (index : Nat)
    (side : Operations.Side) : Option (Checked payloadWidth) :=
  checked? (Abstract.dedupesRoot side) index before
    (Raw.dedupeRoot? before.arena index side)

def literal (reference : Word.Ref payloadWidth) : Tagged.Formula Nat :=
  .literal ⟨reference.word.base / 4, reference.word.negative⟩

def pushRootLiteral? (before : Checked payloadWidth) (index : Nat)
    (side : Operations.Side) (reference : Word.Ref payloadWidth) :
    Option (Checked payloadWidth) :=
  checked? (Abstract.pushesRoot (literal reference) side) index before
    (Raw.pushRootLiteral? before.arena index side reference)

def crossRoot? (before : Checked payloadWidth) (index : Nat)
    (sourceSide : Operations.Side) : Option (Checked payloadWidth) :=
  checked? (Abstract.crossesRoot sourceSide) index before
    (Raw.crossRoot? before.arena index sourceSide)

/-! ## Semantic contracts -/

/-- Truth of every decoded sequent under a partial assignment. -/
def EntailsAt (known : PartialAssignment Nat) (checked : Checked payloadWidth) : Prop :=
  Classical.Tagged.EntailsAt known checked.decoded.sequents

/-- Null-assignment theoremhood for a checked runtime arena. -/
def Syllogism (checked : Checked payloadWidth) : Prop :=
  EntailsAt Classical.bottom checked

private theorem checkedEntailsAt
    {check : Tagged.Sequent Nat → Tagged.Sequent Nat → Bool}
    {relation : Tagged.Sequent Nat → Tagged.Sequent Nat → Prop}
    (reflects : ∀ before after, check before after = true ↔
      relation before after)
    (preserves : ∀ {before after}, relation before after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : Checked payloadWidth}
    {raw : Option (Arena payloadWidth)}
    (ran : checked? check index before raw = some after)
    {known : PartialAssignment Nat} (holds : EntailsAt known before) :
    EntailsAt known after := by
  exact Nucleus.Classical.Mutation.Operations.Tagged.EditedAt.entailsAt preserves
    (checked?_decoded reflects ran) known holds

theorem reorderRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {candidate : List (Word.Ref payloadWidth)}
    {known : PartialAssignment Nat}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  exact checkedEntailsAt (Abstract.permutesRoot_eq_true side)
    Nucleus.Classical.Mutation.Operations.Tagged.PermutesRoot.entailsAt ran holds

theorem sortRootByKey?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {key : Word.Ref payloadWidth → Nat} {known : PartialAssignment Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  exact checkedEntailsAt (Abstract.permutesRoot_eq_true side)
    Nucleus.Classical.Mutation.Operations.Tagged.PermutesRoot.entailsAt ran holds

theorem dedupeRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side} {known : PartialAssignment Nat}
    (ran : dedupeRoot? before index side = some after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  exact checkedEntailsAt (Abstract.dedupesRoot_eq_true side)
    Nucleus.Classical.Mutation.Operations.Tagged.DedupesRoot.entailsAt ran holds

theorem pushRootLiteral?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {reference : Word.Ref payloadWidth} {known : PartialAssignment Nat}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  exact checkedEntailsAt
    (Abstract.pushesRoot_eq_true (literal reference) side)
    Nucleus.Classical.Mutation.Operations.Tagged.PushesRoot.entailsAt ran holds

theorem crossRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {sourceSide : Operations.Side}
    {known : PartialAssignment Nat}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : EntailsAt known before) : EntailsAt known after := by
  exact checkedEntailsAt (Abstract.crossesRoot_eq_true sourceSide)
    Nucleus.Classical.Mutation.Operations.Tagged.CrossesRoot.entailsAt ran holds

theorem reorderRoot?_syllogism {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {candidate : List (Word.Ref payloadWidth)}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Syllogism before) : Syllogism after :=
  reorderRoot?_entailsAt ran holds

theorem sortRootByKey?_syllogism {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {key : Word.Ref payloadWidth → Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Syllogism before) : Syllogism after :=
  sortRootByKey?_entailsAt ran holds

theorem dedupeRoot?_syllogism {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    (ran : dedupeRoot? before index side = some after)
    (holds : Syllogism before) : Syllogism after :=
  dedupeRoot?_entailsAt ran holds

theorem pushRootLiteral?_syllogism {before after : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {reference : Word.Ref payloadWidth}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : Syllogism before) : Syllogism after :=
  pushRootLiteral?_entailsAt ran holds

theorem crossRoot?_syllogism {before after : Checked payloadWidth}
    {index : Nat} {sourceSide : Operations.Side}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Syllogism before) : Syllogism after :=
  crossRoot?_entailsAt ran holds

end Nucleus.Classical.Tagged.Runtime.Mutate
