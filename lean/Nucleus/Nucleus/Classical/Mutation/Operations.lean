import Nucleus.Classical.Mutation
import Nucleus.Classical.Alternating.Equality
import Nucleus.Classical.Packed.Mutate
import Nucleus.Classical.Tagged.Equality

/-!
# Executable packed mutations

This module connects the shared block mutators to complete packed states.  A
raw operation updates the arena memory and retains the allocator layout.  A
design-specific operation additionally decodes both complete states and checks
an exact root-edit relation before returning.  Success supplies exact syntax;
it is not by itself an allocator-validity certificate.  The LCF-facing
theorems combine it with validity from an existing concrete theorem fact and
derive validity of the result.

Array subtrees are uniquely owned in states accepted by the strict decoder.
In particular, `pushRootLiteral?` accepts only a tag-3 literal: pushing an
existing array reference would create an alias and make strict decoding fail.
Reordering and deduplication retain only results for which that complete
ownership-aware decoder succeeds.
-/

namespace Nucleus.Classical.Mutation.Operations

open Nucleus.Classical
open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- Select one side of a sequent root pair. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

namespace Side

def select (side : Side) (roots : Word.Ref payloadWidth × Word.Ref payloadWidth) :
    Word.Ref payloadWidth :=
  match side with
  | .left => roots.1
  | .right => roots.2

/-- The opposite side of one sequent. -/
def flip : Side → Side
  | .left => .right
  | .right => .left

@[simp] theorem flip_flip (side : Side) : side.flip.flip = side := by
  cases side <;> rfl

end Side

namespace State

/-- Replace only the packed memory, retaining roots and the proposed layout. -/
def withMemory (state : Packed.State payloadWidth) (memory : Memory payloadWidth) :
    Packed.State payloadWidth :=
  { arena := { state.arena with memory := memory }
    layout := state.layout }

/-- Find the live block named by a selected non-literal sequent root.
Strict whole-state decoding establishes actual ownership. -/
def rootBlock? (state : Packed.State payloadWidth) (index : Nat) (side : Side) :
    Option Block := do
  let roots ← state.arena.roots[index]?
  let reference := side.select roots
  if reference.word.tag = 3 then
    none
  else
    let (block, _) ← Layout.takeBase? state.layout.live reference.word.base
    some block

theorem rootBlock?_mem {state : Packed.State payloadWidth} {index : Nat}
    {side : Side} {block : Block}
    (found : rootBlock? state index side = some block) :
    block ∈ state.layout.live := by
  cases rootsAt : state.arena.roots[index]? with
  | none => simp [rootBlock?, rootsAt] at found
  | some roots =>
      by_cases literal : (side.select roots).word.tag = 3
      · simp [rootBlock?, rootsAt, literal] at found
      · cases taken : Layout.takeBase? state.layout.live (side.select roots).word.base with
        | none => simp [rootBlock?, rootsAt, literal, taken] at found
        | some result =>
            rcases result with ⟨selected, rest⟩
            have selectedEqual : selected = block := by
              simpa [rootBlock?, rootsAt, literal, taken] using found
            subst selected
            exact (Layout.takeBase?_perm taken).mem_iff.mpr (by simp)

/-- A selected block is never inferred from a literal payload which happens
to share its numerical atom ID with a live block base. -/
theorem rootBlock?_not_literal {state : Packed.State payloadWidth} {index : Nat}
    {side : Side} {block : Block}
    (found : rootBlock? state index side = some block) :
    ∃ roots, state.arena.roots[index]? = some roots ∧
      (side.select roots).word.tag ≠ 3 := by
  cases rootsAt : state.arena.roots[index]? with
  | none => simp [rootBlock?, rootsAt] at found
  | some roots =>
      refine ⟨roots, rfl, ?_⟩
      intro literal
      simp [rootBlock?, rootsAt, literal] at found

end State

/-- Writing one live block preserves the allocator/layout invariants. -/
theorem writeLiveValid {state : Packed.State payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)} {memory : Memory payloadWidth}
    (valid : state.layout.Valid state.arena) (live : block ∈ state.layout.live)
    (written : state.arena.memory.write? block references = some memory) :
    state.layout.Valid (State.withMemory state memory).arena := by
  have wordsSize := Memory.write?_words_size written
  have freeEqual := Memory.write?_free written
  have split := List.pairwise_append.mp valid.disjoint
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro candidate member
    change candidate ∈ state.layout.live ++ memory.free at member
    rw [freeEqual] at member
    have fit := valid.allFit candidate member
    change candidate.Fits memory.words.size
    simpa [wordsSize] using fit
  · simpa [State.withMemory, freeEqual] using valid.disjoint
  · intro freeBlock freeMember
    simp only [State.withMemory] at freeMember ⊢
    rw [freeEqual] at freeMember
    have disjoint : block.Disjoint freeBlock :=
      split.2.2 block live freeBlock freeMember
    rw [Memory.write?_read_disjoint written disjoint]
    exact valid.freeZeroed freeBlock freeMember
  · change memory.words.size ≤ 2 ^ payloadWidth
    simpa [wordsSize] using valid.addressable

namespace Raw

/-- Apply a checked permutation to the block named by one root. -/
def reorderRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (candidate : List (Word.Ref payloadWidth)) : Option (Packed.State payloadWidth) := do
  let block ← State.rootBlock? state index side
  let memory ← state.arena.memory.reorder? block candidate
  some (State.withMemory state memory)

/-- Sort the references in the block named by one root. -/
def sortRootByKey? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (key : Word.Ref payloadWidth → Nat) : Option (Packed.State payloadWidth) := do
  let block ← State.rootBlock? state index side
  let memory ← state.arena.memory.sortByKey? block key
  some (State.withMemory state memory)

/-- Remove duplicate references from the block named by one root. -/
def dedupeRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side) :
    Option (Packed.State payloadWidth) := do
  let block ← State.rootBlock? state index side
  let memory ← state.arena.memory.dedupe? block
  some (State.withMemory state memory)

/-- Append a literal reference to the block named by one root.  The tag check
is the ownership restriction: array references cannot be borrowed here. -/
def pushRootLiteral? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (reference : Word.Ref payloadWidth) : Option (Packed.State payloadWidth) := do
  if reference.word.tag = 3 then
    let block ← State.rootBlock? state index side
    let memory ← state.arena.memory.push? block reference
    some (State.withMemory state memory)
  else
    none

/-- Transfer the last owned child of `sourceSide` to the opposite root and
complement its sign.  Design-specific wrappers decide whether the transferred
subtree is admissible for their semantics. -/
def crossRoot? (state : Packed.State payloadWidth) (index : Nat)
    (sourceSide : Side) : Option (Packed.State payloadWidth) := do
  let source ← State.rootBlock? state index sourceSide
  let target ← State.rootBlock? state index sourceSide.flip
  let (_, memory) ← state.arena.memory.cross? source target
  some (State.withMemory state memory)

theorem reorderRoot?_result {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    (ran : reorderRoot? state index side candidate = some after) :
    ∃ block memory,
      State.rootBlock? state index side = some block ∧
      state.arena.memory.reorder? block candidate = some memory ∧
      after = State.withMemory state memory := by
  cases found : State.rootBlock? state index side with
  | none => simp [reorderRoot?, found] at ran
  | some block =>
      cases mutated : state.arena.memory.reorder? block candidate with
      | none => simp [reorderRoot?, found, mutated] at ran
      | some memory =>
          have equal : State.withMemory state memory = after := by
            simpa [reorderRoot?, found, mutated] using ran
          exact ⟨block, memory, rfl, mutated, equal.symm⟩

theorem sortRootByKey?_result {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    (ran : sortRootByKey? state index side key = some after) :
    ∃ block memory,
      State.rootBlock? state index side = some block ∧
      state.arena.memory.sortByKey? block key = some memory ∧
      after = State.withMemory state memory := by
  cases found : State.rootBlock? state index side with
  | none => simp [sortRootByKey?, found] at ran
  | some block =>
      cases mutated : state.arena.memory.sortByKey? block key with
      | none => simp [sortRootByKey?, found, mutated] at ran
      | some memory =>
          have equal : State.withMemory state memory = after := by
            simpa [sortRootByKey?, found, mutated] using ran
          exact ⟨block, memory, rfl, mutated, equal.symm⟩

theorem dedupeRoot?_result {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side}
    (ran : dedupeRoot? state index side = some after) :
    ∃ block memory,
      State.rootBlock? state index side = some block ∧
      state.arena.memory.dedupe? block = some memory ∧
      after = State.withMemory state memory := by
  cases found : State.rootBlock? state index side with
  | none => simp [dedupeRoot?, found] at ran
  | some block =>
      cases mutated : state.arena.memory.dedupe? block with
      | none => simp [dedupeRoot?, found, mutated] at ran
      | some memory =>
          have equal : State.withMemory state memory = after := by
            simpa [dedupeRoot?, found, mutated] using ran
          exact ⟨block, memory, rfl, mutated, equal.symm⟩

theorem pushRootLiteral?_result {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    (ran : pushRootLiteral? state index side reference = some after) :
    reference.word.tag = 3 ∧ ∃ block memory,
      State.rootBlock? state index side = some block ∧
      state.arena.memory.push? block reference = some memory ∧
      after = State.withMemory state memory := by
  by_cases literal : reference.word.tag = 3
  · cases found : State.rootBlock? state index side with
    | none => simp [pushRootLiteral?, literal, found] at ran
    | some block =>
        cases mutated : state.arena.memory.push? block reference with
        | none => simp [pushRootLiteral?, literal, found, mutated] at ran
        | some memory =>
            have equal : State.withMemory state memory = after := by
              simpa [pushRootLiteral?, literal, found, mutated] using ran
            exact ⟨literal, block, memory, rfl, mutated, equal.symm⟩
  · simp [pushRootLiteral?, literal] at ran

theorem crossRoot?_result {state after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side}
    (ran : crossRoot? state index sourceSide = some after) :
    ∃ source target moved memory,
      State.rootBlock? state index sourceSide = some source ∧
      State.rootBlock? state index sourceSide.flip = some target ∧
      state.arena.memory.cross? source target = some (moved, memory) ∧
      after = State.withMemory state memory := by
  cases sourceFound : State.rootBlock? state index sourceSide with
  | none => simp [crossRoot?, sourceFound] at ran
  | some source =>
      cases targetFound : State.rootBlock? state index sourceSide.flip with
      | none => simp [crossRoot?, sourceFound, targetFound] at ran
      | some target =>
          cases crossed : state.arena.memory.cross? source target with
          | none => simp [crossRoot?, sourceFound, targetFound, crossed] at ran
          | some result =>
              rcases result with ⟨moved, memory⟩
              have equal : State.withMemory state memory = after := by
                simpa [crossRoot?, sourceFound, targetFound, crossed] using ran
              exact ⟨source, target, moved, memory, rfl, rfl,
                crossed, equal.symm⟩

theorem reorderRoot?_valid {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    (valid : state.layout.Valid state.arena)
    (ran : reorderRoot? state index side candidate = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨block, memory, found, mutated, rfl⟩ := reorderRoot?_result ran
  refine writeLiveValid (references := candidate) valid (State.rootBlock?_mem found) ?_
  unfold Memory.reorder? at mutated
  cases read : state.arena.memory.read block with
  | none => simp [read] at mutated
  | some current =>
      rw [read] at mutated
      by_cases permutation : candidate.Perm current
      · simpa [permutation] using mutated
      · simp [permutation] at mutated

theorem sortRootByKey?_valid {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    (valid : state.layout.Valid state.arena)
    (ran : sortRootByKey? state index side key = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨block, memory, found, mutated, rfl⟩ := sortRootByKey?_result ran
  obtain ⟨current, read, _, _⟩ := Memory.sortByKey?_read mutated
  refine writeLiveValid
    (references := current.mergeSort fun left right ↦ key left ≤ key right)
    valid (State.rootBlock?_mem found) ?_
  unfold Memory.sortByKey? at mutated
  simpa [read] using mutated

theorem dedupeRoot?_valid {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side}
    (valid : state.layout.Valid state.arena)
    (ran : dedupeRoot? state index side = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨block, memory, found, mutated, rfl⟩ := dedupeRoot?_result ran
  obtain ⟨current, read, _⟩ := Memory.dedupe?_read mutated
  refine writeLiveValid (references := current.dedup)
    valid (State.rootBlock?_mem found) ?_
  unfold Memory.dedupe? at mutated
  simpa [read] using mutated

theorem pushRootLiteral?_valid {state after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    (valid : state.layout.Valid state.arena)
    (ran : pushRootLiteral? state index side reference = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨_, block, memory, found, mutated, rfl⟩ := pushRootLiteral?_result ran
  obtain ⟨current, read, _⟩ := Memory.push?_read mutated
  refine writeLiveValid (references := current ++ [reference])
    valid (State.rootBlock?_mem found) ?_
  unfold Memory.push? at mutated
  simpa [read] using mutated

theorem crossRoot?_valid {state after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side}
    (valid : state.layout.Valid state.arena)
    (ran : crossRoot? state index sourceSide = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨source, target, moved, memory, sourceFound, targetFound, crossed, rfl⟩ :=
    crossRoot?_result ran
  obtain ⟨sourceInitial, intermediate, targetReferences, _, _, sourceWritten, _,
    targetWritten⟩ := Memory.cross?_steps crossed
  have intermediateValid :
      (State.withMemory state intermediate).layout.Valid
        (State.withMemory state intermediate).arena :=
    writeLiveValid valid (State.rootBlock?_mem sourceFound) sourceWritten
  have targetLive : target ∈ (State.withMemory state intermediate).layout.live := by
    simpa [State.withMemory] using State.rootBlock?_mem targetFound
  have finalValid :
      (State.withMemory (State.withMemory state intermediate) memory).layout.Valid
        (State.withMemory (State.withMemory state intermediate) memory).arena :=
    writeLiveValid intermediateValid targetLive targetWritten
  simpa [State.withMemory] using finalValid

end Raw

/-! ## Exact abstract root edits -/

/-- Check one pointwise edit while requiring every other list element to be
structurally identical. -/
def editAt [DecidableEq α] (check : α → α → Bool) :
    Nat → List α → List α → Bool
  | 0, before :: befores, after :: afters =>
      check before after && decide (befores = afters)
  | index + 1, before :: befores, after :: afters =>
      decide (before = after) && editAt check index befores afters
  | _, _, _ => false

/-- The proposition certified by `editAt`. -/
def EditedAt (relation : α → α → Prop) :
    Nat → List α → List α → Prop
  | 0, before :: befores, after :: afters =>
      relation before after ∧ befores = afters
  | index + 1, before :: befores, after :: afters =>
      before = after ∧ EditedAt relation index befores afters
  | _, _, _ => False

theorem editAt_eq_true [DecidableEq α] {check : α → α → Bool}
    {relation : α → α → Prop}
    (reflects : ∀ before after, check before after = true ↔ relation before after) :
    ∀ index before after,
      editAt check index before after = true ↔
        EditedAt relation index before after
  | 0, [], _ | 0, _ :: _, [] => by simp [editAt, EditedAt]
  | 0, before :: befores, after :: afters => by
      simp [editAt, EditedAt, reflects]
  | _ + 1, [], _ | _ + 1, _ :: _, [] => by simp [editAt, EditedAt]
  | index + 1, before :: befores, after :: afters => by
      simp [editAt, EditedAt, editAt_eq_true reflects index]

theorem EditedAt.all {relation : α → α → Prop} {predicate : α → Prop}
    (preserves : ∀ {before after}, relation before after → predicate before → predicate after) :
    ∀ {index before after}, EditedAt relation index before after →
      (∀ value ∈ before, predicate value) →
      ∀ value ∈ after, predicate value
  | 0, _ :: befores, _ :: afters, ⟨related, tails⟩, source => by
      subst afters
      intro value member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · rw [equal]
        exact preserves related (source _ (by simp))
      · exact source value (by simp [member])
  | index + 1, before :: befores, _ :: afters, ⟨rfl, edited⟩, source => by
      intro value member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · rw [equal]
        exact source _ (by simp)
      · have tailSource : ∀ item ∈ befores, predicate item := by
          intro item itemMember
          exact source item (List.mem_cons_of_mem before itemMember)
        have tailTarget : ∀ item ∈ afters, predicate item :=
          @EditedAt.all α relation predicate preserves index befores afters edited tailSource
        exact tailTarget value member

/-- Decode both complete states and accept only an exact checked edit. -/
def checked? [DecidableEq α]
    (decode : Packed.State payloadWidth → Option (List α))
    (check : α → α → Bool) (index : Nat)
    (before : Packed.State payloadWidth) (raw : Option (Packed.State payloadWidth)) :
    Option (Packed.State payloadWidth) := do
  let source ← decode before
  let after ← raw
  let target ← decode after
  if editAt check index source target then some after else none

theorem checked?_result [DecidableEq α]
    {decode : Packed.State payloadWidth → Option (List α)}
    {check : α → α → Bool} {index : Nat}
    {before after : Packed.State payloadWidth} {raw : Option (Packed.State payloadWidth)}
    (ran : checked? decode check index before raw = some after) :
    ∃ source target,
      decode before = some source ∧ raw = some after ∧
      decode after = some target ∧ editAt check index source target = true := by
  cases sourceDecoded : decode before with
  | none => simp [checked?, sourceDecoded] at ran
  | some source =>
      cases rawResult : raw with
      | none => simp [checked?, sourceDecoded, rawResult] at ran
      | some rawAfter =>
          cases targetDecoded : decode rawAfter with
          | none => simp [checked?, sourceDecoded, rawResult, targetDecoded] at ran
          | some target =>
              cases safe : editAt check index source target with
              | false =>
                  simp [checked?, sourceDecoded, rawResult, targetDecoded, safe] at ran
              | true =>
                  have equal : rawAfter = after := by
                    simpa [checked?, sourceDecoded, rawResult, targetDecoded, safe] using ran
                  subst rawAfter
                  exact ⟨source, target, rfl, rfl, targetDecoded, safe⟩

/-- A successful checked operation exposes the exact whole-arena decodings
and the one-root edit relating them. -/
theorem checked?_decoded [DecidableEq α]
    {decode : Packed.State payloadWidth → Option (List α)}
    {check : α → α → Bool} {relation : α → α → Prop}
    (reflects : ∀ before after, check before after = true ↔ relation before after)
    {index : Nat} {before after : Packed.State payloadWidth}
    {raw : Option (Packed.State payloadWidth)}
    (ran : checked? decode check index before raw = some after) :
    ∃ source target,
      decode before = some source ∧ decode after = some target ∧
        EditedAt relation index source target := by
  obtain ⟨source, target, sourceDecoded, _, targetDecoded, edited⟩ :=
    checked?_result ran
  exact ⟨source, target, sourceDecoded, targetDecoded,
    (editAt_eq_true reflects _ _ _).mp edited⟩

/-- The design-specific postcheck cannot hide an invalid raw result: any raw
layout-preservation theorem lifts directly through `checked?`. -/
theorem checked?_valid [DecidableEq α]
    {decode : Packed.State payloadWidth → Option (List α)}
    {check : α → α → Bool} {index : Nat}
    {before after : Packed.State payloadWidth}
    {raw : Option (Packed.State payloadWidth)}
    (rawValid : before.layout.Valid before.arena → raw = some after →
      after.layout.Valid after.arena)
    (valid : before.layout.Valid before.arena)
    (ran : checked? decode check index before raw = some after) :
    after.layout.Valid after.arena := by
  obtain ⟨_, _, _, rawResult, _, _⟩ := checked?_result ran
  exact rawValid valid rawResult

/-! ## Alternating design -/

namespace Alternating

open Classical.Alternating

def decode (state : Packed.State payloadWidth) : Option (Arena Nat) :=
  Classical.Alternating.Packed.decode? state.arena state.layout

/-- Executable check that one selected alternating root retains its sign and
permutes its children while the other root remains unchanged. -/
def permutesRoot (side : Side) (before after : Sequent Nat) : Bool :=
  match side, before, after with
  | .left, ⟨.node beforeSign beforeChildren, beforeRight⟩,
      ⟨.node afterSign afterChildren, afterRight⟩ =>
      decide (beforeSign = afterSign) &&
        decide (Classical.Alternating.Children.toList beforeChildren |>.Perm
          (Classical.Alternating.Children.toList afterChildren)) &&
        decide (beforeRight = afterRight)
  | .right, ⟨beforeLeft, .node beforeSign beforeChildren⟩,
      ⟨afterLeft, .node afterSign afterChildren⟩ =>
      decide (beforeSign = afterSign) &&
        decide (Classical.Alternating.Children.toList beforeChildren |>.Perm
          (Classical.Alternating.Children.toList afterChildren)) &&
        decide (beforeLeft = afterLeft)
  | _, _, _ => false

def PermutesRoot (side : Side) (before after : Sequent Nat) : Prop :=
  permutesRoot side before after = true

theorem permutesRoot_eq_true (side : Side) (before after : Sequent Nat) :
    permutesRoot side before after = true ↔ PermutesRoot side before after := by
  rfl

def dedupesRoot (side : Side) (before after : Sequent Nat) : Bool :=
  match side with
  | .left => decide (after.left = before.left.dedupeTop) &&
      decide (after.right = before.right)
  | .right => decide (after.left = before.left) &&
      decide (after.right = before.right.dedupeTop)

/-- Exact abstract effect of deduplicating one root's immediate children. -/
def DedupesRoot (side : Side) (before after : Sequent Nat) : Prop :=
  dedupesRoot side before after = true

theorem dedupesRoot_eq_true (side : Side) (before after : Sequent Nat) :
    dedupesRoot side before after = true ↔ DedupesRoot side before after := by
  rfl

def pushTarget? (pushed : Expr Nat) : Side → Sequent Nat → Option (Sequent Nat)
  | .left, ⟨.node false children, right⟩ =>
      some ⟨Expr.array false
        (Classical.Alternating.Children.toList children ++ [pushed]), right⟩
  | .right, ⟨left, .node false children⟩ =>
      some ⟨left, Expr.array false
        (Classical.Alternating.Children.toList children ++ [pushed])⟩
  | _, _ => none

def pushesRoot (pushed : Expr Nat) (side : Side)
    (before after : Sequent Nat) : Bool :=
  match pushTarget? pushed side before with
  | some expected => decide (after = expected)
  | none => false

/-- Exact directional weakening by one literal.  Positivity is load-bearing:
the selected left root is an AND and the selected right root is an OR. -/
def PushesRoot (pushed : Expr Nat) (side : Side)
    (before after : Sequent Nat) : Prop :=
  pushTarget? pushed side before = some after

theorem pushesRoot_eq_true (pushed : Expr Nat) (side : Side)
    (before after : Sequent Nat) :
    pushesRoot pushed side before after = true ↔
      PushesRoot pushed side before after := by
  unfold pushesRoot PushesRoot
  cases target : pushTarget? pushed side before with
  | none => simp
  | some expected => simp [eq_comm]

/-- Exact alternating crossing target.  Arrays are path-typed, so only a
literal may cross between the root AND and root OR arrays. -/
def crossTarget? : Side → Sequent Nat → Option (Sequent Nat)
  | .left, ⟨.node false left, .node false right⟩ => do
      let (initial, moved) ← splitLast?
        (Classical.Alternating.Children.toList left)
      match moved with
      | .literal literal =>
          some ⟨Expr.array false initial,
            Expr.array false
              (Classical.Alternating.Children.toList right ++
                [Classical.Alternating.Syn.literal literal.neg])⟩
      | .node _ _ => none
  | .right, ⟨.node false left, .node false right⟩ => do
      let (initial, moved) ← splitLast?
        (Classical.Alternating.Children.toList right)
      match moved with
      | .literal literal =>
          some ⟨Expr.array false
              (Classical.Alternating.Children.toList left ++
                [Classical.Alternating.Syn.literal literal.neg]),
            Expr.array false initial⟩
      | .node _ _ => none
  | _, _ => none

def crossesRoot (sourceSide : Side) (before after : Sequent Nat) : Bool :=
  match crossTarget? sourceSide before with
  | some expected => decide (after = expected)
  | none => false

/-- Exact abstract effect of transferring and complementing a literal between
the two alternating root arrays. -/
def CrossesRoot (sourceSide : Side) (before after : Sequent Nat) : Prop :=
  crossTarget? sourceSide before = some after

theorem crossesRoot_eq_true (sourceSide : Side) (before after : Sequent Nat) :
    crossesRoot sourceSide before after = true ↔
      CrossesRoot sourceSide before after := by
  unfold crossesRoot CrossesRoot
  cases target : crossTarget? sourceSide before with
  | none => simp
  | some expected => simp [eq_comm]

private theorem eval_node_perm (assignment : Assignment Nat) (mode : Mode)
    (negative : Bool) {before after : Children Nat}
    (permutation : before.toList.Perm after.toList) :
    Expr.eval assignment mode (.node negative before) =
      Expr.eval assignment mode (.node negative after) := by
  rw [← Expr.node_toList negative before, ← Expr.node_toList negative after]
  exact Expr.eval_array_perm assignment mode negative permutation

theorem PermutesRoot.entailsAt {side : Side} {before after : Sequent Nat}
    (edited : PermutesRoot side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforeLeft beforeRight =>
      cases after with
      | mk afterLeft afterRight =>
        cases beforeLeft with
        | literal value => simp [PermutesRoot, permutesRoot] at edited
        | node beforeSign beforeChildren =>
          cases afterLeft with
          | literal value => simp [PermutesRoot, permutesRoot] at edited
          | node afterSign afterChildren =>
            simp only [PermutesRoot, permutesRoot, Bool.and_eq_true,
              decide_eq_true_eq] at edited
            rcases edited with ⟨⟨sign, permutation⟩, unchanged⟩
            cases sign
            cases unchanged
            intro assignment completes premise
            apply holds assignment completes
            rw [eval_node_perm assignment .all _ permutation]
            exact premise
  · cases before with
    | mk beforeLeft beforeRight =>
      cases after with
      | mk afterLeft afterRight =>
        cases beforeRight with
        | literal value => simp [PermutesRoot, permutesRoot] at edited
        | node beforeSign beforeChildren =>
          cases afterRight with
          | literal value => simp [PermutesRoot, permutesRoot] at edited
          | node afterSign afterChildren =>
            simp only [PermutesRoot, permutesRoot, Bool.and_eq_true,
              decide_eq_true_eq] at edited
            rcases edited with ⟨⟨sign, permutation⟩, unchanged⟩
            cases sign
            cases unchanged
            intro assignment completes premise
            rw [← eval_node_perm assignment .any _ permutation]
            exact holds assignment completes premise

theorem DedupesRoot.entailsAt {side : Side} {before after : Sequent Nat}
    (edited : DedupesRoot side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforeLeft beforeRight =>
      cases after with
      | mk afterLeft afterRight =>
        simp only [DedupesRoot, dedupesRoot, Bool.and_eq_true,
          decide_eq_true_eq] at edited
        rcases edited with ⟨selected, unchanged⟩
        cases selected
        cases unchanged
        intro assignment completes premise
        apply holds assignment completes
        change beforeLeft.dedupeTop.eval assignment .all = true at premise
        simpa using premise
  · cases before with
    | mk beforeLeft beforeRight =>
      cases after with
      | mk afterLeft afterRight =>
        simp only [DedupesRoot, dedupesRoot, Bool.and_eq_true,
          decide_eq_true_eq] at edited
        rcases edited with ⟨selected, unchanged⟩
        cases selected
        cases unchanged
        intro assignment completes premise
        change beforeRight.dedupeTop.eval assignment .any = true
        rw [Expr.eval_dedupeTop]
        exact holds assignment completes premise

theorem PushesRoot.entailsAt {pushed : Expr Nat} {side : Side}
    {before after : Sequent Nat}
    (edited : PushesRoot pushed side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforeLeft beforeRight =>
      cases beforeLeft with
      | literal value => simp [PushesRoot, pushTarget?] at edited
      | node negative children =>
        cases negative
        · have afterEqual :
            after = ⟨Expr.array false
              (Classical.Alternating.Children.toList children ++ [pushed]), beforeRight⟩ :=
            (Option.some.inj (by simpa [PushesRoot, pushTarget?] using edited)).symm
          subst after
          intro assignment completes premise
          apply holds assignment completes
          have parts :
              (Expr.array false (Classical.Alternating.Children.toList children)).eval
                  assignment .all = true ∧
                (Expr.array false [pushed]).eval assignment .all = true := by
            simpa only [Expr.eval_array_append_all, Bool.and_eq_true] using premise
          simpa only [Expr.node_toList] using parts.1
        · simp [PushesRoot, pushTarget?] at edited
  · cases before with
    | mk beforeLeft beforeRight =>
      cases beforeRight with
      | literal value => simp [PushesRoot, pushTarget?] at edited
      | node negative children =>
        cases negative
        · have afterEqual :
            after = ⟨beforeLeft, Expr.array false
              (Classical.Alternating.Children.toList children ++ [pushed])⟩ :=
            (Option.some.inj (by simpa [PushesRoot, pushTarget?] using edited)).symm
          subst after
          intro assignment completes premise
          have source := holds assignment completes premise
          simp only [Expr.eval_array_append_any, Bool.or_eq_true]
          exact Or.inl (by simpa only [Expr.node_toList] using source)
        · simp [PushesRoot, pushTarget?] at edited

theorem CrossesRoot.entailsAt {sourceSide : Side}
    {before after : Sequent Nat}
    (edited : CrossesRoot sourceSide before after)
    (known : PartialAssignment Nat) (holds : before.EntailsAt known) :
    after.EntailsAt known := by
  cases sourceSide with
  | left =>
      cases before with
      | mk beforeLeft beforeRight =>
          cases beforeLeft with
          | literal value => simp [CrossesRoot, crossTarget?] at edited
          | node leftNegative leftChildren =>
              cases leftNegative with
              | true => simp [CrossesRoot, crossTarget?] at edited
              | false =>
                  cases beforeRight with
                  | literal value => simp [CrossesRoot, crossTarget?] at edited
                  | node rightNegative rightChildren =>
                      cases rightNegative with
                      | true => simp [CrossesRoot, crossTarget?] at edited
                      | false =>
                          cases split : splitLast?
                              (Classical.Alternating.Children.toList leftChildren) with
                          | none =>
                              simp [CrossesRoot, crossTarget?, split] at edited
                          | some result =>
                              rcases result with ⟨initial, moved⟩
                              cases moved with
                              | node negative children =>
                                  simp [CrossesRoot, crossTarget?, split] at edited
                              | literal literal =>
                                  have afterEqual :
                                      after = ⟨Expr.array false initial,
                                        Expr.array false
                                          (Classical.Alternating.Children.toList
                                              rightChildren ++
                                            [Classical.Alternating.Syn.literal
                                              literal.neg])⟩ :=
                                    (Option.some.inj (by
                                      simpa [CrossesRoot, crossTarget?, split]
                                        using edited)).symm
                                  subst after
                                  have shape := splitLast?_eq_some split
                                  apply Sequent.crossRight literal
                                  simpa [← Expr.node_toList, shape] using holds
  | right =>
      cases before with
      | mk beforeLeft beforeRight =>
          cases beforeLeft with
          | literal value => simp [CrossesRoot, crossTarget?] at edited
          | node leftNegative leftChildren =>
              cases leftNegative with
              | true => simp [CrossesRoot, crossTarget?] at edited
              | false =>
                  cases beforeRight with
                  | literal value => simp [CrossesRoot, crossTarget?] at edited
                  | node rightNegative rightChildren =>
                      cases rightNegative with
                      | true => simp [CrossesRoot, crossTarget?] at edited
                      | false =>
                          cases split : splitLast?
                              (Classical.Alternating.Children.toList rightChildren) with
                          | none =>
                              simp [CrossesRoot, crossTarget?, split] at edited
                          | some result =>
                              rcases result with ⟨initial, moved⟩
                              cases moved with
                              | node negative children =>
                                  simp [CrossesRoot, crossTarget?, split] at edited
                              | literal literal =>
                                  have afterEqual :
                                      after = ⟨Expr.array false
                                          (Classical.Alternating.Children.toList
                                              leftChildren ++
                                            [Classical.Alternating.Syn.literal
                                              literal.neg]),
                                        Expr.array false initial⟩ :=
                                    (Option.some.inj (by
                                      simpa [CrossesRoot, crossTarget?, split]
                                        using edited)).symm
                                  subst after
                                  have shape := splitLast?_eq_some split
                                  apply Sequent.crossLeft literal.neg
                                  simpa [← Expr.node_toList, shape] using holds

theorem EditedAt.entailsAt {relation : Sequent Nat → Sequent Nat → Prop}
    (preserves : ∀ {before after}, relation before after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : Arena Nat}
    (edited : Operations.EditedAt relation index before after)
    (known : PartialAssignment Nat) (holds : before.EntailsAt known) :
    after.EntailsAt known := by
  exact @Operations.EditedAt.all (Sequent Nat) relation
    (fun sequent ↦ sequent.EntailsAt known)
    (fun {before after} related source ↦
      preserves (before := before) (after := after) related known source)
    index before after edited holds

def reorderRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (candidate : List (Word.Ref payloadWidth)) : Option (Packed.State payloadWidth) :=
  checked? decode (permutesRoot side) index state
    (Raw.reorderRoot? state index side candidate)

def sortRootByKey? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (key : Word.Ref payloadWidth → Nat) : Option (Packed.State payloadWidth) :=
  checked? decode (permutesRoot side) index state
    (Raw.sortRootByKey? state index side key)

def dedupeRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side) :
    Option (Packed.State payloadWidth) :=
  checked? decode (dedupesRoot side) index state
    (Raw.dedupeRoot? state index side)

def literal (reference : Word.Ref payloadWidth) : Expr Nat :=
  .literal ⟨reference.word.base / 4, reference.word.negative⟩

def pushRootLiteral? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (reference : Word.Ref payloadWidth) : Option (Packed.State payloadWidth) :=
  checked? decode (pushesRoot (literal reference) side) index state
    (Raw.pushRootLiteral? state index side reference)

/-- Cross the last literal from `sourceSide` to the opposite root. -/
def crossRoot? (state : Packed.State payloadWidth) (index : Nat)
    (sourceSide : Side) : Option (Packed.State payloadWidth) :=
  checked? decode (crossesRoot sourceSide) index state
    (Raw.crossRoot? state index sourceSide)

theorem checkedEntailsAt
    {check : Sequent Nat → Sequent Nat → Bool}
    {relation : Sequent Nat → Sequent Nat → Prop}
    (reflects : ∀ before after, check before after = true ↔ relation before after)
    (preserves : ∀ {before after}, relation before after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : Packed.State payloadWidth}
    {raw : Option (Packed.State payloadWidth)}
    (rawValid : before.layout.Valid before.arena →
      raw = some after → after.layout.Valid after.arena)
    (ran : checked? decode check index before raw = some after)
    {known : PartialAssignment Nat}
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  obtain ⟨source, sourceRepresents, sourceHolds⟩ := holds
  obtain ⟨decodedSource, target, sourceDecoded, rawResult,
    targetDecoded, checked⟩ := checked?_result ran
  have sourceEqual : source = decodedSource :=
    Option.some.inj (sourceRepresents.2.symm.trans sourceDecoded)
  subst source
  have targetValid := rawValid sourceRepresents.1 rawResult
  refine ⟨target, ⟨targetValid, targetDecoded⟩, ?_⟩
  exact (EditedAt.entailsAt preserves
    ((editAt_eq_true reflects _ _ _).mp checked)) known sourceHolds

theorem reorderRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    {known : PartialAssignment Nat}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (permutesRoot_eq_true side) PermutesRoot.entailsAt
    Raw.reorderRoot?_valid ran holds

theorem sortRootByKey?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    {known : PartialAssignment Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (permutesRoot_eq_true side) PermutesRoot.entailsAt
    Raw.sortRootByKey?_valid ran holds

theorem dedupeRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {known : PartialAssignment Nat}
    (ran : dedupeRoot? before index side = some after)
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (dedupesRoot_eq_true side) DedupesRoot.entailsAt
    Raw.dedupeRoot?_valid ran holds

theorem pushRootLiteral?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    {known : PartialAssignment Nat}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (pushesRoot_eq_true (literal reference) side)
    PushesRoot.entailsAt
    Raw.pushRootLiteral?_valid ran holds

theorem crossRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side} {known : PartialAssignment Nat}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Classical.Mutation.Alternating.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Alternating.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (crossesRoot_eq_true sourceSide)
    CrossesRoot.entailsAt Raw.crossRoot?_valid ran holds

theorem reorderRoot?_syllogistic {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Classical.Mutation.Alternating.Syllogistic before.arena before.layout) :
    Classical.Mutation.Alternating.Syllogistic after.arena after.layout :=
  reorderRoot?_entailsAt ran holds

theorem sortRootByKey?_syllogistic {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Classical.Mutation.Alternating.Syllogistic before.arena before.layout) :
    Classical.Mutation.Alternating.Syllogistic after.arena after.layout :=
  sortRootByKey?_entailsAt ran holds

theorem dedupeRoot?_syllogistic {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side}
    (ran : dedupeRoot? before index side = some after)
    (holds : Classical.Mutation.Alternating.Syllogistic before.arena before.layout) :
    Classical.Mutation.Alternating.Syllogistic after.arena after.layout :=
  dedupeRoot?_entailsAt ran holds

theorem pushRootLiteral?_syllogistic {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : Classical.Mutation.Alternating.Syllogistic before.arena before.layout) :
    Classical.Mutation.Alternating.Syllogistic after.arena after.layout :=
  pushRootLiteral?_entailsAt ran holds

theorem crossRoot?_syllogistic {before after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Classical.Mutation.Alternating.Syllogistic before.arena before.layout) :
    Classical.Mutation.Alternating.Syllogistic after.arena after.layout :=
  crossRoot?_entailsAt ran holds

end Alternating

/-! ## Tagged design -/

namespace Tagged

open Classical.Tagged

def decode (state : Packed.State payloadWidth) :
    Option (List (Sequent Nat)) :=
  Classical.Tagged.Packed.decode? state.arena state.layout

def andChildren? : Formula Nat → Option (List (Formula Nat))
  | .and false children => some children
  | _ => none

def orChildren? : Formula Nat → Option (List (Formula Nat))
  | .or false children => some children
  | _ => none

theorem andChildren?_eq_some {formula : Formula Nat} {children : List (Formula Nat)}
    (found : andChildren? formula = some children) :
    formula = .and false children := by
  cases formula with
  | literal value => cases found
  | and negative actual =>
      cases negative with
      | false =>
          simp only [andChildren?, Option.some.injEq] at found
          subst actual
          rfl
      | true => cases found
  | or negative actual => cases found
  | sat negative actual => cases found

theorem orChildren?_eq_some {formula : Formula Nat} {children : List (Formula Nat)}
    (found : orChildren? formula = some children) :
    formula = .or false children := by
  cases formula with
  | literal value => cases found
  | and negative actual => cases found
  | or negative actual =>
      cases negative with
      | false =>
          simp only [orChildren?, Option.some.injEq] at found
          subst actual
          rfl
      | true => cases found
  | sat negative actual => cases found

/-- Root permutation is checked only at the prover's sequent-normal-form
connectives: positive AND on the left and positive OR on the right. -/
def permutesRoot (side : Side) (before after : Sequent Nat) : Bool :=
  match side, andChildren? before.premise, andChildren? after.premise,
      orChildren? before.conclusion, orChildren? after.conclusion with
  | .left, some beforeChildren, some afterChildren, _, _ =>
      decide (beforeChildren.Perm afterChildren) &&
        decide (before.conclusion = after.conclusion)
  | .right, _, _, some beforeChildren, some afterChildren =>
      decide (beforeChildren.Perm afterChildren) &&
        decide (before.premise = after.premise)
  | _, _, _, _, _ => false

def PermutesRoot (side : Side) (before after : Sequent Nat) : Prop :=
  permutesRoot side before after = true

theorem permutesRoot_eq_true (side : Side) (before after : Sequent Nat) :
    permutesRoot side before after = true ↔ PermutesRoot side before after :=
  Iff.rfl

def dedupeTarget? : Side → Sequent Nat → Option (Sequent Nat)
  | .left, ⟨.and false children, conclusion⟩ =>
      some ⟨.and false children.dedup, conclusion⟩
  | .right, ⟨premise, .or false children⟩ =>
      some ⟨premise, .or false children.dedup⟩
  | _, _ => none

def dedupesRoot (side : Side) (before after : Sequent Nat) : Bool :=
  match dedupeTarget? side before with
  | some expected => decide (after = expected)
  | none => false

def DedupesRoot (side : Side) (before after : Sequent Nat) : Prop :=
  dedupeTarget? side before = some after

theorem dedupesRoot_eq_true (side : Side) (before after : Sequent Nat) :
    dedupesRoot side before after = true ↔ DedupesRoot side before after := by
  unfold dedupesRoot DedupesRoot
  cases target : dedupeTarget? side before with
  | none => simp
  | some expected => simp [eq_comm]

def pushTarget? (pushed : Formula Nat) :
    Side → Sequent Nat → Option (Sequent Nat)
  | .left, ⟨.and false children, conclusion⟩ =>
      some ⟨.and false (children ++ [pushed]), conclusion⟩
  | .right, ⟨premise, .or false children⟩ =>
      some ⟨premise, .or false (children ++ [pushed])⟩
  | _, _ => none

def pushesRoot (pushed : Formula Nat) (side : Side)
    (before after : Sequent Nat) : Bool :=
  match pushTarget? pushed side before with
  | some expected => decide (after = expected)
  | none => false

def PushesRoot (pushed : Formula Nat) (side : Side)
    (before after : Sequent Nat) : Prop :=
  pushTarget? pushed side before = some after

theorem pushesRoot_eq_true (pushed : Formula Nat) (side : Side)
    (before after : Sequent Nat) :
    pushesRoot pushed side before after = true ↔
      PushesRoot pushed side before after := by
  unfold pushesRoot PushesRoot
  cases target : pushTarget? pushed side before with
  | none => simp
  | some expected => simp [eq_comm]

/-- Exact tagged crossing target.  Tags preserve a subtree's connective when
ownership moves between roots, so any formula—not merely a literal—may cross. -/
def crossTarget? (sourceSide : Side) (before : Sequent Nat) :
    Option (Sequent Nat) := do
  let left ← andChildren? before.premise
  let right ← orChildren? before.conclusion
  match sourceSide with
  | .left => do
      let (initial, moved) ← splitLast? left
      some ⟨.and false initial, .or false (right ++ [moved.neg])⟩
  | .right => do
      let (initial, moved) ← splitLast? right
      some ⟨.and false (left ++ [moved.neg]), .or false initial⟩

def crossesRoot (sourceSide : Side) (before after : Sequent Nat) : Bool :=
  match crossTarget? sourceSide before with
  | some expected => decide (after = expected)
  | none => false

/-- Exact abstract effect of transferring and complementing a tagged formula
between the positive AND and OR roots. -/
def CrossesRoot (sourceSide : Side) (before after : Sequent Nat) : Prop :=
  crossTarget? sourceSide before = some after

theorem crossesRoot_eq_true (sourceSide : Side) (before after : Sequent Nat) :
    crossesRoot sourceSide before after = true ↔
      CrossesRoot sourceSide before after := by
  unfold crossesRoot CrossesRoot
  cases target : crossTarget? sourceSide before with
  | none => simp
  | some expected => simp [eq_comm]

theorem PermutesRoot.entailsAt {side : Side} {before after : Sequent Nat}
    (edited : PermutesRoot side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases after with
      | mk afterPremise afterConclusion =>
        cases beforeFound : andChildren? beforePremise with
        | none => simp [PermutesRoot, permutesRoot, beforeFound] at edited
        | some beforeChildren =>
          cases afterFound : andChildren? afterPremise with
          | none =>
              simp [PermutesRoot, permutesRoot, beforeFound, afterFound] at edited
          | some afterChildren =>
              simp only [PermutesRoot, permutesRoot, beforeFound, afterFound,
                Bool.and_eq_true, decide_eq_true_eq] at edited
              rcases edited with ⟨permutation, unchanged⟩
              have beforeEqual := andChildren?_eq_some beforeFound
              have afterEqual := andChildren?_eq_some afterFound
              cases beforeEqual
              cases afterEqual
              cases unchanged
              exact Sequent.EntailsAt.lhsAndPermute known permutation holds
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases after with
      | mk afterPremise afterConclusion =>
        cases beforeFound : orChildren? beforeConclusion with
        | none => simp [PermutesRoot, permutesRoot, beforeFound] at edited
        | some beforeChildren =>
          cases afterFound : orChildren? afterConclusion with
          | none =>
              simp [PermutesRoot, permutesRoot, beforeFound, afterFound] at edited
          | some afterChildren =>
              simp only [PermutesRoot, permutesRoot, beforeFound, afterFound,
                Bool.and_eq_true, decide_eq_true_eq] at edited
              rcases edited with ⟨permutation, unchanged⟩
              have beforeEqual := orChildren?_eq_some beforeFound
              have afterEqual := orChildren?_eq_some afterFound
              cases beforeEqual
              cases afterEqual
              cases unchanged
              exact Sequent.EntailsAt.rhsOrPermute known permutation holds

theorem DedupesRoot.entailsAt {side : Side} {before after : Sequent Nat}
    (edited : DedupesRoot side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases beforePremise with
      | literal value => simp [DedupesRoot, dedupeTarget?] at edited
      | and negative children =>
        cases negative
        · have afterEqual : after = ⟨.and false children.dedup, beforeConclusion⟩ :=
            (Option.some.inj (by
              simpa [DedupesRoot, dedupeTarget?] using edited)).symm
          subst after
          exact Sequent.EntailsAt.lhsAndDedupe known children beforeConclusion holds
        · simp [DedupesRoot, dedupeTarget?] at edited
      | or negative children => simp [DedupesRoot, dedupeTarget?] at edited
      | sat negative children => simp [DedupesRoot, dedupeTarget?] at edited
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases beforeConclusion with
      | literal value => simp [DedupesRoot, dedupeTarget?] at edited
      | and negative children => simp [DedupesRoot, dedupeTarget?] at edited
      | or negative children =>
        cases negative
        · have afterEqual : after = ⟨beforePremise, .or false children.dedup⟩ :=
            (Option.some.inj (by
              simpa [DedupesRoot, dedupeTarget?] using edited)).symm
          subst after
          exact Sequent.EntailsAt.rhsOrDedupe known beforePremise children holds
        · simp [DedupesRoot, dedupeTarget?] at edited
      | sat negative children => simp [DedupesRoot, dedupeTarget?] at edited

theorem PushesRoot.entailsAt {pushed : Formula Nat} {side : Side}
    {before after : Sequent Nat}
    (edited : PushesRoot pushed side before after) (known : PartialAssignment Nat)
    (holds : before.EntailsAt known) : after.EntailsAt known := by
  cases side
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases beforePremise with
      | literal value => simp [PushesRoot, pushTarget?] at edited
      | and negative children =>
        cases negative
        · have afterEqual :
              after = ⟨.and false (children ++ [pushed]), beforeConclusion⟩ :=
            (Option.some.inj (by
              simpa [PushesRoot, pushTarget?] using edited)).symm
          subst after
          exact Sequent.EntailsAt.lhsAndPush known children beforeConclusion pushed holds
        · simp [PushesRoot, pushTarget?] at edited
      | or negative children => simp [PushesRoot, pushTarget?] at edited
      | sat negative children => simp [PushesRoot, pushTarget?] at edited
  · cases before with
    | mk beforePremise beforeConclusion =>
      cases beforeConclusion with
      | literal value => simp [PushesRoot, pushTarget?] at edited
      | and negative children => simp [PushesRoot, pushTarget?] at edited
      | or negative children =>
        cases negative
        · have afterEqual :
              after = ⟨beforePremise, .or false (children ++ [pushed])⟩ :=
            (Option.some.inj (by
              simpa [PushesRoot, pushTarget?] using edited)).symm
          subst after
          exact Sequent.EntailsAt.rhsOrPush known beforePremise pushed children holds
        · simp [PushesRoot, pushTarget?] at edited
      | sat negative children => simp [PushesRoot, pushTarget?] at edited

theorem CrossesRoot.entailsAt {sourceSide : Side}
    {before after : Sequent Nat}
    (edited : CrossesRoot sourceSide before after)
    (known : PartialAssignment Nat) (holds : before.EntailsAt known) :
    after.EntailsAt known := by
  cases leftFound : andChildren? before.premise with
  | none => simp [CrossesRoot, crossTarget?, leftFound] at edited
  | some left =>
      cases rightFound : orChildren? before.conclusion with
      | none =>
          simp [CrossesRoot, crossTarget?, leftFound, rightFound] at edited
      | some right =>
          have premiseEqual := andChildren?_eq_some leftFound
          have conclusionEqual := orChildren?_eq_some rightFound
          have beforeEqual : before = ⟨.and false left, .or false right⟩ := by
            cases before
            simp_all
          cases sourceSide with
          | left =>
              cases split : splitLast? left with
              | none =>
                  simp [CrossesRoot, crossTarget?, leftFound, rightFound, split]
                    at edited
              | some result =>
                  rcases result with ⟨initial, moved⟩
                  have afterEqual :
                      after = ⟨.and false initial,
                        .or false (right ++ [moved.neg])⟩ :=
                    (Option.some.inj (by
                      simpa [CrossesRoot, crossTarget?, leftFound, rightFound, split]
                        using edited)).symm
                  subst after
                  have shape := splitLast?_eq_some split
                  rw [beforeEqual] at holds
                  exact Sequent.EntailsAt.cross known initial right moved
                    (by simpa [Formula.conjunction, Formula.disjunction, shape]
                      using holds)
          | right =>
              cases split : splitLast? right with
              | none =>
                  simp [CrossesRoot, crossTarget?, leftFound, rightFound, split]
                    at edited
              | some result =>
                  rcases result with ⟨initial, moved⟩
                  have afterEqual :
                      after = ⟨.and false (left ++ [moved.neg]),
                        .or false initial⟩ :=
                    (Option.some.inj (by
                      simpa [CrossesRoot, crossTarget?, leftFound, rightFound, split]
                        using edited)).symm
                  subst after
                  have shape := splitLast?_eq_some split
                  rw [beforeEqual] at holds
                  exact Sequent.EntailsAt.crossLeft known left initial moved
                    (by simpa [Formula.conjunction, Formula.disjunction, shape]
                      using holds)

theorem EditedAt.entailsAt {relation : Sequent Nat → Sequent Nat → Prop}
    (preserves : ∀ {before after}, relation before after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : List (Sequent Nat)}
    (edited : Operations.EditedAt relation index before after)
    (known : PartialAssignment Nat) (holds : Classical.Tagged.EntailsAt known before) :
    Classical.Tagged.EntailsAt known after := by
  have sourceEach : ∀ sequent ∈ before, sequent.EntailsAt known := by
    intro sequent member assignment completes
    exact holds assignment completes sequent member
  have targetEach : ∀ sequent ∈ after, sequent.EntailsAt known :=
    @Operations.EditedAt.all (Sequent Nat) relation
      (fun sequent ↦ sequent.EntailsAt known)
      (fun {before after} related source ↦
        preserves (before := before) (after := after) related known source)
      index before after edited sourceEach
  intro assignment completes sequent member
  exact targetEach sequent member assignment completes

def reorderRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (candidate : List (Word.Ref payloadWidth)) : Option (Packed.State payloadWidth) :=
  checked? decode (permutesRoot side) index state
    (Raw.reorderRoot? state index side candidate)

def sortRootByKey? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (key : Word.Ref payloadWidth → Nat) : Option (Packed.State payloadWidth) :=
  checked? decode (permutesRoot side) index state
    (Raw.sortRootByKey? state index side key)

def dedupeRoot? (state : Packed.State payloadWidth) (index : Nat) (side : Side) :
    Option (Packed.State payloadWidth) :=
  checked? decode (dedupesRoot side) index state
    (Raw.dedupeRoot? state index side)

def literal (reference : Word.Ref payloadWidth) : Formula Nat :=
  .literal ⟨reference.word.base / 4, reference.word.negative⟩

def pushRootLiteral? (state : Packed.State payloadWidth) (index : Nat) (side : Side)
    (reference : Word.Ref payloadWidth) : Option (Packed.State payloadWidth) :=
  checked? decode (pushesRoot (literal reference) side) index state
    (Raw.pushRootLiteral? state index side reference)

/-- Cross the last tagged formula from `sourceSide` to the opposite root. -/
def crossRoot? (state : Packed.State payloadWidth) (index : Nat)
    (sourceSide : Side) : Option (Packed.State payloadWidth) :=
  checked? decode (crossesRoot sourceSide) index state
    (Raw.crossRoot? state index sourceSide)

theorem checkedEntailsAt
    {check : Sequent Nat → Sequent Nat → Bool}
    {relation : Sequent Nat → Sequent Nat → Prop}
    (reflects : ∀ before after, check before after = true ↔ relation before after)
    (preserves : ∀ {before after}, relation before after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : Packed.State payloadWidth}
    {raw : Option (Packed.State payloadWidth)}
    (rawValid : before.layout.Valid before.arena →
      raw = some after → after.layout.Valid after.arena)
    (ran : checked? decode check index before raw = some after)
    {known : PartialAssignment Nat}
    (holds : Classical.Mutation.Tagged.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  obtain ⟨source, sourceRepresents, sourceHolds⟩ := holds
  obtain ⟨decodedSource, target, sourceDecoded, rawResult,
    targetDecoded, checked⟩ := checked?_result ran
  have sourceEqual : source = decodedSource :=
    Option.some.inj (sourceRepresents.2.symm.trans sourceDecoded)
  subst source
  have targetValid := rawValid sourceRepresents.1 rawResult
  refine ⟨target, ⟨targetValid, targetDecoded⟩, ?_⟩
  exact (EditedAt.entailsAt preserves
    ((editAt_eq_true reflects _ _ _).mp checked)) known sourceHolds

theorem reorderRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    {known : PartialAssignment Nat}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Classical.Mutation.Tagged.EntailsAt known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (permutesRoot_eq_true side) PermutesRoot.entailsAt
    Raw.reorderRoot?_valid ran holds

theorem sortRootByKey?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    {known : PartialAssignment Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Classical.Mutation.Tagged.EntailsAt known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (permutesRoot_eq_true side) PermutesRoot.entailsAt
    Raw.sortRootByKey?_valid ran holds

theorem dedupeRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {known : PartialAssignment Nat}
    (ran : dedupeRoot? before index side = some after)
    (holds : Classical.Mutation.Tagged.EntailsAt known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (dedupesRoot_eq_true side) DedupesRoot.entailsAt
    Raw.dedupeRoot?_valid ran holds

theorem pushRootLiteral?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    {known : PartialAssignment Nat}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : Classical.Mutation.Tagged.EntailsAt known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (pushesRoot_eq_true (literal reference) side)
    PushesRoot.entailsAt Raw.pushRootLiteral?_valid ran holds

theorem crossRoot?_entailsAt {before after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side} {known : PartialAssignment Nat}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Classical.Mutation.Tagged.EntailsAt
      known before.arena before.layout) :
    Classical.Mutation.Tagged.EntailsAt known after.arena after.layout := by
  apply checkedEntailsAt (crossesRoot_eq_true sourceSide)
    CrossesRoot.entailsAt Raw.crossRoot?_valid ran holds

theorem reorderRoot?_syllogism {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {candidate : List (Word.Ref payloadWidth)}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Classical.Mutation.Tagged.Syllogism before.arena before.layout) :
    Classical.Mutation.Tagged.Syllogism after.arena after.layout :=
  reorderRoot?_entailsAt ran holds

theorem sortRootByKey?_syllogism {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {key : Word.Ref payloadWidth → Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Classical.Mutation.Tagged.Syllogism before.arena before.layout) :
    Classical.Mutation.Tagged.Syllogism after.arena after.layout :=
  sortRootByKey?_entailsAt ran holds

theorem dedupeRoot?_syllogism {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side}
    (ran : dedupeRoot? before index side = some after)
    (holds : Classical.Mutation.Tagged.Syllogism before.arena before.layout) :
    Classical.Mutation.Tagged.Syllogism after.arena after.layout :=
  dedupeRoot?_entailsAt ran holds

theorem pushRootLiteral?_syllogism {before after : Packed.State payloadWidth}
    {index : Nat} {side : Side} {reference : Word.Ref payloadWidth}
    (ran : pushRootLiteral? before index side reference = some after)
    (holds : Classical.Mutation.Tagged.Syllogism before.arena before.layout) :
    Classical.Mutation.Tagged.Syllogism after.arena after.layout :=
  pushRootLiteral?_entailsAt ran holds

theorem crossRoot?_syllogism {before after : Packed.State payloadWidth}
    {index : Nat} {sourceSide : Side}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Classical.Mutation.Tagged.Syllogism before.arena before.layout) :
    Classical.Mutation.Tagged.Syllogism after.arena after.layout :=
  crossRoot?_entailsAt ran holds

end Tagged

end Nucleus.Classical.Mutation.Operations
