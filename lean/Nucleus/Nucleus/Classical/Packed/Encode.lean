import Nucleus.Classical.Alternating.Equality
import Nucleus.Classical.Alternating.Packed
import Nucleus.Classical.Tagged.Equality
import Nucleus.Classical.Tagged.Packed

/-!
# Deterministic checked packers for the classical designs

This module attempts to build one fresh, densely laid-out arena from abstract
syntax, starting live storage at address four.  Every array receives the first
power-of-two size class with room for its children and terminator; blocks are
listed in preorder.  Literal and pointer construction use the fixed-width word
constructors, so an atom or address that does not fit makes encoding fail
explicitly.

The packer is outside the trusted surface.  Before returning a state it runs
the ordinary strict decoder and checks allocator validity.  The success
theorems expose exactly those checked facts.  They do not yet prove that the
builder succeeds under a closed-form width bound, nor that this layout is a
wire-level normal form.  No wire format or hash assumption is involved.
-/

namespace Nucleus.Classical.Packed.Encode

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-! ## An intrinsic generic tree and deterministic builder -/

private inductive Ix where
  | expr
  | children

/-- Internal syntax shared by the tagged and alternating encoders. -/
private inductive Syn : Ix → Type where
  | literal (atom : Nat) (negative : Bool) : Syn .expr
  | node (tag : Nat) (negative : Bool) (children : Syn .children) : Syn .expr
  | nil : Syn .children
  | cons (head : Syn .expr) (tail : Syn .children) : Syn .children

private abbrev Expr := Syn .expr
private abbrev Children := Syn .children

private def childrenLength : Children → Nat
  | .nil => 0
  | .cons _ tail => childrenLength tail + 1

/-- The first size class whose block has room for every reference and the
mandatory terminator.  Class `n` is always reached within `needed + 1`
checks, so the bounded fallback is unreachable. -/
private def leastSizeClass (needed : Nat) : Nat :=
  let rec search : Nat → Nat → Nat
    | 0, candidate => candidate
    | fuel + 1, candidate =>
        if needed < 4 * 2 ^ candidate then candidate
        else search fuel (candidate + 1)
  search (needed + 1) 0

mutual
private def ofTagged : Tagged.Formula Nat → Expr
  | .literal value => .literal value.atom value.negative
  | .and negative children => .node 0 negative (ofTaggedList children)
  | .or negative children => .node 1 negative (ofTaggedList children)
  | .sat negative children => .node 2 negative (ofTaggedList children)

private def ofTaggedList : List (Tagged.Formula Nat) → Children
  | [] => .nil
  | head :: tail => .cons (ofTagged head) (ofTaggedList tail)
end

mutual
private def ofAlternating : Alternating.Expr Nat → Expr
  | .literal value => .literal value.atom value.negative
  | .node negative children => .node 0 negative (ofAlternatingChildren children)

private def ofAlternatingChildren : Alternating.Children Nat → Children
  | .nil => .nil
  | .cons head tail => .cons (ofAlternating head) (ofAlternatingChildren tail)
end

/-- The concrete storage generated for one expression. -/
private structure Chunk (payloadWidth : Nat) where
  reference : Word.Ref payloadWidth
  words : List (Word payloadWidth)
  live : List Block

/-- The concrete storage generated for a proper list of children. -/
private structure Forest (payloadWidth : Nat) where
  references : List (Word.Ref payloadWidth)
  words : List (Word payloadWidth)
  live : List Block

private def asRef? (word : Word payloadWidth) : Option (Word.Ref payloadWidth) :=
  if reference : word.IsRef then some ⟨word, reference⟩ else none

mutual
/-- Build one expression at the next aligned storage address. -/
private def buildExpr? (payloadWidth base : Nat) : Expr → Option (Chunk payloadWidth)
  | .literal atom negative => do
      let word ← Word.literal? payloadWidth atom negative
      let reference ← asRef? word
      some ⟨reference, [], []⟩
  | .node tag negative children => do
      let block : Block := ⟨base, leastSizeClass (childrenLength children)⟩
      let forest ← buildChildren? payloadWidth block.stop children
      let encoded ← encodeWords payloadWidth block.capacity forest.references
      let word ← Word.pointer? payloadWidth block.base tag negative
      let reference ← asRef? word
      some ⟨reference, encoded ++ forest.words, block :: forest.live⟩

/-- Build children consecutively after their owner's block. -/
private def buildChildren? (payloadWidth base : Nat) :
    Children → Option (Forest payloadWidth)
  | .nil => some ⟨[], [], []⟩
  | .cons head tail => do
      let builtHead ← buildExpr? payloadWidth base head
      let builtTail ← buildChildren? payloadWidth
        (base + builtHead.words.length) tail
      some ⟨builtHead.reference :: builtTail.references,
        builtHead.words ++ builtTail.words, builtHead.live ++ builtTail.live⟩
end

/-- Generic sequent roots used while constructing either public design. -/
private structure Root where
  left : Expr
  right : Expr

private structure RootChunk (payloadWidth : Nat) where
  roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)
  words : List (Word payloadWidth)
  live : List Block

private def buildRoots? (payloadWidth : Nat) : Nat → List Root →
    Option (RootChunk payloadWidth)
  | _, [] => some ⟨[], [], []⟩
  | base, root :: roots => do
      let left ← buildExpr? payloadWidth base root.left
      let right ← buildExpr? payloadWidth (base + left.words.length) root.right
      let rest ← buildRoots? payloadWidth
        (base + left.words.length + right.words.length) roots
      some ⟨(left.reference, right.reference) :: rest.roots,
        left.words ++ right.words ++ rest.words,
        left.live ++ right.live ++ rest.live⟩

private def candidate? (payloadWidth : Nat) (roots : List Root) :
    Option (State payloadWidth) := do
  let built ← buildRoots? payloadWidth 4 roots
  let header := List.replicate 4 (Word.zero payloadWidth)
  some {
    arena := {
      memory := { words := (header ++ built.words).toArray, free := [] }
      roots := built.roots }
    layout := { live := built.live } }

/-! ## Executable allocator validation -/

private def allFitDec (blocks : List Block) (size : Nat) :
    Decidable (Layout.AllFit blocks size) := by
  induction blocks with
  | nil => exact isTrue (by simp [Layout.AllFit])
  | cons block blocks ih =>
      exact if fit : block.Fits size then
        match ih with
        | isTrue rest => isTrue (by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact fit
            · exact rest candidate member)
        | isFalse rest => isFalse fun all ↦ rest (by
            intro candidate member
            exact all candidate (List.mem_cons_of_mem block member))
      else isFalse fun all ↦ fit (all block (by simp))

private def freeZeroedDec (memory : Memory payloadWidth) :
    Decidable (Layout.FreeZeroed memory) := by
  unfold Layout.FreeZeroed
  induction memory.free with
  | nil => exact isTrue (by simp)
  | cons block blocks ih =>
      exact if zeroed : memory.read block = some [] then
        match ih with
        | isTrue rest => isTrue (by
            intro candidate member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact zeroed
            · exact rest candidate member)
        | isFalse rest => isFalse fun all ↦ rest (by
            intro candidate member
            exact all candidate (List.mem_cons_of_mem block member))
      else isFalse fun all ↦ zeroed (all block (by simp))

private def layoutValidDec (arena : Arena payloadWidth) (layout : Layout) :
    Decidable (layout.Valid arena) :=
  if addressable : arena.memory.words.size ≤ 2 ^ payloadWidth then
    match allFitDec (layout.live ++ arena.memory.free) arena.memory.words.size with
    | isFalse notFit => isFalse fun valid ↦ notFit valid.allFit
    | isTrue fit =>
        if disjoint : (layout.live ++ arena.memory.free).Pairwise Block.Disjoint then
          match freeZeroedDec arena.memory with
          | isTrue zeroed => isTrue ⟨fit, disjoint, zeroed, addressable⟩
          | isFalse notZeroed => isFalse fun valid ↦ notZeroed valid.freeZeroed
        else isFalse fun valid ↦ disjoint valid.disjoint
  else isFalse fun valid ↦ addressable valid.addressable

/-! ## Public design-specific encoders -/

private def taggedRoots (sequents : List (Tagged.Sequent Nat)) : List Root :=
  sequents.map fun sequent ↦ ⟨ofTagged sequent.premise, ofTagged sequent.conclusion⟩

private def alternatingRoots (sequents : Alternating.Arena Nat) : List Root :=
  sequents.map fun sequent ↦ ⟨ofAlternating sequent.left, ofAlternating sequent.right⟩

/-- Pack tagged syntax, rejecting fixed-width overflow or any
candidate rejected by the ordinary allocator and syntax checks. -/
def tagged? (payloadWidth : Nat) (sequents : List (Tagged.Sequent Nat)) :
    Option (State payloadWidth) := do
  let state ← candidate? payloadWidth (taggedRoots sequents)
  letI := layoutValidDec state.arena state.layout
  if _valid : state.layout.Valid state.arena then
    if Tagged.Packed.decode? state.arena state.layout = some sequents then
      some state
    else none
  else none

/-- Success of the tagged encoder supplies the complete representation
relation checked by the normal decoder. -/
theorem tagged?_represents {sequents : List (Tagged.Sequent Nat)}
    {state : State payloadWidth}
    (encoded : tagged? payloadWidth sequents = some state) :
    Tagged.Packed.Represents state.arena state.layout sequents := by
  unfold tagged? at encoded
  cases candidate : candidate? payloadWidth (taggedRoots sequents) with
  | none => simp [candidate] at encoded
  | some proposed =>
      rw [candidate] at encoded
      letI := layoutValidDec proposed.arena proposed.layout
      change (if _valid : proposed.layout.Valid proposed.arena then
          if Tagged.Packed.decode? proposed.arena proposed.layout = some sequents then
            some proposed else none
        else none) = some state at encoded
      split at encoded
      · rename_i valid
        split at encoded
        · rename_i decoded
          have equal := Option.some.inj encoded
          subst state
          exact ⟨valid, decoded⟩
        · contradiction
      · contradiction

/-- In particular, successful tagged encoding decodes to exactly its abstract
input. -/
theorem tagged?_decode {sequents : List (Tagged.Sequent Nat)}
    {state : State payloadWidth}
    (encoded : tagged? payloadWidth sequents = some state) :
    Tagged.Packed.decode? state.arena state.layout = some sequents :=
  (tagged?_represents encoded).2

/-- Successful output fits wholly within its fixed-width address space. -/
theorem tagged?_addressable {sequents : List (Tagged.Sequent Nat)}
    {state : State payloadWidth}
    (encoded : tagged? payloadWidth sequents = some state) :
    state.arena.memory.words.size ≤ 2 ^ payloadWidth :=
  (tagged?_represents encoded).1.addressable

/-- Canonically pack untagged alternating syntax.  All array pointers use tag
zero; their AND/OR meaning remains path-derived in the ordinary decoder. -/
def alternating? (payloadWidth : Nat) (sequents : Alternating.Arena Nat) :
    Option (State payloadWidth) := do
  let state ← candidate? payloadWidth (alternatingRoots sequents)
  letI := layoutValidDec state.arena state.layout
  if _valid : state.layout.Valid state.arena then
    if Alternating.Packed.decode? state.arena state.layout = some sequents then
      some state
    else none
  else none

/-- Success of the alternating encoder supplies the complete representation
relation checked by the normal decoder. -/
theorem alternating?_represents {sequents : Alternating.Arena Nat}
    {state : State payloadWidth}
    (encoded : alternating? payloadWidth sequents = some state) :
    Alternating.Packed.Represents state.arena state.layout sequents := by
  unfold alternating? at encoded
  cases candidate : candidate? payloadWidth (alternatingRoots sequents) with
  | none => simp [candidate] at encoded
  | some proposed =>
      rw [candidate] at encoded
      letI := layoutValidDec proposed.arena proposed.layout
      change (if _valid : proposed.layout.Valid proposed.arena then
          if Alternating.Packed.decode? proposed.arena proposed.layout = some sequents then
            some proposed else none
        else none) = some state at encoded
      split at encoded
      · rename_i valid
        split at encoded
        · rename_i decoded
          have equal := Option.some.inj encoded
          subst state
          exact ⟨valid, decoded⟩
        · contradiction
      · contradiction

/-- In particular, successful alternating encoding decodes to exactly its
abstract input. -/
theorem alternating?_decode {sequents : Alternating.Arena Nat}
    {state : State payloadWidth}
    (encoded : alternating? payloadWidth sequents = some state) :
    Alternating.Packed.decode? state.arena state.layout = some sequents :=
  (alternating?_represents encoded).2

/-- Successful output fits wholly within its fixed-width address space. -/
theorem alternating?_addressable {sequents : Alternating.Arena Nat}
    {state : State payloadWidth}
    (encoded : alternating? payloadWidth sequents = some state) :
    state.arena.memory.words.size ≤ 2 ^ payloadWidth :=
  (alternating?_represents encoded).1.addressable

end Nucleus.Classical.Packed.Encode
