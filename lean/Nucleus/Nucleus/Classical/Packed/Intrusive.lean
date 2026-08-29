import Nucleus.Classical.Packed.Layout

/-!
# Intrusive size-class free rings

This is a candidate runtime allocator representation, distinct from the
external free-block list used by `Packed.Memory` as a simpler specification.
The arena stores one word, `freeRoot`.  Zero means that no block is free;
otherwise it points to a node in the largest nonempty size-class ring.

Every free block begins with four words:

1. canonical zero, marking the block free;
2. an aligned pointer to the next node in its circular ring;
3. an aligned pointer to the previous node;
4. the block's size class.

Ordinary nodes have canonical-zero spare words.  The distinguished root uses
its spare words as a directory: entry `k` is zero or points to a representative
of size-class ring `k`, for every `k < root.sizeClass`; the remaining spare
words are zero.  The root itself represents its own size class.

The executable decoder follows every ring and checks bounds, backlinks,
classes, padding, address width, and pairwise block disjointness.  It does not
interpret proposition words or commit this representation to a wire format.
-/

namespace Nucleus.Classical.Packed.Intrusive

open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- A packed arena whose allocator state is one intrusive root word. -/
structure Arena (payloadWidth : Nat) where
  words : Array (Word payloadWidth)
  freeRoot : Word payloadWidth
  roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)
  deriving DecidableEq, Repr

/-- A decoded intrusive free-node header. -/
structure Header where
  block : Block
  next : Nat
  prev : Nat
  deriving DecidableEq, Repr

namespace Arena

/-- Read one word at an absolute memory index. -/
def word? (arena : Arena payloadWidth) (index : Nat) : Option (Word payloadWidth) :=
  arena.words[index]?

/-- Decode one non-null, unsigned, aligned block pointer. -/
def pointer? (word : Word payloadWidth) : Option Nat :=
  if word.negative then none
  else if word.payload.val = 0 then none
  else if word.tag = 0 then some word.base
  else none

/-- Decode zero as null and a block pointer as non-null.  The outer option
distinguishes malformed words from the null pointer. -/
def optionalPointer? (word : Word payloadWidth) : Option (Option Nat) :=
  if _zero : word.CanonicalZero then some none
  else some <$> pointer? word

/-- Decode an unsigned metadata word. -/
def natural? (word : Word payloadWidth) : Option Nat :=
  if word.negative then none else some word.payload.val

/-- Read and validate the four-word header at `base`. -/
def header? (arena : Arena payloadWidth) (base : Nat) : Option Header := do
  let marker ← arena.word? base
  if _ : marker.CanonicalZero then pure () else none
  let nextWord ← arena.word? (base + 1)
  let next ← pointer? nextWord
  let prevWord ← arena.word? (base + 2)
  let prev ← pointer? prevWord
  let classWord ← arena.word? (base + 3)
  let sizeClass ← natural? classWord
  -- This bound is implied by an addressable block capacity, and checking it
  -- before exponentiation keeps hostile metadata cheap to reject.
  if sizeClass + 2 ≤ payloadWidth then
    let block : Block := ⟨base, sizeClass⟩
    if block.Fits arena.words.size then
      some ⟨block, next, prev⟩
    else
      none
  else
    none

/-- Check that a complete memory range consists of canonical zeroes. -/
def zeroRange (arena : Arena payloadWidth) (start count : Nat) : Bool :=
  let words := (arena.words.toList.drop start).take count
  words.length = count && words.all fun word ↦ decide word.CanonicalZero

/-- A non-root free node carries no directory data. -/
def ordinaryNode? (arena : Arena payloadWidth) (header : Header) : Option Unit :=
  if arena.zeroRange (header.block.base + 4) (header.block.capacity - 4) then
    some ()
  else
    none

/-- Follow one circular doubly linked size-class ring.  `special` is the one
root node whose spare words contain the size-class directory. -/
def walkRing? (arena : Arena payloadWidth) (head expectedClass : Nat)
    (special : Option Nat) : Option (List Block) :=
  let rec walk : Nat → Nat → List Block → Option (List Block)
    | 0, _, _ => none
    | fuel + 1, current, visited => do
        if visited.any fun block ↦ block.base = current then none else pure ()
        let header ← arena.header? current
        if header.block.sizeClass = expectedClass then pure () else none
        if special = some current then pure () else arena.ordinaryNode? header
        let nextHeader ← arena.header? header.next
        if nextHeader.prev = current then pure () else none
        if header.next = head then
          some (header.block :: visited).reverse
        else
          walk fuel header.next (header.block :: visited)
  walk (arena.words.size + 1) head []

/-- Decode a directory pointer word for one smaller size class. -/
def directoryHead? (arena : Arena payloadWidth) (root : Header)
    (sizeClass : Nat) : Option (Option Nat) := do
  let word ← arena.word? (root.block.base + 4 + sizeClass)
  optionalPointer? word

/-- Decode every smaller-class ring named by the root directory. -/
def smallerRings? (arena : Arena payloadWidth) (root : Header) :
    Option (List Block) :=
  (List.range root.block.sizeClass).foldlM (init := []) fun blocks sizeClass ↦ do
    let head ← arena.directoryHead? root sizeClass
    match head with
    | none => some blocks
    | some base => do
        let ring ← arena.walkRing? base sizeClass none
        some (blocks ++ ring)

/-- Check unused words after the root's smaller-class directory. -/
def rootPadding? (arena : Arena payloadWidth) (root : Header) : Option Unit :=
  let spare := root.block.capacity - 4
  if root.block.sizeClass ≤ spare then
    if arena.zeroRange (root.block.base + 4 + root.block.sizeClass)
        (spare - root.block.sizeClass) then
      some ()
    else
      none
  else
    none

/-- Decode all intrusive free rings.  The result is ordered by increasing
smaller size class, followed by the largest-class root ring. -/
def decodeFree? (arena : Arena payloadWidth) : Option (List Block) := do
  if arena.words.size ≤ 2 ^ payloadWidth then pure () else none
  let root ← optionalPointer? arena.freeRoot
  match root with
  | none => some []
  | some rootBase => do
      let rootHeader ← arena.header? rootBase
      arena.rootPadding? rootHeader
      let smaller ← arena.smallerRings? rootHeader
      let largest ← arena.walkRing? rootBase rootHeader.block.sizeClass (some rootBase)
      let blocks := smaller ++ largest
      if blocks.Pairwise Block.Disjoint then some blocks else none

end Arena

/-- Exact interpretation of an intrusive free-list arena. -/
def RepresentsFree (arena : Arena payloadWidth) (blocks : List Block) : Prop :=
  arena.decodeFree? = some blocks

namespace RepresentsFree

theorem functional {arena : Arena payloadWidth} {left right : List Block}
    (leftRepresents : RepresentsFree arena left)
    (rightRepresents : RepresentsFree arena right) : left = right := by
  exact Option.some.inj (leftRepresents.symm.trans rightRepresents)

end RepresentsFree

theorem Arena.decodeFree?_addressable {arena : Arena payloadWidth}
    {blocks : List Block} (decoded : arena.decodeFree? = some blocks) :
    arena.words.size ≤ 2 ^ payloadWidth := by
  unfold Arena.decodeFree? at decoded
  split at decoded
  · assumption
  · contradiction

/-- Relate the intrusive runtime candidate to the existing external-list
allocator specification.  Free-node headers replace zero padding in the
runtime words, so equality is required only outside decoded free blocks. -/
def Corresponds (intrusive : Arena payloadWidth)
    (external : Classical.Packed.Arena payloadWidth) : Prop :=
  ∃ freeBlocks,
    RepresentsFree intrusive freeBlocks ∧
    intrusive.roots = external.roots ∧
    intrusive.words.size = external.memory.words.size ∧
    freeBlocks.Perm external.memory.free ∧
    (∀ block ∈ freeBlocks, external.memory.read block = some []) ∧
    ∀ index,
      (∀ block ∈ freeBlocks, ¬block.Contains index) →
      intrusive.words[index]? = external.memory.words[index]?

namespace Examples

private def word8 (value : Nat) (bound : value < 2 ^ 8 := by decide) : Word 8 :=
  ⟨false, ⟨value, bound⟩⟩

private def zero8 : Word 8 := Word.zero 8
private def pointer4 : Word 8 := word8 4
private def pointer12 : Word 8 := word8 12
private def class1 : Word 8 := word8 1

private def block4 : Block := ⟨4, 1⟩
private def block12 : Block := ⟨12, 0⟩

/-- A class-one root ring whose directory points to one class-zero ring. -/
private def twoClassArena : Arena 8 where
  words := #[
    zero8, zero8, zero8, zero8,
    zero8, pointer4, pointer4, class1,
    pointer12, zero8, zero8, zero8,
    zero8, pointer12, pointer12, zero8]
  freeRoot := pointer4
  roots := []

example : twoClassArena.decodeFree? = some [block12, block4] := by
  decide

example : twoClassArena.words.size ≤ 2 ^ 8 :=
  Arena.decodeFree?_addressable (blocks := [block12, block4]) (by decide)

end Examples

end Nucleus.Classical.Packed.Intrusive
