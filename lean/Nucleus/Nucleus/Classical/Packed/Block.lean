import Nucleus.Classical.Packed.Word
import Mathlib.Data.List.Perm.Basic

/-!
# Zero-terminated blocks and a reusable free list

This is the common concrete storage substrate for the packed classical
designs.  Proposition arrays occupy aligned power-of-two blocks in one flat
word array.  The first canonical zero terminates the live children; remaining
capacity is canonical-zero padding.  Free blocks are carried explicitly and
contain only canonical zeroes.

The logical layout witness used by each decoder records allocated blocks.
That witness is not serialized state: the executable state is the word array,
the free list, and the sequent roots.
-/

namespace Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/-- A size-class block. Its capacity is `4 * 2^sizeClass` words. -/
structure Block where
  base : Nat
  sizeClass : Nat
  deriving DecidableEq, Repr

namespace Block

def capacity (block : Block) : Nat :=
  4 * 2 ^ block.sizeClass

def stop (block : Block) : Nat :=
  block.base + block.capacity

def Aligned (block : Block) : Prop :=
  block.base ≥ 4 ∧ block.base % 4 = 0

instance (block : Block) : Decidable block.Aligned :=
  inferInstanceAs (Decidable (block.base ≥ 4 ∧ block.base % 4 = 0))

def Fits (block : Block) (size : Nat) : Prop :=
  block.Aligned ∧ block.stop ≤ size

instance (block : Block) (size : Nat) : Decidable (block.Fits size) :=
  inferInstanceAs (Decidable (block.Aligned ∧ block.stop ≤ size))

def Contains (block : Block) (address : Nat) : Prop :=
  block.base ≤ address ∧ address < block.stop

def Disjoint (left right : Block) : Prop :=
  left.stop ≤ right.base ∨ right.stop ≤ left.base

instance (left right : Block) : Decidable (left.Disjoint right) :=
  inferInstanceAs (Decidable (left.stop ≤ right.base ∨ right.stop ≤ left.base))

theorem capacity_pos (block : Block) : 0 < block.capacity := by
  exact Nat.mul_pos (by decide) (Nat.two_pow_pos block.sizeClass)

theorem four_le_capacity (block : Block) : 4 ≤ block.capacity := by
  rw [show (4 : Nat) = 4 * 1 by omega, capacity]
  exact Nat.mul_le_mul_left 4
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos block.sizeClass)))

theorem capacity_mod_four (block : Block) : block.capacity % 4 = 0 := by
  simp [capacity]

theorem base_lt_stop (block : Block) : block.base < block.stop := by
  simp [stop, capacity_pos]

theorem Disjoint.symm {left right : Block} (disjoint : left.Disjoint right) :
    right.Disjoint left := by
  rcases disjoint with disjoint | disjoint
  · exact Or.inr disjoint
  · exact Or.inl disjoint

theorem not_contains_of_disjoint {left right : Block} (disjoint : left.Disjoint right)
    {address : Nat} (contained : left.Contains address) : ¬right.Contains address := by
  intro other
  simp only [Contains] at contained other
  simp only [Disjoint] at disjoint
  rcases disjoint with disjoint | disjoint <;> omega

end Block

/-- Decode a zero-terminated block only when every live word is a reference
and every word after the terminator is canonical-zero padding. -/
def decodeWords {payloadWidth : Nat} :
    List (Word payloadWidth) → Option (List (Word.Ref payloadWidth))
  | [] => none
  | word :: words =>
      if _ : word.CanonicalZero then
        if words.all fun tail ↦ decide tail.CanonicalZero then some [] else none
      else if reference : word.IsRef then
        (Word.Ref.mk word reference :: ·) <$> decodeWords words
      else none

/-- The canonical contents of a block: live references, one terminator, then
zero padding through the complete capacity. -/
def encodeWords (payloadWidth capacity : Nat) (references : List (Word.Ref payloadWidth)) :
    Option (List (Word payloadWidth)) :=
  if references.length < capacity then
    some (references.map Word.Ref.word ++
      List.replicate (capacity - references.length) (Word.zero payloadWidth))
  else none

theorem encodeWords_length {payloadWidth capacity : Nat}
    {references : List (Word.Ref payloadWidth)} {words : List (Word payloadWidth)}
    (encoded : encodeWords payloadWidth capacity references = some words) :
    words.length = capacity := by
  unfold encodeWords at encoded
  split at encoded
  · simp only [Option.some.injEq] at encoded
    subst words
    simp
    omega
  · contradiction

private theorem all_zero_replicate (payloadWidth count : Nat) :
    (List.replicate count (Word.zero payloadWidth)).all
      (fun word ↦ decide word.CanonicalZero) = true := by
  simp [Word.CanonicalZero, Word.zero]

private theorem ref_not_zero (reference : Word.Ref payloadWidth) :
    ¬reference.word.CanonicalZero := by
  intro zero
  have payloadZero := congrArg (fun word : Word payloadWidth ↦ word.payload.val) zero
  exact reference.isRef (by simpa [Word.CanonicalZero] using payloadZero)

private theorem decodeWords_refs_padding (references : List (Word.Ref payloadWidth))
    (padding : Nat) (positive : 0 < padding) :
    decodeWords (references.map Word.Ref.word ++
      List.replicate padding (Word.zero payloadWidth)) = some references := by
  induction references with
  | nil =>
      cases padding with
      | zero => omega
      | succ padding =>
          simp [List.replicate_succ, decodeWords, Word.CanonicalZero, Word.zero]
  | cons reference references ih =>
      simp only [List.map_cons, List.cons_append, decodeWords]
      rw [dif_neg (ref_not_zero reference)]
      rw [dif_pos reference.isRef]
      rw [ih]
      cases reference
      rfl

theorem decodeWords_encodeWords {payloadWidth capacity : Nat}
    (references : List (Word.Ref payloadWidth)) (room : references.length < capacity) :
    decodeWords (references.map Word.Ref.word ++
      List.replicate (capacity - references.length) (Word.zero payloadWidth)) =
      some references := by
  exact decodeWords_refs_padding references (capacity - references.length)
    (Nat.sub_pos_of_lt room)

theorem decodeWords_of_encodeWords {payloadWidth capacity : Nat}
    {references : List (Word.Ref payloadWidth)} {words : List (Word payloadWidth)}
    (encoded : encodeWords payloadWidth capacity references = some words) :
    decodeWords words = some references := by
  unfold encodeWords at encoded
  split at encoded
  · rename_i room
    simp only [Option.some.injEq] at encoded
    subst words
    exact decodeWords_encodeWords references room
  · contradiction

/-- Replace exactly `count` array entries beginning at `start`. -/
def replaceRange (words replacement : Array α) (start count : Nat) : Array α :=
  (words.toList.take start ++ replacement.toList ++ words.toList.drop (start + count)).toArray

theorem replaceRange_slice {words replacement : Array α} {start count : Nat}
    (startBound : start ≤ words.size) (replacementSize : replacement.size = count) :
    (((replaceRange words replacement start count).toList.drop start).take count) =
      replacement.toList := by
  unfold replaceRange
  have prefixLength : (words.toList.take start).length = start := by
    simp [startBound]
  rw [← prefixLength, List.drop_append]
  simp [replacementSize]

/-- Replacing an in-bounds range with an equally sized array preserves the
size of the flat word array. -/
theorem replaceRange_size {words replacement : Array α} {start count : Nat}
    (startBound : start ≤ words.size) (endBound : start + count ≤ words.size)
    (replacementSize : replacement.size = count) :
    (replaceRange words replacement start count).size = words.size := by
  unfold replaceRange
  simp
  omega

private theorem replaceRange_slice_before {words replacement : Array α}
    {start count otherStart otherCount : Nat}
    (startBound : start ≤ words.size) (before : otherStart + otherCount ≤ start) :
    (((replaceRange words replacement start count).toList.drop otherStart).take otherCount) =
      ((words.toList.drop otherStart).take otherCount) := by
  unfold replaceRange
  simp only
  rw [List.append_assoc]
  rw [List.take_drop, List.take_drop]
  rw [List.take_append_of_le_length]
  · rw [List.take_take, min_eq_left before]
  · simpa [startBound] using before

private theorem replaceRange_slice_after {words replacement : Array α}
    {start count otherStart otherCount : Nat}
    (startBound : start ≤ words.size) (replacementSize : replacement.size = count)
    (after : start + count ≤ otherStart) :
    (((replaceRange words replacement start count).toList.drop otherStart).take otherCount) =
      ((words.toList.drop otherStart).take otherCount) := by
  unfold replaceRange
  simp only
  rw [List.append_assoc]
  rw [List.drop_append]
  have prefixLength : (words.toList.take start).length = start := by
    simp [startBound]
  rw [prefixLength]
  have startLe : start ≤ otherStart := by omega
  rw [List.drop_eq_nil_of_le (by simpa [prefixLength] using startLe)]
  simp only [List.nil_append]
  rw [List.drop_append]
  have replacementLength : replacement.toList.length = count := by
    simpa using replacementSize
  rw [replacementLength]
  have countLe : count ≤ otherStart - start := by omega
  rw [List.drop_eq_nil_of_le (by simpa [replacementSize] using countLe)]
  simp only [List.nil_append]
  rw [List.drop_drop]
  congr 2
  omega

/-- Replacing one block leaves the raw contents of a disjoint block
unchanged. -/
theorem replaceRange_slice_of_disjoint {words replacement : Array α}
    {changed other : Block} (changedStart : changed.base ≤ words.size)
    (replacementSize : replacement.size = changed.capacity)
    (disjoint : changed.Disjoint other) :
    (((replaceRange words replacement changed.base changed.capacity).toList.drop other.base).take
      other.capacity) = ((words.toList.drop other.base).take other.capacity) := by
  rcases disjoint with after | before
  · exact replaceRange_slice_after changedStart replacementSize after
  · exact replaceRange_slice_before changedStart before

/-- The concrete heap shared by both packed syntaxes. -/
structure Memory (payloadWidth : Nat) where
  words : Array (Word payloadWidth)
  free : List Block
  deriving DecidableEq, Repr

namespace Memory

variable {payloadWidth : Nat}

/-- Read and strictly decode one caller-identified block. -/
def read (memory : Memory payloadWidth) (block : Block) :
    Option (List (Word.Ref payloadWidth)) :=
  if block.Fits memory.words.size then
    decodeWords ((memory.words.toList.drop block.base).take block.capacity)
  else none

/-- Overwrite one in-bounds block with canonical contents. -/
def write? (memory : Memory payloadWidth) (block : Block)
    (references : List (Word.Ref payloadWidth)) : Option (Memory payloadWidth) :=
  if block.Fits memory.words.size then
    match encodeWords payloadWidth block.capacity references with
    | some encoded => some { memory with words :=
        (replaceRange memory.words encoded.toArray block.base block.capacity) }
    | none => none
  else none

/-- A successful write certifies that its target block fit the original word
array. -/
theorem write?_fits {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    block.Fits memory.words.size := by
  unfold write? at written
  split at written
  · assumption
  · contradiction

/-- A successful write certifies that the references and terminator fit in
the target block. -/
theorem write?_capacity {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    references.length < block.capacity := by
  unfold write? at written
  split at written
  · split at written
    · rename_i encodedWords encoded
      unfold encodeWords at encoded
      split at encoded
      · assumption
      · contradiction
    · contradiction
  · contradiction

theorem write?_read {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    after.read block = some references := by
  unfold write? at written
  split at written
  · rename_i fits
    split at written
    · rename_i encodedWords encoded
      have afterEqual := Option.some.inj written
      rw [← afterEqual]
      unfold read
      have replacementSize : encodedWords.toArray.size = block.capacity := by
        simp [encodeWords_length encoded]
      have encodedLength : encodedWords.length = block.capacity :=
        encodeWords_length encoded
      have baseBound : block.base ≤ memory.words.size := by
        exact Nat.le_trans (Nat.le_add_right _ _) fits.2
      have sameSize :
          (replaceRange memory.words encodedWords.toArray block.base block.capacity).size =
            memory.words.size := by
        unfold replaceRange
        simp [encodedLength, baseBound]
        have := fits.2
        simp only [Block.stop] at this
        omega
      rw [if_pos (by simpa [sameSize] using fits)]
      rw [replaceRange_slice baseBound replacementSize]
      exact decodeWords_of_encodeWords encoded
    · contradiction
  · contradiction

/-- A successful block write preserves the size of the flat word array. -/
theorem write?_words_size {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    after.words.size = memory.words.size := by
  unfold write? at written
  split at written
  · rename_i fits
    split at written
    · rename_i encodedWords encoded
      have afterEqual := Option.some.inj written
      rw [← afterEqual]
      exact replaceRange_size
        (Nat.le_trans (Nat.le_add_right _ _) fits.2)
        (by simpa [Block.stop] using fits.2)
        (by simpa using encodeWords_length encoded)
    · contradiction
  · contradiction

/-- The written block also fits the resulting word array. -/
theorem write?_fits_after {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    block.Fits after.words.size := by
  rw [write?_words_size written]
  exact write?_fits written

/-- A successful write preserves every read from a disjoint block. This is
stated without a fitting premise: both successful and failed reads are
preserved because the word-array size is unchanged. -/
theorem write?_read_disjoint {memory after : Memory payloadWidth} {changed other : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? changed references = some after)
    (disjoint : changed.Disjoint other) :
    after.read other = memory.read other := by
  have sameSize := write?_words_size written
  unfold write? at written
  split at written
  · rename_i changedFits
    split at written
    · rename_i encodedWords encoded
      have afterEqual := Option.some.inj written
      rw [← afterEqual] at sameSize ⊢
      unfold read
      by_cases otherFits : other.Fits memory.words.size
      · rw [if_pos otherFits]
        rw [if_pos (by simpa [sameSize] using otherFits)]
        congr 1
        exact replaceRange_slice_of_disjoint
          (Nat.le_trans (Nat.le_add_right _ _) changedFits.2)
          (by simpa using encodeWords_length encoded) disjoint
      · rw [if_neg otherFits]
        rw [if_neg (by simpa [sameSize] using otherFits)]
    · contradiction
  · contradiction

/-- Writing block contents never changes allocator ownership metadata. -/
theorem write?_free {memory after : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (written : memory.write? block references = some after) :
    after.free = memory.free := by
  unfold write? at written
  split at written
  · split at written
    · have afterEqual := Option.some.inj written
      rw [← afterEqual]
    · contradiction
  · contradiction

/-- Select and remove the first free block large enough for `needed` live
references plus the terminator. -/
def takeFree? : List Block → Nat → Option (Block × List Block)
  | [], _ => none
  | block :: blocks, needed =>
      if needed < block.capacity then some (block, blocks)
      else (fun (selected, rest) ↦ (selected, block :: rest)) <$> takeFree? blocks needed

theorem takeFree?_capacity {blocks : List Block} {needed : Nat} {block : Block}
    {rest : List Block} (taken : takeFree? blocks needed = some (block, rest)) :
    needed < block.capacity := by
  induction blocks generalizing block rest with
  | nil => simp [takeFree?] at taken
  | cons head tail ih =>
      by_cases fits : needed < head.capacity
      · rw [takeFree?, if_pos fits] at taken
        have equal := Option.some.inj taken
        have headEqual : head = block := congrArg Prod.fst equal
        subst block
        exact fits
      · cases recursive : takeFree? tail needed with
        | none =>
            rw [takeFree?, if_neg fits, recursive] at taken
            contradiction
        | some pair =>
            rcases pair with ⟨selected, selectedRest⟩
            rw [takeFree?, if_neg fits, recursive] at taken
            have equal := Option.some.inj taken
            have selectedEq : selected = block := congrArg Prod.fst equal
            subst block
            exact ih recursive

theorem takeFree?_perm {blocks : List Block} {needed : Nat} {block : Block}
    {rest : List Block} (taken : takeFree? blocks needed = some (block, rest)) :
    blocks.Perm (block :: rest) := by
  induction blocks generalizing block rest with
  | nil => simp [takeFree?] at taken
  | cons head tail ih =>
      by_cases fits : needed < head.capacity
      · rw [takeFree?, if_pos fits] at taken
        have equal := Option.some.inj taken
        have headEqual : head = block := congrArg Prod.fst equal
        have tailEqual : tail = rest := congrArg Prod.snd equal
        subst block
        subst rest
        exact List.Perm.refl _
      · cases recursive : takeFree? tail needed with
        | none =>
            rw [takeFree?, if_neg fits, recursive] at taken
            contradiction
        | some pair =>
            rcases pair with ⟨selected, selectedRest⟩
            rw [takeFree?, if_neg fits, recursive] at taken
            have equal := Option.some.inj taken
            have selectedEq : selected = block := congrArg Prod.fst equal
            have restEq : head :: selectedRest = rest := congrArg Prod.snd equal
            subst block
            rw [← restEq]
            exact (List.Perm.cons head (ih recursive)).trans (List.Perm.swap _ _ _)

/-- Allocate a reusable zeroed block. The word array is unchanged; ownership
passes from the free list to the caller. -/
def allocate? (memory : Memory payloadWidth) (needed : Nat) :
    Option (Block × Memory payloadWidth) := do
  let (block, rest) ← takeFree? memory.free needed
  some (block, { memory with free := rest })

theorem allocate?_capacity {memory : Memory payloadWidth} {needed : Nat}
    {block : Block} {after : Memory payloadWidth}
    (allocated : memory.allocate? needed = some (block, after)) :
    needed < block.capacity := by
  unfold allocate? at allocated
  cases taken : takeFree? memory.free needed with
  | none => simp [taken] at allocated
  | some pair =>
      rcases pair with ⟨selected, rest⟩
      rw [taken] at allocated
      change some (selected, { memory with free := rest }) = some (block, after) at allocated
      have equal := Option.some.inj allocated
      have selectedEq : selected = block := congrArg Prod.fst equal
      subst block
      exact takeFree?_capacity taken

theorem allocate?_words {memory : Memory payloadWidth} {needed : Nat}
    {block : Block} {after : Memory payloadWidth}
    (allocated : memory.allocate? needed = some (block, after)) :
    after.words = memory.words := by
  unfold allocate? at allocated
  cases taken : takeFree? memory.free needed with
  | none => simp [taken] at allocated
  | some pair =>
      rcases pair with ⟨selected, rest⟩
      rw [taken] at allocated
      change some (selected, { memory with free := rest }) = some (block, after) at allocated
      have equal := Option.some.inj allocated
      have afterEqual : ({ memory with free := rest } : Memory payloadWidth) = after :=
        congrArg Prod.snd equal
      rw [← afterEqual]

/-- Allocation only changes ownership metadata, so every block read is
preserved. -/
theorem allocate?_read {memory : Memory payloadWidth} {needed : Nat}
    {block : Block} {after : Memory payloadWidth}
    (allocated : memory.allocate? needed = some (block, after)) (other : Block) :
    after.read other = memory.read other := by
  unfold read
  rw [allocate?_words allocated]

/-- Allocation transfers exactly one block out of the free list. -/
theorem allocate?_free_perm {memory : Memory payloadWidth} {needed : Nat}
    {block : Block} {after : Memory payloadWidth}
    (allocated : memory.allocate? needed = some (block, after)) :
    memory.free.Perm (block :: after.free) := by
  unfold allocate? at allocated
  cases taken : takeFree? memory.free needed with
  | none => simp [taken] at allocated
  | some pair =>
      rcases pair with ⟨selected, rest⟩
      rw [taken] at allocated
      change some (selected, { memory with free := rest }) =
        some (block, after) at allocated
      have equal := Option.some.inj allocated
      have selectedEq : selected = block := congrArg Prod.fst equal
      have afterEq : ({ memory with free := rest } : Memory payloadWidth) = after :=
        congrArg Prod.snd equal
      subst block
      rw [← afterEq]
      exact takeFree?_perm taken

/-- Release a known block by zeroing it and returning it to the free list. -/
def release? (memory : Memory payloadWidth) (block : Block) : Option (Memory payloadWidth) := do
  let cleared ← memory.write? block []
  some { cleared with free := block :: cleared.free }

/-- Releasing a block returns it to the front of the free list. -/
theorem release?_free {memory after : Memory payloadWidth} {block : Block}
    (released : memory.release? block = some after) :
    after.free = block :: memory.free := by
  unfold release? at released
  cases cleared : memory.write? block [] with
  | none => simp [cleared] at released
  | some intermediate =>
      rw [cleared] at released
      have afterEqual := Option.some.inj released
      rw [← afterEqual, write?_free cleared]

/-- Releasing a block preserves the size of the flat word array. -/
theorem release?_words_size {memory after : Memory payloadWidth} {block : Block}
    (released : memory.release? block = some after) :
    after.words.size = memory.words.size := by
  unfold release? at released
  cases cleared : memory.write? block [] with
  | none => simp [cleared] at released
  | some intermediate =>
      rw [cleared] at released
      have afterEqual := Option.some.inj released
      exact (congrArg (fun state ↦ state.words.size) afterEqual).symm.trans
        (write?_words_size cleared)

/-- Releasing one block preserves every read from a disjoint block. -/
theorem release?_read_disjoint {memory after : Memory payloadWidth} {changed other : Block}
    (released : memory.release? changed = some after)
    (disjoint : changed.Disjoint other) :
    after.read other = memory.read other := by
  unfold release? at released
  cases cleared : memory.write? changed [] with
  | none => simp [cleared] at released
  | some intermediate =>
      rw [cleared] at released
      have afterEqual := Option.some.inj released
      rw [← afterEqual]
      simpa [read] using write?_read_disjoint cleared disjoint

end Memory
end Nucleus.Classical.Packed
