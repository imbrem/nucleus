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

`embed?` first checks the alternating source syntax and then runs the
executable retagger.  Its commuting theorem is proved directly from the two
decoders: no post-hoc abstract equality test is part of the algorithm.
Allocator validity remains explicit evidence at the representation boundary.
-/

namespace Nucleus.Classical.Embedding.AlternatingToTagged.Packed

open Nucleus.Classical
open Nucleus.Classical.Packed

variable {payloadWidth : Nat}

/- Writing a live expression block preserves all allocator invariants.  The
only non-structural clause is free-list zeroing: it follows because every live
block is disjoint from every free block. -/
private theorem valid_write {memory after : Memory payloadWidth}
    {roots roots' : List (Word.Ref payloadWidth × Word.Ref payloadWidth)}
    {layout : Layout} {block : Block} {references : List (Word.Ref payloadWidth)}
    (valid : layout.Valid (Classical.Packed.Arena.mk memory roots))
    (member : block ∈ layout.live)
    (written : memory.write? block references = some after) :
    layout.Valid (Classical.Packed.Arena.mk after roots') := by
  have sameSize := Memory.write?_words_size written
  have sameFree := Memory.write?_free written
  constructor
  · intro candidate candidateMember
    rw [sameFree] at candidateMember
    simpa [sameSize] using valid.allFit candidate candidateMember
  · simpa [sameFree] using valid.disjoint
  · intro freeBlock freeMember
    rw [sameFree] at freeMember
    have cross := (List.pairwise_append.mp valid.disjoint).2.2
      block member freeBlock freeMember
    rw [Memory.write?_read_disjoint written cross]
    exact valid.freeZeroed freeBlock freeMember
  · simpa [sameSize] using valid.addressable

private def nodeTag : Alternating.Mode → Nat
  | .all => 0
  | .any => 1

private def pointerRef? (payloadWidth base tag : Nat) (negative : Bool) :
    Option (Word.Ref payloadWidth) :=
  match Word.pointer? payloadWidth base tag negative with
  | none => none
  | some word =>
      if reference : word.IsRef then some ⟨word, reference⟩ else none

private theorem decodeWords_length_lt {words : List (Word payloadWidth)}
    {references : List (Word.Ref payloadWidth)}
    (decoded : decodeWords words = some references) :
    references.length < words.length := by
  induction words generalizing references with
  | nil => simp [decodeWords] at decoded
  | cons word words ih =>
      unfold decodeWords at decoded
      split at decoded
      · split at decoded
        · have equal := Option.some.inj decoded
          subst references
          simp
        · contradiction
      · split at decoded
        · cases tailDecoded : decodeWords words with
          | none => simp [tailDecoded] at decoded
          | some tail =>
              rw [tailDecoded] at decoded
              have equal := Option.some.inj decoded
              subst references
              simpa using ih tailDecoded
        · contradiction

private theorem read_length_lt {memory : Memory payloadWidth} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (read : memory.read block = some references) :
    references.length < block.capacity := by
  unfold Memory.read at read
  split at read
  · exact lt_of_lt_of_le (decodeWords_length_lt read) (List.length_take_le _ _)
  · contradiction

private theorem pointerRef?_array (mode : Alternating.Mode)
    (reference : Word.Ref payloadWidth) (array : reference.word.tag = 0) :
    ∃ target, pointerRef? payloadWidth reference.word.base (nodeTag mode)
      reference.word.negative = some target := by
  have payloadBase : reference.word.payload.val = reference.word.base := by
    simp [Word.base, array]
  have baseNonzero : reference.word.base ≠ 0 := by
    intro zero
    apply reference.isRef
    rw [payloadBase, zero]
  have widthAtLeastTwo : 2 ≤ payloadWidth := by
    by_contra tooNarrow
    have widthLt : payloadWidth < 2 := Nat.lt_of_not_ge tooNarrow
    have aligned := reference.word.base_aligned
    have bound := reference.word.payload.isLt
    have cases : payloadWidth = 0 ∨ payloadWidth = 1 := by omega
    rcases cases with rfl | rfl
    · have narrow : reference.word.payload.val < 1 := by
        simpa only [pow_zero] using bound
      rw [payloadBase] at narrow
      omega
    · have narrow : reference.word.payload.val < 2 := by
        simpa only [pow_one] using bound
      rw [payloadBase] at narrow
      omega
  obtain ⟨extra, widthEq⟩ := Nat.exists_eq_add_of_le widthAtLeastTwo
  have powerMod : 2 ^ payloadWidth % 4 = 0 := by
    rw [widthEq, pow_add]
    simp
  have baseBound := reference.word.payload.isLt
  rw [payloadBase] at baseBound
  have tagBound : nodeTag mode < 4 := by cases mode <;> decide
  have tagNotLiteral : nodeTag mode ≠ 3 := by cases mode <;> decide
  have encodedBound : reference.word.base + nodeTag mode < 2 ^ payloadWidth := by
    have aligned := reference.word.base_aligned
    cases mode <;> simp [nodeTag] <;> omega
  have encoded : Word.pointer? payloadWidth reference.word.base (nodeTag mode)
      reference.word.negative = some
        ⟨reference.word.negative,
          ⟨reference.word.base + nodeTag mode, encodedBound⟩⟩ := by
    unfold Word.pointer?
    rw [if_neg tagNotLiteral, if_neg baseNonzero]
    unfold Word.withTag?
    rw [if_pos ⟨reference.word.base_aligned, tagBound⟩]
    rw [dif_pos encodedBound]
  let targetWord : Word payloadWidth :=
    ⟨reference.word.negative,
      ⟨reference.word.base + nodeTag mode, encodedBound⟩⟩
  have targetIsRef : targetWord.IsRef := Word.pointer?_isRef encoded
  let target : Word.Ref payloadWidth := ⟨targetWord, targetIsRef⟩
  refine ⟨target, ?_⟩
  simp [pointerRef?, encoded, target, targetWord, targetIsRef]

private theorem pointerRef?_fields {base tag : Nat} {negative : Bool}
    {target : Word.Ref payloadWidth}
    (encoded : pointerRef? payloadWidth base tag negative = some target) :
    target.word.base = base ∧ target.word.tag = tag ∧
      target.word.negative = negative := by
  unfold pointerRef? at encoded
  split at encoded
  · contradiction
  · rename_i word wordEncoded
    split at encoded
    · have targetEqual := Option.some.inj encoded
      subst target
      exact ⟨Word.pointer?_base wordEncoded, Word.pointer?_tag wordEncoded,
        Word.pointer?_negative wordEncoded⟩
    · contradiction

private def ReadsAgree (left right : Memory payloadWidth) (blocks : List Block) : Prop :=
  ∀ block ∈ blocks, left.read block = right.read block

private theorem readsAgree_refl (memory : Memory payloadWidth) (blocks : List Block) :
    ReadsAgree memory memory blocks := by
  intro block member
  rfl

private theorem ReadsAgree.trans {first second third : Memory payloadWidth}
    {blocks : List Block} (left : ReadsAgree first second blocks)
    (right : ReadsAgree second third blocks) : ReadsAgree first third blocks := by
  intro block member
  exact (left block member).trans (right block member)

private def ReadsAgreeOutside (left right : Memory payloadWidth)
    (owned live : List Block) : Prop :=
  ∀ block ∈ live, block ∉ owned → left.read block = right.read block

private theorem readsAgreeOutside_refl (memory : Memory payloadWidth)
    (owned live : List Block) : ReadsAgreeOutside memory memory owned live := by
  intro block member outside
  rfl

private theorem pairwise_rel_of_mem_ne {α : Type} {relation : α → α → Prop}
    (symmetric : ∀ {left right}, relation left right → relation right left)
    {items : List α} (pairwise : items.Pairwise relation)
    {left right : α} (leftMember : left ∈ items) (rightMember : right ∈ items)
    (different : left ≠ right) : relation left right := by
  induction items with
  | nil => simp at leftMember
  | cons head tail ih =>
      have separated := (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · contradiction
        · exact separated right rightMember
      · rcases rightMember with rfl | rightMember
        · exact symmetric (separated left leftMember)
        · exact ih tailPairwise leftMember rightMember

private theorem write_readsAgreeOutside {memory after : Memory payloadWidth}
    {owned live : List Block} {selected : Block}
    {references : List (Word.Ref payloadWidth)}
    (livePairwise : live.Pairwise Block.Disjoint)
    (selectedMember : selected ∈ owned) (ownedLive : owned.Sublist live)
    (written : memory.write? selected references = some after) :
    ReadsAgreeOutside memory after owned live := by
  intro candidate candidateMember outside
  have selectedLive := ownedLive.subset selectedMember
  have different : selected ≠ candidate := by
    intro equal
    subst candidate
    exact outside selectedMember
  have disjoint := pairwise_rel_of_mem_ne (fun {_ _} value => value.symm)
    livePairwise selectedLive candidateMember different
  exact (Memory.write?_read_disjoint written disjoint).symm

private theorem readsAgree_mono {left right : Memory payloadWidth}
    {outer inner : List Block} (agree : ReadsAgree left right outer)
    (subset : ∀ block ∈ inner, block ∈ outer) : ReadsAgree left right inner := by
  intro block member
  exact agree block (subset block member)

private theorem takeBase?_rest_sublist {blocks : List Block} {base : Nat}
    {selected : Block} {rest : List Block}
    (taken : Layout.takeBase? blocks base = some (selected, rest)) :
    rest.Sublist blocks := by
  induction blocks generalizing selected rest with
  | nil => simp [Layout.takeBase?] at taken
  | cons head tail ih =>
      by_cases equal : head.base = base
      · rw [Layout.takeBase?, if_pos equal] at taken
        have pairEqual := Option.some.inj taken
        have restEqual : tail = rest := congrArg Prod.snd pairEqual
        subst rest
        exact List.Sublist.cons _ (List.Sublist.refl tail)
      · cases recursive : Layout.takeBase? tail base with
        | none => simp [Layout.takeBase?, equal, recursive] at taken
        | some pair =>
            rcases pair with ⟨chosen, chosenRest⟩
            rw [Layout.takeBase?, if_neg equal, recursive] at taken
            have pairEqual := Option.some.inj taken
            have restEqual : head :: chosenRest = rest := congrArg Prod.snd pairEqual
            subst rest
            exact List.Sublist.cons_cons head (ih recursive)

private theorem write_readsAgree_rest {memory after : Memory payloadWidth}
    {blocks : List Block} {base : Nat} {selected : Block} {rest : List Block}
    {references : List (Word.Ref payloadWidth)}
    (pairwise : blocks.Pairwise Block.Disjoint)
    (taken : Layout.takeBase? blocks base = some (selected, rest))
    (written : memory.write? selected references = some after) :
    ReadsAgree memory after rest := by
  have permutation := Layout.takeBase?_perm taken
  have reordered := pairwise.perm permutation fun {_ _} disjoint => disjoint.symm
  have separated : ∀ candidate ∈ rest, selected.Disjoint candidate :=
    (List.pairwise_cons.mp reordered).1
  intro candidate member
  exact (Memory.write?_read_disjoint written (separated candidate member)).symm

private theorem alternating_decodeRef_remaining_sublist :
    ∀ (fuel : Nat) (memory : Memory payloadWidth) (mode : Alternating.Mode)
      (blocks : List Block) (reference : Word.Ref payloadWidth)
      (expr : Alternating.Expr Nat) (rest : List Block),
      Alternating.Packed.decodeRef memory fuel mode blocks reference = some (expr, rest) →
      rest.Sublist blocks := by
  intro fuel
  induction fuel with
  | zero =>
      intro memory mode blocks reference expr rest decoded
      simp [Alternating.Packed.decodeRef] at decoded
  | succ fuel ih =>
      intro memory mode blocks reference expr rest decoded
      simp only [Alternating.Packed.decodeRef] at decoded
      split at decoded
      · have equal := Option.some.inj decoded
        have restEqual : blocks = rest := congrArg Prod.snd equal
        subst rest
        exact List.Sublist.refl blocks
      · split at decoded
        · rename_i notLiteral array
          cases taken : Layout.takeBase? blocks reference.word.base with
          | none => simp [taken] at decoded
          | some pair =>
              rcases pair with ⟨block, remaining⟩
              rw [taken] at decoded
              cases read : memory.read block with
              | none => simp [read] at decoded
              | some children =>
                  change (do
                    let children ← memory.read block
                    let result ← List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (childExpr, childRest) ←
                          Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                        some (childExpr :: state.1, childRest))
                      ([], remaining) children
                    some (Alternating.Expr.array reference.word.negative result.1.reverse,
                      result.2)) = some (expr, rest) at decoded
                  rw [read] at decoded
                  change (List.foldlM
                    (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                      let (childExpr, childRest) ←
                        Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                      some (childExpr :: state.1, childRest))
                    ([], remaining) children).bind
                      (fun result => some
                        (Alternating.Expr.array reference.word.negative result.1.reverse,
                          result.2)) = some (expr, rest) at decoded
                  have foldRemaining : ∀ (items : List (Word.Ref payloadWidth))
                      (decodedRev : List (Alternating.Expr Nat))
                      (owned : List Block) (resultRev : List (Alternating.Expr Nat))
                      (resultBlocks : List Block),
                      List.foldlM
                          (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                            let (childExpr, childRest) ←
                              Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                            some (childExpr :: state.1, childRest))
                          (decodedRev, owned) items = some (resultRev, resultBlocks) →
                      resultBlocks.Sublist owned := by
                    intro items
                    induction items with
                    | nil =>
                        intro decodedRev owned resultRev resultBlocks folded
                        have equal := Option.some.inj folded
                        have blocksEqual : owned = resultBlocks := congrArg Prod.snd equal
                        subst resultBlocks
                        exact List.Sublist.refl owned
                    | cons child items itemsIh =>
                        intro decodedRev owned resultRev resultBlocks folded
                        simp only [List.foldlM_cons] at folded
                        cases childDecoded : Alternating.Packed.decodeRef memory fuel mode.flip
                            owned child with
                        | none => simp [childDecoded] at folded
                        | some result =>
                            rcases result with ⟨childExpr, childRest⟩
                            rw [childDecoded] at folded
                            have afterItems := itemsIh (childExpr :: decodedRev) childRest
                              resultRev resultBlocks folded
                            exact afterItems.trans
                              (ih memory mode.flip owned child childExpr childRest childDecoded)
                  cases folded : List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (childExpr, childRest) ←
                          Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                        some (childExpr :: state.1, childRest))
                      ([], remaining) children with
                  | none =>
                      rw [folded] at decoded
                      contradiction
                  | some result =>
                      rcases result with ⟨decodedRev, resultBlocks⟩
                      rw [folded] at decoded
                      have equal := Option.some.inj decoded
                      have restEqual : resultBlocks = rest := congrArg Prod.snd equal
                      subst rest
                      have inRemaining := foldRemaining children [] remaining decodedRev
                        resultBlocks folded
                      have permutation := Layout.takeBase?_perm taken
                      exact inRemaining.trans (takeBase?_rest_sublist taken)
        · contradiction

private theorem alternating_decodeRef_remaining
    {fuel : Nat} {memory : Memory payloadWidth} {mode : Alternating.Mode}
    {blocks : List Block} {reference : Word.Ref payloadWidth}
    {expr : Alternating.Expr Nat} {rest : List Block}
    (decoded : Alternating.Packed.decodeRef memory fuel mode blocks reference =
      some (expr, rest)) : ∀ block ∈ rest, block ∈ blocks :=
  (alternating_decodeRef_remaining_sublist fuel memory mode blocks reference expr rest
    decoded).subset

/- Alternating decoding observes memory only through blocks still owned by the
current traversal. -/
private theorem alternating_decodeRef_congr :
    ∀ (fuel : Nat) (mode : Alternating.Mode) (blocks : List Block)
      (reference : Word.Ref payloadWidth) (left right : Memory payloadWidth),
      ReadsAgree left right blocks →
      Alternating.Packed.decodeRef left fuel mode blocks reference =
        Alternating.Packed.decodeRef right fuel mode blocks reference := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode blocks reference left right agree
      simp [Alternating.Packed.decodeRef]
  | succ fuel ih =>
      intro mode blocks reference left right agree
      simp only [Alternating.Packed.decodeRef]
      split
      · rfl
      · split
        · rename_i notLiteral array
          cases taken : Layout.takeBase? blocks reference.word.base with
          | none => rfl
          | some pair =>
              rcases pair with ⟨block, remaining⟩
              have permutation := Layout.takeBase?_perm taken
              have blockMember : block ∈ blocks :=
                permutation.mem_iff.mpr (by simp)
              have remainingSubset : ∀ candidate ∈ remaining, candidate ∈ blocks := by
                intro candidate member
                exact permutation.mem_iff.mpr (by simp [member])
              have blockRead := agree block blockMember
              change (do
                  let children ← left.read block
                  let result ← List.foldlM
                    (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                      let (expr, rest) ←
                        Alternating.Packed.decodeRef left fuel mode.flip state.2 child
                      some (expr :: state.1, rest))
                    ([], remaining) children
                  some (Alternating.Expr.array reference.word.negative result.1.reverse,
                    result.2)) =
                (do
                  let children ← right.read block
                  let result ← List.foldlM
                    (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                      let (expr, rest) ←
                        Alternating.Packed.decodeRef right fuel mode.flip state.2 child
                      some (expr :: state.1, rest))
                    ([], remaining) children
                  some (Alternating.Expr.array reference.word.negative result.1.reverse,
                    result.2))
              rw [blockRead]
              cases readRight : right.read block with
              | none => simp
              | some children =>
                  change (List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (expr, rest) ←
                          Alternating.Packed.decodeRef left fuel mode.flip state.2 child
                        some (expr :: state.1, rest))
                      ([], remaining) children).bind
                        (fun result => some
                          (Alternating.Expr.array reference.word.negative result.1.reverse,
                            result.2)) =
                    (List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (expr, rest) ←
                          Alternating.Packed.decodeRef right fuel mode.flip state.2 child
                        some (expr :: state.1, rest))
                      ([], remaining) children).bind
                        (fun result => some
                          (Alternating.Expr.array reference.word.negative result.1.reverse,
                            result.2))
                  have foldCongr : ∀ (items : List (Word.Ref payloadWidth))
                      (decoded : List (Alternating.Expr Nat))
                      (owned : List Block),
                      (∀ candidate ∈ owned, candidate ∈ remaining) →
                      List.foldlM
                          (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                            let (expr, rest) ←
                              Alternating.Packed.decodeRef left fuel mode.flip state.2 child
                            some (expr :: state.1, rest))
                          (decoded, owned) items =
                        List.foldlM
                          (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                            let (expr, rest) ←
                              Alternating.Packed.decodeRef right fuel mode.flip state.2 child
                            some (expr :: state.1, rest))
                          (decoded, owned) items := by
                    intro items
                    induction items with
                    | nil => intro decoded owned subset; rfl
                    | cons child items childIh =>
                        intro decoded owned subset
                        simp only [List.foldlM_cons]
                        have ownedOuter : ∀ candidate ∈ owned, candidate ∈ blocks := by
                          intro candidate member
                          exact remainingSubset candidate (subset candidate member)
                        rw [ih mode.flip owned child left right
                          (readsAgree_mono agree ownedOuter)]
                        cases recursive : Alternating.Packed.decodeRef right fuel mode.flip
                            owned child with
                        | none => simp
                        | some result =>
                            rcases result with ⟨expr, rest⟩
                            have restSubsetOwned : ∀ candidate ∈ rest, candidate ∈ owned :=
                              alternating_decodeRef_remaining recursive
                            exact childIh (expr :: decoded) rest fun candidate member =>
                              subset candidate (restSubsetOwned candidate member)
                  rw [foldCongr children [] remaining (fun _ member => member)]
        · rfl

private theorem alternating_decodeRoots_congr :
    ∀ (roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth))
      (left right : Memory payloadWidth) (fuel : Nat) (blocks : List Block),
      ReadsAgree left right blocks →
      Alternating.Packed.decodeRoots left fuel blocks roots =
        Alternating.Packed.decodeRoots right fuel blocks roots := by
  intro roots
  induction roots with
  | nil => intro left right fuel blocks agree; rfl
  | cons root roots rootsIh =>
      rcases root with ⟨premise, conclusion⟩
      intro left right fuel blocks agree
      simp only [Alternating.Packed.decodeRoots]
      rw [alternating_decodeRef_congr fuel .all blocks premise left right agree]
      cases leftDecoded : Alternating.Packed.decodeRef right fuel .all blocks premise with
      | none => rfl
      | some leftResult =>
          rcases leftResult with ⟨leftExpr, afterLeft⟩
          have afterLeftSubset := alternating_decodeRef_remaining leftDecoded
          change (do
              let rightResult ← Alternating.Packed.decodeRef left fuel .any afterLeft conclusion
              let tail ← Alternating.Packed.decodeRoots left fuel rightResult.2 roots
              some (Alternating.Sequent.mk leftExpr rightResult.1 :: tail.1, tail.2)) =
            (do
              let rightResult ← Alternating.Packed.decodeRef right fuel .any afterLeft conclusion
              let tail ← Alternating.Packed.decodeRoots right fuel rightResult.2 roots
              some (Alternating.Sequent.mk leftExpr rightResult.1 :: tail.1, tail.2))
          rw [alternating_decodeRef_congr fuel .any afterLeft conclusion left right
            (readsAgree_mono agree afterLeftSubset)]
          cases rightDecoded : Alternating.Packed.decodeRef right fuel .any afterLeft
              conclusion with
          | none => rfl
          | some rightResult =>
              rcases rightResult with ⟨rightExpr, afterRight⟩
              have afterRightSubset := alternating_decodeRef_remaining rightDecoded
              change (Alternating.Packed.decodeRoots left fuel afterRight roots).bind
                    (fun tail => some
                      (Alternating.Sequent.mk leftExpr rightExpr :: tail.1, tail.2)) =
                (Alternating.Packed.decodeRoots right fuel afterRight roots).bind
                    (fun tail => some
                      (Alternating.Sequent.mk leftExpr rightExpr :: tail.1, tail.2))
              rw [rootsIh left right fuel afterRight
                (readsAgree_mono agree fun block member =>
                  afterLeftSubset block (afterRightSubset block member))]

private theorem alternating_decodeRoots_remaining_sublist :
    ∀ (roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth))
      (memory : Memory payloadWidth) (fuel : Nat) (blocks : List Block)
      (sequents : List (Alternating.Sequent Nat)) (rest : List Block),
      Alternating.Packed.decodeRoots memory fuel blocks roots = some (sequents, rest) →
      rest.Sublist blocks := by
  intro roots
  induction roots with
  | nil =>
      intro memory fuel blocks sequents rest decoded
      simp only [Alternating.Packed.decodeRoots] at decoded
      have equal := Option.some.inj decoded
      have restEqual : blocks = rest := congrArg Prod.snd equal
      subst rest
      exact List.Sublist.refl blocks
  | cons root roots rootsIh =>
      rcases root with ⟨left, right⟩
      intro memory fuel blocks sequents rest decoded
      simp only [Alternating.Packed.decodeRoots] at decoded
      cases leftDecoded : Alternating.Packed.decodeRef memory fuel .all blocks left with
      | none => simp [leftDecoded] at decoded
      | some leftResult =>
          rcases leftResult with ⟨leftExpr, afterLeft⟩
          rw [leftDecoded] at decoded
          change (do
            let rightResult ← Alternating.Packed.decodeRef memory fuel .any afterLeft right
            let tail ← Alternating.Packed.decodeRoots memory fuel rightResult.2 roots
            some (Alternating.Sequent.mk leftExpr rightResult.1 :: tail.1, tail.2)) =
              some (sequents, rest) at decoded
          cases rightDecoded : Alternating.Packed.decodeRef memory fuel .any afterLeft right with
          | none => simp [rightDecoded] at decoded
          | some rightResult =>
              rcases rightResult with ⟨rightExpr, afterRight⟩
              rw [rightDecoded] at decoded
              change (Alternating.Packed.decodeRoots memory fuel afterRight roots).bind
                  (fun tail => some
                    (Alternating.Sequent.mk leftExpr rightExpr :: tail.1, tail.2)) =
                some (sequents, rest) at decoded
              cases tailDecoded : Alternating.Packed.decodeRoots memory fuel afterRight roots with
              | none => simp [tailDecoded] at decoded
              | some tailResult =>
                  rcases tailResult with ⟨tailSequents, finalRest⟩
                  rw [tailDecoded] at decoded
                  have equal := Option.some.inj decoded
                  have restEqual : finalRest = rest := congrArg Prod.snd equal
                  subst rest
                  exact (rootsIh memory fuel afterRight tailSequents finalRest tailDecoded).trans
                    ((alternating_decodeRef_remaining_sublist fuel memory .any afterLeft right
                      rightExpr afterRight rightDecoded).trans
                    (alternating_decodeRef_remaining_sublist fuel memory .all blocks left
                      leftExpr afterLeft leftDecoded))

private theorem tagged_decodeRef_remaining_sublist :
    ∀ (fuel : Nat) (memory : Memory payloadWidth) (blocks : List Block)
      (reference : Word.Ref payloadWidth) (formula : Tagged.Formula Nat)
      (rest : List Block),
      Tagged.Packed.decodeRef memory fuel blocks reference = some (formula, rest) →
      rest.Sublist blocks := by
  intro fuel
  induction fuel with
  | zero =>
      intro memory blocks reference formula rest decoded
      simp [Tagged.Packed.decodeRef] at decoded
  | succ fuel ih =>
      intro memory blocks reference formula rest decoded
      simp only [Tagged.Packed.decodeRef] at decoded
      split at decoded
      · have equal := Option.some.inj decoded
        have restEqual : blocks = rest := congrArg Prod.snd equal
        subst rest
        exact List.Sublist.refl blocks
      · cases taken : Layout.takeBase? blocks reference.word.base with
        | none => simp [taken] at decoded
        | some pair =>
            rcases pair with ⟨block, remaining⟩
            rw [taken] at decoded
            cases read : memory.read block with
            | none => simp [read] at decoded
            | some children =>
                change (do
                  let children ← memory.read block
                  let result ← List.foldlM
                    (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                      let (childFormula, childRest) ←
                        Tagged.Packed.decodeRef memory fuel state.2 child
                      some (childFormula :: state.1, childRest))
                    ([], remaining) children
                  let resultFormula ← Tagged.Packed.node reference.word.tag
                    reference.word.negative result.1.reverse
                  some (resultFormula, result.2)) = some (formula, rest) at decoded
                rw [read] at decoded
                change (List.foldlM
                  (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                    let (childFormula, childRest) ←
                      Tagged.Packed.decodeRef memory fuel state.2 child
                    some (childFormula :: state.1, childRest))
                  ([], remaining) children).bind
                    (fun result => do
                      let resultFormula ← Tagged.Packed.node reference.word.tag
                        reference.word.negative result.1.reverse
                      some (resultFormula, result.2)) = some (formula, rest) at decoded
                have foldRemaining : ∀ (items : List (Word.Ref payloadWidth))
                    (decodedRev : List (Tagged.Formula Nat)) (owned : List Block)
                    (resultRev : List (Tagged.Formula Nat)) (resultBlocks : List Block),
                    List.foldlM
                        (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                          let (childFormula, childRest) ←
                            Tagged.Packed.decodeRef memory fuel state.2 child
                          some (childFormula :: state.1, childRest))
                        (decodedRev, owned) items = some (resultRev, resultBlocks) →
                    resultBlocks.Sublist owned := by
                  intro items
                  induction items with
                  | nil =>
                      intro decodedRev owned resultRev resultBlocks folded
                      have equal := Option.some.inj folded
                      have blocksEqual : owned = resultBlocks := congrArg Prod.snd equal
                      subst resultBlocks
                      exact List.Sublist.refl owned
                  | cons child items itemsIh =>
                      intro decodedRev owned resultRev resultBlocks folded
                      simp only [List.foldlM_cons] at folded
                      cases childDecoded : Tagged.Packed.decodeRef memory fuel owned child with
                      | none => simp [childDecoded] at folded
                      | some childResult =>
                          rcases childResult with ⟨childFormula, childRest⟩
                          rw [childDecoded] at folded
                          exact (itemsIh (childFormula :: decodedRev) childRest resultRev
                            resultBlocks folded).trans
                            (ih memory owned child childFormula childRest childDecoded)
                cases folded : List.foldlM
                    (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                      let (childFormula, childRest) ←
                        Tagged.Packed.decodeRef memory fuel state.2 child
                      some (childFormula :: state.1, childRest))
                    ([], remaining) children with
                | none =>
                    rw [folded] at decoded
                    contradiction
                | some result =>
                    rcases result with ⟨decodedRev, resultBlocks⟩
                    rw [folded] at decoded
                    change (do
                      let resultFormula ← Tagged.Packed.node reference.word.tag
                        reference.word.negative decodedRev.reverse
                      some (resultFormula, resultBlocks)) = some (formula, rest) at decoded
                    cases nodeDecoded : Tagged.Packed.node reference.word.tag
                        reference.word.negative decodedRev.reverse with
                    | none => simp [nodeDecoded] at decoded
                    | some resultFormula =>
                        rw [nodeDecoded] at decoded
                        have equal := Option.some.inj decoded
                        have restEqual : resultBlocks = rest := congrArg Prod.snd equal
                        subst rest
                        exact (foldRemaining children [] remaining decodedRev resultBlocks
                          folded).trans (takeBase?_rest_sublist taken)

private theorem tagged_decodeFold_remaining_sublist :
    ∀ (items : List (Word.Ref payloadWidth)) (memory : Memory payloadWidth)
      (fuel : Nat) (decodedRev : List (Tagged.Formula Nat)) (owned : List Block)
      (resultRev : List (Tagged.Formula Nat)) (resultBlocks : List Block),
      List.foldlM
          (fun (state : List (Tagged.Formula Nat) × List Block) child => do
            let (childFormula, childRest) ←
              Tagged.Packed.decodeRef memory fuel state.2 child
            some (childFormula :: state.1, childRest))
          (decodedRev, owned) items = some (resultRev, resultBlocks) →
      resultBlocks.Sublist owned := by
  intro items
  induction items with
  | nil =>
      intro memory fuel decodedRev owned resultRev resultBlocks folded
      have equal := Option.some.inj folded
      have blocksEqual : owned = resultBlocks := congrArg Prod.snd equal
      subst resultBlocks
      exact List.Sublist.refl owned
  | cons child items itemsIh =>
      intro memory fuel decodedRev owned resultRev resultBlocks folded
      simp only [List.foldlM_cons] at folded
      cases childDecoded : Tagged.Packed.decodeRef memory fuel owned child with
      | none => simp [childDecoded] at folded
      | some childResult =>
          rcases childResult with ⟨childFormula, childRest⟩
          rw [childDecoded] at folded
          exact (itemsIh memory fuel (childFormula :: decodedRev) childRest resultRev
            resultBlocks folded).trans
            (tagged_decodeRef_remaining_sublist fuel memory owned child childFormula
              childRest childDecoded)

private def ReadsAgreeExcept (left right : Memory payloadWidth)
    (blocks rest : List Block) : Prop :=
  ∀ block ∈ blocks, block ∉ rest → left.read block = right.read block

private theorem selected_not_mem_rest {blocks : List Block} {base : Nat}
    {selected : Block} {remaining rest : List Block}
    (pairwise : blocks.Pairwise Block.Disjoint)
    (taken : Layout.takeBase? blocks base = some (selected, remaining))
    (restSublist : rest.Sublist remaining) : selected ∉ rest := by
  have permutation := Layout.takeBase?_perm taken
  have reordered := pairwise.perm permutation fun {_ _} disjoint => disjoint.symm
  have separated := (List.pairwise_cons.mp reordered).1
  intro selectedMember
  have inRemaining := restSublist.subset selectedMember
  have selfDisjoint := separated selected inRemaining
  simp only [Block.Disjoint, Block.stop] at selfDisjoint
  have positive := selected.capacity_pos
  omega

/- A successful tagged decode is insensitive to changes in blocks returned to
its caller; it observes exactly the blocks it consumes. -/
private theorem tagged_decodeRef_congr_except :
    ∀ (fuel : Nat) (left right : Memory payloadWidth) (blocks : List Block)
      (reference : Word.Ref payloadWidth) (formula : Tagged.Formula Nat)
      (rest : List Block),
      blocks.Pairwise Block.Disjoint →
      Tagged.Packed.decodeRef left fuel blocks reference = some (formula, rest) →
      ReadsAgreeExcept left right blocks rest →
      Tagged.Packed.decodeRef right fuel blocks reference = some (formula, rest) := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right blocks reference formula rest pairwise decoded agree
      simp [Tagged.Packed.decodeRef] at decoded
  | succ fuel ih =>
      intro left right blocks reference formula rest pairwise decoded agree
      simp only [Tagged.Packed.decodeRef] at decoded ⊢
      by_cases notArray : reference.word.tag = 3
      · rw [dif_pos notArray] at decoded ⊢
        exact decoded
      · rw [dif_neg notArray] at decoded ⊢
        have decodedFull : Tagged.Packed.decodeRef left (fuel + 1) blocks reference =
            some (formula, rest) := by
          simp only [Tagged.Packed.decodeRef]
          rw [dif_neg notArray]
          exact decoded
        cases taken : Layout.takeBase? blocks reference.word.base with
        | none => simp [taken] at decoded
        | some pair =>
            rcases pair with ⟨block, remaining⟩
            rw [taken] at decoded
            have remainingSublist := takeBase?_rest_sublist taken
            have remainingPairwise := List.Pairwise.sublist remainingSublist pairwise
            have restSublist := tagged_decodeRef_remaining_sublist (fuel + 1) left
              blocks reference formula rest decodedFull
            have restInRemaining : rest.Sublist remaining := by
              -- The selected root block is consumed before all children.
              change (do
                let children ← left.read block
                let result ← List.foldlM
                  (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                    let (childFormula, childRest) ←
                      Tagged.Packed.decodeRef left fuel state.2 child
                    some (childFormula :: state.1, childRest))
                  ([], remaining) children
                let resultFormula ← Tagged.Packed.node reference.word.tag
                  reference.word.negative result.1.reverse
                some (resultFormula, result.2)) = some (formula, rest) at decoded
              cases leftRead : left.read block with
              | none =>
                  rw [leftRead] at decoded
                  contradiction
              | some children =>
                  rw [leftRead] at decoded
                  change (do
                    let result ← List.foldlM
                      (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                        let (childFormula, childRest) ←
                          Tagged.Packed.decodeRef left fuel state.2 child
                        some (childFormula :: state.1, childRest))
                      ([], remaining) children
                    let resultFormula ← Tagged.Packed.node reference.word.tag
                      reference.word.negative result.1.reverse
                    some (resultFormula, result.2)) = some (formula, rest) at decoded
                  cases folded : List.foldlM
                      (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                        let (childFormula, childRest) ←
                          Tagged.Packed.decodeRef left fuel state.2 child
                        some (childFormula :: state.1, childRest))
                      ([], remaining) children with
                  | none =>
                      rw [folded] at decoded
                      contradiction
                  | some result =>
                      rcases result with ⟨decodedRev, resultBlocks⟩
                      rw [folded] at decoded
                      change (do
                        let resultFormula ← Tagged.Packed.node reference.word.tag
                          reference.word.negative decodedRev.reverse
                        some (resultFormula, resultBlocks)) = some (formula, rest) at decoded
                      cases nodeDecoded : Tagged.Packed.node reference.word.tag
                          reference.word.negative decodedRev.reverse with
                      | none => simp [nodeDecoded] at decoded
                      | some resultFormula =>
                          rw [nodeDecoded] at decoded
                          have equal := Option.some.inj decoded
                          have restEqual : resultBlocks = rest := congrArg Prod.snd equal
                          subst rest
                          exact tagged_decodeFold_remaining_sublist children left fuel []
                            remaining decodedRev resultBlocks folded
            have selectedOutside := selected_not_mem_rest pairwise taken restInRemaining
            have blockRead := agree block
              ((Layout.takeBase?_perm taken).mem_iff.mpr (by simp)) selectedOutside
            change (do
              let children ← left.read block
              let result ← List.foldlM
                (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                  let (childFormula, childRest) ←
                    Tagged.Packed.decodeRef left fuel state.2 child
                  some (childFormula :: state.1, childRest))
                ([], remaining) children
              let resultFormula ← Tagged.Packed.node reference.word.tag
                reference.word.negative result.1.reverse
              some (resultFormula, result.2)) = some (formula, rest) at decoded
            change (do
              let children ← right.read block
              let result ← List.foldlM
                (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                  let (childFormula, childRest) ←
                    Tagged.Packed.decodeRef right fuel state.2 child
                  some (childFormula :: state.1, childRest))
                ([], remaining) children
              let resultFormula ← Tagged.Packed.node reference.word.tag
                reference.word.negative result.1.reverse
              some (resultFormula, result.2)) = some (formula, rest)
            rw [← blockRead]
            cases readRight : left.read block with
            | none =>
                rw [readRight] at decoded
                contradiction
            | some children =>
                rw [readRight] at decoded
                change (List.foldlM
                    (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                      let (childFormula, childRest) ←
                        Tagged.Packed.decodeRef left fuel state.2 child
                      some (childFormula :: state.1, childRest))
                    ([], remaining) children).bind
                      (fun result => do
                        let resultFormula ← Tagged.Packed.node reference.word.tag
                          reference.word.negative result.1.reverse
                        some (resultFormula, result.2)) = some (formula, rest) at decoded
                change (List.foldlM
                    (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                      let (childFormula, childRest) ←
                        Tagged.Packed.decodeRef right fuel state.2 child
                      some (childFormula :: state.1, childRest))
                    ([], remaining) children).bind
                      (fun result => do
                        let resultFormula ← Tagged.Packed.node reference.word.tag
                          reference.word.negative result.1.reverse
                        some (resultFormula, result.2)) = some (formula, rest)
                have foldCongr : ∀ (items : List (Word.Ref payloadWidth))
                    (decodedRev : List (Tagged.Formula Nat)) (owned : List Block)
                    (resultRev : List (Tagged.Formula Nat)),
                    owned.Pairwise Block.Disjoint →
                    owned.Sublist remaining →
                    List.foldlM
                        (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                          let (childFormula, childRest) ←
                            Tagged.Packed.decodeRef left fuel state.2 child
                          some (childFormula :: state.1, childRest))
                        (decodedRev, owned) items = some (resultRev, rest) →
                    List.foldlM
                        (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                          let (childFormula, childRest) ←
                            Tagged.Packed.decodeRef right fuel state.2 child
                          some (childFormula :: state.1, childRest))
                        (decodedRev, owned) items = some (resultRev, rest) := by
                  intro items
                  induction items with
                  | nil =>
                      intro decodedRev owned resultRev ownedPairwise ownedRemaining folded
                      exact folded
                  | cons child items itemsIh =>
                      intro decodedRev owned resultRev ownedPairwise ownedRemaining folded
                      simp only [List.foldlM_cons] at folded ⊢
                      cases childDecoded : Tagged.Packed.decodeRef left fuel owned child with
                      | none => simp [childDecoded] at folded
                      | some childResult =>
                          rcases childResult with ⟨childFormula, childRest⟩
                          rw [childDecoded] at folded
                          have tailSublist := tagged_decodeFold_remaining_sublist items left fuel
                            (childFormula :: decodedRev) childRest resultRev rest folded
                          have childRestSublist := tagged_decodeRef_remaining_sublist fuel left
                            owned child childFormula childRest childDecoded
                          have childPairwise := List.Pairwise.sublist childRestSublist
                            ownedPairwise
                          have childAgree : ReadsAgreeExcept left right owned childRest := by
                            intro candidate candidateMember candidateOutside
                            exact agree candidate
                              ((ownedRemaining.trans remainingSublist).subset candidateMember)
                              fun inRest =>
                              candidateOutside (tailSublist.subset inRest)
                          have childRight := ih left right owned child childFormula childRest
                            ownedPairwise childDecoded childAgree
                          rw [childRight]
                          exact itemsIh (childFormula :: decodedRev) childRest resultRev
                            childPairwise (childRestSublist.trans ownedRemaining) folded
                cases leftFolded : List.foldlM
                    (fun (state : List (Tagged.Formula Nat) × List Block) child => do
                      let (childFormula, childRest) ←
                        Tagged.Packed.decodeRef left fuel state.2 child
                      some (childFormula :: state.1, childRest))
                    ([], remaining) children with
                | none =>
                    rw [leftFolded] at decoded
                    contradiction
                | some result =>
                    rcases result with ⟨decodedRev, resultBlocks⟩
                    have restEqual : resultBlocks = rest := by
                      rw [leftFolded] at decoded
                      change (do
                        let resultFormula ← Tagged.Packed.node reference.word.tag
                          reference.word.negative decodedRev.reverse
                        some (resultFormula, resultBlocks)) = some (formula, rest) at decoded
                      cases nodeDecoded : Tagged.Packed.node reference.word.tag
                          reference.word.negative decodedRev.reverse with
                      | none => simp [nodeDecoded] at decoded
                      | some resultFormula =>
                          rw [nodeDecoded] at decoded
                          exact congrArg Prod.snd (Option.some.inj decoded)
                    subst resultBlocks
                    have rightFolded := foldCongr children [] remaining decodedRev
                      remainingPairwise (List.Sublist.refl remaining) leftFolded
                    rw [leftFolded] at decoded
                    rw [rightFolded]
                    exact decoded

/- Recursive, order-preserving views of the decoder folds make the concrete
embedding proof state the same traversal on both representations. -/
private def decodeAlternatingRefs (memory : Memory payloadWidth) (fuel : Nat)
    (mode : Alternating.Mode) : List Block → List (Word.Ref payloadWidth) →
      Option (List (Alternating.Expr Nat) × List Block)
  | blocks, [] => some ([], blocks)
  | blocks, reference :: references => do
      let (expr, remaining) ←
        Alternating.Packed.decodeRef memory fuel mode blocks reference
      let (exprs, remaining) ←
        decodeAlternatingRefs memory fuel mode remaining references
      some (expr :: exprs, remaining)

private def decodeTaggedRefs (memory : Memory payloadWidth) (fuel : Nat) :
    List Block → List (Word.Ref payloadWidth) →
      Option (List (Tagged.Formula Nat) × List Block)
  | blocks, [] => some ([], blocks)
  | blocks, reference :: references => do
      let (formula, remaining) ←
        Tagged.Packed.decodeRef memory fuel blocks reference
      let (formulas, remaining) ←
        decodeTaggedRefs memory fuel remaining references
      some (formula :: formulas, remaining)

private theorem alternating_fold_eq_decodeRefs
    (memory : Memory payloadWidth) (fuel : Nat) (mode : Alternating.Mode) :
    ∀ (items : List (Word.Ref payloadWidth))
      (decodedRev : List (Alternating.Expr Nat)) (blocks : List Block),
      List.foldlM
          (fun (state : List (Alternating.Expr Nat) × List Block) child => do
            let (childExpr, childRest) ←
              Alternating.Packed.decodeRef memory fuel mode state.2 child
            some (childExpr :: state.1, childRest))
          (decodedRev, blocks) items = (do
        let (decoded, remaining) ← decodeAlternatingRefs memory fuel mode blocks items
        some (decoded.reverse ++ decodedRev, remaining)) := by
  intro items
  induction items with
  | nil => intro decodedRev blocks; rfl
  | cons child items ih =>
      intro decodedRev blocks
      simp only [List.foldlM_cons, decodeAlternatingRefs]
      cases childDecoded : Alternating.Packed.decodeRef memory fuel mode blocks child with
      | none => simp
      | some childResult =>
          rcases childResult with ⟨childExpr, childRest⟩
          cases tailDecoded : decodeAlternatingRefs memory fuel mode childRest items with
          | none => simp_all
          | some tailResult =>
              rcases tailResult with ⟨tailExprs, finalRest⟩
              simp_all [List.reverse_cons, List.append_assoc]

private theorem tagged_fold_eq_decodeRefs
    (memory : Memory payloadWidth) (fuel : Nat) :
    ∀ (items : List (Word.Ref payloadWidth))
      (decodedRev : List (Tagged.Formula Nat)) (blocks : List Block),
      List.foldlM
          (fun (state : List (Tagged.Formula Nat) × List Block) child => do
            let (childFormula, childRest) ←
              Tagged.Packed.decodeRef memory fuel state.2 child
            some (childFormula :: state.1, childRest))
          (decodedRev, blocks) items = (do
        let (decoded, remaining) ← decodeTaggedRefs memory fuel blocks items
        some (decoded.reverse ++ decodedRev, remaining)) := by
  intro items
  induction items with
  | nil => intro decodedRev blocks; rfl
  | cons child items ih =>
      intro decodedRev blocks
      simp only [List.foldlM_cons, decodeTaggedRefs]
      cases childDecoded : Tagged.Packed.decodeRef memory fuel blocks child with
      | none => simp
      | some childResult =>
          rcases childResult with ⟨childFormula, childRest⟩
          cases tailDecoded : decodeTaggedRefs memory fuel childRest items with
          | none => simp_all
          | some tailResult =>
              rcases tailResult with ⟨tailFormulas, finalRest⟩
              simp_all [List.reverse_cons, List.append_assoc]

private theorem decodeAlternatingRefs_remaining_sublist
    (memory : Memory payloadWidth) (fuel : Nat) (mode : Alternating.Mode) :
    ∀ (blocks : List Block) (items : List (Word.Ref payloadWidth))
      (exprs : List (Alternating.Expr Nat)) (rest : List Block),
      decodeAlternatingRefs memory fuel mode blocks items = some (exprs, rest) →
      rest.Sublist blocks := by
  intro blocks items
  induction items generalizing blocks with
  | nil =>
      intro exprs rest decoded
      simp only [decodeAlternatingRefs] at decoded
      have equal := Option.some.inj decoded
      have restEqual : blocks = rest := congrArg Prod.snd equal
      simp [← restEqual]
  | cons child items ih =>
      intro exprs rest decoded
      simp only [decodeAlternatingRefs] at decoded
      cases childDecoded : Alternating.Packed.decodeRef memory fuel mode blocks child with
      | none => simp [childDecoded] at decoded
      | some childResult =>
          rcases childResult with ⟨childExpr, childRest⟩
          rw [childDecoded] at decoded
          cases tailDecoded : decodeAlternatingRefs memory fuel mode childRest items with
          | none => simp [tailDecoded] at decoded
          | some tailResult =>
              rcases tailResult with ⟨tailExprs, finalRest⟩
              have decoded' : some (childExpr :: tailExprs, finalRest) =
                  some (exprs, rest) := by
                simpa [tailDecoded] using decoded
              have equal := Option.some.inj decoded'
              have restEqual : finalRest = rest := congrArg Prod.snd equal
              subst rest
              exact (ih childRest tailExprs finalRest tailDecoded).trans
                (alternating_decodeRef_remaining_sublist fuel memory mode blocks child
                  childExpr childRest childDecoded)

private theorem decodeTaggedRefs_remaining_sublist
    (memory : Memory payloadWidth) (fuel : Nat) :
    ∀ (blocks : List Block) (items : List (Word.Ref payloadWidth))
      (formulas : List (Tagged.Formula Nat)) (rest : List Block),
      decodeTaggedRefs memory fuel blocks items = some (formulas, rest) →
      rest.Sublist blocks := by
  intro blocks items
  induction items generalizing blocks with
  | nil =>
      intro formulas rest decoded
      simp only [decodeTaggedRefs] at decoded
      have equal := Option.some.inj decoded
      have restEqual : blocks = rest := congrArg Prod.snd equal
      simp [← restEqual]
  | cons child items ih =>
      intro formulas rest decoded
      simp only [decodeTaggedRefs] at decoded
      cases childDecoded : Tagged.Packed.decodeRef memory fuel blocks child with
      | none => simp [childDecoded] at decoded
      | some childResult =>
          rcases childResult with ⟨childFormula, childRest⟩
          rw [childDecoded] at decoded
          cases tailDecoded : decodeTaggedRefs memory fuel childRest items with
          | none => simp [tailDecoded] at decoded
          | some tailResult =>
              rcases tailResult with ⟨tailFormulas, finalRest⟩
              have decoded' : some (childFormula :: tailFormulas, finalRest) =
                  some (formulas, rest) := by
                simpa [tailDecoded] using decoded
              have equal := Option.some.inj decoded'
              have restEqual : finalRest = rest := congrArg Prod.snd equal
              subst rest
              exact (ih childRest tailFormulas finalRest tailDecoded).trans
                (tagged_decodeRef_remaining_sublist fuel memory blocks child childFormula
                  childRest childDecoded)

private theorem decodeTaggedRefs_congr_except
    (left right : Memory payloadWidth) (fuel : Nat) :
    ∀ (blocks : List Block) (items : List (Word.Ref payloadWidth))
      (formulas : List (Tagged.Formula Nat)) (rest : List Block),
      blocks.Pairwise Block.Disjoint →
      decodeTaggedRefs left fuel blocks items = some (formulas, rest) →
      ReadsAgreeExcept left right blocks rest →
      decodeTaggedRefs right fuel blocks items = some (formulas, rest) := by
  intro blocks items
  induction items generalizing blocks with
  | nil =>
      intro formulas rest pairwise decoded agree
      simpa [decodeTaggedRefs] using decoded
  | cons child items ih =>
      intro formulas rest pairwise decoded agree
      simp only [decodeTaggedRefs] at decoded ⊢
      cases childDecoded : Tagged.Packed.decodeRef left fuel blocks child with
      | none => simp [childDecoded] at decoded
      | some childResult =>
          rcases childResult with ⟨childFormula, childRest⟩
          rw [childDecoded] at decoded
          cases tailDecoded : decodeTaggedRefs left fuel childRest items with
          | none => simp [tailDecoded] at decoded
          | some tailResult =>
              rcases tailResult with ⟨tailFormulas, finalRest⟩
              have decoded' : some (childFormula :: tailFormulas, finalRest) =
                  some (formulas, rest) := by
                simpa [tailDecoded] using decoded
              have decodedEqual := Option.some.inj decoded'
              have formulasEqual : childFormula :: tailFormulas = formulas :=
                congrArg Prod.fst decodedEqual
              have restEqual : finalRest = rest := congrArg Prod.snd decodedEqual
              subst formulas
              subst rest
              have tailSublist := decodeTaggedRefs_remaining_sublist left fuel childRest items
                tailFormulas finalRest tailDecoded
              have childRestSublist := tagged_decodeRef_remaining_sublist fuel left blocks child
                childFormula childRest childDecoded
              have childAgree : ReadsAgreeExcept left right blocks childRest := by
                intro candidate candidateMember candidateOutside
                exact agree candidate candidateMember fun inFinal =>
                  candidateOutside (tailSublist.subset inFinal)
              have childRight := tagged_decodeRef_congr_except fuel left right blocks child
                childFormula childRest pairwise childDecoded childAgree
              rw [childRight]
              have tailPairwise := List.Pairwise.sublist childRestSublist pairwise
              have tailAgree : ReadsAgreeExcept left right childRest finalRest := by
                intro candidate candidateMember candidateOutside
                exact agree candidate (childRestSublist.subset candidateMember) candidateOutside
              have tailRight :=
                ih childRest tailFormulas finalRest tailPairwise tailDecoded tailAgree
              simp [tailRight]

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

/-- Order-preserving view of retagging a proper child list. -/
private def retagRefs (fuel : Nat) (mode : Alternating.Mode) :
    Memory payloadWidth → List Block → List (Word.Ref payloadWidth) →
      Option (List (Word.Ref payloadWidth) × Memory payloadWidth × List Block)
  | memory, blocks, [] => some ([], memory, blocks)
  | memory, blocks, reference :: references => do
      let (target, memory, remaining) ← retagRef fuel mode memory blocks reference
      let (targets, memory, remaining) ←
        retagRefs fuel mode memory remaining references
      some (target :: targets, memory, remaining)

private theorem retag_fold_eq_retagRefs (fuel : Nat) (mode : Alternating.Mode) :
    ∀ (items : List (Word.Ref payloadWidth))
      (targetRev : List (Word.Ref payloadWidth)) (memory : Memory payloadWidth)
      (blocks : List Block),
      List.foldlM
          (fun (state : List (Word.Ref payloadWidth) × Memory payloadWidth ×
              List Block) child => do
            let (target, nextMemory, childRest) ←
              retagRef fuel mode state.2.1 state.2.2 child
            some (target :: state.1, nextMemory, childRest))
          (targetRev, memory, blocks) items = (do
        let (targets, after, remaining) ← retagRefs fuel mode memory blocks items
        some (targets.reverse ++ targetRev, after, remaining)) := by
  intro items
  induction items with
  | nil => intro targetRev memory blocks; rfl
  | cons child items ih =>
      intro targetRev memory blocks
      simp only [List.foldlM_cons, retagRefs]
      cases childRetagged : retagRef fuel mode memory blocks child with
      | none => simp
      | some childResult =>
          rcases childResult with ⟨targetChild, childMemory, childRest⟩
          cases tailRetagged : retagRefs fuel mode childMemory childRest items with
          | none => simp_all
          | some tailResult =>
              rcases tailResult with ⟨targetTail, after, finalRest⟩
              simp_all [List.reverse_cons, List.append_assoc]

/- A successful alternating decode is sufficient for structural retagging:
the transformer cannot run out of word width or block capacity, preserves the
allocator certificate, and changes no block still owned by its caller. -/
private theorem retagRef_of_decodeRef :
    ∀ (fuel : Nat) (mode : Alternating.Mode) (memory : Memory payloadWidth)
      (blocks : List Block) (reference : Word.Ref payloadWidth)
      (expr : Alternating.Expr Nat) (rest : List Block)
      (layout : Layout) (roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)),
      layout.Valid (Classical.Packed.Arena.mk memory roots) →
      blocks.Pairwise Block.Disjoint →
      blocks.Sublist layout.live →
      Alternating.Packed.decodeRef memory fuel mode blocks reference = some (expr, rest) →
      ∃ target after,
        retagRef fuel mode memory blocks reference = some (target, after, rest) ∧
        layout.Valid (Classical.Packed.Arena.mk after roots) ∧
        ReadsAgree memory after rest ∧
        ReadsAgreeOutside memory after blocks layout.live := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode memory blocks reference expr rest layout roots valid pairwise sublist decoded
      simp [Alternating.Packed.decodeRef] at decoded
  | succ fuel ih =>
      intro mode memory blocks reference expr rest layout roots valid pairwise sublist decoded
      simp only [Alternating.Packed.decodeRef] at decoded
      by_cases literal : reference.word.tag = 3
      · rw [dif_pos literal] at decoded
        have equal := Option.some.inj decoded
        have restEqual : blocks = rest := congrArg Prod.snd equal
        subst rest
        refine ⟨reference, memory, ?_, valid, readsAgree_refl memory blocks,
          readsAgreeOutside_refl memory blocks layout.live⟩
        simp [retagRef, literal]
      · rw [dif_neg literal] at decoded
        by_cases array : reference.word.tag = 0
        · rw [dif_pos array] at decoded
          cases taken : Layout.takeBase? blocks reference.word.base with
          | none => simp [taken] at decoded
          | some pair =>
              rcases pair with ⟨block, remaining⟩
              rw [taken] at decoded
              cases read : memory.read block with
              | none => simp [read] at decoded
              | some children =>
                  change (do
                    let children ← memory.read block
                    let result ← List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (childExpr, childRest) ←
                          Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                        some (childExpr :: state.1, childRest))
                      ([], remaining) children
                    some (Alternating.Expr.array reference.word.negative result.1.reverse,
                      result.2)) = some (expr, rest) at decoded
                  rw [read] at decoded
                  change (List.foldlM
                    (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                      let (childExpr, childRest) ←
                        Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                      some (childExpr :: state.1, childRest))
                    ([], remaining) children).bind
                      (fun result => some
                        (Alternating.Expr.array reference.word.negative result.1.reverse,
                          result.2)) = some (expr, rest) at decoded
                  cases folded : List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (childExpr, childRest) ←
                          Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                        some (childExpr :: state.1, childRest))
                      ([], remaining) children with
                  | none =>
                      rw [folded] at decoded
                      contradiction
                  | some result =>
                      rcases result with ⟨decodedRev, resultBlocks⟩
                      rw [folded] at decoded
                      have resultEqual := Option.some.inj decoded
                      have restEqual : resultBlocks = rest := congrArg Prod.snd resultEqual
                      subst rest
                      have selectedMemberBlocks : block ∈ blocks :=
                        (Layout.takeBase?_perm taken).mem_iff.mpr (by simp)
                      have selectedMemberLive : block ∈ layout.live :=
                        sublist.subset selectedMemberBlocks
                      have remainingSublist := takeBase?_rest_sublist taken
                      have remainingPairwise := List.Pairwise.sublist remainingSublist pairwise
                      have remainingLive := remainingSublist.trans sublist
                      have retagFold : ∀ (items : List (Word.Ref payloadWidth))
                          (sourceRev : List (Alternating.Expr Nat))
                          (owned : List Block) (sourceResult : List (Alternating.Expr Nat))
                          (sourceRest : List Block)
                          (current : Memory payloadWidth)
                          (targetRev : List (Word.Ref payloadWidth)),
                          List.foldlM
                              (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                                let (childExpr, childRest) ←
                                  Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                                some (childExpr :: state.1, childRest))
                              (sourceRev, owned) items = some (sourceResult, sourceRest) →
                          layout.Valid (Classical.Packed.Arena.mk current roots) →
                          owned.Pairwise Block.Disjoint →
                          owned.Sublist layout.live →
                          ReadsAgree memory current owned →
                          ∃ rewritten after,
                            List.foldlM
                                (fun (state : List (Word.Ref payloadWidth) ×
                                    Memory payloadWidth × List Block) child => do
                                  let (child, nextMemory, childRest) ←
                                    retagRef fuel mode.flip state.2.1 state.2.2 child
                                  some (child :: state.1, nextMemory, childRest))
                                (targetRev, current, owned) items =
                              some (rewritten, after, sourceRest) ∧
                            layout.Valid (Classical.Packed.Arena.mk after roots) ∧
                            ReadsAgree memory after sourceRest ∧
                            sourceRest.Sublist owned ∧
                            ReadsAgreeOutside current after owned layout.live ∧
                            rewritten.length = targetRev.length + items.length := by
                        intro items
                        induction items with
                        | nil =>
                            intro sourceRev owned sourceResult sourceRest current targetRev
                              sourceFold currentValid ownedPairwise ownedLive agree
                            have sourceEqual := Option.some.inj sourceFold
                            have sourceRestEqual : owned = sourceRest :=
                              congrArg Prod.snd sourceEqual
                            subst sourceRest
                            refine ⟨targetRev, current, rfl, currentValid, agree,
                              List.Sublist.refl owned,
                              readsAgreeOutside_refl current owned layout.live, ?_⟩
                            simp
                        | cons child items itemsIh =>
                            intro sourceRev owned sourceResult sourceRest current targetRev
                              sourceFold currentValid ownedPairwise ownedLive agree
                            simp only [List.foldlM_cons] at sourceFold ⊢
                            cases childDecoded : Alternating.Packed.decodeRef memory fuel mode.flip
                                owned child with
                            | none => simp [childDecoded] at sourceFold
                            | some childResult =>
                                rcases childResult with ⟨childExpr, childRest⟩
                                rw [childDecoded] at sourceFold
                                have currentDecoded :
                                    Alternating.Packed.decodeRef current fuel mode.flip owned
                                        child =
                                      some (childExpr, childRest) := by
                                  rw [← childDecoded]
                                  exact (alternating_decodeRef_congr fuel mode.flip owned child
                                    memory current agree).symm
                                have childPairwise := List.Pairwise.sublist
                                  (alternating_decodeRef_remaining_sublist fuel current mode.flip
                                    owned child childExpr childRest currentDecoded) ownedPairwise
                                have childLive :=
                                  (alternating_decodeRef_remaining_sublist fuel current mode.flip
                                    owned child childExpr childRest currentDecoded).trans ownedLive
                                obtain ⟨targetChild, childMemory, childRetagged,
                                    childValid, childAgree, childOutside⟩ :=
                                  ih mode.flip current owned child childExpr childRest layout roots
                                    currentValid ownedPairwise ownedLive currentDecoded
                                rw [childRetagged]
                                have baseToChild : ReadsAgree memory childMemory childRest :=
                                  (readsAgree_mono agree
                                    (alternating_decodeRef_remaining childDecoded)).trans childAgree
                                obtain ⟨rewritten, after, tailRetagged, afterValid, afterAgree,
                                    tailSublist, tailOutside, rewrittenLength⟩ :=
                                  itemsIh (childExpr :: sourceRev) childRest sourceResult sourceRest
                                    childMemory (targetChild :: targetRev) sourceFold childValid
                                    childPairwise childLive baseToChild
                                change ∃ rewritten after,
                                  List.foldlM
                                      (fun (state : List (Word.Ref payloadWidth) ×
                                          Memory payloadWidth × List Block) child => do
                                        let (next, nextMemory, nextRest) ←
                                          retagRef fuel mode.flip state.2.1 state.2.2 child
                                        some (next :: state.1, nextMemory, nextRest))
                                      (targetChild :: targetRev, childMemory, childRest) items =
                                    some (rewritten, after, sourceRest) ∧
                                  layout.Valid (Classical.Packed.Arena.mk after roots) ∧
                                  ReadsAgree memory after sourceRest ∧
                                  sourceRest.Sublist owned ∧
                                  ReadsAgreeOutside current after owned layout.live ∧
                                  rewritten.length = targetRev.length + (child :: items).length
                                have outsideCombined :
                                    ReadsAgreeOutside current after owned layout.live := by
                                  intro candidate candidateLive candidateOutside
                                  have childRestSubset :=
                                    (alternating_decodeRef_remaining_sublist fuel current
                                      mode.flip owned child childExpr childRest
                                      currentDecoded).subset
                                  exact
                                    (childOutside candidate candidateLive candidateOutside).trans
                                      (tailOutside candidate candidateLive fun inChildRest =>
                                        candidateOutside (childRestSubset inChildRest))
                                refine ⟨rewritten, after, tailRetagged, afterValid,
                                  afterAgree, tailSublist.trans
                                    (alternating_decodeRef_remaining_sublist fuel memory mode.flip
                                      owned child childExpr childRest childDecoded),
                                  outsideCombined, ?_⟩
                                simp only [List.length_cons] at rewrittenLength ⊢
                                omega
                      obtain ⟨rewritten, childrenMemory, childrenRetagged, childrenValid,
                          childrenAgree, resultSublist, childrenOutside,
                          rewrittenLength⟩ :=
                        retagFold children [] remaining decodedRev resultBlocks memory [] folded
                          valid remainingPairwise remainingLive
                          (readsAgree_refl memory remaining)
                      have rewrittenRoom : rewritten.length < block.capacity := by
                        simpa [rewrittenLength] using read_length_lt read
                      have blockFits : block.Fits childrenMemory.words.size :=
                        childrenValid.live_fit selectedMemberLive
                      have writeExists : ∃ after,
                          childrenMemory.write? block rewritten.reverse = some after := by
                        unfold Memory.write?
                        rw [if_pos blockFits]
                        unfold encodeWords
                        rw [if_pos (by simpa using rewrittenRoom)]
                        exact ⟨_, rfl⟩
                      obtain ⟨after, written⟩ := writeExists
                      obtain ⟨target, targetEncoded⟩ := pointerRef?_array mode reference array
                      have afterValid := valid_write (roots' := roots) childrenValid
                        selectedMemberLive written
                      have afterAgree : ReadsAgree memory after resultBlocks :=
                        childrenAgree.trans
                          (readsAgree_mono (write_readsAgree_rest pairwise taken written)
                            resultSublist.subset)
                      have outsideAfter :
                          ReadsAgreeOutside memory after blocks layout.live := by
                        intro candidate candidateLive candidateOutside
                        exact (childrenOutside candidate candidateLive fun inRemaining =>
                          candidateOutside (remainingSublist.subset inRemaining)).trans
                          (write_readsAgreeOutside
                            ((List.pairwise_append.mp valid.disjoint).1)
                            selectedMemberBlocks sublist written candidate candidateLive
                            candidateOutside)
                      refine ⟨target, after, ?_, afterValid, afterAgree, outsideAfter⟩
                      simp only [retagRef]
                      rw [dif_neg literal, dif_pos array]
                      rw [taken]
                      change (do
                        let children ← memory.read block
                        let result ← List.foldlM
                          (fun (state : List (Word.Ref payloadWidth) ×
                              Memory payloadWidth × List Block) child => do
                            let (next, nextMemory, nextRest) ←
                              retagRef fuel mode.flip state.2.1 state.2.2 child
                            some (next :: state.1, nextMemory, nextRest))
                          ([], memory, remaining) children
                        let nextMemory ← result.2.1.write? block result.1.reverse
                        let nextReference ← pointerRef? payloadWidth reference.word.base
                          (nodeTag mode) reference.word.negative
                        some (nextReference, nextMemory, result.2.2)) =
                          some (target, after, resultBlocks)
                      rw [read]
                      change (List.foldlM
                        (fun (state : List (Word.Ref payloadWidth) ×
                            Memory payloadWidth × List Block) child => do
                          let (next, nextMemory, nextRest) ←
                            retagRef fuel mode.flip state.2.1 state.2.2 child
                          some (next :: state.1, nextMemory, nextRest))
                        ([], memory, remaining) children).bind
                          (fun result => do
                            let nextMemory ← result.2.1.write? block result.1.reverse
                            let nextReference ← pointerRef? payloadWidth reference.word.base
                              (nodeTag mode) reference.word.negative
                            some (nextReference, nextMemory, result.2.2)) =
                        some (target, after, resultBlocks)
                      rw [childrenRetagged]
                      change (do
                        let nextMemory ← childrenMemory.write? block rewritten.reverse
                        let nextReference ← pointerRef? payloadWidth reference.word.base
                          (nodeTag mode) reference.word.negative
                        some (nextReference, nextMemory, resultBlocks)) =
                          some (target, after, resultBlocks)
                      rw [written, targetEncoded]
                      change some (target, after, resultBlocks) =
                        some (target, after, resultBlocks)
                      rfl
        · rw [dif_neg array] at decoded
          contradiction

/- Structural retagging is the concrete realization of the abstract
alternating-to-tagged embedding.  In particular, no abstract equality check is
needed to establish the result of a successful rewrite. -/
private theorem retagRef_decode_commutes :
    ∀ (fuel : Nat) (mode : Alternating.Mode) (memory : Memory payloadWidth)
      (blocks : List Block) (reference : Word.Ref payloadWidth)
      (expr : Alternating.Expr Nat) (rest : List Block)
      (target : Word.Ref payloadWidth) (after : Memory payloadWidth)
      (layout : Layout) (roots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)),
      layout.Valid (Classical.Packed.Arena.mk memory roots) →
      blocks.Pairwise Block.Disjoint →
      blocks.Sublist layout.live →
      Alternating.Packed.decodeRef memory fuel mode blocks reference = some (expr, rest) →
      retagRef fuel mode memory blocks reference = some (target, after, rest) →
      Tagged.Packed.decodeRef after fuel blocks target =
        some (AlternatingToTagged.formula mode expr, rest) := by
  intro fuel
  induction fuel with
  | zero =>
      intro mode memory blocks reference expr rest target after layout roots valid pairwise
        live decoded retagged
      simp [Alternating.Packed.decodeRef] at decoded
  | succ fuel ih =>
      intro mode memory blocks reference expr rest target after layout roots valid pairwise
        live decoded retagged
      have retagList : ∀ (items : List (Word.Ref payloadWidth))
          (base current : Memory payloadWidth) (owned : List Block)
          (exprs : List (Alternating.Expr Nat)) (sourceRest : List Block)
          (targets : List (Word.Ref payloadWidth)) (result : Memory payloadWidth),
          layout.Valid (Classical.Packed.Arena.mk current roots) →
          owned.Pairwise Block.Disjoint →
          owned.Sublist layout.live →
          ReadsAgree base current owned →
          decodeAlternatingRefs base fuel mode.flip owned items =
            some (exprs, sourceRest) →
          retagRefs fuel mode.flip current owned items =
            some (targets, result, sourceRest) →
          layout.Valid (Classical.Packed.Arena.mk result roots) ∧
          ReadsAgree base result sourceRest ∧
          ReadsAgreeOutside current result owned layout.live ∧
          decodeTaggedRefs result fuel owned targets =
            some (exprs.map (AlternatingToTagged.formula mode.flip), sourceRest) := by
        intro items
        induction items with
        | nil =>
            intro base current owned exprs sourceRest targets result currentValid
              ownedPairwise ownedLive agree sourceDecoded targetRetagged
            simp only [decodeAlternatingRefs] at sourceDecoded
            simp only [retagRefs] at targetRetagged
            have sourceEqual := Option.some.inj sourceDecoded
            have targetEqual := Option.some.inj targetRetagged
            have exprsEqual : [] = exprs := congrArg Prod.fst sourceEqual
            have sourceRestEqual : owned = sourceRest := congrArg Prod.snd sourceEqual
            have targetsEqual : [] = targets := congrArg Prod.fst targetEqual
            have resultEqual : current = result := congrArg (fun value => value.2.1) targetEqual
            subst exprs
            subst sourceRest
            subst targets
            subst result
            exact ⟨currentValid, agree,
              readsAgreeOutside_refl current owned layout.live, rfl⟩
        | cons child items itemsIh =>
            intro base current owned exprs sourceRest targets result currentValid
              ownedPairwise ownedLive agree sourceDecoded targetRetagged
            simp only [decodeAlternatingRefs] at sourceDecoded
            cases childDecoded : Alternating.Packed.decodeRef base fuel mode.flip owned child with
            | none => simp [childDecoded] at sourceDecoded
            | some childResult =>
                rcases childResult with ⟨childExpr, childRest⟩
                rw [childDecoded] at sourceDecoded
                cases tailDecoded : decodeAlternatingRefs base fuel mode.flip childRest items with
                | none => simp [tailDecoded] at sourceDecoded
                | some tailResult =>
                    rcases tailResult with ⟨tailExprs, finalRest⟩
                    have sourceDecoded' : some (childExpr :: tailExprs, finalRest) =
                        some (exprs, sourceRest) := by
                      simpa [tailDecoded] using sourceDecoded
                    have sourceEqual := Option.some.inj sourceDecoded'
                    have exprsEqual : childExpr :: tailExprs = exprs :=
                      congrArg Prod.fst sourceEqual
                    have restEqual : finalRest = sourceRest :=
                      congrArg Prod.snd sourceEqual
                    subst exprs
                    subst sourceRest
                    have currentDecoded :
                        Alternating.Packed.decodeRef current fuel mode.flip owned child =
                          some (childExpr, childRest) := by
                      rw [← childDecoded]
                      exact (alternating_decodeRef_congr fuel mode.flip owned child base current
                        agree).symm
                    have childRestSublist :=
                      alternating_decodeRef_remaining_sublist fuel current mode.flip owned child
                        childExpr childRest currentDecoded
                    have childPairwise := List.Pairwise.sublist childRestSublist ownedPairwise
                    have childLive := childRestSublist.trans ownedLive
                    obtain ⟨targetChild, childMemory, childRetagged, childValid,
                        childAgree, childOutside⟩ :=
                      retagRef_of_decodeRef fuel mode.flip current owned child childExpr childRest
                        layout roots currentValid ownedPairwise ownedLive currentDecoded
                    have childTagged :=
                      ih mode.flip current owned child childExpr childRest targetChild childMemory
                        layout roots currentValid ownedPairwise ownedLive currentDecoded
                        childRetagged
                    simp only [retagRefs] at targetRetagged
                    rw [childRetagged] at targetRetagged
                    cases tailRetagged : retagRefs fuel mode.flip childMemory childRest items with
                    | none => simp [tailRetagged] at targetRetagged
                    | some tailTarget =>
                        rcases tailTarget with ⟨targetTail, tailMemory, tailRest⟩
                        have targetRetagged' :
                            some (targetChild :: targetTail, tailMemory, tailRest) =
                              some (targets, result, finalRest) := by
                          simpa [tailRetagged] using targetRetagged
                        have targetEqual := Option.some.inj targetRetagged'
                        have targetsEqual : targetChild :: targetTail = targets :=
                          congrArg Prod.fst targetEqual
                        have resultEqual : tailMemory = result :=
                          congrArg (fun value => value.2.1) targetEqual
                        have tailRestEqual : tailRest = finalRest :=
                          congrArg (fun value => value.2.2) targetEqual
                        subst targets
                        subst result
                        subst tailRest
                        have baseToChild : ReadsAgree base childMemory childRest :=
                          (readsAgree_mono agree childRestSublist.subset).trans childAgree
                        obtain ⟨tailValid, tailAgree, tailOutside, tailTagged⟩ :=
                          itemsIh base childMemory childRest tailExprs finalRest targetTail
                            tailMemory childValid childPairwise childLive baseToChild tailDecoded
                            tailRetagged
                        have childFinal :
                            Tagged.Packed.decodeRef tailMemory fuel owned targetChild =
                              some
                                (AlternatingToTagged.formula mode.flip childExpr,
                                  childRest) := by
                          apply tagged_decodeRef_congr_except fuel childMemory tailMemory owned
                            targetChild (AlternatingToTagged.formula mode.flip childExpr) childRest
                            ownedPairwise childTagged
                          intro candidate candidateMember candidateOutside
                          exact tailOutside candidate
                            (ownedLive.subset candidateMember) candidateOutside
                        have outsideCombined :
                            ReadsAgreeOutside current tailMemory owned layout.live := by
                          intro candidate candidateLive candidateOutside
                          have childRestSubset := childRestSublist.subset
                          exact (childOutside candidate candidateLive candidateOutside).trans
                            (tailOutside candidate candidateLive fun inChildRest =>
                              candidateOutside (childRestSubset inChildRest))
                        refine ⟨tailValid, tailAgree, outsideCombined, ?_⟩
                        simp [decodeTaggedRefs, childFinal, tailTagged]
      simp only [Alternating.Packed.decodeRef] at decoded
      by_cases literal : reference.word.tag = 3
      · rw [dif_pos literal] at decoded
        have sourceEqual := Option.some.inj decoded
        have exprEqual :
            (Alternating.Syn.literal ⟨reference.word.base / 4,
              reference.word.negative⟩ : Alternating.Expr Nat) = expr :=
          congrArg Prod.fst sourceEqual
        have restEqual : blocks = rest := congrArg Prod.snd sourceEqual
        subst expr
        subst rest
        have targetEqual : (reference, memory, blocks) = (target, after, blocks) := by
          exact Option.some.inj (by simpa [retagRef, literal] using retagged)
        have referenceEqual : reference = target := congrArg Prod.fst targetEqual
        have memoryEqual : memory = after := congrArg (fun value => value.2.1) targetEqual
        subst target
        subst after
        simp [Tagged.Packed.decodeRef, literal]
        cases mode <;> simp [AlternatingToTagged.formula]
      · rw [dif_neg literal] at decoded
        by_cases array : reference.word.tag = 0
        · rw [dif_pos array] at decoded
          cases taken : Layout.takeBase? blocks reference.word.base with
          | none => simp [taken] at decoded
          | some selected =>
              rcases selected with ⟨block, remaining⟩
              rw [taken] at decoded
              cases read : memory.read block with
              | none => simp_all
              | some children =>
                  have decodedAfterRead :
                      (List.foldlM
                          (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                            let (childExpr, childRest) ←
                              Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                            some (childExpr :: state.1, childRest))
                          ([], remaining) children).bind
                            (fun result => some
                              (Alternating.Expr.array reference.word.negative
                                result.1.reverse, result.2)) = some (expr, rest) := by
                    simpa [read] using decoded
                  cases sourceFold : List.foldlM
                      (fun (state : List (Alternating.Expr Nat) × List Block) child => do
                        let (childExpr, childRest) ←
                          Alternating.Packed.decodeRef memory fuel mode.flip state.2 child
                        some (childExpr :: state.1, childRest))
                      ([], remaining) children with
                  | none => simp_all
                  | some sourceResult =>
                      rcases sourceResult with ⟨decodedRev, resultBlocks⟩
                      have decoded' :
                          some (Alternating.Expr.array reference.word.negative
                            decodedRev.reverse, resultBlocks) = some (expr, rest) := by
                        rw [sourceFold] at decodedAfterRead
                        exact decodedAfterRead
                      have sourceEqual := Option.some.inj decoded'
                      have exprEqual :
                          Alternating.Expr.array reference.word.negative decodedRev.reverse =
                            expr := congrArg Prod.fst sourceEqual
                      have restEqual : resultBlocks = rest := congrArg Prod.snd sourceEqual
                      subst expr
                      subst rest
                      have sourceFoldView :=
                        alternating_fold_eq_decodeRefs memory fuel mode.flip children [] remaining
                      rw [sourceFold] at sourceFoldView
                      cases childrenDecoded :
                          decodeAlternatingRefs memory fuel mode.flip remaining children with
                      | none => simp [childrenDecoded] at sourceFoldView
                      | some sourceChildrenResult =>
                          rcases sourceChildrenResult with ⟨sourceChildren, sourceChildrenRest⟩
                          rw [childrenDecoded] at sourceFoldView
                          have sourceViewEqual := Option.some.inj sourceFoldView
                          have decodedRevEqual : decodedRev = sourceChildren.reverse :=
                            by simpa using congrArg Prod.fst sourceViewEqual
                          have sourceRestEqual : resultBlocks = sourceChildrenRest :=
                            congrArg Prod.snd sourceViewEqual
                          subst decodedRev
                          subst sourceChildrenRest
                          simp only [retagRef] at retagged
                          have notLiteral : reference.word.tag ≠ 3 := by omega
                          rw [dif_neg notLiteral, dif_pos array] at retagged
                          have retaggedAfterRead :
                              (List.foldlM
                                  (fun (state : List (Word.Ref payloadWidth) ×
                                      Memory payloadWidth × List Block) child =>
                                    (retagRef fuel mode.flip state.2.1 state.2.2 child).bind
                                      fun next => some (next.1 :: state.1, next.2))
                                  ([], memory, remaining) children).bind
                                    (fun result =>
                                      (result.2.1.write? block result.1.reverse).bind
                                        fun nextMemory =>
                                          (pointerRef? payloadWidth reference.word.base
                                            (nodeTag mode) reference.word.negative).bind
                                              fun nextReference => some
                                                (nextReference, nextMemory, result.2.2)) =
                                some (target, after, resultBlocks) := by
                            simpa [taken, read] using retagged
                          cases targetFold : List.foldlM
                              (fun (state : List (Word.Ref payloadWidth) ×
                                  Memory payloadWidth × List Block) child =>
                                (retagRef fuel mode.flip state.2.1 state.2.2 child).bind
                                  fun next => some (next.1 :: state.1, next.2))
                              ([], memory, remaining) children with
                          | none => simp [targetFold] at retaggedAfterRead
                          | some targetFoldResult =>
                              rcases targetFoldResult with
                                ⟨rewrittenRev, childrenMemory, targetRest⟩
                              rw [targetFold] at retaggedAfterRead
                              cases written : childrenMemory.write? block rewrittenRev.reverse with
                              | none => simp_all
                              | some finalMemory =>
                                  have retaggedAfterWrite :
                                      (pointerRef? payloadWidth reference.word.base
                                        (nodeTag mode) reference.word.negative).bind
                                          (fun targetReference => some
                                            (targetReference, finalMemory, targetRest)) =
                                        some (target, after, resultBlocks) := by
                                    simpa [written] using retaggedAfterRead
                                  cases targetEncoded : pointerRef? payloadWidth
                                      reference.word.base (nodeTag mode)
                                      reference.word.negative with
                                  | none => simp [targetEncoded] at retaggedAfterWrite
                                  | some targetReference =>
                                      rw [targetEncoded] at retaggedAfterWrite
                                      have retagEqual := Option.some.inj retaggedAfterWrite
                                      have targetEqual : targetReference = target :=
                                        congrArg Prod.fst retagEqual
                                      have afterEqual : finalMemory = after :=
                                        congrArg (fun value => value.2.1) retagEqual
                                      have targetRestEqual : targetRest = resultBlocks :=
                                        congrArg (fun value => value.2.2) retagEqual
                                      subst target
                                      subst after
                                      subst targetRest
                                      have targetFoldForView : List.foldlM
                                          (fun (state : List (Word.Ref payloadWidth) ×
                                              Memory payloadWidth × List Block) child => do
                                            let (next, nextMemory, nextRest) ←
                                              retagRef fuel mode.flip state.2.1 state.2.2 child
                                            some (next :: state.1, nextMemory, nextRest))
                                          ([], memory, remaining) children =
                                            some (rewrittenRev, childrenMemory,
                                              resultBlocks) := by
                                        exact targetFold
                                      have targetFoldView :=
                                        retag_fold_eq_retagRefs fuel mode.flip children [] memory
                                          remaining
                                      rw [targetFoldForView] at targetFoldView
                                      cases childrenRetagged :
                                          retagRefs fuel mode.flip memory remaining children with
                                      | none => simp [childrenRetagged] at targetFoldView
                                      | some targetChildrenResult =>
                                          rcases targetChildrenResult with
                                            ⟨targetChildren, targetChildrenMemory,
                                              targetChildrenRest⟩
                                          rw [childrenRetagged] at targetFoldView
                                          have targetViewEqual := Option.some.inj targetFoldView
                                          have rewrittenEqual :
                                              rewrittenRev = targetChildren.reverse :=
                                            by simpa using congrArg Prod.fst targetViewEqual
                                          have childrenMemoryEqual :
                                              childrenMemory = targetChildrenMemory :=
                                            congrArg (fun value => value.2.1) targetViewEqual
                                          have targetChildrenRestEqual :
                                              resultBlocks = targetChildrenRest :=
                                            congrArg (fun value => value.2.2) targetViewEqual
                                          subst rewrittenRev
                                          subst targetChildrenMemory
                                          subst targetChildrenRest
                                          have remainingSublist := takeBase?_rest_sublist taken
                                          have remainingPairwise := List.Pairwise.sublist
                                            remainingSublist pairwise
                                          have remainingLive := remainingSublist.trans live
                                          obtain ⟨childrenValid, childrenAgree,
                                              childrenOutside, childrenTagged⟩ :=
                                            retagList children memory memory remaining
                                              sourceChildren resultBlocks targetChildren
                                              childrenMemory valid remainingPairwise remainingLive
                                              (readsAgree_refl memory remaining) childrenDecoded
                                              childrenRetagged
                                          have writtenTargets :
                                              childrenMemory.write? block targetChildren =
                                                some finalMemory := by
                                            simpa using written
                                          have remainingWriteAgree :=
                                            write_readsAgree_rest pairwise taken writtenTargets
                                          have childrenTaggedFinal :
                                              decodeTaggedRefs finalMemory fuel remaining
                                                  targetChildren =
                                                some (sourceChildren.map
                                                  (AlternatingToTagged.formula mode.flip),
                                                  resultBlocks) := by
                                            apply decodeTaggedRefs_congr_except childrenMemory
                                              finalMemory fuel remaining targetChildren
                                              (sourceChildren.map
                                                (AlternatingToTagged.formula mode.flip))
                                              resultBlocks remainingPairwise childrenTagged
                                            intro candidate candidateMember candidateOutside
                                            exact remainingWriteAgree candidate candidateMember
                                          have fields := pointerRef?_fields targetEncoded
                                          have targetNotLiteral : targetReference.word.tag ≠ 3 := by
                                            rw [fields.2.1]
                                            cases mode <;> decide
                                          have targetDecodedShape :
                                              Tagged.Packed.decodeRef finalMemory (fuel + 1)
                                                  blocks targetReference =
                                                (List.foldlM
                                                    (fun (state : List (Tagged.Formula Nat) ×
                                                        List Block) child =>
                                                      (Tagged.Packed.decodeRef finalMemory fuel
                                                        state.2 child).bind fun decoded =>
                                                          some (decoded.1 :: state.1,
                                                            decoded.2))
                                                    ([], remaining) targetChildren).bind
                                                      (fun result =>
                                                        (Tagged.Packed.node
                                                          targetReference.word.tag
                                                          targetReference.word.negative
                                                          result.1.reverse).bind fun formula =>
                                                            some (formula, result.2)) := by
                                            simp [Tagged.Packed.decodeRef, targetNotLiteral,
                                              fields.1, taken,
                                              Memory.write?_read writtenTargets]
                                          rw [targetDecodedShape]
                                          have taggedFoldView :=
                                            tagged_fold_eq_decodeRefs finalMemory fuel
                                              targetChildren [] remaining
                                          rw [childrenTaggedFinal] at taggedFoldView
                                          have taggedFold : List.foldlM
                                              (fun (state : List (Tagged.Formula Nat) ×
                                                  List Block) child =>
                                                (Tagged.Packed.decodeRef finalMemory fuel state.2
                                                  child).bind fun decoded =>
                                                    some (decoded.1 :: state.1, decoded.2))
                                              ([], remaining) targetChildren =
                                                some ((sourceChildren.map
                                                  (AlternatingToTagged.formula mode.flip)).reverse,
                                                  resultBlocks) := by
                                            simpa using taggedFoldView
                                          rw [taggedFold]
                                          rw [fields.2.1, fields.2.2]
                                          cases mode <;>
                                            simp [Tagged.Packed.node, nodeTag,
                                              Alternating.Mode.flip]
        · rw [dif_neg array] at decoded
          contradiction

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

private theorem retagRoots_of_decodeRoots :
    ∀ (sourceRoots : List (Word.Ref payloadWidth × Word.Ref payloadWidth))
      (memory : Memory payloadWidth) (fuel : Nat) (blocks : List Block)
      (sequents : List (Alternating.Sequent Nat)) (rest : List Block)
      (layout : Layout)
      (certificateRoots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)),
      layout.Valid (Classical.Packed.Arena.mk memory certificateRoots) →
      blocks.Pairwise Block.Disjoint →
      blocks.Sublist layout.live →
      Alternating.Packed.decodeRoots memory fuel blocks sourceRoots =
        some (sequents, rest) →
      ∃ targetRoots after,
        retagRoots fuel memory blocks sourceRoots = some (targetRoots, after, rest) ∧
        layout.Valid (Classical.Packed.Arena.mk after certificateRoots) ∧
        ReadsAgree memory after rest ∧
        ReadsAgreeOutside memory after blocks layout.live := by
  intro sourceRoots
  induction sourceRoots with
  | nil =>
      intro memory fuel blocks sequents rest layout certificateRoots valid pairwise
        live decoded
      simp only [Alternating.Packed.decodeRoots] at decoded
      have equal := Option.some.inj decoded
      have restEqual : blocks = rest := congrArg Prod.snd equal
      subst rest
      exact ⟨[], memory, rfl, valid, readsAgree_refl memory blocks,
        readsAgreeOutside_refl memory blocks layout.live⟩
  | cons sourceRoot sourceRoots rootsIh =>
      rcases sourceRoot with ⟨left, right⟩
      intro memory fuel blocks sequents rest layout certificateRoots valid pairwise
        live decoded
      simp only [Alternating.Packed.decodeRoots] at decoded
      cases leftDecoded : Alternating.Packed.decodeRef memory fuel .all blocks left with
      | none => simp [leftDecoded] at decoded
      | some leftResult =>
          rcases leftResult with ⟨leftExpr, afterLeft⟩
          rw [leftDecoded] at decoded
          change (do
            let rightResult ← Alternating.Packed.decodeRef memory fuel .any afterLeft right
            let tail ← Alternating.Packed.decodeRoots memory fuel rightResult.2 sourceRoots
            some (Alternating.Sequent.mk leftExpr rightResult.1 :: tail.1, tail.2)) =
              some (sequents, rest) at decoded
          cases rightDecoded : Alternating.Packed.decodeRef memory fuel .any afterLeft right with
          | none => simp [rightDecoded] at decoded
          | some rightResult =>
              rcases rightResult with ⟨rightExpr, afterRight⟩
              rw [rightDecoded] at decoded
              change (Alternating.Packed.decodeRoots memory fuel afterRight sourceRoots).bind
                  (fun tail => some
                    (Alternating.Sequent.mk leftExpr rightExpr :: tail.1, tail.2)) =
                some (sequents, rest) at decoded
              cases rootsDecoded : Alternating.Packed.decodeRoots memory fuel afterRight
                  sourceRoots with
              | none => simp [rootsDecoded] at decoded
              | some rootsResult =>
                  rcases rootsResult with ⟨tailSequents, finalRest⟩
                  rw [rootsDecoded] at decoded
                  have decodedEqual := Option.some.inj decoded
                  have restEqual : finalRest = rest := congrArg Prod.snd decodedEqual
                  subst rest
                  have afterLeftSublist :=
                    alternating_decodeRef_remaining_sublist fuel memory .all blocks left
                      leftExpr afterLeft leftDecoded
                  have afterRightSublist :=
                    alternating_decodeRef_remaining_sublist fuel memory .any afterLeft right
                      rightExpr afterRight rightDecoded
                  have afterLeftPairwise := List.Pairwise.sublist afterLeftSublist pairwise
                  have afterLeftLive := afterLeftSublist.trans live
                  obtain ⟨targetLeft, leftMemory, leftRetagged, leftValid, leftAgree,
                      leftOutside⟩ :=
                    retagRef_of_decodeRef fuel .all memory blocks left leftExpr afterLeft layout
                      certificateRoots valid pairwise live leftDecoded
                  have currentRightDecoded :
                      Alternating.Packed.decodeRef leftMemory fuel .any afterLeft right =
                        some (rightExpr, afterRight) := by
                    rw [← rightDecoded]
                    exact (alternating_decodeRef_congr fuel .any afterLeft right memory
                      leftMemory leftAgree).symm
                  have afterRightPairwise := List.Pairwise.sublist afterRightSublist
                    afterLeftPairwise
                  have afterRightLive := afterRightSublist.trans afterLeftLive
                  obtain ⟨targetRight, rightMemory, rightRetagged, rightValid, rightAgree,
                      rightOutside⟩ :=
                    retagRef_of_decodeRef fuel .any leftMemory afterLeft right rightExpr
                      afterRight layout certificateRoots leftValid afterLeftPairwise afterLeftLive
                      currentRightDecoded
                  have memoryToRight : ReadsAgree memory rightMemory afterRight :=
                    (readsAgree_mono leftAgree afterRightSublist.subset).trans rightAgree
                  have currentRootsDecoded :
                      Alternating.Packed.decodeRoots rightMemory fuel afterRight sourceRoots =
                        some (tailSequents, finalRest) := by
                    rw [← rootsDecoded]
                    exact (alternating_decodeRoots_congr sourceRoots memory rightMemory fuel
                      afterRight memoryToRight).symm
                  obtain ⟨targetTail, after, tailRetagged, afterValid, tailAgree,
                      tailOutside⟩ :=
                    rootsIh rightMemory fuel afterRight tailSequents finalRest layout
                      certificateRoots rightValid afterRightPairwise afterRightLive
                      currentRootsDecoded
                  have memoryToAfter : ReadsAgree memory after finalRest :=
                    (readsAgree_mono memoryToRight
                      (alternating_decodeRoots_remaining_sublist sourceRoots memory fuel
                        afterRight tailSequents finalRest rootsDecoded).subset).trans
                      tailAgree
                  have outsideAfter :
                      ReadsAgreeOutside memory after blocks layout.live := by
                    intro candidate candidateLive candidateOutside
                    have outsideAfterLeft : candidate ∉ afterLeft := fun member =>
                      candidateOutside (afterLeftSublist.subset member)
                    have outsideAfterRight : candidate ∉ afterRight := fun member =>
                      outsideAfterLeft (afterRightSublist.subset member)
                    exact (leftOutside candidate candidateLive candidateOutside).trans
                      ((rightOutside candidate candidateLive outsideAfterLeft).trans
                        (tailOutside candidate candidateLive outsideAfterRight))
                  refine ⟨(targetLeft, targetRight) :: targetTail, after, ?_, afterValid,
                    memoryToAfter, outsideAfter⟩
                  simp only [retagRoots]
                  rw [leftRetagged]
                  change (do
                    let rightResult ← retagRef fuel .any leftMemory afterLeft right
                    let tailResult ← retagRoots fuel rightResult.2.1 rightResult.2.2 sourceRoots
                    some ((targetLeft, rightResult.1) :: tailResult.1,
                      tailResult.2.1, tailResult.2.2)) =
                      some ((targetLeft, targetRight) :: targetTail, after, finalRest)
                  rw [rightRetagged]
                  change (do
                    let tailResult ← retagRoots fuel rightMemory afterRight sourceRoots
                    some ((targetLeft, targetRight) :: tailResult.1,
                      tailResult.2.1, tailResult.2.2)) =
                      some ((targetLeft, targetRight) :: targetTail, after, finalRest)
                  rw [tailRetagged]
                  change some ((targetLeft, targetRight) :: targetTail, after, finalRest) =
                    some ((targetLeft, targetRight) :: targetTail, after, finalRest)
                  rfl

private theorem retagRoots_decode_commutes :
    ∀ (sourceRoots : List (Word.Ref payloadWidth × Word.Ref payloadWidth))
      (memory : Memory payloadWidth) (fuel : Nat) (blocks : List Block)
      (sequents : List (Alternating.Sequent Nat)) (rest : List Block)
      (targetRoots : List (Word.Ref payloadWidth × Word.Ref payloadWidth))
      (after : Memory payloadWidth) (layout : Layout)
      (certificateRoots : List (Word.Ref payloadWidth × Word.Ref payloadWidth)),
      layout.Valid (Classical.Packed.Arena.mk memory certificateRoots) →
      blocks.Pairwise Block.Disjoint →
      blocks.Sublist layout.live →
      Alternating.Packed.decodeRoots memory fuel blocks sourceRoots =
        some (sequents, rest) →
      retagRoots fuel memory blocks sourceRoots = some (targetRoots, after, rest) →
      Tagged.Packed.decodeRoots after fuel blocks targetRoots =
        some (AlternatingToTagged.arena sequents, rest) := by
  intro sourceRoots
  induction sourceRoots with
  | nil =>
      intro memory fuel blocks sequents rest targetRoots after layout certificateRoots
        valid pairwise live sourceDecoded targetRetagged
      simp only [Alternating.Packed.decodeRoots] at sourceDecoded
      have sourceEqual := Option.some.inj sourceDecoded
      have sequentsEqual : [] = sequents := congrArg Prod.fst sourceEqual
      have restEqual : blocks = rest := congrArg Prod.snd sourceEqual
      subst sequents
      subst rest
      simp only [retagRoots] at targetRetagged
      have targetEqual := Option.some.inj targetRetagged
      have rootsEqual : [] = targetRoots := congrArg Prod.fst targetEqual
      have memoryEqual : memory = after := congrArg (fun value => value.2.1) targetEqual
      subst targetRoots
      subst after
      rfl
  | cons sourceRoot sourceRoots rootsIh =>
      rcases sourceRoot with ⟨left, right⟩
      intro memory fuel blocks sequents rest targetRoots after layout certificateRoots
        valid pairwise live sourceDecoded targetRetagged
      simp only [Alternating.Packed.decodeRoots] at sourceDecoded
      cases leftDecoded : Alternating.Packed.decodeRef memory fuel .all blocks left with
      | none => simp [leftDecoded] at sourceDecoded
      | some leftResult =>
          rcases leftResult with ⟨leftExpr, afterLeft⟩
          rw [leftDecoded] at sourceDecoded
          have sourceAfterLeft :
              (do
                let (rightExpr, afterRight) ←
                  Alternating.Packed.decodeRef memory fuel .any afterLeft right
                let (tailSequents, finalRest) ←
                  Alternating.Packed.decodeRoots memory fuel afterRight sourceRoots
                some (Alternating.Sequent.mk leftExpr rightExpr :: tailSequents,
                  finalRest)) = some (sequents, rest) := by
            simpa using sourceDecoded
          cases rightDecoded : Alternating.Packed.decodeRef memory fuel .any afterLeft right with
          | none => simp [rightDecoded] at sourceAfterLeft
          | some rightResult =>
              rcases rightResult with ⟨rightExpr, afterRight⟩
              have sourceAfterRight :
                  (do
                    let (tailSequents, finalRest) ←
                      Alternating.Packed.decodeRoots memory fuel afterRight sourceRoots
                    some (Alternating.Sequent.mk leftExpr rightExpr :: tailSequents,
                      finalRest)) = some (sequents, rest) := by
                simpa [rightDecoded] using sourceAfterLeft
              cases tailDecoded : Alternating.Packed.decodeRoots memory fuel afterRight
                  sourceRoots with
              | none => simp [tailDecoded] at sourceAfterRight
              | some tailResult =>
                  rcases tailResult with ⟨tailSequents, finalRest⟩
                  have sourceDecoded' :
                      some (Alternating.Sequent.mk leftExpr rightExpr :: tailSequents,
                        finalRest) = some (sequents, rest) := by
                    simpa [tailDecoded] using sourceAfterRight
                  have sourceEqual := Option.some.inj sourceDecoded'
                  have sequentsEqual :
                      Alternating.Sequent.mk leftExpr rightExpr :: tailSequents = sequents :=
                    congrArg Prod.fst sourceEqual
                  have restEqual : finalRest = rest := congrArg Prod.snd sourceEqual
                  subst sequents
                  subst rest
                  have afterLeftSublist :=
                    alternating_decodeRef_remaining_sublist fuel memory .all blocks left
                      leftExpr afterLeft leftDecoded
                  have afterLeftPairwise := List.Pairwise.sublist afterLeftSublist pairwise
                  have afterLeftLive := afterLeftSublist.trans live
                  obtain ⟨targetLeft, leftMemory, leftRetagged, leftValid, leftAgree,
                      leftOutside⟩ :=
                    retagRef_of_decodeRef fuel .all memory blocks left leftExpr afterLeft layout
                      certificateRoots valid pairwise live leftDecoded
                  have leftTagged :=
                    retagRef_decode_commutes fuel .all memory blocks left leftExpr afterLeft
                      targetLeft leftMemory layout certificateRoots valid pairwise live leftDecoded
                      leftRetagged
                  have currentRightDecoded :
                      Alternating.Packed.decodeRef leftMemory fuel .any afterLeft right =
                        some (rightExpr, afterRight) := by
                    rw [← rightDecoded]
                    exact (alternating_decodeRef_congr fuel .any afterLeft right memory
                      leftMemory leftAgree).symm
                  have afterRightSublist :=
                    alternating_decodeRef_remaining_sublist fuel leftMemory .any afterLeft right
                      rightExpr afterRight currentRightDecoded
                  have afterRightPairwise := List.Pairwise.sublist afterRightSublist
                    afterLeftPairwise
                  have afterRightLive := afterRightSublist.trans afterLeftLive
                  obtain ⟨targetRight, rightMemory, rightRetagged, rightValid, rightAgree,
                      rightOutside⟩ :=
                    retagRef_of_decodeRef fuel .any leftMemory afterLeft right rightExpr
                      afterRight layout certificateRoots leftValid afterLeftPairwise afterLeftLive
                      currentRightDecoded
                  have rightTagged :=
                    retagRef_decode_commutes fuel .any leftMemory afterLeft right rightExpr
                      afterRight targetRight rightMemory layout certificateRoots leftValid
                      afterLeftPairwise afterLeftLive currentRightDecoded rightRetagged
                  have memoryToRight : ReadsAgree memory rightMemory afterRight :=
                    (readsAgree_mono leftAgree afterRightSublist.subset).trans rightAgree
                  have currentTailDecoded :
                      Alternating.Packed.decodeRoots rightMemory fuel afterRight sourceRoots =
                        some (tailSequents, finalRest) := by
                    rw [← tailDecoded]
                    exact (alternating_decodeRoots_congr sourceRoots memory rightMemory fuel
                      afterRight memoryToRight).symm
                  obtain ⟨targetTail, finalMemory, tailRetagged, finalValid, tailAgree,
                      tailOutside⟩ :=
                    retagRoots_of_decodeRoots sourceRoots rightMemory fuel afterRight
                      tailSequents finalRest layout certificateRoots rightValid afterRightPairwise
                      afterRightLive currentTailDecoded
                  have tailTagged :=
                    rootsIh rightMemory fuel afterRight tailSequents finalRest targetTail
                      finalMemory layout certificateRoots rightValid afterRightPairwise
                      afterRightLive currentTailDecoded tailRetagged
                  have leftFinal :
                      Tagged.Packed.decodeRef finalMemory fuel blocks targetLeft =
                        some (AlternatingToTagged.formula .all leftExpr, afterLeft) := by
                    apply tagged_decodeRef_congr_except fuel leftMemory finalMemory blocks
                      targetLeft (AlternatingToTagged.formula .all leftExpr) afterLeft pairwise
                      leftTagged
                    intro candidate candidateMember candidateOutside
                    have candidateLive := live.subset candidateMember
                    exact (rightOutside candidate candidateLive candidateOutside).trans
                      (tailOutside candidate candidateLive fun inAfterRight =>
                        candidateOutside (afterRightSublist.subset inAfterRight))
                  have rightFinal :
                      Tagged.Packed.decodeRef finalMemory fuel afterLeft targetRight =
                        some (AlternatingToTagged.formula .any rightExpr, afterRight) := by
                    apply tagged_decodeRef_congr_except fuel rightMemory finalMemory afterLeft
                      targetRight (AlternatingToTagged.formula .any rightExpr) afterRight
                      afterLeftPairwise rightTagged
                    intro candidate candidateMember candidateOutside
                    exact tailOutside candidate
                      (afterLeftLive.subset candidateMember) candidateOutside
                  have expectedRetagged :
                      retagRoots fuel memory blocks ((left, right) :: sourceRoots) =
                        some ((targetLeft, targetRight) :: targetTail, finalMemory,
                          finalRest) := by
                    simp [retagRoots, leftRetagged, rightRetagged, tailRetagged]
                  have targetEqual := Option.some.inj (expectedRetagged.symm.trans targetRetagged)
                  have rootsEqual : (targetLeft, targetRight) :: targetTail = targetRoots :=
                    congrArg Prod.fst targetEqual
                  have memoryEqual : finalMemory = after :=
                    congrArg (fun value => value.2.1) targetEqual
                  subst targetRoots
                  subst after
                  simp [Tagged.Packed.decodeRoots, leftFinal, rightFinal, tailTagged,
                    AlternatingToTagged.arena, AlternatingToTagged.sequent]

/-- Perform the structural packed-to-packed retagging. -/
def retag? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (Classical.Packed.Arena payloadWidth) := do
  let (roots, memory, remaining) ←
    retagRoots (layout.live.length + 1) arena.memory layout.live arena.roots
  if remaining.isEmpty then some ⟨memory, roots⟩ else none

/- Structural decoding alone drives the executable transformer to success.
No post-hoc abstract equality check is used, and allocator validity is carried
through every in-place block write. -/
theorem retag?_of_represents {source : Classical.Packed.Arena payloadWidth}
    {layout : Layout} {abstract : Alternating.Arena Nat}
    (represents : Alternating.Packed.Represents source layout abstract) :
    ∃ target,
      retag? source layout = some target ∧
      layout.Valid target ∧
      Tagged.Packed.decode? target layout =
        some (AlternatingToTagged.arena abstract) := by
  rcases represents with ⟨sourceValid, sourceDecoded⟩
  unfold Alternating.Packed.decode? at sourceDecoded
  cases rootsDecoded : Alternating.Packed.decodeRoots source.memory
      (layout.live.length + 1) layout.live source.roots with
  | none => simp [rootsDecoded] at sourceDecoded
  | some result =>
      rcases result with ⟨sequents, remaining⟩
      rw [rootsDecoded] at sourceDecoded
      cases remaining with
      | nil =>
          have sequentsEqual : sequents = abstract := by
            simpa using Option.some.inj sourceDecoded
          subst abstract
          have livePairwise : layout.live.Pairwise Block.Disjoint :=
            (List.pairwise_append.mp sourceValid.disjoint).1
          obtain ⟨targetRoots, after, rootsRetagged, afterValid, afterAgree,
              afterOutside⟩ :=
            retagRoots_of_decodeRoots source.roots source.memory
              (layout.live.length + 1) layout.live sequents [] layout source.roots
              sourceValid livePairwise (List.Sublist.refl layout.live) rootsDecoded
          let target : Classical.Packed.Arena payloadWidth := ⟨after, targetRoots⟩
          have targetValid : layout.Valid target := by
            exact ⟨afterValid.allFit, afterValid.disjoint, afterValid.freeZeroed,
              afterValid.addressable⟩
          have targetRootsDecoded :=
            retagRoots_decode_commutes source.roots source.memory
              (layout.live.length + 1) layout.live sequents [] targetRoots after layout
              source.roots sourceValid livePairwise (List.Sublist.refl layout.live)
              rootsDecoded rootsRetagged
          have targetDecoded :
              Tagged.Packed.decode? target layout =
                some (AlternatingToTagged.arena sequents) := by
            unfold Tagged.Packed.decode?
            rw [targetRootsDecoded]
            rfl
          refine ⟨target, ?_, targetValid, targetDecoded⟩
          unfold retag?
          rw [rootsRetagged]
          change some target = some target
          rfl
      | cons block blocks => simp at sourceDecoded

/-- Executable concrete embedding.  Source syntax is checked once and the
structural retagger is then run without a post-hoc abstract equality test. -/
def embed? (arena : Classical.Packed.Arena payloadWidth) (layout : Layout) :
    Option (Classical.Packed.Arena payloadWidth) := do
  let _ ← Alternating.Packed.decode? arena layout
  retag? arena layout

/-- Every successful concrete embedding has a source abstract arena and a
target representation of its abstract embedding.  This is the commuting
square, stated using the exact representation relations on both sides. -/
theorem embed?_commutes {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target)
    (sourceValid : layout.Valid source) :
    ∃ abstract,
      Alternating.Packed.decode? source layout = some abstract ∧
      layout.Valid target ∧
      Tagged.Packed.decode? target layout =
        some (AlternatingToTagged.arena abstract) := by
  unfold embed? at embedded
  cases decoded : Alternating.Packed.decode? source layout with
  | none => simp [decoded] at embedded
  | some abstract =>
      rw [decoded] at embedded
      have represents : Alternating.Packed.Represents source layout abstract :=
        ⟨sourceValid, decoded⟩
      obtain ⟨candidate, candidateRetagged, candidateValid, candidateDecoded⟩ :=
        retag?_of_represents represents
      have targetEqual := Option.some.inj (candidateRetagged.symm.trans embedded)
      subst target
      exact ⟨abstract, by simp, candidateValid, candidateDecoded⟩

/-- Adding allocator-validity evidence upgrades the syntactic square to the
exact representation relations used by both concrete designs. -/
theorem embed?_represents {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target)
    (sourceValid : layout.Valid source) :
    ∃ abstract,
      Alternating.Packed.Represents source layout abstract ∧
      Tagged.Packed.Represents target layout (AlternatingToTagged.arena abstract) := by
  obtain ⟨abstract, sourceDecoded, targetValid, targetDecoded⟩ :=
    embed?_commutes embedded sourceValid
  exact ⟨abstract, ⟨sourceValid, sourceDecoded⟩, ⟨targetValid, targetDecoded⟩⟩

/-- The concrete embedding also preserves semantics at every partial
assignment, not only at the null assignment. -/
theorem embed?_entailsAt_iff {source target : Classical.Packed.Arena payloadWidth}
    {layout : Layout} (embedded : embed? source layout = some target)
    (sourceValid : layout.Valid source) (known : PartialAssignment Nat) :
    ∃ abstract tagged,
      Alternating.Packed.Represents source layout abstract ∧
      Tagged.Packed.Represents target layout tagged ∧
      (Tagged.EntailsAt known tagged ↔ abstract.EntailsAt known) := by
  obtain ⟨abstract, sourceRepresents, targetRepresents⟩ :=
    embed?_represents embedded sourceValid
  exact ⟨abstract, AlternatingToTagged.arena abstract, sourceRepresents,
    targetRepresents, AlternatingToTagged.arena_entailsAt_iff known abstract⟩

end Nucleus.Classical.Embedding.AlternatingToTagged.Packed
