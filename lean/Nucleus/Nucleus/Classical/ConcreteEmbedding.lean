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
      layout.Valid target := by
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
          refine ⟨target, ?_, targetValid⟩
          unfold retag?
          rw [rootsRetagged]
          change some target = some target
          rfl
      | cons block blocks => simp at sourceDecoded

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
