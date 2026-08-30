import Nucleus.Classical.Tagged.Runtime.Encode

/-!
# Correctness of the canonical tagged runtime encoder

This module proves the raw canonical builder corresponds to the independent
runtime decoder.  The proof is kept separate from the executable builder so
the implementation remains easy to translate directly into Rust.
-/

namespace Nucleus.Classical.Tagged.Runtime.Encode

open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged.Runtime
open Nucleus.Classical.Tagged.Runtime.Allocator

variable {payloadWidth : Nat}

mutual
  /-- Maximum array nesting below one formula. -/
  private def formulaDepth : Tagged.Formula Nat → Nat
    | .literal _ => 0
    | .and _ children | .or _ children | .sat _ children =>
        formulasDepth children + 1

  /-- Maximum depth in a proper formula list. -/
  private def formulasDepth : List (Tagged.Formula Nat) → Nat
    | [] => 0
    | formula :: formulas => max (formulaDepth formula) (formulasDepth formulas)
end

mutual
  private theorem formulaDepth_le_words : ∀ formula : Tagged.Formula Nat,
      formulaDepth formula ≤ formulaWords formula
    | .literal _ => by simp [formulaDepth, formulaWords]
    | .and _ children | .or _ children | .sat _ children => by
        have capacity : 4 ≤ 4 * 2 ^ leastSizeClass children.length := by
          simpa [Block.capacity] using Block.four_le_capacity
            (⟨0, leastSizeClass children.length⟩ : Block)
        have childrenBound := formulasDepth_le_words children
        simp only [formulaDepth, formulaWords]
        omega

  private theorem formulasDepth_le_words : ∀ formulas : List (Tagged.Formula Nat),
      formulasDepth formulas ≤ formulasWords formulas
    | [] => by simp [formulasDepth, formulasWords]
    | formula :: formulas => by
        have head := formulaDepth_le_words formula
        have tail := formulasDepth_le_words formulas
        simp only [formulasDepth, formulasWords]
        omega
end

/-- Every block in `owned` ends before the next canonical allocation base. -/
private def Before (owned : List Block) (base : Nat) : Prop :=
  ∀ block ∈ owned, block.stop ≤ base

private theorem Before.mono {owned : List Block} {left right : Nat}
    (before : Before owned left) (less : left ≤ right) : Before owned right := by
  intro block member
  exact (before block member).trans less

private theorem Before.append {left right : List Block} {base : Nat}
    (leftBefore : Before left base) (rightBefore : Before right base) :
    Before (left ++ right) base := by
  intro block member
  rcases List.mem_append.mp member with member | member
  · exact leftBefore block member
  · exact rightBefore block member

private theorem Before.reverse {owned : List Block} {base : Nat}
    (before : Before owned base) : Before owned.reverse base := by
  intro block member
  exact before block (List.mem_reverse.mp member)

private theorem disjointFrom_of_before {block : Block} {owned : List Block}
    (before : Before owned block.base) :
    Arena.disjointFrom block owned = true := by
  unfold Arena.disjointFrom
  rw [List.all_eq_true]
  intro other member
  simp only [decide_eq_true_eq]
  exact Or.inr (before other member)

mutual
  /-- Structural evidence corresponding exactly to one successful formula
builder run. -/
  private def BuiltFormula (payloadWidth base : Nat) :
      Tagged.Formula Nat → Chunk payloadWidth → Prop
    | .literal value, chunk =>
        ∃ word reference,
          Word.literal? payloadWidth value.atom value.negative = some word ∧
          asRef? word = some reference ∧
          chunk = ⟨reference, [], []⟩
    | .and negative children, chunk =>
        BuiltNode payloadWidth base 0 negative children chunk
    | .or negative children, chunk =>
        BuiltNode payloadWidth base 1 negative children chunk
    | .sat negative children, chunk =>
        BuiltNode payloadWidth base 2 negative children chunk

  /-- Structural evidence for one successfully built array. -/
  private def BuiltNode (payloadWidth base tag : Nat) (negative : Bool)
      (children : List (Tagged.Formula Nat)) (chunk : Chunk payloadWidth) : Prop :=
    let block : Block := ⟨base, leastSizeClass children.length⟩
    ∃ forest contents word reference,
      BuiltFormulas payloadWidth block.stop children forest ∧
      liveWords? payloadWidth block forest.references = some contents ∧
      Word.pointer? payloadWidth base tag negative = some word ∧
      asRef? word = some reference ∧
      chunk = ⟨reference, contents ++ forest.words, block :: forest.live⟩

  /-- Structural evidence for one successful proper-list builder run. -/
  private def BuiltFormulas (payloadWidth base : Nat) :
      List (Tagged.Formula Nat) → Forest payloadWidth → Prop
    | [], forest => forest = ⟨[], [], []⟩
    | formula :: formulas, forest =>
        ∃ head tail,
          BuiltFormula payloadWidth base formula head ∧
          BuiltFormulas payloadWidth (base + head.words.length) formulas tail ∧
          forest = ⟨head.reference :: tail.references,
            head.words ++ tail.words, head.live ++ tail.live⟩
end

/-- Structural evidence corresponding exactly to one successful sequent-table
builder run. -/
private def BuiltSequents (payloadWidth base : Nat) :
    List (Tagged.Sequent Nat) → RootChunk payloadWidth → Prop
  | [], built => built = ⟨[], [], []⟩
  | sequent :: sequents, built =>
      ∃ premise conclusion rest,
        BuiltFormula payloadWidth base sequent.premise premise ∧
        BuiltFormula payloadWidth (base + premise.words.length)
          sequent.conclusion conclusion ∧
        BuiltSequents payloadWidth
          (base + premise.words.length + conclusion.words.length)
          sequents rest ∧
        built =
          ⟨(premise.reference, conclusion.reference) :: rest.roots,
            premise.words ++ conclusion.words ++ rest.words,
            premise.live ++ conclusion.live ++ rest.live⟩

mutual
  private theorem formula?_built {payloadWidth base : Nat}
      (formula : Tagged.Formula Nat) {chunk : Chunk payloadWidth}
      (built : formula? payloadWidth base formula = some chunk) :
      BuiltFormula payloadWidth base formula chunk := by
    cases formula with
    | literal value =>
        rw [formula?] at built
        cases wordEncoded : Word.literal? payloadWidth value.atom value.negative with
        | none => simp [wordEncoded] at built
        | some word =>
            rw [wordEncoded] at built
            change (do
              let reference ← asRef? word
              some (⟨reference, [], []⟩ : Chunk payloadWidth)) = some chunk at built
            cases referenceEncoded : asRef? word with
            | none => simp [referenceEncoded] at built
            | some reference =>
                rw [referenceEncoded] at built
                change some (⟨reference, [], []⟩ : Chunk payloadWidth) =
                  some chunk at built
                have equal := Option.some.inj built
                subst chunk
                unfold BuiltFormula
                exact ⟨word, reference, wordEncoded, referenceEncoded, rfl⟩
    | and negative children =>
        rw [BuiltFormula]
        rw [formula?] at built
        exact node?_built negative children built
    | or negative children =>
        rw [BuiltFormula]
        rw [formula?] at built
        exact node?_built negative children built
    | sat negative children =>
        rw [BuiltFormula]
        rw [formula?] at built
        exact node?_built negative children built

  private theorem node?_built {payloadWidth base tag : Nat} (negative : Bool)
      (children : List (Tagged.Formula Nat)) {chunk : Chunk payloadWidth}
      (built : node? payloadWidth base tag negative children = some chunk) :
      BuiltNode payloadWidth base tag negative children chunk := by
    let block : Block := ⟨base, leastSizeClass children.length⟩
    rw [node?] at built
    cases forestEncoded : formulas? payloadWidth block.stop children with
    | none => simp [block, forestEncoded] at built
    | some forest =>
        rw [show Block.stop ⟨base, leastSizeClass children.length⟩ = block.stop by rfl,
          forestEncoded] at built
        change (do
          let contents ← liveWords? payloadWidth block forest.references
          let word ← Word.pointer? payloadWidth block.base tag negative
          let reference ← asRef? word
          some (⟨reference, contents ++ forest.words, block :: forest.live⟩ :
            Chunk payloadWidth)) = some chunk at built
        cases contentsEncoded : liveWords? payloadWidth block forest.references with
        | none => simp [contentsEncoded] at built
        | some contents =>
            rw [contentsEncoded] at built
            change (do
              let word ← Word.pointer? payloadWidth block.base tag negative
              let reference ← asRef? word
              some (⟨reference, contents ++ forest.words, block :: forest.live⟩ :
                Chunk payloadWidth)) = some chunk at built
            cases wordEncoded : Word.pointer? payloadWidth block.base tag negative with
            | none => simp [wordEncoded] at built
            | some word =>
                rw [wordEncoded] at built
                change (do
                  let reference ← asRef? word
                  some (⟨reference, contents ++ forest.words, block :: forest.live⟩ :
                    Chunk payloadWidth)) = some chunk at built
                cases referenceEncoded : asRef? word with
                | none => simp [referenceEncoded] at built
                | some reference =>
                    rw [referenceEncoded] at built
                    change some (⟨reference, contents ++ forest.words,
                      block :: forest.live⟩ : Chunk payloadWidth) = some chunk at built
                    have equal := Option.some.inj built
                    subst chunk
                    unfold BuiltNode
                    exact ⟨forest, contents, word, reference,
                      formulas?_built children forestEncoded,
                      contentsEncoded, wordEncoded, referenceEncoded, rfl⟩

  private theorem formulas?_built {payloadWidth base : Nat}
      (formulas : List (Tagged.Formula Nat)) {forest : Forest payloadWidth}
      (built : formulas? payloadWidth base formulas = some forest) :
      BuiltFormulas payloadWidth base formulas forest := by
    cases formulas with
    | nil =>
        rw [formulas?] at built
        unfold BuiltFormulas
        exact (Option.some.inj built).symm
    | cons formula formulas =>
        rw [formulas?] at built
        cases headEncoded : formula? payloadWidth base formula with
        | none => simp [headEncoded] at built
        | some head =>
            rw [headEncoded] at built
            change (do
              let tail ← formulas? payloadWidth (base + head.words.length) formulas
              some (⟨head.reference :: tail.references,
                head.words ++ tail.words, head.live ++ tail.live⟩ :
                Forest payloadWidth)) = some forest at built
            cases tailEncoded :
                formulas? payloadWidth (base + head.words.length) formulas with
            | none => simp [tailEncoded] at built
            | some tail =>
                rw [tailEncoded] at built
                change some (⟨head.reference :: tail.references,
                  head.words ++ tail.words, head.live ++ tail.live⟩ :
                  Forest payloadWidth) = some forest at built
                have equal := Option.some.inj built
                subst forest
                unfold BuiltFormulas
                exact ⟨head, tail, formula?_built formula headEncoded,
                  formulas?_built formulas tailEncoded, rfl⟩
end

private theorem sequents?_built {payloadWidth base : Nat}
    (input : List (Tagged.Sequent Nat)) {built : RootChunk payloadWidth}
    (encoded : sequents? payloadWidth base input = some built) :
    BuiltSequents payloadWidth base input built := by
  induction input generalizing base built with
  | nil =>
      rw [sequents?] at encoded
      unfold BuiltSequents
      exact (Option.some.inj encoded).symm
  | cons sequent sequents ih =>
      rw [sequents?] at encoded
      cases premiseEncoded : formula? payloadWidth base sequent.premise with
      | none => simp [premiseEncoded] at encoded
      | some premise =>
          rw [premiseEncoded] at encoded
          change (do
            let conclusion ← formula? payloadWidth
              (base + premise.words.length) sequent.conclusion
            let rest ← sequents? payloadWidth
              (base + premise.words.length + conclusion.words.length) sequents
            some (⟨(premise.reference, conclusion.reference) :: rest.roots,
              premise.words ++ conclusion.words ++ rest.words,
              premise.live ++ conclusion.live ++ rest.live⟩ :
                RootChunk payloadWidth)) = some built at encoded
          cases conclusionEncoded : formula? payloadWidth
              (base + premise.words.length) sequent.conclusion with
          | none => simp [conclusionEncoded] at encoded
          | some conclusion =>
              rw [conclusionEncoded] at encoded
              change (do
                let rest ← sequents? payloadWidth
                  (base + premise.words.length + conclusion.words.length) sequents
                some (⟨(premise.reference, conclusion.reference) :: rest.roots,
                  premise.words ++ conclusion.words ++ rest.words,
                  premise.live ++ conclusion.live ++ rest.live⟩ :
                    RootChunk payloadWidth)) = some built at encoded
              cases restEncoded : sequents? payloadWidth
                  (base + premise.words.length + conclusion.words.length)
                  sequents with
              | none => simp [restEncoded] at encoded
              | some rest =>
                  rw [restEncoded] at encoded
                  have equal := Option.some.inj encoded
                  subst built
                  unfold BuiltSequents
                  exact ⟨premise, conclusion, rest,
                    formula?_built sequent.premise premiseEncoded,
                    formula?_built sequent.conclusion conclusionEncoded,
                    ih restEncoded, rfl⟩

mutual
  private theorem BuiltFormula.words_length {payloadWidth base : Nat}
      {formula : Tagged.Formula Nat} {chunk : Chunk payloadWidth}
      (built : BuiltFormula payloadWidth base formula chunk) :
      chunk.words.length = formulaWords formula := by
    cases formula with
    | literal value =>
        unfold BuiltFormula at built
        obtain ⟨word, reference, _, _, equal⟩ := built
        subst chunk
        rfl
    | and negative children =>
        rw [BuiltFormula] at built
        simpa only [formulaWords] using BuiltNode.words_length built
    | or negative children =>
        rw [BuiltFormula] at built
        simpa only [formulaWords] using BuiltNode.words_length built
    | sat negative children =>
        rw [BuiltFormula] at built
        simpa only [formulaWords] using BuiltNode.words_length built

  private theorem BuiltNode.words_length {payloadWidth base tag : Nat}
      {negative : Bool} {children : List (Tagged.Formula Nat)}
      {chunk : Chunk payloadWidth}
      (built : BuiltNode payloadWidth base tag negative children chunk) :
      chunk.words.length =
        4 * 2 ^ leastSizeClass children.length + formulasWords children := by
    let block : Block := ⟨base, leastSizeClass children.length⟩
    unfold BuiltNode at built
    obtain ⟨forest, contents, word, reference, forestBuilt, contentsEncoded,
      _, _, equal⟩ := built
    subst chunk
    have forestLength := BuiltFormulas.words_length forestBuilt
    obtain ⟨_, childrenWords, _, _, childrenEncoded, contentsEqual⟩ :=
      liveWords?_result contentsEncoded
    have childrenLength := encodeWords_length childrenEncoded
    change childrenWords.length = block.capacity - 1 at childrenLength
    have contentsLength : contents.length = block.capacity := by
      rw [contentsEqual, List.length_cons, childrenLength]
      have positive := Block.capacity_pos block
      omega
    rw [List.length_append, contentsLength, forestLength]
    rfl

  private theorem BuiltFormulas.words_length {payloadWidth base : Nat}
      {formulas : List (Tagged.Formula Nat)} {forest : Forest payloadWidth}
      (built : BuiltFormulas payloadWidth base formulas forest) :
      forest.words.length = formulasWords formulas := by
    cases formulas with
    | nil =>
        unfold BuiltFormulas at built
        subst forest
        rfl
    | cons formula formulas =>
        unfold BuiltFormulas at built
        obtain ⟨head, tail, headBuilt, tailBuilt, equal⟩ := built
        subst forest
        rw [List.length_append, BuiltFormula.words_length headBuilt,
          BuiltFormulas.words_length tailBuilt, formulasWords]
end

/-- The listed live blocks own every word in one dense canonical interval. -/
private def Covers (blocks : List Block) (base length : Nat) : Prop :=
  ∀ index, base ≤ index → index < base + length →
    ∃ block ∈ blocks, block.Contains index

private theorem Covers.reverse {blocks : List Block} {base length : Nat}
    (covers : Covers blocks base length) : Covers blocks.reverse base length := by
  intro index lower upper
  obtain ⟨block, member, contains⟩ := covers index lower upper
  exact ⟨block, List.mem_reverse.mpr member, contains⟩

mutual
  private theorem BuiltFormula.covers {payloadWidth base : Nat}
      {formula : Tagged.Formula Nat} {chunk : Chunk payloadWidth}
      (built : BuiltFormula payloadWidth base formula chunk) :
      Covers chunk.live base chunk.words.length := by
    cases formula with
    | literal value =>
        unfold BuiltFormula at built
        obtain ⟨word, reference, _, _, equal⟩ := built
        subst chunk
        intro index lower upper
        change index < base + 0 at upper
        omega
    | and negative children =>
        rw [BuiltFormula] at built
        exact BuiltNode.covers built
    | or negative children =>
        rw [BuiltFormula] at built
        exact BuiltNode.covers built
    | sat negative children =>
        rw [BuiltFormula] at built
        exact BuiltNode.covers built
    termination_by sizeOf formula

  private theorem BuiltNode.covers {payloadWidth base tag : Nat}
      {negative : Bool} {children : List (Tagged.Formula Nat)}
      {chunk : Chunk payloadWidth}
      (built : BuiltNode payloadWidth base tag negative children chunk) :
      Covers chunk.live base chunk.words.length := by
    let block : Block := ⟨base, leastSizeClass children.length⟩
    unfold BuiltNode at built
    obtain ⟨forest, contents, word, reference, forestBuilt, contentsEncoded,
      _, _, equal⟩ := built
    subst chunk
    obtain ⟨_, childrenWords, _, _, childrenEncoded, contentsEqual⟩ :=
      liveWords?_result contentsEncoded
    have childrenLength := encodeWords_length childrenEncoded
    change childrenWords.length = block.capacity - 1 at childrenLength
    have contentsLength : contents.length = block.capacity := by
      rw [contentsEqual, List.length_cons, childrenLength]
      have positive := Block.capacity_pos block
      omega
    have forestCovers := BuiltFormulas.covers forestBuilt
    intro index lower upper
    by_cases inBlock : index < block.stop
    · refine ⟨block, by simp [block], ?_⟩
      exact ⟨by simpa [block] using lower, inBlock⟩
    · have lowerForest : block.stop ≤ index := Nat.le_of_not_gt inBlock
      have upperForest : index < block.stop + forest.words.length := by
        simp only [List.length_append] at upper
        rw [contentsLength] at upper
        simpa [block, Block.stop, Nat.add_assoc] using upper
      obtain ⟨candidate, member, contains⟩ := forestCovers index (by
          simpa [block] using lowerForest) (by
          simpa [block] using upperForest)
      exact ⟨candidate, by simp [member], contains⟩
    termination_by sizeOf children + 1

  private theorem BuiltFormulas.covers {payloadWidth base : Nat}
      {formulas : List (Tagged.Formula Nat)} {forest : Forest payloadWidth}
      (built : BuiltFormulas payloadWidth base formulas forest) :
      Covers forest.live base forest.words.length := by
    cases formulas with
    | nil =>
        unfold BuiltFormulas at built
        subst forest
        intro index lower upper
        change index < base + 0 at upper
        omega
    | cons formula formulas =>
        unfold BuiltFormulas at built
        obtain ⟨head, tail, headBuilt, tailBuilt, equal⟩ := built
        subst forest
        have headCovers := BuiltFormula.covers headBuilt
        have tailCovers := BuiltFormulas.covers tailBuilt
        intro index lower upper
        by_cases inHead : index < base + head.words.length
        · obtain ⟨block, member, contains⟩ := headCovers index lower inHead
          exact ⟨block, List.mem_append_left _ member, contains⟩
        · obtain ⟨block, member, contains⟩ := tailCovers index (by omega) (by
              simp only [List.length_append] at upper
              omega)
          exact ⟨block, List.mem_append_right _ member, contains⟩
    termination_by sizeOf formulas
end

/-- A successful sequent-table build densely owns its complete word table. -/
private theorem BuiltSequents.covers {payloadWidth base : Nat}
    {input : List (Tagged.Sequent Nat)} {built : RootChunk payloadWidth}
    (builtEvidence : BuiltSequents payloadWidth base input built) :
    Covers built.live base built.words.length := by
  induction input generalizing base built with
  | nil =>
      unfold BuiltSequents at builtEvidence
      subst built
      intro index lower upper
      change index < base + 0 at upper
      omega
  | cons sequent sequents ih =>
      unfold BuiltSequents at builtEvidence
      obtain ⟨premise, conclusion, rest, premiseBuilt, conclusionBuilt,
        restBuilt, equal⟩ := builtEvidence
      subst built
      have premiseCovers := BuiltFormula.covers premiseBuilt
      have conclusionCovers := BuiltFormula.covers conclusionBuilt
      have restCovers := ih restBuilt
      intro index lower upper
      by_cases inPremise : index < base + premise.words.length
      · obtain ⟨block, member, contains⟩ :=
          premiseCovers index lower inPremise
        exact ⟨block, by simp [member], contains⟩
      · by_cases inConclusion :
            index < base + premise.words.length + conclusion.words.length
        · obtain ⟨block, member, contains⟩ :=
            conclusionCovers index (by omega) inConclusion
          exact ⟨block, by simp [member], contains⟩
        · obtain ⟨block, member, contains⟩ := restCovers index (by omega) (by
              simp only [List.length_append] at upper
              omega)
          exact ⟨block, by simp [member], contains⟩

/-- Dense ownership after the reserved prefix satisfies the executable arena
coverage check. -/
private theorem coversStorage_of_covers {blocks : List Block} {length : Nat}
    (covers : Covers blocks 4 length) :
    Arena.coversStorage blocks (4 + length) = true := by
  unfold Arena.coversStorage
  rw [List.all_eq_true]
  intro offset member
  have offsetBound : offset < length := by
    have := List.mem_range.mp member
    omega
  obtain ⟨block, blockMember, contains⟩ :=
    covers (4 + offset) (by omega) (by omega)
  rw [List.any_eq_true]
  refine ⟨block, blockMember, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact contains

private theorem Arena.decodeFree?_empty {arena : Arena payloadWidth}
    (addressable : arena.words.size ≤ 2 ^ payloadWidth)
    (empty : arena.freeRoot = Word.zero payloadWidth) :
    arena.decodeFree? = some [] := by
  unfold Packed.Intrusive.Arena.decodeFree?
  rw [if_pos addressable, empty]
  simp [Packed.Intrusive.Arena.optionalPointer?, Word.CanonicalZero]

private theorem Arena.word?_span {arena : Arena payloadWidth}
    {before suffix : List (Word payloadWidth)} {word : Word payloadWidth}
    {index : Nat}
    (words : arena.words = (before ++ word :: suffix).toArray)
    (beforeLength : before.length = index) :
    arena.word? index = some word := by
  unfold Packed.Intrusive.Arena.word?
  rw [words, List.getElem?_toArray, List.getElem?_append]
  simp [beforeLength]

private theorem Arena.readLive?_span {arena : Arena payloadWidth}
    {before suffix contents : List (Word payloadWidth)} {block : Block}
    {references : List (Word.Ref payloadWidth)}
    (words : arena.words = (before ++ contents ++ suffix).toArray)
    (beforeLength : before.length = block.base)
    (encoded : liveWords? payloadWidth block references = some contents)
    (fits : block.Fits arena.words.size) :
    arena.readLive? block = some references := by
  obtain ⟨header, children, classBound, headerEncoded, childrenEncoded,
    contentsEqual⟩ := liveWords?_result encoded
  subst contents
  have words' :
      arena.words = (before ++ header :: (children ++ suffix)).toArray := by
    simpa [List.append_assoc] using words
  have wordRead : arena.word? block.base = some header :=
    Arena.word?_span words' beforeLength
  have naturalDecoded := natural?_decodes headerEncoded
  have blockDecoded : arena.liveBlock? block.base = some block := by
    simp [Arena.liveBlock?, wordRead, naturalDecoded, classBound, fits]
  have childrenLength : children.length = block.capacity - 1 :=
    encodeWords_length childrenEncoded
  have slice :
      ((arena.words.toList.drop (block.base + 1)).take (block.capacity - 1)) =
        children := by
    rw [words']
    calc
      List.take (block.capacity - 1)
          (List.drop (block.base + 1) (before ++ header :: (children ++ suffix))) =
          List.take children.length
            (List.drop (before ++ [header]).length
              ((before ++ [header]) ++ (children ++ suffix))) := by
            congr 2 <;> simp [beforeLength, childrenLength, List.append_assoc]
      _ = children := by rw [List.drop_left, List.take_append_length]
  unfold Arena.readLive?
  rw [blockDecoded]
  change (if block = block then
      decodeWords ((arena.words.toList.drop (block.base + 1)).take
        (block.capacity - 1)) else none) = some references
  rw [if_pos rfl, slice]
  exact decodeWords_of_encodeWords childrenEncoded

private theorem Arena.liveBlock?_of_readLive {arena : Arena payloadWidth}
    {block : Block} {references : List (Word.Ref payloadWidth)}
    (read : arena.readLive? block = some references) :
    arena.liveBlock? block.base = some block := by
  unfold Arena.readLive? at read
  cases decoded : arena.liveBlock? block.base with
  | none => simp [decoded] at read
  | some candidate =>
      rw [decoded] at read
      change (if candidate = block then
        decodeWords ((arena.words.toList.drop (block.base + 1)).take
          (block.capacity - 1)) else none) = some references at read
      split at read
      · rename_i equal
        subst candidate
        rfl
      · contradiction

private theorem literal?_base {atom : Nat} {negative : Bool}
    {word : Word payloadWidth}
    (encoded : Word.literal? payloadWidth atom negative = some word) :
    word.base = 4 * atom := by
  exact Word.withTag?_base encoded

private theorem literal?_negative {atom : Nat} {negative : Bool}
    {word : Word payloadWidth}
    (encoded : Word.literal? payloadWidth atom negative = some word) :
    word.negative = negative := by
  exact Word.withTag?_negative encoded

private theorem Arena.decodeLiteral {arena : Arena payloadWidth}
    {value : Classical.Literal Nat} {word : Word payloadWidth}
    {reference : Word.Ref payloadWidth} {fuel : Nat} {owned : List Block}
    (wordEncoded : Word.literal? payloadWidth value.atom value.negative = some word)
    (referenceEncoded : asRef? word = some reference)
    (positive : 0 < fuel) :
    arena.decodeRef [] fuel owned reference = some (.literal value, owned) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      have referenceWord := asRef?_word referenceEncoded
      have tag := Word.literal?_tag wordEncoded
      have base := literal?_base wordEncoded
      have negative := literal?_negative wordEncoded
      unfold Arena.decodeRef
      rw [referenceWord]
      change (if _ : word.tag = 3 then
        some (Tagged.Formula.literal ⟨word.base / 4, word.negative⟩, owned) else _) =
          some (Tagged.Formula.literal value, owned)
      rw [dif_pos tag]
      simp [base, negative]

/-- The child fold used by the runtime decoder, named for the correspondence
proof. -/
private def decodeReferences (arena : Arena payloadWidth) (fuel : Nat)
    (decoded : List (Tagged.Formula Nat)) (owned : List Block)
    (references : List (Word.Ref payloadWidth)) :
    Option (List (Tagged.Formula Nat) × List Block) :=
  references.foldlM (init := (decoded, owned)) fun (decoded, owned) reference => do
    let (formula, owned) ← arena.decodeRef [] fuel owned reference
    some (formula :: decoded, owned)

private theorem decodeReferences_cons {arena : Arena payloadWidth} {fuel : Nat}
    {decoded : List (Tagged.Formula Nat)} {owned : List Block}
    {reference : Word.Ref payloadWidth} {references : List (Word.Ref payloadWidth)} :
    decodeReferences arena fuel decoded owned (reference :: references) = (do
      let (formula, owned) ← arena.decodeRef [] fuel owned reference
      decodeReferences arena fuel (formula :: decoded) owned references) := by
  unfold decodeReferences
  rw [List.foldlM_cons]
  cases decodedReference : arena.decodeRef [] fuel owned reference with
  | none => simp [decodedReference]
  | some result =>
      obtain ⟨formula, owned⟩ := result
      simp [decodedReference]

mutual
  private theorem BuiltFormula.decode {payloadWidth base fuel : Nat}
      {arena : Arena payloadWidth} {before suffix : List (Word payloadWidth)}
      {owned : List Block} {formula : Tagged.Formula Nat}
      {chunk : Chunk payloadWidth}
      (built : BuiltFormula payloadWidth base formula chunk)
      (fits : FitsFormula payloadWidth base formula)
      (words : arena.words = (before ++ chunk.words ++ suffix).toArray)
      (beforeLength : before.length = base)
      (ownedBefore : Before owned base)
      (deepEnough : formulaDepth formula < fuel) :
      arena.decodeRef [] fuel owned chunk.reference =
          some (formula, chunk.live.reverse ++ owned) ∧
        Before (chunk.live.reverse ++ owned) (base + chunk.words.length) := by
    cases formula with
    | literal value =>
        unfold BuiltFormula at built
        obtain ⟨word, reference, wordEncoded, referenceEncoded, equal⟩ := built
        subst chunk
        have decoded := Arena.decodeLiteral (arena := arena) (owned := owned) wordEncoded
          referenceEncoded (by simpa [formulaDepth] using deepEnough)
        refine ⟨by simpa using decoded, ?_⟩
        simpa using ownedBefore
    | and negative children =>
        rw [BuiltFormula] at built
        cases fuel with
        | zero => simp [formulaDepth] at deepEnough
        | succ fuel =>
            apply BuiltNode.decode (formula := .and negative children) (tagBound := by decide)
              (meaning := rfl) built fits words beforeLength ownedBefore
            simpa [formulaDepth] using deepEnough
    | or negative children =>
        rw [BuiltFormula] at built
        cases fuel with
        | zero => simp [formulaDepth] at deepEnough
        | succ fuel =>
            apply BuiltNode.decode (formula := .or negative children) (tagBound := by decide)
              (meaning := rfl) built fits words beforeLength ownedBefore
            simpa [formulaDepth] using deepEnough
    | sat negative children =>
        rw [BuiltFormula] at built
        cases fuel with
        | zero => simp [formulaDepth] at deepEnough
        | succ fuel =>
            apply BuiltNode.decode (formula := .sat negative children) (tagBound := by decide)
              (meaning := rfl) built fits words beforeLength ownedBefore
            simpa [formulaDepth] using deepEnough
    termination_by sizeOf formula

  private theorem BuiltNode.decode {payloadWidth base tag fuel : Nat}
      {arena : Arena payloadWidth} {before suffix : List (Word payloadWidth)}
      {owned : List Block} {negative : Bool}
      {children : List (Tagged.Formula Nat)} {formula : Tagged.Formula Nat}
      {chunk : Chunk payloadWidth}
      (tagBound : tag < 3)
      (meaning : Tagged.Packed.node tag negative children = some formula)
      (built : BuiltNode payloadWidth base tag negative children chunk)
      (fits :
        let block : Block := ⟨base, leastSizeClass children.length⟩
        block.Aligned ∧ block.stop ≤ 2 ^ payloadWidth ∧
          block.sizeClass + 2 ≤ payloadWidth ∧
          FitsFormulas payloadWidth block.stop children)
      (words : arena.words = (before ++ chunk.words ++ suffix).toArray)
      (beforeLength : before.length = base)
      (ownedBefore : Before owned base)
      (deepEnough : formulasDepth children < fuel) :
      arena.decodeRef [] (fuel + 1) owned chunk.reference =
          some (formula, chunk.live.reverse ++ owned) ∧
        Before (chunk.live.reverse ++ owned) (base + chunk.words.length) := by
    let block : Block := ⟨base, leastSizeClass children.length⟩
    unfold BuiltNode at built
    obtain ⟨forest, contents, word, reference, forestBuilt, contentsEncoded,
      wordEncoded, referenceEncoded, equal⟩ := built
    subst chunk
    change block.Aligned ∧ block.stop ≤ 2 ^ payloadWidth ∧
      block.sizeClass + 2 ≤ payloadWidth ∧
      FitsFormulas payloadWidth block.stop children at fits
    obtain ⟨_, childWords, _, _, childWordsEncoded, contentsEqual⟩ :=
      liveWords?_result contentsEncoded
    have childWordsLength := encodeWords_length childWordsEncoded
    change childWords.length = block.capacity - 1 at childWordsLength
    have contentsLength : contents.length = block.capacity := by
      rw [contentsEqual, List.length_cons, childWordsLength]
      have positive := Block.capacity_pos block
      omega
    have arenaSize : arena.words.size =
        before.length + contents.length + forest.words.length + suffix.length := by
      rw [words]
      simp [List.length_append, Nat.add_assoc]
    have blockBase : block.base = base := rfl
    have blockFits : block.Fits arena.words.size := by
      refine ⟨fits.1, ?_⟩
      simp only [Block.stop]
      rw [arenaSize, beforeLength, contentsLength]
      omega
    have wordsAtBlock :
        arena.words = (before ++ contents ++ (forest.words ++ suffix)).toArray := by
      simpa [List.append_assoc] using words
    have childrenRead : arena.readLive? block = some forest.references :=
      Arena.readLive?_span wordsAtBlock beforeLength contentsEncoded blockFits
    have blockDecoded := Arena.liveBlock?_of_readLive childrenRead
    have beforeChildren : Before (block :: owned) block.stop := by
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl _
      · exact (ownedBefore candidate member).trans (Nat.le_add_right _ _)
    have wordsAtChildren :
        arena.words = ((before ++ contents) ++ forest.words ++ suffix).toArray := by
      simpa [List.append_assoc] using words
    have beforeChildrenLength : (before ++ contents).length = block.stop := by
      simp only [List.length_append, beforeLength, contentsLength, Block.stop]
      exact congrArg (fun value ↦ value + block.capacity) blockBase.symm
    obtain ⟨childrenDecoded, childrenBefore⟩ :=
      BuiltFormulas.decode forestBuilt fits.2.2.2 wordsAtChildren
        beforeChildrenLength beforeChildren deepEnough ([] : List (Tagged.Formula Nat))
    have referenceWord := asRef?_word referenceEncoded
    have wordTag := Word.pointer?_tag wordEncoded
    have wordBase := Word.pointer?_base wordEncoded
    have wordNegative := Word.pointer?_negative wordEncoded
    have notLiteral : word.tag ≠ 3 := by rw [wordTag]; omega
    have disjoint : Arena.disjointFrom block (owned ++ []) = true := by
      simpa using disjointFrom_of_before
        (block := block) (owned := owned) ownedBefore
    constructor
    · unfold Arena.decodeRef
      rw [referenceWord]
      change (if _ : word.tag = 3 then _ else _) = _
      rw [dif_neg notLiteral, wordBase, blockDecoded]
      change (do
        if Arena.disjointFrom block (owned ++ []) then pure () else none
        let references ← arena.readLive? block
        let (decoded, owned) ← decodeReferences arena fuel [] (block :: owned) references
        let formula ← Tagged.Packed.node word.tag word.negative decoded.reverse
        some (formula, owned)) =
          some (formula, (block :: forest.live).reverse ++ owned)
      simp only [disjoint, ↓reduceIte, childrenRead]
      change (do
        let (decoded, owned) ←
          decodeReferences arena fuel [] (block :: owned) forest.references
        let formula ← Tagged.Packed.node word.tag word.negative decoded.reverse
        some (formula, owned)) = _
      rw [childrenDecoded]
      change (do
        let formula ← Tagged.Packed.node word.tag word.negative
          (children.reverse ++ []).reverse
        some (formula, forest.live.reverse ++ block :: owned)) = _
      simp only [List.append_nil, List.reverse_reverse]
      rw [wordTag, wordNegative, meaning]
      simp [List.append_assoc]
    · have forestBefore : Before forest.live.reverse
          (block.stop + forest.words.length) := by
        intro candidate member
        exact childrenBefore candidate (List.mem_append_left _ member)
      have blockBefore : Before [block] (block.stop + forest.words.length) := by
        intro candidate member
        simp only [List.mem_singleton] at member
        subst candidate
        omega
      have ownedFinal : Before owned (block.stop + forest.words.length) :=
        ownedBefore.mono (by
          simp only [Block.stop]
          rw [blockBase]
          omega)
      have combined := forestBefore.append (blockBefore.append ownedFinal)
      simpa [List.reverse_cons, List.append_assoc, contentsLength, Block.stop,
        blockBase, Nat.add_assoc] using combined
    termination_by sizeOf children + 1

  private theorem BuiltFormulas.decode {payloadWidth base fuel : Nat}
      {arena : Arena payloadWidth} {before suffix : List (Word payloadWidth)}
      {owned : List Block} {formulas : List (Tagged.Formula Nat)}
      {forest : Forest payloadWidth}
      (built : BuiltFormulas payloadWidth base formulas forest)
      (fits : FitsFormulas payloadWidth base formulas)
      (words : arena.words = (before ++ forest.words ++ suffix).toArray)
      (beforeLength : before.length = base)
      (ownedBefore : Before owned base)
      (deepEnough : formulasDepth formulas < fuel)
      (decoded : List (Tagged.Formula Nat)) :
      decodeReferences arena fuel decoded owned forest.references =
          some (formulas.reverse ++ decoded, forest.live.reverse ++ owned) ∧
        Before (forest.live.reverse ++ owned) (base + forest.words.length) := by
    cases formulas with
    | nil =>
        unfold BuiltFormulas at built
        subst forest
        refine ⟨by rfl, ?_⟩
        simpa using ownedBefore
    | cons formula formulas =>
        unfold BuiltFormulas at built
        obtain ⟨head, tail, headBuilt, tailBuilt, equal⟩ := built
        subst forest
        have headWords :
            arena.words = (before ++ head.words ++ (tail.words ++ suffix)).toArray := by
          simpa [List.append_assoc] using words
        have headDepth : formulaDepth formula < fuel := by
          simpa [formulasDepth] using lt_of_le_of_lt (Nat.le_max_left _ _) deepEnough
        obtain ⟨headDecoded, headBefore⟩ :=
          BuiltFormula.decode headBuilt fits.1 headWords beforeLength ownedBefore headDepth
        have tailWords :
            arena.words = ((before ++ head.words) ++ tail.words ++ suffix).toArray := by
          simpa [List.append_assoc] using words
        have tailLength : (before ++ head.words).length =
            base + head.words.length := by simp [beforeLength]
        have tailFits : FitsFormulas payloadWidth
            (base + head.words.length) formulas := by
          rw [BuiltFormula.words_length headBuilt]
          exact fits.2
        have tailDepth : formulasDepth formulas < fuel := by
          simpa [formulasDepth] using lt_of_le_of_lt (Nat.le_max_right _ _) deepEnough
        obtain ⟨tailDecoded, tailBefore⟩ :=
          BuiltFormulas.decode tailBuilt tailFits tailWords tailLength headBefore
            tailDepth (formula :: decoded)
        constructor
        · rw [decodeReferences_cons]
          rw [headDecoded]
          change decodeReferences arena fuel (formula :: decoded)
            (head.live.reverse ++ owned) tail.references = _
          rw [tailDecoded]
          simp [List.reverse_cons, List.append_assoc]
        · simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using tailBefore
    termination_by sizeOf formulas
end

/-- A successfully built complete sequent table is read back exactly by the
independent runtime root decoder. -/
private theorem BuiltSequents.decode {payloadWidth base : Nat}
    {arena : Arena payloadWidth} {before suffix : List (Word payloadWidth)}
    {owned : List Block} {input : List (Tagged.Sequent Nat)}
    {built : RootChunk payloadWidth}
    (builtEvidence : BuiltSequents payloadWidth base input built)
    (fits : FitsSequents payloadWidth base input)
    (words : arena.words = (before ++ built.words ++ suffix).toArray)
    (beforeLength : before.length = base)
    (ownedBefore : Before owned base) :
    arena.decodeRoots [] (arena.words.size + 1) owned built.roots =
        some (input, built.live.reverse ++ owned) ∧
      Before (built.live.reverse ++ owned) (base + built.words.length) := by
  induction input generalizing base before owned built with
  | nil =>
      unfold BuiltSequents at builtEvidence
      subst built
      refine ⟨by rfl, ?_⟩
      simpa using ownedBefore
  | cons sequent sequents ih =>
      unfold BuiltSequents at builtEvidence
      obtain ⟨premise, conclusion, rest, premiseBuilt, conclusionBuilt,
        restBuilt, equal⟩ := builtEvidence
      subst built
      have premiseLength := BuiltFormula.words_length premiseBuilt
      have conclusionLength := BuiltFormula.words_length conclusionBuilt
      have premiseWords :
          arena.words =
            (before ++ premise.words ++
              ((conclusion.words ++ rest.words) ++ suffix)).toArray := by
        simpa [List.append_assoc] using words
      have premiseStored : premise.words.length ≤ arena.words.size := by
        rw [words]
        simp
        omega
      have premiseDepth :
          formulaDepth sequent.premise < arena.words.size + 1 := by
        have depth := formulaDepth_le_words sequent.premise
        rw [← premiseLength] at depth
        omega
      obtain ⟨premiseDecoded, premiseBefore⟩ :=
        BuiltFormula.decode premiseBuilt fits.1 premiseWords beforeLength
          ownedBefore premiseDepth
      have conclusionFits : FitsFormula payloadWidth
          (base + premise.words.length) sequent.conclusion := by
        rw [premiseLength]
        exact fits.2.1
      have conclusionWords :
          arena.words =
            ((before ++ premise.words) ++ conclusion.words ++
              (rest.words ++ suffix)).toArray := by
        simpa [List.append_assoc] using words
      have conclusionBase : (before ++ premise.words).length =
          base + premise.words.length := by
        simp [beforeLength]
      have conclusionStored : conclusion.words.length ≤ arena.words.size := by
        rw [words]
        simp
        omega
      have conclusionDepth :
          formulaDepth sequent.conclusion < arena.words.size + 1 := by
        have depth := formulaDepth_le_words sequent.conclusion
        rw [← conclusionLength] at depth
        omega
      obtain ⟨conclusionDecoded, conclusionBefore⟩ :=
        BuiltFormula.decode conclusionBuilt conclusionFits conclusionWords
          conclusionBase premiseBefore conclusionDepth
      have restFits : FitsSequents payloadWidth
          (base + premise.words.length + conclusion.words.length) sequents := by
        rw [premiseLength, conclusionLength]
        exact fits.2.2
      have restWords :
          arena.words =
            ((before ++ premise.words ++ conclusion.words) ++ rest.words ++
              suffix).toArray := by
        simpa [List.append_assoc] using words
      have restBase : (before ++ premise.words ++ conclusion.words).length =
          base + premise.words.length + conclusion.words.length := by
        simp [beforeLength, Nat.add_assoc]
      obtain ⟨restDecoded, restBefore⟩ :=
        ih restBuilt restFits restWords restBase conclusionBefore
      constructor
      · unfold Arena.decodeRoots
        rw [premiseDecoded]
        change (do
          let (conclusionFormula, live) ← arena.decodeRef []
            (arena.words.size + 1) (premise.live.reverse ++ owned)
            conclusion.reference
          let (roots, live) ← arena.decodeRoots [] (arena.words.size + 1)
            live rest.roots
          some ((⟨sequent.premise, conclusionFormula⟩ : Tagged.Sequent Nat) ::
            roots, live)) = _
        rw [conclusionDecoded]
        change (do
          let (roots, live) ← arena.decodeRoots [] (arena.words.size + 1)
            (conclusion.live.reverse ++ (premise.live.reverse ++ owned))
            rest.roots
          some (sequent :: roots, live)) = _
        rw [restDecoded]
        simp [List.append_assoc]
      · simpa [List.reverse_append, List.append_assoc, Nat.add_assoc] using
          restBefore

/-- Under the public explicit bounds, the raw canonical arena is accepted by
the independent runtime decoder and denotes exactly its input. -/
theorem raw?_decodes {payloadWidth : Nat}
    {input : List (Tagged.Sequent Nat)} {arena : Arena payloadWidth}
    (fits : Fits payloadWidth input)
    (encoded : raw? payloadWidth input = some arena) :
    arena.decode? = some input := by
  unfold raw? at encoded
  cases builtEncoded : sequents? payloadWidth 4 input with
  | none => simp [builtEncoded] at encoded
  | some built =>
      rw [builtEncoded] at encoded
      change some ({
        words := (List.replicate 4 (Word.zero payloadWidth) ++
          built.words).toArray
        freeRoot := Word.zero payloadWidth
        roots := built.roots } : Arena payloadWidth) = some arena at encoded
      have arenaEqual := Option.some.inj encoded
      subst arena
      let candidate : Arena payloadWidth := {
        words := (List.replicate 4 (Word.zero payloadWidth) ++
          built.words).toArray
        freeRoot := Word.zero payloadWidth
        roots := built.roots }
      change candidate.decode? = some input
      have builtEvidence := sequents?_built input builtEncoded
      obtain ⟨other, otherEncoded, _, otherLength⟩ :=
        sequents?_complete input fits.2
      have same : built = other :=
        Option.some.inj (builtEncoded.symm.trans otherEncoded)
      have builtLength : built.words.length = tableWords input := by
        rw [same]
        exact otherLength
      have candidateSize : candidate.words.size = 4 + built.words.length := by
        simp [candidate]
        omega
      have addressable : candidate.words.size ≤ 2 ^ payloadWidth := by
        have endBound := FitsSequents.end_le fits.1 fits.2
        rw [candidateSize, builtLength]
        exact endBound
      have freeDecoded : candidate.decodeFree? = some [] :=
        Arena.decodeFree?_empty addressable rfl
      have rootsResult := BuiltSequents.decode
        (arena := candidate)
        (before := List.replicate 4 (Word.zero payloadWidth))
        (suffix := []) (owned := []) builtEvidence fits.2 (by
          simp [candidate]) (by simp) (by
          intro block member
          simp at member)
      have rootsDecoded : candidate.decodeRoots [] (candidate.words.size + 1)
          [] built.roots = some (input, built.live.reverse) := by
        simpa using rootsResult.1
      have zeroed : candidate.zeroRange 0 4 = true := by
        simp [candidate, Packed.Intrusive.Arena.zeroRange, Word.CanonicalZero]
      have covered : Arena.coversStorage built.live.reverse
          candidate.words.size = true := by
        have dense :=
          coversStorage_of_covers (BuiltSequents.covers builtEvidence).reverse
        rw [candidateSize]
        exact dense
      unfold Arena.decode? Arena.decodeState?
      simp only [zeroed, ↓reduceIte, freeDecoded]
      change Decoded.sequents <$> (do
        let (sequents, live) ← candidate.decodeRoots []
          (candidate.words.size + 1) [] built.roots
        if Arena.coversStorage (live ++ []) candidate.words.size then
          some (⟨sequents, live, []⟩ : Decoded)
        else none) = some input
      rw [rootsDecoded]
      simp [covered]

/-- The canonical checked packer is total under its explicit resource bound. -/
theorem pack?_complete {payloadWidth : Nat}
    {input : List (Tagged.Sequent Nat)} (fits : Fits payloadWidth input) :
    ∃ checked, pack? payloadWidth input = some checked := by
  obtain ⟨arena, encoded, _, _⟩ := raw?_complete fits
  have decoded := raw?_decodes fits encoded
  unfold Arena.decode? at decoded
  cases stateDecoded : arena.decodeState? with
  | none => simp [stateDecoded] at decoded
  | some state =>
      have same : state.sequents = input := by
        rw [stateDecoded] at decoded
        exact Option.some.inj decoded
      let checked : Checked payloadWidth := ⟨arena, state, stateDecoded⟩
      refine ⟨checked, ?_⟩
      have validated : check? arena = some checked := by
        unfold check?
        split
        · rename_i impossible
          rw [stateDecoded] at impossible
          contradiction
        · rename_i value valueDecoded
          have valueEqual : value = state :=
            Option.some.inj (valueDecoded.symm.trans stateDecoded)
          subst value
          simp [checked]
      unfold pack?
      rw [encoded]
      change (do
        let result ← check? arena
        if result.decoded.sequents = input then some result else none) =
          some checked
      rw [validated]
      simp [checked, same]

end Nucleus.Classical.Tagged.Runtime.Encode
