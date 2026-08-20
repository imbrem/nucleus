import Nucleus.HolE.Named.Unsorted.Context.Repr
import Nucleus.HolE.Named.Unsorted.Kernel
import Nucleus.HolE.Cut
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Antisymmetrization

/-!
# Contexts and entailment for unsorted named HolE

The ambient type-variable scope, term-variable scope, and locally nameless
bound context are fixed throughout.  The contexts defined here are lists of
named, unsorted assumptions.

Cut admissibility requires every hypothesis to have the syntax-directed
Boolean type, rather than merely a type convertible to Boolean.  `WellFormed`
exposes precisely that invariant.  Entailment records validity of both
endpoints, so its reflexive domain is exactly the well-formed contexts.
-/

namespace Nucleus.HolE.Named.Unsorted.Context

open Nucleus.HolE

set_option relaxedAutoImplicit true
set_option linter.unusedSectionVars false

variable {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
variable {types : List Kind} {depth : Nat}
variable (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
variable (boundContext : BoundCtx Sig types depth)

/-- An unsorted expression is a valid assumption when it checks as a term,
lowers under the named scopes, and has the syntax-directed Boolean type.  The
raw typing is what makes Boolean case analysis available without asking type
conversion to change the explicit operand type of an equality node. -/
def IsProposition (proposition : Expr Sig) : Prop :=
  ∃ sorted lowered,
    check .tm proposition = some sorted ∧
    Named.lowerTm typeScope termScope sorted = some lowered ∧
    Nucleus.HolE.HasType boundContext lowered .boolTy

/-- Every member of a well-formed assumption context is a valid proposition. -/
def WellFormed (context : ListCtx Sig) : Prop :=
  ∀ proposition, proposition ∈ context →
    IsProposition typeScope termScope boundContext proposition

@[simp] theorem wellFormed_nil :
    WellFormed typeScope termScope boundContext ([] : ListCtx Sig) := by
  intro proposition membership
  simp at membership

theorem WellFormed.cons {proposition : Expr Sig} {context : ListCtx Sig}
    (head : IsProposition typeScope termScope boundContext proposition)
    (tail : WellFormed typeScope termScope boundContext context) :
    WellFormed typeScope termScope boundContext (proposition :: context) := by
  intro candidate membership
  rcases List.mem_cons.mp membership with rfl | membership
  · exact head
  · exact tail candidate membership

theorem WellFormed.head {proposition : Expr Sig} {context : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext (proposition :: context)) :
    IsProposition typeScope termScope boundContext proposition :=
  valid proposition (by simp)

theorem WellFormed.tail {proposition : Expr Sig} {context : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext (proposition :: context)) :
    WellFormed typeScope termScope boundContext context := by
  intro candidate membership
  exact valid candidate (List.mem_cons_of_mem proposition membership)

theorem WellFormed.append {left right : ListCtx Sig}
    (leftValid : WellFormed typeScope termScope boundContext left)
    (rightValid : WellFormed typeScope termScope boundContext right) :
    WellFormed typeScope termScope boundContext (left ++ right) := by
  intro proposition membership
  rcases List.mem_append.mp membership with membership | membership
  · exact leftValid proposition membership
  · exact rightValid proposition membership

theorem WellFormed.of_append_left {left right : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext (left ++ right)) :
    WellFormed typeScope termScope boundContext left := by
  intro proposition membership
  exact valid proposition (List.mem_append_left right membership)

theorem WellFormed.of_append_right {left right : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext (left ++ right)) :
    WellFormed typeScope termScope boundContext right := by
  intro proposition membership
  exact valid proposition (List.mem_append_right left membership)

theorem WellFormed.perm {left right : ListCtx Sig}
    (permutation : left.Perm right)
    (valid : WellFormed typeScope termScope boundContext left) :
    WellFormed typeScope termScope boundContext right := by
  intro proposition membership
  exact valid proposition (permutation.mem_iff.mpr membership)

/-- The well-formed list presentation in a typed bound-variable ambient.

The ambient typing certificate is an index, rather than a field, so it is
available to zero-argument constructions and typeclass instances. -/
structure WfList (boundTyped : TypedCtx boundContext) where
  raw : ListCtx Sig
  valid : WellFormed typeScope termScope boundContext raw

namespace WfList

@[ext] theorem ext {boundTyped : TypedCtx boundContext}
    {left right : WfList typeScope termScope boundContext boundTyped}
    (raw : left.raw = right.raw) : left = right := by
  cases left
  cases right
  cases raw
  rfl

def empty (boundTyped : TypedCtx boundContext) :
    WfList typeScope termScope boundContext boundTyped :=
  ⟨[], wellFormed_nil typeScope termScope boundContext⟩

def append {boundTyped : TypedCtx boundContext}
    (left right : WfList typeScope termScope boundContext boundTyped) :
    WfList typeScope termScope boundContext boundTyped :=
  ⟨left.raw ++ right.raw,
    left.valid.append typeScope termScope boundContext right.valid⟩

@[simp] theorem raw_empty (boundTyped : TypedCtx boundContext) :
    (empty typeScope termScope boundContext boundTyped).raw = [] := rfl

@[simp] theorem raw_append
    {boundTyped : TypedCtx boundContext}
    (left right : WfList typeScope termScope boundContext boundTyped) :
    (WfList.append typeScope termScope boundContext left right).raw =
      left.raw ++ right.raw := rfl

@[simp] theorem empty_append (boundTyped : TypedCtx boundContext)
    (context : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext
      (empty typeScope termScope boundContext boundTyped) context = context := by
  apply ext
  simp

@[simp] theorem append_empty (boundTyped : TypedCtx boundContext)
    (context : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext context
      (empty typeScope termScope boundContext boundTyped) = context := by
  apply ext
  simp

@[simp] theorem append_assoc
    {boundTyped : TypedCtx boundContext}
    (first second third : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext
      (append typeScope termScope boundContext first second) third =
    append typeScope termScope boundContext first
      (append typeScope termScope boundContext second third) := by
  apply ext
  simp [List.append_assoc]

end WfList

/-- Well-formedness of a dense implementation is well-formedness of its list view. -/
def Indexed.WellFormed (context : Indexed Sig) : Prop :=
  Context.WellFormed typeScope termScope boundContext context.toList

/-- Well-formedness of an ordered-map implementation is well-formedness of its
declared order. -/
noncomputable def OrderedMap.WellFormed (context : OrderedMap Sig Name) : Prop :=
  Context.WellFormed typeScope termScope boundContext context.toList

private theorem checkTerms_mem_forward {context : ListCtx Sig}
    {sorted : List (Named.Tm Sig)}
    (checked : checkTerms Sig context = some sorted) {proposition : Expr Sig}
    (membership : proposition ∈ context) :
    ∃ sortedProposition,
      check .tm proposition = some sortedProposition ∧ sortedProposition ∈ sorted := by
  induction context generalizing sorted with
  | nil => simp at membership
  | cons head tail ih =>
      cases headCheck : check .tm head with
      | none => simp [checkTerms, headCheck] at checked
      | some sortedHead =>
          cases tailCheck : checkTerms Sig tail with
          | none => simp [checkTerms, headCheck, tailCheck] at checked
          | some sortedTail =>
              have equality : sortedHead :: sortedTail = sorted := by
                simpa [checkTerms, headCheck, tailCheck] using checked
              subst sorted
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨sortedHead, headCheck, by simp⟩
              · obtain ⟨candidate, candidateCheck, candidateMem⟩ :=
                  ih tailCheck membership
                exact ⟨candidate, candidateCheck, by simp [candidateMem]⟩

private theorem checkTerms_mem_reverse {context : ListCtx Sig}
    {sorted : List (Named.Tm Sig)}
    (checked : checkTerms Sig context = some sorted) {proposition : Named.Tm Sig}
    (membership : proposition ∈ sorted) :
    ∃ rawProposition,
      rawProposition ∈ context ∧ check .tm rawProposition = some proposition := by
  induction context generalizing sorted with
  | nil =>
      have equality : ([] : List (Named.Tm Sig)) = sorted := by
        simpa [checkTerms] using checked
      subst sorted
      simp at membership
  | cons head tail ih =>
      cases headCheck : check .tm head with
      | none => simp [checkTerms, headCheck] at checked
      | some sortedHead =>
          cases tailCheck : checkTerms Sig tail with
          | none => simp [checkTerms, headCheck, tailCheck] at checked
          | some sortedTail =>
              have equality : sortedHead :: sortedTail = sorted := by
                simpa [checkTerms, headCheck, tailCheck] using checked
              subst sorted
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨head, by simp, headCheck⟩
              · obtain ⟨candidate, candidateMem, candidateCheck⟩ :=
                  ih tailCheck membership
                exact ⟨candidate, by simp [candidateMem], candidateCheck⟩

private theorem lowerTerms_mem_forward {context : List (Named.Tm Sig)}
    {lowered : List (Nucleus.HolE.Tm Sig types depth)}
    (lowering : Named.lowerTerms typeScope termScope context = some lowered)
    {proposition : Named.Tm Sig} (membership : proposition ∈ context) :
    ∃ loweredProposition,
      Named.lowerTm typeScope termScope proposition = some loweredProposition ∧
      loweredProposition ∈ lowered := by
  induction context generalizing lowered with
  | nil => simp at membership
  | cons head tail ih =>
      cases headLowering : Named.lowerTm typeScope termScope head with
      | none => simp [Named.lowerTerms, headLowering] at lowering
      | some loweredHead =>
          cases tailLowering : Named.lowerTerms typeScope termScope tail with
          | none => simp [Named.lowerTerms, headLowering, tailLowering] at lowering
          | some loweredTail =>
              have equality : loweredHead :: loweredTail = lowered := by
                simpa [Named.lowerTerms, headLowering, tailLowering] using
                  lowering
              subst lowered
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨loweredHead, headLowering, by simp⟩
              · obtain ⟨candidate, candidateLowering, candidateMem⟩ :=
                  ih tailLowering membership
                exact ⟨candidate, candidateLowering, by simp [candidateMem]⟩

private theorem lowerTerms_mem_reverse {context : List (Named.Tm Sig)}
    {lowered : List (Nucleus.HolE.Tm Sig types depth)}
    (lowering : Named.lowerTerms typeScope termScope context = some lowered)
    {proposition : Nucleus.HolE.Tm Sig types depth} (membership : proposition ∈ lowered) :
    ∃ namedProposition,
      namedProposition ∈ context ∧
      Named.lowerTm typeScope termScope namedProposition = some proposition := by
  induction context generalizing lowered with
  | nil =>
      have equality : ([] : List (Nucleus.HolE.Tm Sig types depth)) = lowered := by
        simpa [Named.lowerTerms] using lowering
      subst lowered
      simp at membership
  | cons head tail ih =>
      cases headLowering : Named.lowerTm typeScope termScope head with
      | none => simp [Named.lowerTerms, headLowering] at lowering
      | some loweredHead =>
          cases tailLowering : Named.lowerTerms typeScope termScope tail with
          | none => simp [Named.lowerTerms, headLowering, tailLowering] at lowering
          | some loweredTail =>
              have equality : loweredHead :: loweredTail = lowered := by
                simpa [Named.lowerTerms, headLowering, tailLowering] using
                  lowering
              subst lowered
              rcases List.mem_cons.mp membership with rfl | membership
              · exact ⟨head, by simp, headLowering⟩
              · obtain ⟨candidate, candidateMem, candidateLowering⟩ :=
                  ih tailLowering membership
                exact ⟨candidate, by simp [candidateMem], candidateLowering⟩

/-- A well-formed context compiles to the sorted named and locally nameless
hypothesis lists expected by the proof kernel. -/
theorem WellFormed.compile {context : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext context) :
    ∃ sorted lowered,
      checkTerms Sig context = some sorted ∧
      Named.lowerTerms typeScope termScope sorted = some lowered ∧
      (∀ proposition, proposition ∈ lowered →
        Nucleus.HolE.HasType boundContext proposition .boolTy) := by
  induction context with
  | nil =>
      exact ⟨[], [], by simp [checkTerms], by simp [Named.lowerTerms],
        fun proposition membership => by simp at membership⟩
  | cons head tail ih =>
      obtain ⟨sortedHead, loweredHead, headCheck, headLowering, headTyping⟩ :=
        valid.head typeScope termScope boundContext
      obtain ⟨sortedTail, loweredTail, tailCheck, tailLowering, tailTyping⟩ :=
        ih (valid.tail typeScope termScope boundContext)
      refine ⟨sortedHead :: sortedTail, loweredHead :: loweredTail, ?_, ?_, ?_⟩
      · simp [checkTerms, headCheck, tailCheck]
      · simp [Named.lowerTerms, headLowering, tailLowering]
      · intro proposition membership
        rcases List.mem_cons.mp membership with rfl | membership
        · exact headTyping
        · exact tailTyping proposition membership

/-- Derivability from an unsorted named assumption list. -/
def Derives (context : ListCtx Sig) (conclusion : Expr Sig) : Prop :=
  Nonempty (Unsorted.Proves typeScope termScope boundContext context conclusion)

/-- Every assumption of a well-formed context is derivable. -/
theorem Derives.hyp {context : ListCtx Sig} {proposition : Expr Sig}
    (valid : WellFormed typeScope termScope boundContext context)
    (membership : proposition ∈ context) :
    Derives typeScope termScope boundContext context proposition := by
  obtain ⟨sorted, lowered, contextCheck, contextLowering, typed⟩ :=
    valid.compile typeScope termScope boundContext
  have typedDefEq : TypedHyps boundContext lowered :=
    fun proposition membership => .exact (typed proposition membership)
  obtain ⟨sortedProposition, propositionCheck, sortedMembership⟩ :=
    checkTerms_mem_forward contextCheck membership
  obtain ⟨loweredProposition, propositionLowering, loweredMembership⟩ :=
    lowerTerms_mem_forward typeScope termScope contextLowering sortedMembership
  exact ⟨⟨sorted, sortedProposition, contextCheck, propositionCheck,
    ⟨lowered, loweredProposition, contextLowering, propositionLowering,
      .hyp typedDefEq (.exact (typed loweredProposition loweredMembership))
        loweredMembership⟩⟩⟩

@[simp] theorem isProposition_true :
    IsProposition typeScope termScope boundContext (.bool true) := by
  exact ⟨.bool true, .bool true, rfl, by simp [Named.lowerTm], .bool true⟩

@[simp] theorem isProposition_false :
    IsProposition typeScope termScope boundContext (.bool false) := by
  exact ⟨.bool false, .bool false, rfl, by simp [Named.lowerTm], .bool false⟩

/-- Primitive true is derivable from every well-formed context. -/
theorem Derives.truth {context : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext context) :
    Derives typeScope termScope boundContext context (.bool true) := by
  obtain ⟨sorted, lowered, contextCheck, contextLowering, typed⟩ :=
    valid.compile typeScope termScope boundContext
  have typedDefEq : TypedHyps boundContext lowered :=
    fun proposition membership => .exact (typed proposition membership)
  exact ⟨⟨sorted, .bool true, contextCheck, rfl,
    ⟨lowered, .bool true, contextLowering, by simp [Named.lowerTm],
      .truth typedDefEq (.exact (.bool true))⟩⟩⟩

/-- A proof of false eliminates to any syntax-directed Boolean proposition. -/
theorem Derives.falseElim {context : ListCtx Sig} {conclusion : Expr Sig}
    (conclusionValid : IsProposition typeScope termScope boundContext conclusion)
    (falseProof : Derives typeScope termScope boundContext context (.bool false)) :
    Derives typeScope termScope boundContext context conclusion := by
  obtain ⟨proof⟩ := falseProof
  obtain ⟨sortedConclusion, loweredConclusion, conclusionCheck,
    conclusionLowering, conclusionTyping⟩ := conclusionValid
  have sortedFalseEq : proof.sortedConclusion = (.bool false : Named.Tm Sig) :=
    Option.some.inj (proof.conclusionCheck.symm.trans rfl)
  have loweredFalseEq :
      proof.derivation.loweredConclusion =
        (.bool false : Nucleus.HolE.Tm Sig types depth) :=
    Option.some.inj <| calc
      some proof.derivation.loweredConclusion =
          Named.lowerTm typeScope termScope proof.sortedConclusion :=
        proof.derivation.conclusionLowering.symm
      _ = Named.lowerTm typeScope termScope (.bool false) :=
        congrArg (Named.lowerTm typeScope termScope) sortedFalseEq
      _ = some (.bool false) := by simp [Named.lowerTm]
  have loweredFalseProof :
      Nucleus.HolE.Proves boundContext proof.derivation.loweredHypotheses
        (.bool false) :=
    loweredFalseEq ▸ proof.derivation.derivation
  exact ⟨⟨proof.sortedHypotheses, sortedConclusion, proof.hypothesesCheck,
    conclusionCheck,
    ⟨proof.derivation.loweredHypotheses, loweredConclusion,
      proof.derivation.hypothesesLowering, conclusionLowering,
      .falseElim proof.derivation.derivation.typedHypotheses
        (.exact conclusionTyping) (.exact conclusionTyping) loweredFalseProof⟩⟩⟩

/-- Structural weakening of an unsorted named proof. -/
theorem Derives.mono {source target : ListCtx Sig} {conclusion : Expr Sig}
    (targetValid : WellFormed typeScope termScope boundContext target)
    (subset : ∀ proposition, proposition ∈ source → proposition ∈ target)
    (proof : Derives typeScope termScope boundContext source conclusion) :
    Derives typeScope termScope boundContext target conclusion := by
  obtain ⟨proof⟩ := proof
  obtain ⟨targetSorted, targetLowered, targetCheck, targetLowering, targetRawTyped⟩ :=
    targetValid.compile typeScope termScope boundContext
  have targetTyped : TypedHyps boundContext targetLowered :=
    fun proposition membership => .exact (targetRawTyped proposition membership)
  let loweredSubset : ∀ proposition, proposition ∈ proof.derivation.loweredHypotheses →
      proposition ∈ targetLowered := by
    intro loweredProposition loweredMembership
    obtain ⟨sortedProposition, sortedMembership, propositionLowering⟩ :=
      lowerTerms_mem_reverse typeScope termScope proof.derivation.hypothesesLowering
        loweredMembership
    obtain ⟨rawProposition, rawMembership, propositionCheck⟩ :=
      checkTerms_mem_reverse proof.hypothesesCheck sortedMembership
    have targetMembership := subset rawProposition rawMembership
    obtain ⟨targetSortedProposition, targetPropositionCheck, targetSortedMembership⟩ :=
      checkTerms_mem_forward targetCheck targetMembership
    rw [propositionCheck] at targetPropositionCheck
    cases Option.some.inj targetPropositionCheck
    obtain ⟨targetLoweredProposition, targetPropositionLowering,
      targetLoweredMembership⟩ := lowerTerms_mem_forward typeScope termScope
        targetLowering targetSortedMembership
    rw [propositionLowering] at targetPropositionLowering
    cases Option.some.inj targetPropositionLowering
    exact targetLoweredMembership
  exact ⟨⟨targetSorted, proof.sortedConclusion, targetCheck, proof.conclusionCheck,
    ⟨targetLowered, proof.derivation.loweredConclusion, targetLowering,
      proof.derivation.conclusionLowering,
      proof.derivation.derivation.mapHypotheses targetTyped loweredSubset⟩⟩⟩

/-- Substitution of named, unsorted proof hypotheses, obtained by compiling to
the locally nameless kernel and applying its admissible cut operation. -/
theorem Derives.cut {source target : ListCtx Sig} {conclusion : Expr Sig}
    (typedContext : TypedCtx boundContext)
    (sourceValid : WellFormed typeScope termScope boundContext source)
    (targetValid : WellFormed typeScope termScope boundContext target)
    (replacement : ∀ proposition, proposition ∈ source →
      Derives typeScope termScope boundContext target proposition)
    (derivation : Derives typeScope termScope boundContext source conclusion) :
    Derives typeScope termScope boundContext target conclusion := by
  obtain ⟨derivation⟩ := derivation
  obtain ⟨sourceSorted, sourceLowered, sourceCheck, sourceLowering,
    sourceRawTyped⟩ := sourceValid.compile typeScope termScope boundContext
  have sourceSortedEq : derivation.sortedHypotheses = sourceSorted :=
    Option.some.inj (derivation.hypothesesCheck.symm.trans sourceCheck)
  cases sourceSortedEq
  have sourceLoweredEq : derivation.derivation.loweredHypotheses = sourceLowered :=
    Option.some.inj
      (derivation.derivation.hypothesesLowering.symm.trans sourceLowering)
  cases sourceLoweredEq
  obtain ⟨targetSorted, targetLowered, targetCheck, targetLowering,
    targetRawTyped⟩ := targetValid.compile typeScope termScope boundContext
  have targetTyped : TypedHyps boundContext targetLowered :=
    fun proposition membership => .exact (targetRawTyped proposition membership)
  have loweredReplacement : ∀ proposition,
      proposition ∈ derivation.derivation.loweredHypotheses →
      Nucleus.HolE.Proves boundContext targetLowered proposition := by
    intro loweredProposition loweredMembership
    have sortedWitness :=
      lowerTerms_mem_reverse typeScope termScope sourceLowering loweredMembership
    let sortedProposition := Classical.choose sortedWitness
    have sortedProperties := Classical.choose_spec sortedWitness
    have sortedMembership := sortedProperties.1
    have propositionLowering := sortedProperties.2
    have rawWitness := checkTerms_mem_reverse sourceCheck sortedMembership
    let rawProposition := Classical.choose rawWitness
    have rawProperties := Classical.choose_spec rawWitness
    have rawMembership := rawProperties.1
    have propositionCheck := rawProperties.2
    let proof := Classical.choice (replacement rawProposition rawMembership)
    have targetSortedEq : proof.sortedHypotheses = targetSorted :=
      Option.some.inj (proof.hypothesesCheck.symm.trans targetCheck)
    have conclusionSortedEq : proof.sortedConclusion = sortedProposition :=
      Option.some.inj (proof.conclusionCheck.symm.trans propositionCheck)
    have targetLoweredEq : proof.derivation.loweredHypotheses = targetLowered :=
      Option.some.inj <| calc
        some proof.derivation.loweredHypotheses =
            Named.lowerTerms typeScope termScope proof.sortedHypotheses :=
          proof.derivation.hypothesesLowering.symm
        _ = Named.lowerTerms typeScope termScope targetSorted :=
          congrArg (Named.lowerTerms typeScope termScope) targetSortedEq
        _ = some targetLowered := targetLowering
    have conclusionLoweredEq :
        proof.derivation.loweredConclusion = loweredProposition :=
      Option.some.inj <| calc
        some proof.derivation.loweredConclusion =
            Named.lowerTm typeScope termScope proof.sortedConclusion :=
          proof.derivation.conclusionLowering.symm
        _ = Named.lowerTm typeScope termScope sortedProposition :=
          congrArg (Named.lowerTm typeScope termScope) conclusionSortedEq
        _ = some loweredProposition := propositionLowering
    have proofTypeEq :
        Nucleus.HolE.Proves boundContext proof.derivation.loweredHypotheses
            proof.derivation.loweredConclusion =
          Nucleus.HolE.Proves boundContext targetLowered loweredProposition := by
      rw [targetLoweredEq, conclusionLoweredEq]
    exact proofTypeEq.mp proof.derivation.derivation
  exact ⟨⟨targetSorted, derivation.sortedConclusion, targetCheck,
    derivation.conclusionCheck,
    ⟨targetLowered, derivation.derivation.loweredConclusion, targetLowering,
      derivation.derivation.conclusionLowering,
      Nucleus.HolE.Proves.cut typedContext targetTyped sourceRawTyped
        loweredReplacement derivation.derivation.derivation⟩⟩⟩

/-- `source ⇒ target` means that both endpoints are valid assumption
contexts and `source` proves every assumption in `target`.  Carrying endpoint
validity makes this a partial preorder whose reflexive domain is exactly the
well-formed contexts. -/
def Entails (source target : ListCtx Sig) : Prop :=
  WellFormed typeScope termScope boundContext source ∧
  WellFormed typeScope termScope boundContext target ∧
  ∀ proposition, proposition ∈ target →
    Derives typeScope termScope boundContext source proposition

theorem entails_self_iff (context : ListCtx Sig) :
    Entails typeScope termScope boundContext context context ↔
    WellFormed typeScope termScope boundContext context := by
  constructor
  · exact And.left
  · intro valid
    exact ⟨valid, valid, fun proposition membership =>
      Derives.hyp typeScope termScope boundContext valid membership⟩

theorem entails_of_subset {source target : ListCtx Sig}
    (sourceValid : WellFormed typeScope termScope boundContext source)
    (subset : ∀ proposition, proposition ∈ target → proposition ∈ source) :
    Entails typeScope termScope boundContext source target :=
  ⟨sourceValid,
    fun proposition membership => sourceValid proposition (subset proposition membership),
    fun proposition membership =>
      Derives.hyp typeScope termScope boundContext sourceValid (subset proposition membership)⟩

theorem entails_of_sublist {source target : ListCtx Sig}
    (sourceValid : WellFormed typeScope termScope boundContext source)
    (sublist : target.Sublist source) :
    Entails typeScope termScope boundContext source target :=
  entails_of_subset typeScope termScope boundContext sourceValid
    (fun _ membership => sublist.subset membership)

theorem entails_permutation {source target : ListCtx Sig}
    (sourceValid : WellFormed typeScope termScope boundContext source)
    (permutation : source.Perm target) :
    Entails typeScope termScope boundContext source target :=
  entails_of_subset typeScope termScope boundContext sourceValid
    (fun _ membership => permutation.mem_iff.mpr membership)

theorem entails_all_permutations_iff (context : ListCtx Sig) :
    (∀ candidate, context.Perm candidate →
      Entails typeScope termScope boundContext context candidate) ↔
    WellFormed typeScope termScope boundContext context := by
  constructor
  · intro all
    exact (all context (List.Perm.refl context)).1
  · intro valid candidate permutation
    exact entails_permutation typeScope termScope boundContext valid permutation

theorem Entails.target_wellFormed {source target : ListCtx Sig}
    (entailment : Entails typeScope termScope boundContext source target) :
    WellFormed typeScope termScope boundContext target :=
  entailment.2.1

theorem Entails.trans (typedContext : TypedCtx boundContext)
    {first second third : ListCtx Sig}
    (left : Entails typeScope termScope boundContext first second)
    (right : Entails typeScope termScope boundContext second third) :
    Entails typeScope termScope boundContext first third := by
  refine ⟨left.1, right.2.1, ?_⟩
  intro proposition membership
  exact Derives.cut typeScope termScope boundContext typedContext
    right.1 left.1 left.2.2 (right.2.2 proposition membership)

theorem entails_append_left {boundTyped : TypedCtx boundContext}
    (left right : WfList typeScope termScope boundContext boundTyped) :
    Entails typeScope termScope boundContext (left.raw ++ right.raw) left.raw :=
  entails_of_subset typeScope termScope boundContext
    (left.valid.append typeScope termScope boundContext right.valid)
    (fun _ membership => List.mem_append_left _ membership)

theorem entails_append_right {boundTyped : TypedCtx boundContext}
    (left right : WfList typeScope termScope boundContext boundTyped) :
    Entails typeScope termScope boundContext (left.raw ++ right.raw) right.raw :=
  entails_of_subset typeScope termScope boundContext
    (left.valid.append typeScope termScope boundContext right.valid)
    (fun _ membership => List.mem_append_right _ membership)

theorem entails_append_mono
    {boundTyped : TypedCtx boundContext}
    {left₁ left₂ right₁ right₂ :
      WfList typeScope termScope boundContext boundTyped}
    (left : Entails typeScope termScope boundContext left₁.raw left₂.raw)
    (right : Entails typeScope termScope boundContext right₁.raw right₂.raw) :
    Entails typeScope termScope boundContext
      (left₁.raw ++ right₁.raw) (left₂.raw ++ right₂.raw) := by
  refine ⟨left₁.valid.append typeScope termScope boundContext right₁.valid,
    left₂.valid.append typeScope termScope boundContext right₂.valid, ?_⟩
  intro proposition membership
  rcases List.mem_append.mp membership with membership | membership
  · exact Derives.mono typeScope termScope boundContext
      (left₁.valid.append typeScope termScope boundContext right₁.valid)
      (fun candidate candidateMem => List.mem_append_left _ candidateMem)
      (left.2.2 proposition membership)
  · exact Derives.mono typeScope termScope boundContext
      (left₁.valid.append typeScope termScope boundContext right₁.valid)
      (fun candidate candidateMem => List.mem_append_right _ candidateMem)
      (right.2.2 proposition membership)

namespace WfList

/-- The one-assumption presentation containing primitive true. -/
def singletonTrue (boundTyped : TypedCtx boundContext) :
    WfList typeScope termScope boundContext boundTyped :=
  ⟨[.bool true],
    WellFormed.cons typeScope termScope boundContext
      (isProposition_true typeScope termScope boundContext)
      (wellFormed_nil typeScope termScope boundContext)⟩

@[simp] theorem raw_singletonTrue (boundTyped : TypedCtx boundContext) :
    (singletonTrue typeScope termScope boundContext boundTyped).raw =
      [.bool true] := rfl

/-- The one-assumption presentation containing primitive false. -/
def singletonFalse (boundTyped : TypedCtx boundContext) :
    WfList typeScope termScope boundContext boundTyped :=
  ⟨[.bool false],
    WellFormed.cons typeScope termScope boundContext
      (isProposition_false typeScope termScope boundContext)
      (wellFormed_nil typeScope termScope boundContext)⟩

@[simp] theorem raw_singletonFalse (boundTyped : TypedCtx boundContext) :
    (singletonFalse typeScope termScope boundContext boundTyped).raw =
      [.bool false] := rfl

end WfList

/-- Every well-formed context entails the empty assumption list. -/
theorem entails_empty {boundTyped : TypedCtx boundContext}
    (context : WfList typeScope termScope boundContext boundTyped) :
    Entails typeScope termScope boundContext context.raw [] :=
  entails_of_subset typeScope termScope boundContext context.valid (by simp)

/-- Every well-formed context entails primitive true. -/
theorem entails_singletonTrue {boundTyped : TypedCtx boundContext}
    (context : WfList typeScope termScope boundContext boundTyped) :
    Entails typeScope termScope boundContext context.raw
      (WfList.singletonTrue typeScope termScope boundContext boundTyped).raw := by
  let trueContext := WfList.singletonTrue typeScope termScope boundContext boundTyped
  refine ⟨context.valid, trueContext.valid, ?_⟩
  intro proposition membership
  have equality : proposition = (.bool true : Expr Sig) := by simpa using membership
  subst proposition
  exact Derives.truth typeScope termScope boundContext context.valid

/-- Primitive false entails every well-formed context. -/
theorem entails_singletonFalse {boundTyped : TypedCtx boundContext}
    (context : WfList typeScope termScope boundContext boundTyped) :
    Entails typeScope termScope boundContext
      (WfList.singletonFalse typeScope termScope boundContext boundTyped).raw
      context.raw := by
  let falseContext :=
    WfList.singletonFalse typeScope termScope boundContext boundTyped
  refine ⟨falseContext.valid, context.valid, ?_⟩
  intro proposition membership
  exact Derives.falseElim typeScope termScope boundContext
    (context.valid proposition membership)
    (Derives.hyp typeScope termScope boundContext falseContext.valid (by simp))

/-- Concatenation is the greatest lower bound for context entailment. -/
theorem entails_append {boundTyped : TypedCtx boundContext}
    {source left right : WfList typeScope termScope boundContext boundTyped}
    (sourceLeft : Entails typeScope termScope boundContext source.raw left.raw)
    (sourceRight : Entails typeScope termScope boundContext source.raw right.raw) :
    Entails typeScope termScope boundContext source.raw (left.raw ++ right.raw) := by
  refine ⟨sourceLeft.1,
    left.valid.append typeScope termScope boundContext right.valid, ?_⟩
  intro proposition membership
  rcases List.mem_append.mp membership with membership | membership
  · exact sourceLeft.2.2 proposition membership
  · exact sourceRight.2.2 proposition membership

section Quotient

variable (boundTyped : TypedCtx boundContext)

instance : LE (WfList typeScope termScope boundContext boundTyped) where
  le left right := Entails typeScope termScope boundContext left.raw right.raw

instance : Preorder (WfList typeScope termScope boundContext boundTyped) where
  le_refl context := (entails_self_iff typeScope termScope boundContext context.raw).2
    context.valid
  le_trans _ _ _ := Entails.trans typeScope termScope boundContext boundTyped

namespace WfList

/-- The empty presentation is greatest up to entailment. -/
theorem le_empty
    (context : WfList typeScope termScope boundContext boundTyped) :
    context ≤ empty typeScope termScope boundContext boundTyped :=
  entails_empty typeScope termScope boundContext context

/-- The singleton-true presentation is also greatest up to entailment. -/
theorem le_singletonTrue
    (context : WfList typeScope termScope boundContext boundTyped) :
    context ≤ singletonTrue typeScope termScope boundContext boundTyped :=
  entails_singletonTrue typeScope termScope boundContext context

/-- The singleton-false presentation is least up to entailment. -/
theorem singletonFalse_le
    (context : WfList typeScope termScope boundContext boundTyped) :
    singletonFalse typeScope termScope boundContext boundTyped ≤ context :=
  entails_singletonFalse typeScope termScope boundContext context

/-- Concatenation entails its left input. -/
theorem append_le_left
    (left right : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext left right ≤ left :=
  entails_append_left typeScope termScope boundContext left right

/-- Concatenation entails its right input. -/
theorem append_le_right
    (left right : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext left right ≤ right :=
  entails_append_right typeScope termScope boundContext left right

/-- Any common lower bound entails the concatenated presentation. -/
theorem le_append
    {source left right : WfList typeScope termScope boundContext boundTyped}
    (sourceLeft : source ≤ left) (sourceRight : source ≤ right) :
    source ≤ append typeScope termScope boundContext left right :=
  entails_append typeScope termScope boundContext sourceLeft sourceRight

/-- Empty and singleton true are mutually entailing presentations. -/
theorem singletonTrue_equivalent_empty :
    singletonTrue typeScope termScope boundContext boundTyped ≤
        empty typeScope termScope boundContext boundTyped ∧
      empty typeScope termScope boundContext boundTyped ≤
        singletonTrue typeScope termScope boundContext boundTyped :=
  ⟨le_empty typeScope termScope boundContext boundTyped _,
    le_singletonTrue typeScope termScope boundContext boundTyped _⟩

end WfList

/-- Mutual derivability is the partial-equivalence relation induced by
context entailment.  Restricted to `WfList`, it is an equivalence relation. -/
def Equivalent
    (left right : WfList typeScope termScope boundContext boundTyped) : Prop :=
  left ≤ right ∧ right ≤ left

/-- Contexts modulo mutual derivability.  Mathlib's antisymmetrization equips
this quotient with the induced partial order. -/
abbrev QuotientCtx :=
  Antisymmetrization
    (WfList typeScope termScope boundContext boundTyped) (· ≤ ·)

namespace QuotientCtx

/-- Inject a well-formed presentation into the context quotient. -/
def ofWfList
    (context : WfList typeScope termScope boundContext boundTyped) :
    QuotientCtx typeScope termScope boundContext boundTyped :=
  toAntisymmetrization (· ≤ ·) context

/-- The empty context modulo mutual derivability. -/
def empty (boundTyped : TypedCtx boundContext) :
    QuotientCtx typeScope termScope boundContext boundTyped :=
  ofWfList typeScope termScope boundContext boundTyped
    (WfList.empty typeScope termScope boundContext boundTyped)

/-- Primitive true as a one-assumption quotient presentation. -/
def singletonTrue : QuotientCtx typeScope termScope boundContext boundTyped :=
  ofWfList typeScope termScope boundContext boundTyped
    (WfList.singletonTrue typeScope termScope boundContext boundTyped)

/-- Primitive false as a one-assumption quotient presentation. -/
def singletonFalse : QuotientCtx typeScope termScope boundContext boundTyped :=
  ofWfList typeScope termScope boundContext boundTyped
    (WfList.singletonFalse typeScope termScope boundContext boundTyped)

/-- Concatenation descends through mutual derivability. -/
def append : QuotientCtx typeScope termScope boundContext boundTyped →
    QuotientCtx typeScope termScope boundContext boundTyped →
    QuotientCtx typeScope termScope boundContext boundTyped :=
  Quotient.map₂ (WfList.append typeScope termScope boundContext) <| by
    intro left₁ left₂ leftEquivalent right₁ right₂ rightEquivalent
    exact ⟨
      entails_append_mono typeScope termScope boundContext
        leftEquivalent.1 rightEquivalent.1,
      entails_append_mono typeScope termScope boundContext
        leftEquivalent.2 rightEquivalent.2⟩

@[simp] theorem append_ofWfList
    (left right : WfList typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped
      (ofWfList typeScope termScope boundContext boundTyped left)
      (ofWfList typeScope termScope boundContext boundTyped right) =
    ofWfList typeScope termScope boundContext boundTyped
      (WfList.append typeScope termScope boundContext left right) := rfl

/-- Every quotient context lies below the empty presentation. -/
theorem le_empty
    (context : QuotientCtx typeScope termScope boundContext boundTyped) :
    context ≤ empty typeScope termScope boundContext boundTyped := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      exact WfList.le_empty typeScope termScope boundContext boundTyped context

/-- Every quotient context lies below the singleton-true presentation. -/
theorem le_singletonTrue
    (context : QuotientCtx typeScope termScope boundContext boundTyped) :
    context ≤ singletonTrue typeScope termScope boundContext boundTyped := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      exact WfList.le_singletonTrue typeScope termScope boundContext boundTyped context

/-- The singleton-false presentation lies below every quotient context. -/
theorem singletonFalse_le
    (context : QuotientCtx typeScope termScope boundContext boundTyped) :
    singletonFalse typeScope termScope boundContext boundTyped ≤ context := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      exact WfList.singletonFalse_le typeScope termScope boundContext boundTyped context

/-- Quotient concatenation lies below its left input. -/
theorem append_le_left
    (left right : QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped left right ≤ left := by
  induction left using Antisymmetrization.induction_on with
  | _ left =>
      induction right using Antisymmetrization.induction_on with
      | _ right =>
          exact WfList.append_le_left typeScope termScope boundContext boundTyped left right

/-- Quotient concatenation lies below its right input. -/
theorem append_le_right
    (left right : QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped left right ≤ right := by
  induction left using Antisymmetrization.induction_on with
  | _ left =>
      induction right using Antisymmetrization.induction_on with
      | _ right =>
          exact WfList.append_le_right typeScope termScope boundContext boundTyped left right

/-- Quotient concatenation is above every common lower bound. -/
theorem le_append
    {source left right : QuotientCtx typeScope termScope boundContext boundTyped}
    (sourceLeft : source ≤ left) (sourceRight : source ≤ right) :
    source ≤ append typeScope termScope boundContext boundTyped left right := by
  induction source using Antisymmetrization.induction_on with
  | _ source =>
      induction left using Antisymmetrization.induction_on with
      | _ left =>
          induction right using Antisymmetrization.induction_on with
          | _ right =>
              exact WfList.le_append typeScope termScope boundContext boundTyped
                sourceLeft sourceRight

instance instOrderTop :
    OrderTop (QuotientCtx typeScope termScope boundContext boundTyped) where
  top := empty typeScope termScope boundContext boundTyped
  le_top := le_empty typeScope termScope boundContext boundTyped

instance instOrderBot :
    OrderBot (QuotientCtx typeScope termScope boundContext boundTyped) where
  bot := singletonFalse typeScope termScope boundContext boundTyped
  bot_le := singletonFalse_le typeScope termScope boundContext boundTyped

instance instSemilatticeInf :
    SemilatticeInf (QuotientCtx typeScope termScope boundContext boundTyped) where
  toPartialOrder := inferInstance
  inf := append typeScope termScope boundContext boundTyped
  inf_le_left := append_le_left typeScope termScope boundContext boundTyped
  inf_le_right := append_le_right typeScope termScope boundContext boundTyped
  le_inf := fun _ _ _ => le_append typeScope termScope boundContext boundTyped

@[simp] theorem empty_eq_top :
    empty typeScope termScope boundContext boundTyped = ⊤ := rfl

@[simp] theorem singletonFalse_eq_bot :
    singletonFalse typeScope termScope boundContext boundTyped = ⊥ := rfl

@[simp] theorem append_eq_inf
    (left right : QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped left right = left ⊓ right := rfl

/-- The singleton primitive-true context is the greatest quotient context. -/
@[simp] theorem singletonTrue_eq_top :
    singletonTrue typeScope termScope boundContext boundTyped = ⊤ := by
  apply le_antisymm
  · exact le_top
  · exact le_singletonTrue typeScope termScope boundContext boundTyped ⊤

/-- A greatest quotient context is the canonical top element. -/
theorem eq_top_of_forall_le
    (candidate : QuotientCtx typeScope termScope boundContext boundTyped)
    (greatest : ∀ context, context ≤ candidate) : candidate = ⊤ := by
  apply le_antisymm
  · exact le_top
  · exact greatest ⊤

/-- A least quotient context is the canonical bottom element. -/
theorem eq_bot_of_le_all
    (candidate : QuotientCtx typeScope termScope boundContext boundTyped)
    (least : ∀ context, candidate ≤ context) : candidate = ⊥ := by
  apply le_antisymm
  · exact least ⊥
  · exact bot_le

/-- The greatest lower bound characterized by the order laws is concatenation. -/
theorem eq_append_of_glb
    (candidate left right :
      QuotientCtx typeScope termScope boundContext boundTyped)
    (candidateLeft : candidate ≤ left) (candidateRight : candidate ≤ right)
    (greatest : ∀ context, context ≤ left → context ≤ right →
      context ≤ candidate) :
    candidate = append typeScope termScope boundContext boundTyped left right := by
  apply le_antisymm
  · exact le_append typeScope termScope boundContext boundTyped
      candidateLeft candidateRight
  · exact greatest _
      (append_le_left typeScope termScope boundContext boundTyped left right)
      (append_le_right typeScope termScope boundContext boundTyped left right)

@[simp] theorem empty_append
    (boundTyped : TypedCtx boundContext)
    (context : QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped
      (empty typeScope termScope boundContext boundTyped) context = context := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      change append typeScope termScope boundContext boundTyped
        (ofWfList typeScope termScope boundContext boundTyped
          (WfList.empty typeScope termScope boundContext boundTyped))
        (ofWfList typeScope termScope boundContext boundTyped context) =
        ofWfList typeScope termScope boundContext boundTyped context
      rw [append_ofWfList, WfList.empty_append]

@[simp] theorem append_empty
    (boundTyped : TypedCtx boundContext)
    (context : QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped context
      (empty typeScope termScope boundContext boundTyped) = context := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      change append typeScope termScope boundContext boundTyped
        (ofWfList typeScope termScope boundContext boundTyped context)
        (ofWfList typeScope termScope boundContext boundTyped
          (WfList.empty typeScope termScope boundContext boundTyped)) =
        ofWfList typeScope termScope boundContext boundTyped context
      rw [append_ofWfList, WfList.append_empty]

@[simp] theorem append_assoc
    (first second third :
      QuotientCtx typeScope termScope boundContext boundTyped) :
    append typeScope termScope boundContext boundTyped
      (append typeScope termScope boundContext boundTyped first second) third =
    append typeScope termScope boundContext boundTyped first
      (append typeScope termScope boundContext boundTyped second third) := by
  induction first using Antisymmetrization.induction_on with
  | _ first =>
      induction second using Antisymmetrization.induction_on with
      | _ second =>
          induction third using Antisymmetrization.induction_on with
          | _ third =>
              change append typeScope termScope boundContext boundTyped
                (append typeScope termScope boundContext boundTyped
                  (ofWfList typeScope termScope boundContext boundTyped first)
                  (ofWfList typeScope termScope boundContext boundTyped second))
                (ofWfList typeScope termScope boundContext boundTyped third) =
                append typeScope termScope boundContext boundTyped
                  (ofWfList typeScope termScope boundContext boundTyped first)
                  (append typeScope termScope boundContext boundTyped
                    (ofWfList typeScope termScope boundContext boundTyped second)
                    (ofWfList typeScope termScope boundContext boundTyped third))
              rw [append_ofWfList, append_ofWfList, append_ofWfList,
                append_ofWfList, WfList.append_assoc]

end QuotientCtx

end Quotient

end Nucleus.HolE.Named.Unsorted.Context
