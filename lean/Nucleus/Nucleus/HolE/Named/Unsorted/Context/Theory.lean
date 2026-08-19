import Nucleus.HolE.Named.Unsorted.Context.Repr
import Nucleus.HolE.Named.Unsorted.Kernel
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Antisymmetrization

/-!
# Contexts and entailment for unsorted named HolE

The ambient type-variable scope, term-variable scope, and locally nameless
bound context are fixed throughout.  The contexts defined here are lists of
named, unsorted assumptions.

The proof kernel requires every hypothesis to have Boolean type up to type
conversion.  `WellFormed` exposes precisely that invariant.  In particular,
entailment includes well-formedness of its source; without it, raw pointwise
derivability is not transitive when the intermediate context is empty.
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
lowers under the named scopes, and has Boolean type up to type conversion. -/
def IsProposition (proposition : Expr Sig) : Prop :=
  ∃ sorted lowered,
    check .tm proposition = some sorted ∧
    Named.lowerTm typeScope termScope sorted = some lowered ∧
    HasTypeDefEq boundContext lowered .boolTy

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

/-- The well-formed list presentation. -/
structure WfList where
  raw : ListCtx Sig
  valid : WellFormed typeScope termScope boundContext raw

namespace WfList

@[ext] theorem ext {left right : WfList typeScope termScope boundContext}
    (raw : left.raw = right.raw) : left = right := by
  cases left
  cases right
  cases raw
  rfl

def empty : WfList typeScope termScope boundContext :=
  ⟨[], wellFormed_nil typeScope termScope boundContext⟩

def append (left right : WfList typeScope termScope boundContext) :
    WfList typeScope termScope boundContext :=
  ⟨left.raw ++ right.raw, left.valid.append typeScope termScope boundContext right.valid⟩

@[simp] theorem raw_empty : (empty typeScope termScope boundContext).raw = [] := rfl

@[simp] theorem raw_append
    (left right : WfList typeScope termScope boundContext) :
    (WfList.append typeScope termScope boundContext left right).raw =
      left.raw ++ right.raw := rfl

@[simp] theorem empty_append (context : WfList typeScope termScope boundContext) :
    append typeScope termScope boundContext
      (empty typeScope termScope boundContext) context = context := by
  apply ext
  simp

@[simp] theorem append_empty (context : WfList typeScope termScope boundContext) :
    append typeScope termScope boundContext context
      (empty typeScope termScope boundContext) = context := by
  apply ext
  simp

@[simp] theorem append_assoc
    (first second third : WfList typeScope termScope boundContext) :
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
      TypedHyps boundContext lowered := by
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
  obtain ⟨sortedProposition, propositionCheck, sortedMembership⟩ :=
    checkTerms_mem_forward contextCheck membership
  obtain ⟨loweredProposition, propositionLowering, loweredMembership⟩ :=
    lowerTerms_mem_forward typeScope termScope contextLowering sortedMembership
  exact ⟨⟨sorted, sortedProposition, contextCheck, propositionCheck,
    ⟨lowered, loweredProposition, contextLowering, propositionLowering,
      .hyp typed (typed loweredProposition loweredMembership) loweredMembership⟩⟩⟩

/-- Structural weakening of an unsorted named proof. -/
theorem Derives.mono {source target : ListCtx Sig} {conclusion : Expr Sig}
    (targetValid : WellFormed typeScope termScope boundContext target)
    (subset : ∀ proposition, proposition ∈ source → proposition ∈ target)
    (proof : Derives typeScope termScope boundContext source conclusion) :
    Derives typeScope termScope boundContext target conclusion := by
  obtain ⟨proof⟩ := proof
  obtain ⟨targetSorted, targetLowered, targetCheck, targetLowering, targetTyped⟩ :=
    targetValid.compile typeScope termScope boundContext
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

/-- `source ⇒ target` means that `source` is a valid assumption context and
proves every assumption in `target`. -/
def Entails (source target : ListCtx Sig) : Prop :=
  WellFormed typeScope termScope boundContext source ∧
  ∀ proposition, proposition ∈ target →
    Derives typeScope termScope boundContext source proposition

theorem entails_self_iff (context : ListCtx Sig) :
    Entails typeScope termScope boundContext context context ↔
    WellFormed typeScope termScope boundContext context := by
  constructor
  · exact And.left
  · intro valid
    exact ⟨valid, fun proposition membership =>
      Derives.hyp typeScope termScope boundContext valid membership⟩

theorem entails_of_subset {source target : ListCtx Sig}
    (sourceValid : WellFormed typeScope termScope boundContext source)
    (subset : ∀ proposition, proposition ∈ target → proposition ∈ source) :
    Entails typeScope termScope boundContext source target :=
  ⟨sourceValid, fun proposition membership =>
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
    WellFormed typeScope termScope boundContext target := by
  intro proposition membership
  obtain ⟨proof⟩ := entailment.2 proposition membership
  refine ⟨proof.sortedConclusion, proof.derivation.loweredConclusion,
    proof.conclusionCheck, proof.derivation.conclusionLowering, ?_⟩
  exact proof.derivation.derivation.conclusionTyping

/-- Cut admissibility for the named unsorted presentation.  This is isolated
as a capability because the current kernel exposes weakening but has not yet
proved the general proof-substitution theorem needed to implement cut. -/
class HasCut : Prop where
  cut : ∀ {source target : ListCtx Sig} {conclusion : Expr Sig},
    WellFormed typeScope termScope boundContext target →
    (∀ proposition, proposition ∈ source →
      Derives typeScope termScope boundContext target proposition) →
    Derives typeScope termScope boundContext source conclusion →
    Derives typeScope termScope boundContext target conclusion

theorem Entails.trans [HasCut typeScope termScope boundContext]
    {first second third : ListCtx Sig}
    (left : Entails typeScope termScope boundContext first second)
    (right : Entails typeScope termScope boundContext second third) :
    Entails typeScope termScope boundContext first third := by
  refine ⟨left.1, ?_⟩
  intro proposition membership
  exact HasCut.cut left.1 left.2 (right.2 proposition membership)

theorem entails_append_left (left right : WfList typeScope termScope boundContext) :
    Entails typeScope termScope boundContext (left.raw ++ right.raw) left.raw :=
  entails_of_subset typeScope termScope boundContext
    (left.valid.append typeScope termScope boundContext right.valid)
    (fun _ membership => List.mem_append_left _ membership)

theorem entails_append_right (left right : WfList typeScope termScope boundContext) :
    Entails typeScope termScope boundContext (left.raw ++ right.raw) right.raw :=
  entails_of_subset typeScope termScope boundContext
    (left.valid.append typeScope termScope boundContext right.valid)
    (fun _ membership => List.mem_append_right _ membership)

theorem entails_append_mono
    {left₁ left₂ right₁ right₂ : WfList typeScope termScope boundContext}
    (left : Entails typeScope termScope boundContext left₁.raw left₂.raw)
    (right : Entails typeScope termScope boundContext right₁.raw right₂.raw) :
    Entails typeScope termScope boundContext
      (left₁.raw ++ right₁.raw) (left₂.raw ++ right₂.raw) := by
  refine ⟨left₁.valid.append typeScope termScope boundContext right₁.valid, ?_⟩
  intro proposition membership
  rcases List.mem_append.mp membership with membership | membership
  · exact Derives.mono typeScope termScope boundContext
      (left₁.valid.append typeScope termScope boundContext right₁.valid)
      (fun candidate candidateMem => List.mem_append_left _ candidateMem)
      (left.2 proposition membership)
  · exact Derives.mono typeScope termScope boundContext
      (left₁.valid.append typeScope termScope boundContext right₁.valid)
      (fun candidate candidateMem => List.mem_append_right _ candidateMem)
      (right.2 proposition membership)

section Quotient

variable [HasCut typeScope termScope boundContext]

instance : LE (WfList typeScope termScope boundContext) where
  le left right := Entails typeScope termScope boundContext left.raw right.raw

instance : Preorder (WfList typeScope termScope boundContext) where
  le_refl context := (entails_self_iff typeScope termScope boundContext context.raw).2
    context.valid
  le_trans _ _ _ := Entails.trans typeScope termScope boundContext

/-- Mutual derivability is the partial-equivalence relation induced by
context entailment.  Restricted to `WfList`, it is an equivalence relation. -/
def Equivalent (left right : WfList typeScope termScope boundContext) : Prop :=
  left ≤ right ∧ right ≤ left

/-- Contexts modulo mutual derivability.  Mathlib's antisymmetrization equips
this quotient with the induced partial order. -/
abbrev QuotientCtx :=
  Antisymmetrization (WfList typeScope termScope boundContext) (· ≤ ·)

namespace QuotientCtx

/-- Inject a well-formed presentation into the context quotient. -/
def ofWfList (context : WfList typeScope termScope boundContext) :
    QuotientCtx typeScope termScope boundContext :=
  toAntisymmetrization (· ≤ ·) context

/-- The empty context modulo mutual derivability. -/
def empty : QuotientCtx typeScope termScope boundContext :=
  ofWfList typeScope termScope boundContext
    (WfList.empty typeScope termScope boundContext)

/-- Concatenation descends through mutual derivability. -/
def append : QuotientCtx typeScope termScope boundContext →
    QuotientCtx typeScope termScope boundContext →
    QuotientCtx typeScope termScope boundContext :=
  Quotient.map₂ (WfList.append typeScope termScope boundContext) <| by
    intro left₁ left₂ leftEquivalent right₁ right₂ rightEquivalent
    exact ⟨
      entails_append_mono typeScope termScope boundContext
        leftEquivalent.1 rightEquivalent.1,
      entails_append_mono typeScope termScope boundContext
        leftEquivalent.2 rightEquivalent.2⟩

@[simp] theorem append_ofWfList
    (left right : WfList typeScope termScope boundContext) :
    append typeScope termScope boundContext
      (ofWfList typeScope termScope boundContext left)
      (ofWfList typeScope termScope boundContext right) =
    ofWfList typeScope termScope boundContext
      (WfList.append typeScope termScope boundContext left right) := rfl

@[simp] theorem empty_append
    (context : QuotientCtx typeScope termScope boundContext) :
    append typeScope termScope boundContext
      (empty typeScope termScope boundContext) context = context := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      change append typeScope termScope boundContext
        (ofWfList typeScope termScope boundContext
          (WfList.empty typeScope termScope boundContext))
        (ofWfList typeScope termScope boundContext context) =
        ofWfList typeScope termScope boundContext context
      rw [append_ofWfList, WfList.empty_append]

@[simp] theorem append_empty
    (context : QuotientCtx typeScope termScope boundContext) :
    append typeScope termScope boundContext context
      (empty typeScope termScope boundContext) = context := by
  induction context using Antisymmetrization.induction_on with
  | _ context =>
      change append typeScope termScope boundContext
        (ofWfList typeScope termScope boundContext context)
        (ofWfList typeScope termScope boundContext
          (WfList.empty typeScope termScope boundContext)) =
        ofWfList typeScope termScope boundContext context
      rw [append_ofWfList, WfList.append_empty]

@[simp] theorem append_assoc
    (first second third : QuotientCtx typeScope termScope boundContext) :
    append typeScope termScope boundContext
      (append typeScope termScope boundContext first second) third =
    append typeScope termScope boundContext first
      (append typeScope termScope boundContext second third) := by
  induction first using Antisymmetrization.induction_on with
  | _ first =>
      induction second using Antisymmetrization.induction_on with
      | _ second =>
          induction third using Antisymmetrization.induction_on with
          | _ third =>
              change append typeScope termScope boundContext
                (append typeScope termScope boundContext
                  (ofWfList typeScope termScope boundContext first)
                  (ofWfList typeScope termScope boundContext second))
                (ofWfList typeScope termScope boundContext third) =
                append typeScope termScope boundContext
                  (ofWfList typeScope termScope boundContext first)
                  (append typeScope termScope boundContext
                    (ofWfList typeScope termScope boundContext second)
                    (ofWfList typeScope termScope boundContext third))
              rw [append_ofWfList, append_ofWfList, append_ofWfList,
                append_ofWfList, WfList.append_assoc]

end QuotientCtx

end Quotient

end Nucleus.HolE.Named.Unsorted.Context
