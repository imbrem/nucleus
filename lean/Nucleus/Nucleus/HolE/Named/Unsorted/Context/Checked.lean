import Nucleus.HolE.Named.Unsorted.Context.Theory
import Nucleus.HolE.Named.Unsorted.Connectives

/-!
# Checked views of unsorted named HolE contexts

This file connects the raw context API to the checked proof façade.  A checked
view preserves list order and both stages of compilation exactly.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true
set_option linter.unusedSectionVars false

/-- Successful sort checking preserves the raw syntax exactly. -/
theorem erase_eq_of_check_eq_some {expression : Expr Sig Name}
    {checked : Named.Expr Sig Name sort}
    (result : check sort expression = some checked) :
    erase checked = expression := by
  induction expression generalizing sort checked with
  | boolTy =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = .star
          · subst expected
            cases Option.some.inj (by simpa [check] using result)
            rfl
          · simp [check, equality] at result
  | arr domain codomain domainIH codomainIH =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = .star
          · subst expected
            cases domainCheck : check (.kind .star) domain with
            | none => simp [check, domainCheck] at result
            | some domain' =>
                cases codomainCheck : check (.kind .star) codomain with
                | none => simp [check, domainCheck, codomainCheck] at result
                | some codomain' =>
                    cases Option.some.inj (by
                      simpa [check, domainCheck, codomainCheck] using result)
                    simp [erase, domainIH domainCheck, codomainIH codomainCheck]
          · simp [check, equality] at result
  | tyApp domain codomain function argument functionIH argumentIH =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = codomain
          · subst expected
            cases functionCheck : check (.kind (.arr domain codomain)) function with
            | none => simp [check, functionCheck] at result
            | some function' =>
                cases argumentCheck : check (.kind domain) argument with
                | none => simp [check, functionCheck, argumentCheck] at result
                | some argument' =>
                    cases Option.some.inj (by
                      simpa [check, functionCheck, argumentCheck] using result)
                    simp [erase, functionIH functionCheck, argumentIH argumentCheck]
          · simp [check, equality] at result
  | tyLam domain codomain name body bodyIH =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = .arr domain codomain
          · subst expected
            cases bodyCheck : check (.kind codomain) body with
            | none => simp [check, bodyCheck] at result
            | some body' =>
                cases Option.some.inj (by simpa [check, bodyCheck] using result)
                simp [erase, bodyIH bodyCheck]
          · simp [check, equality] at result
  | tyFv name kind =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = kind
          · subst expected
            cases Option.some.inj (by simpa [check] using result)
            rfl
          · simp [check, equality] at result
  | sub carrier name predicate carrierIH predicateIH =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = .star
          · subst expected
            cases carrierCheck : check (.kind .star) carrier with
            | none => simp [check, carrierCheck] at result
            | some carrier' =>
                cases predicateCheck : check .tm predicate with
                | none => simp [check, carrierCheck, predicateCheck] at result
                | some predicate' =>
                    cases Option.some.inj (by
                      simpa [check, carrierCheck, predicateCheck] using result)
                    simp [erase, carrierIH carrierCheck, predicateIH predicateCheck]
          · simp [check, equality] at result
  | tyExists name predicate predicateIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases predicateCheck : check .tm predicate with
          | none => simp [check, predicateCheck] at result
          | some predicate' =>
              cases Option.some.inj (by simpa [check, predicateCheck] using result)
              simp [erase, predicateIH predicateCheck]
  | model name predicate predicateIH =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = .star
          · subst expected
            cases predicateCheck : check .tm predicate with
            | none => simp [check, predicateCheck] at result
            | some predicate' =>
                cases Option.some.inj (by simpa [check, predicateCheck] using result)
                simp [erase, predicateIH predicateCheck]
          · simp [check, equality] at result
  | primFam kind symbol =>
      cases sort with
      | tm => simp [check] at result
      | kind expected =>
          by_cases equality : expected = kind
          · subst expected
            cases Option.some.inj (by simpa [check] using result)
            rfl
          · simp [check, equality] at result
  | primTm symbol =>
      cases sort with
      | kind _ => simp [check] at result
      | tm => simpa [check, erase] using congrArg erase (Option.some.inj result).symm
  | tmFv name type typeIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases typeCheck : check (.kind .star) type with
          | none => simp [check, typeCheck] at result
          | some type' =>
              cases Option.some.inj (by simpa [check, typeCheck] using result)
              simp [erase, typeIH typeCheck]
  | app function argument functionIH argumentIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases functionCheck : check .tm function with
          | none => simp [check, functionCheck] at result
          | some function' =>
              cases argumentCheck : check .tm argument with
              | none => simp [check, functionCheck, argumentCheck] at result
              | some argument' =>
                  cases Option.some.inj (by
                    simpa [check, functionCheck, argumentCheck] using result)
                  simp [erase, functionIH functionCheck, argumentIH argumentCheck]
  | lam name domain body domainIH bodyIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases domainCheck : check (.kind .star) domain with
          | none => simp [check, domainCheck] at result
          | some domain' =>
              cases bodyCheck : check .tm body with
              | none => simp [check, domainCheck, bodyCheck] at result
              | some body' =>
                  cases Option.some.inj (by
                    simpa [check, domainCheck, bodyCheck] using result)
                  simp [erase, domainIH domainCheck, bodyIH bodyCheck]
  | bool value =>
      cases sort with
      | kind _ => simp [check] at result
      | tm => simpa [check, erase] using congrArg erase (Option.some.inj result).symm
  | eq type left right typeIH leftIH rightIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases typeCheck : check (.kind .star) type with
          | none => simp [check, typeCheck] at result
          | some type' =>
              cases leftCheck : check .tm left with
              | none => simp [check, typeCheck, leftCheck] at result
              | some left' =>
                  cases rightCheck : check .tm right with
                  | none => simp [check, typeCheck, leftCheck, rightCheck] at result
                  | some right' =>
                      cases Option.some.inj (by
                        simpa [check, typeCheck, leftCheck, rightCheck] using result)
                      simp [erase, typeIH typeCheck, leftIH leftCheck,
                        rightIH rightCheck]
  | eps type predicate typeIH predicateIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases typeCheck : check (.kind .star) type with
          | none => simp [check, typeCheck] at result
          | some type' =>
              cases predicateCheck : check .tm predicate with
              | none => simp [check, typeCheck, predicateCheck] at result
              | some predicate' =>
                  cases Option.some.inj (by
                    simpa [check, typeCheck, predicateCheck] using result)
                  simp [erase, typeIH typeCheck, predicateIH predicateCheck]
  | abs carrier name predicate value carrierIH predicateIH valueIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases carrierCheck : check (.kind .star) carrier with
          | none => simp [check, carrierCheck] at result
          | some carrier' =>
              cases predicateCheck : check .tm predicate with
              | none => simp [check, carrierCheck, predicateCheck] at result
              | some predicate' =>
                  cases valueCheck : check .tm value with
                  | none =>
                      simp [check, carrierCheck, predicateCheck, valueCheck] at result
                  | some value' =>
                      cases Option.some.inj (by
                        simpa [check, carrierCheck, predicateCheck, valueCheck]
                          using result)
                      simp [erase, carrierIH carrierCheck, predicateIH predicateCheck,
                        valueIH valueCheck]
  | rep carrier name predicate value carrierIH predicateIH valueIH =>
      cases sort with
      | kind _ => simp [check] at result
      | tm =>
          cases carrierCheck : check (.kind .star) carrier with
          | none => simp [check, carrierCheck] at result
          | some carrier' =>
              cases predicateCheck : check .tm predicate with
              | none => simp [check, carrierCheck, predicateCheck] at result
              | some predicate' =>
                  cases valueCheck : check .tm value with
                  | none =>
                      simp [check, carrierCheck, predicateCheck, valueCheck] at result
                  | some value' =>
                      cases Option.some.inj (by
                        simpa [check, carrierCheck, predicateCheck, valueCheck]
                          using result)
                      simp [erase, carrierIH carrierCheck, predicateIH predicateCheck,
                        valueIH valueCheck]

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  [Nucleus.HolE.SigFamilyEquality Sig]

/-- Checking the raw projections of checked hypotheses recovers their stored
sorted terms in the same order. -/
@[simp] theorem checkTerms_map_raw
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (hypotheses : List (BoolTerm typeScope termScope Γ)) :
    checkTerms Sig (hypotheses.map Term.raw) =
      some (hypotheses.map (fun proposition => proposition.expression.sorted)) := by
  induction hypotheses with
  | nil => rfl
  | cons head tail ih =>
      simp [checkTerms, Term.raw, WellSorted.raw, ih]

/-- Lowering the stored sorted hypotheses recovers the kernel hypothesis list
in the same order. -/
@[simp] theorem lowerTerms_map_sorted
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (hypotheses : List (BoolTerm typeScope termScope Γ)) :
    Named.lowerTerms typeScope termScope
        (hypotheses.map (fun proposition => proposition.expression.sorted)) =
      some (rawHypotheses hypotheses) := by
  induction hypotheses with
  | nil => rfl
  | cons head tail ih =>
      simp [Named.lowerTerms, rawHypotheses, head.lowering, ih]

namespace Proof

/-- Forget the checked façade while retaining the same raw sequent. -/
def toUnsorted
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (BoolTerm typeScope termScope Γ)}
    {conclusion : BoolTerm typeScope termScope Γ}
    (proof : Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion) :
    Unsorted.Proves typeScope termScope Γ
      (hypotheses.map Term.raw) conclusion.raw :=
  ⟨hypotheses.map (fun proposition => proposition.expression.sorted),
    conclusion.expression.sorted,
    checkTerms_map_raw hypotheses,
    by simp [Term.raw, WellSorted.raw],
    ⟨rawHypotheses hypotheses, conclusion.lowered,
      lowerTerms_map_sorted hypotheses, conclusion.lowering, proof.kernel⟩⟩

/-- Recover the checked façade from a proof over its exact raw projection. -/
def ofUnsorted
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (BoolTerm typeScope termScope Γ)}
    {conclusion : BoolTerm typeScope termScope Γ}
    (proof : Unsorted.Proves typeScope termScope Γ
      (hypotheses.map Term.raw) conclusion.raw) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion := by
  have sortedHypotheses : proof.sortedHypotheses =
      hypotheses.map (fun proposition => proposition.expression.sorted) :=
    Option.some.inj (proof.hypothesesCheck.symm.trans
      (checkTerms_map_raw hypotheses))
  have canonicalHypothesesLowering : Named.lowerTerms typeScope termScope
      proof.sortedHypotheses = some (rawHypotheses hypotheses) := by
    rw [sortedHypotheses]
    exact lowerTerms_map_sorted hypotheses
  have sortedConclusion : proof.sortedConclusion = conclusion.expression.sorted :=
    Option.some.inj (proof.conclusionCheck.symm.trans (by
      simp [Term.raw, WellSorted.raw]))
  have canonicalConclusionLowering : Named.lowerTm typeScope termScope
      proof.sortedConclusion = some conclusion.lowered := by
    rw [sortedConclusion]
    exact conclusion.lowering
  have loweredHypotheses : proof.derivation.loweredHypotheses =
      rawHypotheses hypotheses :=
    Option.some.inj (proof.derivation.hypothesesLowering.symm.trans
      canonicalHypothesesLowering)
  have loweredConclusion : proof.derivation.loweredConclusion = conclusion.lowered :=
    Option.some.inj (proof.derivation.conclusionLowering.symm.trans
      canonicalConclusionLowering)
  exact ⟨by
    rw [← loweredHypotheses, ← loweredConclusion]
    exact proof.derivation.derivation⟩

end Proof

namespace Context

open Nucleus.HolE

variable {types : List Kind} {depth : Nat}
variable (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
variable (boundContext : BoundCtx Sig types depth)

/-- A checked list view of one raw context. -/
structure CheckedList (context : ListCtx Sig) where
  terms : List (BoolTerm typeScope termScope boundContext)
  raw_eq : terms.map Term.raw = context

namespace CheckedList

@[ext] theorem ext {context : ListCtx Sig}
    {left right : CheckedList typeScope termScope boundContext context}
    (terms : left.terms = right.terms) : left = right := by
  cases left
  cases right
  cases terms
  rfl

end CheckedList

/-- A valid proposition has a checked Boolean representative with exactly the
same raw syntax. -/
theorem IsProposition.existsBoolTerm {proposition : Expr Sig}
    (valid : IsProposition typeScope termScope boundContext proposition) :
    ∃ term : BoolTerm typeScope termScope boundContext,
      term.raw = proposition := by
  obtain ⟨sorted, lowered, checked, lowering, typing⟩ := valid
  let term : BoolTerm typeScope termScope boundContext :=
    ⟨⟨sorted⟩, lowered, lowering, by simpa [Family.boolTy] using typing⟩
  exact ⟨term, erase_eq_of_check_eq_some checked⟩

/-- Every well-formed raw context has an order-preserving checked view. -/
theorem WellFormed.existsChecked {context : ListCtx Sig}
    (valid : WellFormed typeScope termScope boundContext context) :
    Nonempty (CheckedList typeScope termScope boundContext context) := by
  induction context with
  | nil => exact ⟨⟨[], rfl⟩⟩
  | cons head tail ih =>
      obtain ⟨checkedHead, headRaw⟩ :=
        (valid.head typeScope termScope boundContext).existsBoolTerm
      obtain ⟨checkedTail⟩ :=
        ih (valid.tail typeScope termScope boundContext)
      exact ⟨⟨checkedHead :: checkedTail.terms, by
        simp [headRaw, checkedTail.raw_eq]⟩⟩

/-- Choose one checked view.  Logical results are independent of this choice
because the raw list and both compilation stages are fixed. -/
noncomputable def WfList.checked
    (context : WfList typeScope termScope boundContext) :
    CheckedList typeScope termScope boundContext context.raw :=
  Classical.choice context.valid.existsChecked

@[simp] theorem WfList.checked_raw
    (context : WfList typeScope termScope boundContext) :
    context.checked.terms.map Term.raw = context.raw :=
  context.checked.raw_eq

/-- Checked and raw provability coincide on the exact raw projection of a
checked sequent. -/
theorem Proof.nonempty_iff_derives
    {hypotheses : List (BoolTerm typeScope termScope boundContext)}
    {conclusion : BoolTerm typeScope termScope boundContext} :
    Nonempty (Proof (Sig := Sig) typeScope termScope boundContext
      hypotheses conclusion) ↔
    Derives typeScope termScope boundContext
      (hypotheses.map Term.raw) conclusion.raw := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨proof.toUnsorted⟩
  · rintro ⟨proof⟩
    exact ⟨Proof.ofUnsorted proof⟩

end Context

end Nucleus.HolE.Named.Unsorted
