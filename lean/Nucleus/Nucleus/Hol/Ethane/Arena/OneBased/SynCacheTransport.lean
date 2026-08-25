import Nucleus.Hol.Ethane.Arena.OneBased.DenseKernelTransport

/-!
# Syntactic-cache transport across dense-column rewrites

Dense equality union leaves definition syntax and the syntactic-fact allocator
unchanged.  Resolution may nevertheless re-advertise a term with a convertible
classifier.  This file proves that the resulting `Value.SamePayload` transport
preserves every cached syntactic judgment, and hence `SynArena.Sound`.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value.SamePayload

@[simp] theorem syntax?_eq (same : SamePayload before after) :
    before.syntax? = after.syntax? := by
  cases same <;> rfl

theorem symm (same : SamePayload before after) : SamePayload after before := by
  cases same with
  | kind kind => exact .kind kind
  | family kind expression => exact .family kind expression
  | term oldType newType expression conversion =>
      rcases conversion with ⟨conversion⟩
      exact .term newType oldType expression ⟨conversion.symm⟩

theorem payloadCompatible (same : SamePayload before after) :
    Compatible before after := by
  cases same with
  | kind kind => exact .kind kind
  | family kind expression => exact .family kind expression expression
  | term oldType newType expression conversion => exact .term conversion

/-- Classifier re-advertising on either side preserves compatibility. -/
theorem compatible (left : SamePayload oldLeft newLeft)
    (right : SamePayload oldRight newRight)
    (oldLeftWellFormed : oldLeft.WellFormed)
    (oldRightWellFormed : oldRight.WellFormed)
    (related : Compatible oldLeft oldRight) :
    Compatible newLeft newRight := by
  exact (left.symm.payloadCompatible.trans oldLeftWellFormed related).trans
    oldRightWellFormed right.payloadCompatible

/-- Literal syntax, alpha, and conversion all ignore a convertible change to
the separately advertised term classifier. -/
theorem holds (left : SamePayload oldLeft newLeft)
    (right : SamePayload oldRight newRight)
    (oldLeftWellFormed : oldLeft.WellFormed)
    (oldRightWellFormed : oldRight.WellFormed)
    (newLeftWellFormed : newLeft.WellFormed)
    (newRightWellFormed : newRight.WellFormed)
    (related : SynRel.Holds relation oldLeft oldRight) :
    SynRel.Holds relation newLeft newRight := by
  cases relation with
  | syn =>
      cases left <;> cases right <;> cases related
      · exact .kind _
      · exact .family _
      · exact .term _
  | alpha =>
      cases left <;> cases right <;> cases related
      · exact .kind _
      · exact .family ‹_›
      · exact .term ‹_›
  | conv =>
      exact (left.equal oldLeftWellFormed newLeftWellFormed).symm.trans
        oldLeftWellFormed
        (related.trans oldRightWellFormed
          (right.equal oldRightWellFormed newRightWellFormed))

end Value.SamePayload

namespace Value.Substitutes

/-- Capture-avoiding substitution depends on named syntax, not on a term's
separately advertised classifier. -/
theorem samePayload
    (subVarSame : SamePayload oldSubVar newSubVar)
    (replacementSame : SamePayload oldReplacement newReplacement)
    (inputSame : SamePayload oldInput newInput)
    (outputSame : SamePayload oldOutput newOutput)
    (substitutes : Substitutes oldSubVar oldReplacement oldInput oldOutput) :
    Substitutes newSubVar newReplacement newInput newOutput := by
  cases substitutes with
  | kind kind =>
      cases inputSame
      cases outputSame
      exact .kind kind
  | «syntax» variableIsSyntax replacementIsSyntax inputIsSyntax outputIsSyntax
      derivation =>
      apply Substitutes.syntax
      · simpa only [subVarSame.syntax?_eq] using variableIsSyntax
      · simpa only [replacementSame.syntax?_eq] using replacementIsSyntax
      · simpa only [inputSame.syntax?_eq] using inputIsSyntax
      · simpa only [outputSame.syntax?_eq] using outputIsSyntax
      · exact derivation

end Value.Substitutes

namespace Value.LocalSynMeaning

/-- Full transport of a cached local judgment across payload-preserving
reclassification of all referenced values. -/
theorem samePayload
    (subVarSame : Option.Rel Value.SamePayload oldSubVar newSubVar)
    (replacementSame : Option.Rel Value.SamePayload oldReplacement newReplacement)
    (inputSame : Value.SamePayload oldInput newInput)
    (outputSame : Value.SamePayload oldOutput newOutput)
    (oldInputWellFormed : oldInput.WellFormed)
    (oldOutputWellFormed : oldOutput.WellFormed)
    (newInputWellFormed : newInput.WellFormed)
    (newOutputWellFormed : newOutput.WellFormed)
    (oldSubVarWellFormed : ∀ value, oldSubVar = some value → value.WellFormed)
    (newSubVarWellFormed : ∀ value, newSubVar = some value → value.WellFormed)
    (meaning : LocalSynMeaning relation oldSubVar oldReplacement oldInput oldOutput) :
    LocalSynMeaning relation newSubVar newReplacement newInput newOutput := by
  cases subVarSame with
  | none => cases replacementSame with
    | none =>
      rcases meaning with ⟨compatible, related⟩
      exact ⟨inputSame.compatible outputSame oldInputWellFormed
          oldOutputWellFormed compatible,
      inputSame.holds outputSame oldInputWellFormed oldOutputWellFormed
        newInputWellFormed newOutputWellFormed related⟩
    | some valueSame => exact meaning
  | some varSame => cases replacementSame with
    | none =>
      intro replacement replacementWellFormed newCompatible
      have replacementSame := Value.SamePayload.refl replacementWellFormed
      have oldVarWellFormed := oldSubVarWellFormed _ rfl
      have newVarWellFormed := newSubVarWellFormed _ rfl
      have oldCompatible : Value.Compatible _ replacement :=
        varSame.symm.compatible replacementSame newVarWellFormed
          replacementWellFormed newCompatible
      rcases meaning replacement replacementWellFormed oldCompatible with
        ⟨oldSubstituted, substituted, substitutedWellFormed,
          substitutedCompatible, related⟩
      refine ⟨oldSubstituted, ?_, substitutedWellFormed, ?_, ?_⟩
      · exact substituted.samePayload varSame replacementSame inputSame
          (Value.SamePayload.refl substitutedWellFormed)
      · exact (Value.SamePayload.refl substitutedWellFormed).compatible
          outputSame substitutedWellFormed oldOutputWellFormed
          substitutedCompatible
      · exact (Value.SamePayload.refl substitutedWellFormed).holds outputSame
          substitutedWellFormed oldOutputWellFormed substitutedWellFormed
          newOutputWellFormed related
    | some valueSame =>
      rcases meaning with ⟨oldSubstituted, substituted, substitutedWellFormed,
        substitutedCompatible, related⟩
      refine ⟨oldSubstituted, ?_, substitutedWellFormed, ?_, ?_⟩
      · exact substituted.samePayload varSame valueSame inputSame
          (Value.SamePayload.refl substitutedWellFormed)
      · exact (Value.SamePayload.refl substitutedWellFormed).compatible
          outputSame substitutedWellFormed oldOutputWellFormed
          substitutedCompatible
      · exact (Value.SamePayload.refl substitutedWellFormed).holds outputSame
          substitutedWellFormed oldOutputWellFormed substitutedWellFormed
          newOutputWellFormed related

end Value.LocalSynMeaning

namespace SynFact.Valid

/-- A cached fact stays valid when every referenced value resolves with the
same syntax payload. -/
theorem samePayload
    (transport : ∀ reference oldValue,
      Resolves resolve before.withoutSyn reference oldValue →
        ∃ newValue, Resolves resolve after.withoutSyn reference newValue ∧
          Value.SamePayload oldValue newValue ∧ newValue.WellFormed)
    (valid : SynFact.Valid resolve before fact) :
    SynFact.Valid resolve after fact := by
  rcases valid with ⟨oldInput, oldOutput, oldInputResolved, oldOutputResolved,
    oldInputWellFormed, oldOutputWellFormed, oldCompatible, meaning⟩
  obtain ⟨newInput, newInputResolved, inputSame, newInputWellFormed⟩ :=
    transport fact.input oldInput oldInputResolved
  obtain ⟨newOutput, newOutputResolved, outputSame, newOutputWellFormed⟩ :=
    transport fact.output oldOutput oldOutputResolved
  refine ⟨newInput, newOutput, newInputResolved, newOutputResolved,
    newInputWellFormed, newOutputWellFormed,
    inputSame.compatible outputSame oldInputWellFormed oldOutputWellFormed
      oldCompatible, ?_⟩
  cases varFound : fact.var <;> cases valFound : fact.val
  · simp only [varFound, valFound] at meaning ⊢
    exact meaning.samePayload .none .none inputSame outputSame
      oldInputWellFormed oldOutputWellFormed newInputWellFormed newOutputWellFormed
      (by simp) (by simp)
  · simp [varFound, valFound] at meaning
  · simp only [varFound, valFound] at meaning ⊢
    rcases meaning with ⟨oldVar, oldVarResolved, oldVarWellFormed, meaning⟩
    obtain ⟨newVar, newVarResolved, varSame, newVarWellFormed⟩ :=
      transport _ oldVar oldVarResolved
    exact ⟨newVar, newVarResolved, newVarWellFormed,
      meaning.samePayload (.some varSame) .none inputSame outputSame
        oldInputWellFormed oldOutputWellFormed newInputWellFormed
        newOutputWellFormed (by intro value equal; cases equal; exact oldVarWellFormed)
        (by intro value equal; cases equal; exact newVarWellFormed)⟩
  · simp only [varFound, valFound] at meaning ⊢
    rcases meaning with ⟨oldVar, oldValue, oldVarResolved, oldValueResolved,
      oldVarWellFormed, oldValueWellFormed, meaning⟩
    obtain ⟨newVar, newVarResolved, varSame, newVarWellFormed⟩ :=
      transport _ oldVar oldVarResolved
    obtain ⟨newValue, newValueResolved, valueSame, newValueWellFormed⟩ :=
      transport _ oldValue oldValueResolved
    exact ⟨newVar, newValue, newVarResolved, newValueResolved,
      newVarWellFormed, newValueWellFormed,
      meaning.samePayload (.some varSame) (.some valueSame) inputSame outputSame
        oldInputWellFormed oldOutputWellFormed newInputWellFormed
        newOutputWellFormed (by intro value equal; cases equal; exact oldVarWellFormed)
        (by intro value equal; cases equal; exact newVarWellFormed)⟩

end SynFact.Valid

namespace SynArena

@[simp] theorem Arena.synFacts_withDense (arena : Arena) (dense : Dense) :
    (arena.withDense dense).synFacts = arena.synFacts := by
  cases arena
  rfl

/-- Allocator safety is independent of dense definitions and columns. -/
theorem freeListSafe_withDense (safe : FreeListSafe arena) (dense : Dense) :
    FreeListSafe (arena.withDense dense) := by
  cases arena
  exact safe

/-- Cache soundness is preserved by a sound dense-column rewrite. -/
theorem Sound.withDense (sound : Sound resolve before)
    (change : CoreDenseChange resolve before (before.withDense dense))
    (valid : before.CoreKernelValid resolve) :
    Sound resolve (before.withDense dense) := by
  intro fact member
  have oldMember : SynSlot.fact fact ∈ before.synFacts := by
    simpa only [Arena.synFacts_withDense] using member
  apply (sound fact oldMember).samePayload
  intro reference oldValue oldResolved
  have oldResolvedCore : Resolves resolve before reference oldValue :=
    (resolves_withoutSyn_iff resolve before reference oldValue).mp oldResolved
  obtain ⟨newValue, newResolved, same, newWellFormed⟩ :=
    change.resolves valid reference oldValue oldResolvedCore
  exact ⟨newValue,
    (resolves_withoutSyn_iff resolve (before.withDense dense) reference newValue).mpr
      newResolved,
    same, newWellFormed⟩

end SynArena

end Nucleus.Hol.Ethane.OneBased
