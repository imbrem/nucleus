import Nucleus.Classical.Tagged.Runtime.EncodeCorrect
import Nucleus.Classical.Tagged.Runtime.Mutate

/-!
# Complete canonical mutation fallback

Direct runtime mutations reuse existing blocks and can legitimately run out
of local capacity.  This module gives the same runtime a complete reference
path: compute one exact abstract edit, then canonically repack the whole arena.
It is executable, directly translatable to Rust, and required to succeed under
the public `Encode.Fits` address bound.

The direct mutators are the optimization; canonical repacking fixes their
meaning and supplies a simple fallback for growth and fragmentation.
-/

namespace Nucleus.Classical.Tagged.Runtime.Canonical

open Nucleus.Classical
open Nucleus.Classical.Tagged.Runtime

namespace Operations
export Nucleus.Classical.Mutation.Operations (EditedAt)
end Operations

namespace Abstract
export Nucleus.Classical.Mutation.Operations.Tagged
  (dedupeTarget? pushTarget? crossTarget?)
end Abstract

variable {payloadWidth : Nat}

/-- Apply one partial edit at an exact list index. -/
def applyAt? (edit : α → Option α) : Nat → List α → Option (List α)
  | 0, value :: values => (fun result ↦ result :: values) <$> edit value
  | index + 1, value :: values =>
      (fun results ↦ value :: results) <$> applyAt? edit index values
  | _, _ => none

theorem applyAt?_edited {edit : α → Option α} {index : Nat}
    {before after : List α} (ran : applyAt? edit index before = some after) :
    Operations.EditedAt (fun source target ↦ edit source = some target)
      index before after := by
  induction index generalizing before after with
  | zero =>
      cases before with
      | nil => simp [applyAt?] at ran
      | cons value values =>
          cases edited : edit value with
          | none => simp [applyAt?, edited] at ran
          | some result =>
              have equal : result :: values = after := by
                simpa [applyAt?, edited] using ran
              subst after
              exact ⟨edited, rfl⟩
  | succ index ih =>
      cases before with
      | nil => simp [applyAt?] at ran
      | cons value values =>
          cases edited : applyAt? edit index values with
          | none => simp [applyAt?, edited] at ran
          | some results =>
              have equal : value :: results = after := by
                simpa [applyAt?, edited] using ran
              subst after
              exact ⟨rfl, ih edited⟩

/-- Apply one abstract sequent edit and canonically repack its result. -/
def edit? (edit : Tagged.Sequent Nat → Option (Tagged.Sequent Nat))
    (index : Nat) (before : Checked payloadWidth) :
    Option (Checked payloadWidth) := do
  let target ← applyAt? edit index before.decoded.sequents
  Encode.pack? payloadWidth target

theorem edit?_result
    {edit : Tagged.Sequent Nat → Option (Tagged.Sequent Nat)}
    {index : Nat} {before after : Checked payloadWidth}
    (ran : edit? edit index before = some after) :
    Operations.EditedAt (fun source target ↦ edit source = some target)
      index before.decoded.sequents after.decoded.sequents := by
  unfold edit? at ran
  cases targetEdited : applyAt? edit index before.decoded.sequents with
  | none => simp [targetEdited] at ran
  | some target =>
      have packed : Encode.pack? payloadWidth target = some after := by
        simpa [targetEdited] using ran
      have decoded := (Encode.pack?_result packed).2.1
      rw [decoded]
      exact applyAt?_edited targetEdited

/-- Canonical editing succeeds whenever the abstract edit exists and its
result fits the fixed-width arena. -/
theorem edit?_complete
    {edit : Tagged.Sequent Nat → Option (Tagged.Sequent Nat)}
    {index : Nat} {before : Checked payloadWidth}
    {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? edit index before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, edit? edit index before = some after := by
  obtain ⟨after, packed⟩ := Encode.pack?_complete fits
  exact ⟨after, by simp [edit?, edited, packed]⟩

/-- Replace one positive root's children after checking an actual
permutation. -/
def reorderTarget? (candidate : List (Tagged.Formula Nat)) :
    Nucleus.Classical.Mutation.Operations.Side →
      Tagged.Sequent Nat → Option (Tagged.Sequent Nat)
  | .left, ⟨.and false current, conclusion⟩ =>
      if candidate.Perm current then
        some ⟨.and false candidate, conclusion⟩
      else none
  | .right, ⟨premise, .or false current⟩ =>
      if candidate.Perm current then
        some ⟨premise, .or false candidate⟩
      else none
  | _, _ => none

/-- Construct the permutation internally by sorting abstract children. -/
def sortTarget? (key : Tagged.Formula Nat → Nat)
    (side : Nucleus.Classical.Mutation.Operations.Side)
    (before : Tagged.Sequent Nat) : Option (Tagged.Sequent Nat) :=
  match side, before with
  | .left, ⟨.and false current, _⟩ =>
      reorderTarget? (current.mergeSort fun left right ↦ key left ≤ key right)
        side before
  | .right, ⟨_, .or false current⟩ =>
      reorderTarget? (current.mergeSort fun left right ↦ key left ≤ key right)
        side before
  | _, _ => none

/-- Canonically install a caller-proposed abstract permutation. -/
def reorderRoot? (before : Checked payloadWidth) (index : Nat)
    (side : Nucleus.Classical.Mutation.Operations.Side)
    (candidate : List (Tagged.Formula Nat)) : Option (Checked payloadWidth) :=
  edit? (reorderTarget? candidate side) index before

/-- Canonically sort one positive root by an abstract key. -/
def sortRootByKey? (before : Checked payloadWidth) (index : Nat)
    (side : Nucleus.Classical.Mutation.Operations.Side)
    (key : Tagged.Formula Nat → Nat) : Option (Checked payloadWidth) :=
  edit? (sortTarget? key side) index before

/-- Canonical deduplication of a positive left-AND or right-OR root. -/
def dedupeRoot? (before : Checked payloadWidth) (index : Nat)
    (side : Nucleus.Classical.Mutation.Operations.Side) :
    Option (Checked payloadWidth) :=
  edit? (Abstract.dedupeTarget? side) index before

/-- Canonical weakening by an arbitrary owned formula. -/
def pushRoot? (before : Checked payloadWidth) (index : Nat)
    (side : Nucleus.Classical.Mutation.Operations.Side)
    (pushed : Tagged.Formula Nat) : Option (Checked payloadWidth) :=
  edit? (Abstract.pushTarget? pushed side) index before

/-- Canonical corrected crossing in either direction. -/
def crossRoot? (before : Checked payloadWidth) (index : Nat)
    (sourceSide : Nucleus.Classical.Mutation.Operations.Side) :
    Option (Checked payloadWidth) :=
  edit? (Abstract.crossTarget? sourceSide) index before

/-- Semantic preservation for any canonical edit relation. -/
theorem edit?_entailsAt
    {edit : Tagged.Sequent Nat → Option (Tagged.Sequent Nat)}
    (preserves : ∀ {before after}, edit before = some after →
      ∀ known, before.EntailsAt known → after.EntailsAt known)
    {index : Nat} {before after : Checked payloadWidth}
    (ran : edit? edit index before = some after)
    {known : PartialAssignment Nat} (holds : Mutate.EntailsAt known before) :
    Mutate.EntailsAt known after := by
  exact Nucleus.Classical.Mutation.Operations.Tagged.EditedAt.entailsAt
    preserves (edit?_result ran) known holds

private theorem reorderTarget?_entailsAt
    {candidate : List (Tagged.Formula Nat)}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {before after : Tagged.Sequent Nat}
    (edited : reorderTarget? candidate side before = some after)
    (known : PartialAssignment Nat) (holds : before.EntailsAt known) :
    after.EntailsAt known := by
  cases side with
  | left =>
      cases before with
      | mk premise conclusion =>
          cases premise with
          | literal value => simp [reorderTarget?] at edited
          | or negative children => simp [reorderTarget?] at edited
          | sat negative children => simp [reorderTarget?] at edited
          | and negative children =>
              cases negative with
              | true => simp [reorderTarget?] at edited
              | false =>
                  by_cases permutation : candidate.Perm children
                  · have equal :
                        (⟨.and false candidate, conclusion⟩ : Tagged.Sequent Nat) =
                          after := by
                      simpa [reorderTarget?, permutation] using edited
                    subst after
                    exact Tagged.Sequent.EntailsAt.lhsAndPermute known
                      permutation.symm holds
                  · simp [reorderTarget?, permutation] at edited
  | right =>
      cases before with
      | mk premise conclusion =>
          cases conclusion with
          | literal value => simp [reorderTarget?] at edited
          | and negative children => simp [reorderTarget?] at edited
          | sat negative children => simp [reorderTarget?] at edited
          | or negative children =>
              cases negative with
              | true => simp [reorderTarget?] at edited
              | false =>
                  by_cases permutation : candidate.Perm children
                  · have equal :
                        (⟨premise, .or false candidate⟩ : Tagged.Sequent Nat) =
                          after := by
                      simpa [reorderTarget?, permutation] using edited
                    subst after
                    exact Tagged.Sequent.EntailsAt.rhsOrPermute known
                      permutation.symm holds
                  · simp [reorderTarget?, permutation] at edited

private theorem sortTarget?_entailsAt
    {key : Tagged.Formula Nat → Nat}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {before after : Tagged.Sequent Nat}
    (edited : sortTarget? key side before = some after)
    (known : PartialAssignment Nat) (holds : before.EntailsAt known) :
    after.EntailsAt known := by
  cases side with
  | left =>
      cases before with
      | mk premise conclusion =>
          cases premise with
          | literal value => simp [sortTarget?] at edited
          | or negative children => simp [sortTarget?] at edited
          | sat negative children => simp [sortTarget?] at edited
          | and negative children =>
              cases negative with
              | true => simp [sortTarget?] at edited
              | false =>
                  exact reorderTarget?_entailsAt
                    (by simpa [sortTarget?] using edited) known holds
  | right =>
      cases before with
      | mk premise conclusion =>
          cases conclusion with
          | literal value => simp [sortTarget?] at edited
          | and negative children => simp [sortTarget?] at edited
          | sat negative children => simp [sortTarget?] at edited
          | or negative children =>
              cases negative with
              | true => simp [sortTarget?] at edited
              | false =>
                  exact reorderTarget?_entailsAt
                    (by simpa [sortTarget?] using edited) known holds

theorem reorderRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Nucleus.Classical.Mutation.Operations.Side}
    {candidate : List (Tagged.Formula Nat)} {known : PartialAssignment Nat}
    (ran : reorderRoot? before index side candidate = some after)
    (holds : Mutate.EntailsAt known before) : Mutate.EntailsAt known after := by
  exact edit?_entailsAt reorderTarget?_entailsAt ran holds

theorem sortRootByKey?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Nucleus.Classical.Mutation.Operations.Side}
    {key : Tagged.Formula Nat → Nat} {known : PartialAssignment Nat}
    (ran : sortRootByKey? before index side key = some after)
    (holds : Mutate.EntailsAt known before) : Mutate.EntailsAt known after := by
  exact edit?_entailsAt sortTarget?_entailsAt ran holds

theorem dedupeRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Nucleus.Classical.Mutation.Operations.Side}
    {known : PartialAssignment Nat}
    (ran : dedupeRoot? before index side = some after)
    (holds : Mutate.EntailsAt known before) : Mutate.EntailsAt known after := by
  exact edit?_entailsAt
    (fun edited known source ↦
      Nucleus.Classical.Mutation.Operations.Tagged.DedupesRoot.entailsAt
        edited known source)
    ran holds

theorem pushRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {side : Nucleus.Classical.Mutation.Operations.Side}
    {pushed : Tagged.Formula Nat} {known : PartialAssignment Nat}
    (ran : pushRoot? before index side pushed = some after)
    (holds : Mutate.EntailsAt known before) : Mutate.EntailsAt known after := by
  exact edit?_entailsAt
    (fun edited known source ↦
      Nucleus.Classical.Mutation.Operations.Tagged.PushesRoot.entailsAt
        edited known source)
    ran holds

theorem crossRoot?_entailsAt {before after : Checked payloadWidth}
    {index : Nat} {sourceSide : Nucleus.Classical.Mutation.Operations.Side}
    {known : PartialAssignment Nat}
    (ran : crossRoot? before index sourceSide = some after)
    (holds : Mutate.EntailsAt known before) : Mutate.EntailsAt known after := by
  exact edit?_entailsAt
    (fun edited known source ↦
      Nucleus.Classical.Mutation.Operations.Tagged.CrossesRoot.entailsAt
        edited known source)
    ran holds

/-! ## Concrete success contracts -/

theorem reorderRoot?_complete {before : Checked payloadWidth} {index : Nat}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {candidate : List (Tagged.Formula Nat)}
    {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? (reorderTarget? candidate side) index
      before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, reorderRoot? before index side candidate = some after := by
  exact edit?_complete edited fits

theorem sortRootByKey?_complete {before : Checked payloadWidth} {index : Nat}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {key : Tagged.Formula Nat → Nat} {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? (sortTarget? key side) index
      before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, sortRootByKey? before index side key = some after := by
  exact edit?_complete edited fits

theorem dedupeRoot?_complete {before : Checked payloadWidth} {index : Nat}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? (Abstract.dedupeTarget? side) index
      before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, dedupeRoot? before index side = some after := by
  exact edit?_complete edited fits

theorem pushRoot?_complete {before : Checked payloadWidth} {index : Nat}
    {side : Nucleus.Classical.Mutation.Operations.Side}
    {pushed : Tagged.Formula Nat} {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? (Abstract.pushTarget? pushed side) index
      before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, pushRoot? before index side pushed = some after := by
  exact edit?_complete edited fits

theorem crossRoot?_complete {before : Checked payloadWidth} {index : Nat}
    {sourceSide : Nucleus.Classical.Mutation.Operations.Side}
    {target : List (Tagged.Sequent Nat)}
    (edited : applyAt? (Abstract.crossTarget? sourceSide) index
      before.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, crossRoot? before index sourceSide = some after := by
  exact edit?_complete edited fits

end Nucleus.Classical.Tagged.Runtime.Canonical
