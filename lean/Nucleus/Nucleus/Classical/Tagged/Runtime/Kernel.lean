import Nucleus.Classical.Tagged.Runtime.Correspondence
import Nucleus.Classical.Tagged.Runtime.Refutation

/-!
# LCF theorem boundary for the selected runtime

`Checked` means structurally valid syntax and allocation.  `Theorem` adds the
semantic invariant that every decoded sequent is a syllogism.  Rust must keep
the `Theorem` constructor private and expose only the introductions below.
Parsing, imports, signatures, storage, and names do not construct theorem
facts.
-/

namespace Nucleus.Classical.Tagged.Runtime.Kernel

open Nucleus.Classical
open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged.Runtime

namespace Operations
export Nucleus.Classical.Mutation.Operations (Side)
end Operations

variable {payloadWidth : Nat}

/-- An LCF theorem fact: checked runtime syntax plus its semantic invariant.
The corresponding Rust fields and constructor are private. -/
structure Theorem (payloadWidth : Nat) where
  checked : Checked payloadWidth
  sound : Mutate.Syllogism checked

namespace Theorem

/-- Theorem equality is structural equality of decoded sequent lists. -/
def equal (left right : Theorem payloadWidth) : Bool :=
  left.checked.equal right.checked

/-- Hash exactly the same decoded structure used by theorem equality. -/
def hashTrace (fact : Theorem payloadWidth) : List Nat :=
  fact.checked.hashTrace

theorem hashTrace_eq_of_equal {left right : Theorem payloadWidth}
    (equal : left.equal right = true) : left.hashTrace = right.hashTrace :=
  Checked.hashTrace_eq_of_equal equal

end Theorem

private theorem identity_sound {formula : Tagged.Formula Nat}
    {checked : Checked payloadWidth}
    (packed : Encode.pack? payloadWidth [⟨formula, formula⟩] = some checked) :
    Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  unfold Mutate.Syllogism Mutate.EntailsAt
  rw [decoded]
  intro assignment completes sequent member
  have equal : sequent = ⟨formula, formula⟩ := by simpa using member
  subst sequent
  exact id

/-- The primitive identity theorem. -/
def identity? (payloadWidth : Nat) (formula : Tagged.Formula Nat) :
    Option (Theorem payloadWidth) :=
  match packed : Encode.pack? payloadWidth [⟨formula, formula⟩] with
  | none => none
  | some checked => some ⟨checked, identity_sound packed⟩

/-- Identity construction is total under the ordinary packing bound. -/
theorem identity?_complete {formula : Tagged.Formula Nat}
    (fits : Encode.Fits payloadWidth [⟨formula, formula⟩]) :
    ∃ result, identity? payloadWidth formula = some result := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  unfold identity?
  split
  · rename_i impossible
    rw [packed] at impossible
    contradiction
  · exact ⟨_, rfl⟩

private theorem append_sound {left right : Theorem payloadWidth}
    {checked : Checked payloadWidth}
    (packed : Encode.pack? payloadWidth
      (left.checked.decoded.sequents ++ right.checked.decoded.sequents) =
        some checked) : Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  have leftSound := left.sound
  have rightSound := right.sound
  unfold Mutate.Syllogism Mutate.EntailsAt at leftSound rightSound ⊢
  rw [decoded]
  intro assignment completes sequent member
  rcases List.mem_append.mp member with member | member
  · exact leftSound assignment completes sequent member
  · exact rightSound assignment completes sequent member

/-- Combine two theorem tables by canonical repacking. -/
def append? (left right : Theorem payloadWidth) : Option (Theorem payloadWidth) :=
  match packed : Encode.pack? payloadWidth
      (left.checked.decoded.sequents ++ right.checked.decoded.sequents) with
  | none => none
  | some checked => some ⟨checked, append_sound packed⟩

theorem append?_complete {left right : Theorem payloadWidth}
    (fits : Encode.Fits payloadWidth
      (left.checked.decoded.sequents ++ right.checked.decoded.sequents)) :
    ∃ result, append? left right = some result := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  unfold append?
  split
  · rename_i impossible
    rw [packed] at impossible
    contradiction
  · exact ⟨_, rfl⟩

/-! ## Direct in-place rules -/

def reorderRoot? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (candidate : List (Word.Ref payloadWidth)) :
    Option (Theorem payloadWidth) :=
  match ran : Mutate.reorderRoot? before.checked index side candidate with
  | none => none
  | some checked =>
      some ⟨checked, Mutate.reorderRoot?_syllogism ran before.sound⟩

def sortRootByKey? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (key : Word.Ref payloadWidth → Nat) :
    Option (Theorem payloadWidth) :=
  match ran : Mutate.sortRootByKey? before.checked index side key with
  | none => none
  | some checked =>
      some ⟨checked, Mutate.sortRootByKey?_syllogism ran before.sound⟩

def dedupeRoot? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) : Option (Theorem payloadWidth) :=
  match ran : Mutate.dedupeRoot? before.checked index side with
  | none => none
  | some checked =>
      some ⟨checked, Mutate.dedupeRoot?_syllogism ran before.sound⟩

def pushRootLiteral? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (reference : Word.Ref payloadWidth) :
    Option (Theorem payloadWidth) :=
  match ran : Mutate.pushRootLiteral? before.checked index side reference with
  | none => none
  | some checked =>
      some ⟨checked, Mutate.pushRootLiteral?_syllogism ran before.sound⟩

def crossRoot? (before : Theorem payloadWidth) (index : Nat)
    (sourceSide : Operations.Side) : Option (Theorem payloadWidth) :=
  match ran : Mutate.crossRoot? before.checked index sourceSide with
  | none => none
  | some checked =>
      some ⟨checked, Mutate.crossRoot?_syllogism ran before.sound⟩

/-! ## Complete canonical rules -/

def canonicalReorderRoot? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (candidate : List (Tagged.Formula Nat)) :
    Option (Theorem payloadWidth) :=
  match ran : Canonical.reorderRoot? before.checked index side candidate with
  | none => none
  | some checked => some ⟨checked,
      Canonical.reorderRoot?_entailsAt ran before.sound⟩

def canonicalSortRootByKey? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (key : Tagged.Formula Nat → Nat) :
    Option (Theorem payloadWidth) :=
  match ran : Canonical.sortRootByKey? before.checked index side key with
  | none => none
  | some checked => some ⟨checked,
      Canonical.sortRootByKey?_entailsAt ran before.sound⟩

def canonicalDedupeRoot? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) : Option (Theorem payloadWidth) :=
  match ran : Canonical.dedupeRoot? before.checked index side with
  | none => none
  | some checked => some ⟨checked,
      Canonical.dedupeRoot?_entailsAt ran before.sound⟩

def canonicalPushRoot? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (pushed : Tagged.Formula Nat) :
    Option (Theorem payloadWidth) :=
  match ran : Canonical.pushRoot? before.checked index side pushed with
  | none => none
  | some checked => some ⟨checked,
      Canonical.pushRoot?_entailsAt ran before.sound⟩

def canonicalCrossRoot? (before : Theorem payloadWidth) (index : Nat)
    (sourceSide : Operations.Side) : Option (Theorem payloadWidth) :=
  match ran : Canonical.crossRoot? before.checked index sourceSide with
  | none => none
  | some checked => some ⟨checked,
      Canonical.crossRoot?_entailsAt ran before.sound⟩

theorem canonicalReorderRoot?_complete {before : Theorem payloadWidth}
    {index : Nat} {side : Operations.Side}
    {candidate : List (Tagged.Formula Nat)}
    {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt? (Canonical.reorderTarget? candidate side)
      index before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, canonicalReorderRoot? before index side candidate = some after := by
  obtain ⟨checked, ran⟩ := Canonical.reorderRoot?_complete edited fits
  unfold canonicalReorderRoot?
  split
  · rename_i impossible
    rw [ran] at impossible
    contradiction
  · exact ⟨_, rfl⟩

theorem canonicalSortRootByKey?_complete {before : Theorem payloadWidth}
    {index : Nat} {side : Operations.Side}
    {key : Tagged.Formula Nat → Nat} {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt? (Canonical.sortTarget? key side)
      index before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, canonicalSortRootByKey? before index side key = some after := by
  obtain ⟨checked, ran⟩ := Canonical.sortRootByKey?_complete edited fits
  unfold canonicalSortRootByKey?
  split
  · rename_i impossible
    rw [ran] at impossible
    contradiction
  · exact ⟨_, rfl⟩

theorem canonicalDedupeRoot?_complete {before : Theorem payloadWidth}
    {index : Nat} {side : Operations.Side}
    {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt?
      (Nucleus.Classical.Mutation.Operations.Tagged.dedupeTarget? side) index
      before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, canonicalDedupeRoot? before index side = some after := by
  obtain ⟨checked, ran⟩ := Canonical.dedupeRoot?_complete edited fits
  unfold canonicalDedupeRoot?
  split
  · rename_i impossible
    rw [ran] at impossible
    contradiction
  · exact ⟨_, rfl⟩

theorem canonicalPushRoot?_complete {before : Theorem payloadWidth}
    {index : Nat} {side : Operations.Side} {pushed : Tagged.Formula Nat}
    {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt?
      (Nucleus.Classical.Mutation.Operations.Tagged.pushTarget? pushed side)
      index before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, canonicalPushRoot? before index side pushed = some after := by
  obtain ⟨checked, ran⟩ := Canonical.pushRoot?_complete edited fits
  unfold canonicalPushRoot?
  split
  · rename_i impossible
    rw [ran] at impossible
    contradiction
  · exact ⟨_, rfl⟩

theorem canonicalCrossRoot?_complete {before : Theorem payloadWidth}
    {index : Nat} {sourceSide : Operations.Side}
    {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt?
      (Nucleus.Classical.Mutation.Operations.Tagged.crossTarget? sourceSide)
      index before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, canonicalCrossRoot? before index sourceSide = some after := by
  obtain ⟨checked, ran⟩ := Canonical.crossRoot?_complete edited fits
  unfold canonicalCrossRoot?
  split
  · rename_i impossible
    rw [ran] at impossible
    contradiction
  · exact ⟨_, rfl⟩

/-- Extract the Boolean unsatisfiability conclusion represented by a theorem
member.  No signature or content address can replace this semantic evidence. -/
theorem refutes {fact : Theorem payloadWidth}
    {value : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    (member : Runtime.Refutation.Contains fact.checked
      (Nucleus.Classical.Refutation.Tagged.sequent value)) :
    Nucleus.Classical.Refutation.Matrix.BooleanUnsat value :=
  Runtime.Refutation.unsat_of_sequent fact.sound member

end Nucleus.Classical.Tagged.Runtime.Kernel
