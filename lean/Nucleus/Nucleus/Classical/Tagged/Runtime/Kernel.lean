import Nucleus.Classical.Tagged.Runtime.Correspondence
import Nucleus.Classical.Tagged.Runtime.Derive
import Nucleus.Classical.Tagged.Runtime.Matrix
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
  private mk ::
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

private theorem copy_sound {source : Theorem payloadWidth}
    {checked : Checked payloadWidth}
    (packed : Encode.pack? payloadWidth source.checked.decoded.sequents =
      some checked) : Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  have sourceSound := source.sound
  unfold Mutate.Syllogism Mutate.EntailsAt at sourceSound ⊢
  rw [decoded]
  exact sourceSound

/-- Canonically deep-copy a theorem table.  Repacking recreates every owned
formula subtree instead of aliasing storage from `source`. -/
def copy? (source : Theorem payloadWidth) : Option (Theorem payloadWidth) :=
  match packed : Encode.pack? payloadWidth source.checked.decoded.sequents with
  | none => none
  | some checked => some ⟨checked, copy_sound packed⟩

/-- Canonical copying is total whenever the decoded theorem table fits the
fixed-width arena. -/
theorem copy?_complete {source : Theorem payloadWidth}
    (fits : Encode.Fits payloadWidth source.checked.decoded.sequents) :
    ∃ result, copy? source = some result := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  unfold copy?
  split
  · rename_i impossible
    rw [packed] at impossible
    contradiction
  · exact ⟨_, rfl⟩

/-- A successful canonical copy has exactly the source's decoded theorem
table. -/
theorem copy?_decoded {source result : Theorem payloadWidth}
    (copied : copy? source = some result) :
    result.checked.decoded.sequents = source.checked.decoded.sequents := by
  unfold copy? at copied
  split at copied
  · contradiction
  · rename_i checked packed
    have equal : result = ⟨checked, copy_sound packed⟩ := by
      simpa using Option.some.inj copied.symm
    subst result
    exact (Encode.pack?_result packed).2.1

private theorem member_of_getElem? {values : List α} {index : Nat} {value : α}
    (selected : values[index]? = some value) : value ∈ values := by
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp selected
  exact List.mem_iff_getElem.mpr ⟨index, bound, equal⟩

private theorem selected_entailsAt {fact : Theorem payloadWidth}
    {index : Nat} {sequent : Tagged.Sequent Nat}
    (selected : fact.checked.decoded.sequents[index]? = some sequent) :
    sequent.EntailsAt Classical.bottom := by
  have sound := fact.sound
  unfold Mutate.Syllogism Mutate.EntailsAt at sound
  intro assignment completes
  exact sound assignment completes sequent (member_of_getElem? selected)

private theorem cut_sound {left right : Theorem payloadWidth}
    {leftIndex rightIndex : Nat} {pivot : Tagged.Formula Nat}
    {leftSequent rightSequent result : Tagged.Sequent Nat}
    {checked : Checked payloadWidth}
    (leftSelected : left.checked.decoded.sequents[leftIndex]? = some leftSequent)
    (rightSelected : right.checked.decoded.sequents[rightIndex]? = some rightSequent)
    (derived : Derive.cutTarget? pivot leftSequent rightSequent = some result)
    (packed : Encode.pack? payloadWidth [result] = some checked) :
    Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  have resultSound := Derive.cutTarget?_entailsAt derived Classical.bottom
    (selected_entailsAt leftSelected) (selected_entailsAt rightSelected)
  unfold Mutate.Syllogism Mutate.EntailsAt
  rw [decoded]
  intro assignment completes sequent member
  have equal : sequent = result := by simpa using member
  subst sequent
  exact resultSound assignment completes

/-- Cut the first matching pivot from a selected left conclusion and selected
right premise.  The result is a singleton theorem table produced entirely by
canonical decoded-AST construction and repacking. -/
def cut? (left : Theorem payloadWidth) (leftIndex : Nat)
    (right : Theorem payloadWidth) (rightIndex : Nat)
    (pivot : Tagged.Formula Nat) : Option (Theorem payloadWidth) :=
  match leftSelected : left.checked.decoded.sequents[leftIndex]? with
  | none => none
  | some leftSequent =>
      match rightSelected : right.checked.decoded.sequents[rightIndex]? with
      | none => none
      | some rightSequent =>
          match derived : Derive.cutTarget? pivot leftSequent rightSequent with
          | none => none
          | some result =>
              match packed : Encode.pack? payloadWidth [result] with
              | none => none
              | some checked => some ⟨checked,
                  cut_sound leftSelected rightSelected derived packed⟩

private theorem resolve_sound {left right : Theorem payloadWidth}
    {leftIndex rightIndex : Nat} {pivot : Tagged.Formula Nat}
    {leftSequent rightSequent result : Tagged.Sequent Nat}
    {checked : Checked payloadWidth}
    (leftSelected : left.checked.decoded.sequents[leftIndex]? = some leftSequent)
    (rightSelected : right.checked.decoded.sequents[rightIndex]? = some rightSequent)
    (derived : Derive.resolveTarget? pivot leftSequent rightSequent = some result)
    (packed : Encode.pack? payloadWidth [result] = some checked) :
    Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  have resultSound := Derive.resolveTarget?_entailsAt derived Classical.bottom
    (selected_entailsAt leftSelected) (selected_entailsAt rightSelected)
  unfold Mutate.Syllogism Mutate.EntailsAt
  rw [decoded]
  intro assignment completes sequent member
  have equal : sequent = result := by simpa using member
  subst sequent
  exact resultSound assignment completes

/-- Resolve the first pivot and complement in two selected conclusions.  SAT
nodes remain ordinary closed formulas here; the rule never interprets their
bound atoms as ambient HOL literals. -/
def resolve? (left : Theorem payloadWidth) (leftIndex : Nat)
    (right : Theorem payloadWidth) (rightIndex : Nat)
    (pivot : Tagged.Formula Nat) : Option (Theorem payloadWidth) :=
  match leftSelected : left.checked.decoded.sequents[leftIndex]? with
  | none => none
  | some leftSequent =>
      match rightSelected : right.checked.decoded.sequents[rightIndex]? with
      | none => none
      | some rightSequent =>
          match derived : Derive.resolveTarget? pivot leftSequent rightSequent with
          | none => none
          | some result =>
              match packed : Encode.pack? payloadWidth [result] with
              | none => none
              | some checked => some ⟨checked,
                  resolve_sound leftSelected rightSelected derived packed⟩

/-! ## Matrix rules -/

private theorem singleton_sound {result : Tagged.Sequent Nat}
    {checked : Checked payloadWidth}
    (resultSound : result.EntailsAt Classical.bottom)
    (packed : Encode.pack? payloadWidth [result] = some checked) :
    Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  unfold Mutate.Syllogism Mutate.EntailsAt
  rw [decoded]
  intro assignment completes sequent member
  have equal : sequent = result := by simpa using member
  subst sequent
  exact resultSound assignment completes

private def sealSingleton? (payloadWidth : Nat) (result : Tagged.Sequent Nat)
    (resultSound : result.EntailsAt Classical.bottom) :
    Option (Theorem payloadWidth) :=
  match packed : Encode.pack? payloadWidth [result] with
  | none => none
  | some checked => some ⟨checked, singleton_sound resultSound packed⟩

private def deriveMatrixUnary? (fact : Theorem payloadWidth) (index : Nat)
    (derive : Tagged.Sequent Nat → Option (Tagged.Sequent Nat))
    (preserves : ∀ {source result}, derive source = some result →
      source.EntailsAt Classical.bottom → result.EntailsAt Classical.bottom) :
    Option (Theorem payloadWidth) :=
  match selected : fact.checked.decoded.sequents[index]? with
  | none => none
  | some source =>
      match derived : derive source with
      | none => none
      | some result => sealSingleton? payloadWidth result
          (preserves derived (selected_entailsAt selected))

private def deriveMatrixBinary? (left : Theorem payloadWidth) (leftIndex : Nat)
    (right : Theorem payloadWidth) (rightIndex : Nat)
    (derive : Tagged.Sequent Nat → Tagged.Sequent Nat →
      Option (Tagged.Sequent Nat))
    (preserves : ∀ {left right result}, derive left right = some result →
      left.EntailsAt Classical.bottom → right.EntailsAt Classical.bottom →
      result.EntailsAt Classical.bottom) : Option (Theorem payloadWidth) :=
  match leftSelected : left.checked.decoded.sequents[leftIndex]? with
  | none => none
  | some leftSource =>
      match rightSelected : right.checked.decoded.sequents[rightIndex]? with
      | none => none
      | some rightSource =>
          match derived : derive leftSource rightSource with
          | none => none
          | some result => sealSingleton? payloadWidth result
              (preserves derived (selected_entailsAt leftSelected)
                (selected_entailsAt rightSelected))

namespace Matrix

abbrev Side := Nucleus.Classical.Tagged.Runtime.Matrix.Side

/-- Construct singleton matrix identity. -/
def identity? (payloadWidth : Nat) (pivot : Classical.Literal Nat) :
    Option (Theorem payloadWidth) :=
  sealSingleton? payloadWidth
    (Nucleus.Classical.Tagged.Runtime.Matrix.identity pivot)
    (Nucleus.Classical.Tagged.Runtime.Matrix.identity_entailsAt pivot)

/-- Append one clause to the CNF of a selected matrix theorem. -/
def weakenCnfRow? (fact : Theorem payloadWidth) (index : Nat)
    (row : List (Classical.Literal Nat)) : Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source =>
      Nucleus.Classical.Tagged.Runtime.Matrix.weakenCnfRowTarget? source row)
    Nucleus.Classical.Tagged.Runtime.Matrix.weakenCnfRowTarget?_entailsAt

/-- Append one cube to the DNF of a selected matrix theorem. -/
def weakenDnfRow? (fact : Theorem payloadWidth) (index : Nat)
    (row : List (Classical.Literal Nat)) : Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source =>
      Nucleus.Classical.Tagged.Runtime.Matrix.weakenDnfRowTarget? source row)
    Nucleus.Classical.Tagged.Runtime.Matrix.weakenDnfRowTarget?_entailsAt

/-- Cut matching singleton DNF/CNF rows from two selected matrix theorems. -/
def unitCut? (left : Theorem payloadWidth) (leftIndex : Nat)
    (right : Theorem payloadWidth) (rightIndex : Nat)
    (pivot : Classical.Literal Nat) : Option (Theorem payloadWidth) :=
  deriveMatrixBinary? left leftIndex right rightIndex
    (Nucleus.Classical.Tagged.Runtime.Matrix.unitCutTarget? pivot)
    Nucleus.Classical.Tagged.Runtime.Matrix.unitCutTarget?_entailsAt

/-- Resolve complementary singleton DNF rows in two selected matrices. -/
def unitResolve? (left : Theorem payloadWidth) (leftIndex : Nat)
    (right : Theorem payloadWidth) (rightIndex : Nat)
    (pivot : Classical.Literal Nat) : Option (Theorem payloadWidth) :=
  deriveMatrixBinary? left leftIndex right rightIndex
    (Nucleus.Classical.Tagged.Runtime.Matrix.unitResolveTarget? pivot)
    Nucleus.Classical.Tagged.Runtime.Matrix.unitResolveTarget?_entailsAt

/-- Cross one CNF row to a pointwise-complemented DNF row. -/
def crossCnfRow? (fact : Theorem payloadWidth) (index rowIndex : Nat) :
    Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source =>
      Nucleus.Classical.Tagged.Runtime.Matrix.crossCnfRowTarget? source rowIndex)
    Nucleus.Classical.Tagged.Runtime.Matrix.crossCnfRowTarget?_entailsAt

/-- Cross one DNF row to a pointwise-complemented CNF row. -/
def crossDnfRow? (fact : Theorem payloadWidth) (index rowIndex : Nat) :
    Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source =>
      Nucleus.Classical.Tagged.Runtime.Matrix.crossDnfRowTarget? source rowIndex)
    Nucleus.Classical.Tagged.Runtime.Matrix.crossDnfRowTarget?_entailsAt

/-- Replace a selected row by a checked literal permutation. -/
def permuteRow? (fact : Theorem payloadWidth) (index : Nat) (side : Side)
    (rowIndex : Nat) (candidate : List (Classical.Literal Nat)) :
    Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source => Nucleus.Classical.Tagged.Runtime.Matrix.permuteRowTarget?
      source side rowIndex candidate)
    Nucleus.Classical.Tagged.Runtime.Matrix.permuteRowTarget?_entailsAt

/-- Deduplicate literals in one selected matrix row. -/
def dedupeRow? (fact : Theorem payloadWidth) (index : Nat) (side : Side)
    (rowIndex : Nat) : Option (Theorem payloadWidth) :=
  deriveMatrixUnary? fact index
    (fun source => Nucleus.Classical.Tagged.Runtime.Matrix.dedupeRowTarget?
      source side rowIndex)
    Nucleus.Classical.Tagged.Runtime.Matrix.dedupeRowTarget?_entailsAt

end Matrix

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

/-- Weaken one selected sequent by appending an arbitrary owned formula to a
positive left conjunction or positive right disjunction.  The canonical
packer deep-copies `pushed`; no subtree from another arena is borrowed. -/
def weaken? (before : Theorem payloadWidth) (index : Nat)
    (side : Operations.Side) (pushed : Tagged.Formula Nat) :
    Option (Theorem payloadWidth) :=
  canonicalPushRoot? before index side pushed

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

theorem weaken?_complete {before : Theorem payloadWidth}
    {index : Nat} {side : Operations.Side} {pushed : Tagged.Formula Nat}
    {target : List (Tagged.Sequent Nat)}
    (edited : Canonical.applyAt?
      (Nucleus.Classical.Mutation.Operations.Tagged.pushTarget? pushed side)
      index before.checked.decoded.sequents = some target)
    (fits : Encode.Fits payloadWidth target) :
    ∃ after, weaken? before index side pushed = some after := by
  exact canonicalPushRoot?_complete edited fits

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

/-! ## Certificate sealing -/

private theorem checkedRefutation_sound
    {initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    {checked : Checked payloadWidth}
    (certificate : Runtime.Refutation.Checker.Result initial)
    (packed : Encode.pack? payloadWidth
      [Nucleus.Classical.Refutation.Tagged.sequent initial] = some checked) :
    Mutate.Syllogism checked := by
  have decoded := (Encode.pack?_result packed).2.1
  have unsat : Nucleus.Classical.Refutation.Matrix.BooleanUnsat initial :=
    (Nucleus.Classical.Refutation.Matrix.booleanUnsat_iff_legacy initial).mpr
      certificate.unsat
  have sound :=
    (Nucleus.Classical.Refutation.Tagged.sequent_syllogism_iff initial).mpr unsat
  unfold Mutate.Syllogism Mutate.EntailsAt
  rw [decoded]
  intro assignment completes sequent member
  have equal : sequent = Nucleus.Classical.Refutation.Tagged.sequent initial := by
    simpa using member
  subst sequent
  exact sound assignment completes

/-- Seal a checked universal CNF refutation as an LCF theorem.  A
`Checker.Result` is an opaque proof token
created only by the stateful checked API; it need not retain parser data or a
second copy of the replay trace. -/
def sealRefutation? (payloadWidth : Nat)
    (initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat)
    (certificate : Runtime.Refutation.Checker.Result initial) :
    Option (Theorem payloadWidth) :=
  match packed : Encode.pack? payloadWidth
    [Nucleus.Classical.Refutation.Tagged.sequent initial] with
  | none => none
  | some checked => some ⟨checked, checkedRefutation_sound certificate packed⟩

theorem sealRefutation?_decoded {payloadWidth : Nat}
    {initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    {certificate : Runtime.Refutation.Checker.Result initial}
    {result : Theorem payloadWidth}
    (sealed : sealRefutation? payloadWidth initial certificate = some result) :
    result.checked.decoded.sequents =
      [Nucleus.Classical.Refutation.Tagged.sequent initial] := by
  unfold sealRefutation? at sealed
  split at sealed
  · contradiction
  · rename_i checked packed
    have equal : result =
        ⟨checked, checkedRefutation_sound certificate packed⟩ := by
      simpa using Option.some.inj sealed.symm
    subst result
    exact (Encode.pack?_result packed).2.1

/-- A checked refutation token can always be sealed under the ordinary packing
bound. -/
theorem sealRefutation?_complete {payloadWidth : Nat}
    {initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    {certificate : Runtime.Refutation.Checker.Result initial}
    (fits : Encode.Fits payloadWidth
      [Nucleus.Classical.Refutation.Tagged.sequent initial]) :
    ∃ result, sealRefutation? payloadWidth initial certificate = some result := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  unfold sealRefutation?
  split
  · rename_i impossible
    rw [packed] at impossible
    contradiction
  · exact ⟨_, rfl⟩

/-- Stateless convenience composition for callers which already retain the
complete certificate trace. -/
def checkRefutation? (payloadWidth : Nat)
    (initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat)
    (steps : List Runtime.Refutation.Checker.Step) : Option (Theorem payloadWidth) := do
  let certificate ← Runtime.Refutation.Checker.refute? initial steps
  sealRefutation? payloadWidth initial certificate

theorem checkRefutation?_decoded {payloadWidth : Nat}
    {initial : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    {steps : List Runtime.Refutation.Checker.Step}
    {result : Theorem payloadWidth}
    (accepted : checkRefutation? payloadWidth initial steps = some result) :
    result.checked.decoded.sequents =
      [Nucleus.Classical.Refutation.Tagged.sequent initial] := by
  unfold checkRefutation? at accepted
  cases replayed : Runtime.Refutation.Checker.refute? initial steps with
  | none => simp [replayed] at accepted
  | some certificate =>
      have sealed : sealRefutation? payloadWidth initial certificate = some result := by
        simpa [replayed] using accepted
      exact sealRefutation?_decoded sealed

/-- Extract the Boolean unsatisfiability conclusion represented by a theorem
member.  No signature or content address can replace this semantic evidence. -/
theorem refutes {fact : Theorem payloadWidth}
    {value : Nucleus.Hol.Ethane.ClassicalMatrix.Cnf Nat}
    (member : Runtime.Refutation.Contains fact.checked
      (Nucleus.Classical.Refutation.Tagged.sequent value)) :
    Nucleus.Classical.Refutation.Matrix.BooleanUnsat value :=
  Runtime.Refutation.unsat_of_sequent fact.sound member

end Nucleus.Classical.Tagged.Runtime.Kernel
