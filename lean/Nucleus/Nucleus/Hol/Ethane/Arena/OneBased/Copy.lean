import Nucleus.Hol.Ethane.Arena.OneBased.Kernel

/-!
# Cross-kernel term-copy contract

This module specifies the observable result of the Rust DAG copier.  A copy
maps every reachable source reference into the destination, maps a shared
compiled-init prefix identically, and preserves lookup, classification, and
resolution.  The latter is the denotation used by the checked one-based
kernel, so its preservation immediately gives typing and HOL denotation
preservation without assigning meaning to cache or proof metadata.
-/

namespace Nucleus.Hol.Ethane.OneBased

set_option relaxedAutoImplicit true

/-- Two arenas have the same raw definition prefix of the advertised length.
The executable implementation establishes this by comparing the compiled
prefix address and length before traversing any root. -/
def InitPrefixCompatible (source destination : Arena) (length : Nat) : Prop :=
  length ≤ source.defs.length ∧ length ≤ destination.defs.length ∧
    source.defs.take length = destination.defs.take length

/-- A successful, atomic cross-kernel copy.

`map` is defined on the complete reachable closure (roots, syntax children,
and classifiers).  Exact destination row bytes differ because their local
references are remapped; `rowPresent` is consequently the appropriate raw
lookup statement, while `sortMap` and `resolves` state the checked semantic
correspondence. -/
structure CopyResult (resolve : Resolver) (source destination : Arena) where
  map : Ref → Ref
  sourceRoots : List Ref
  destinationRoots : List Ref
  prefixLength : Nat
  initCompatible : InitPrefixCompatible source destination prefixLength
  prefixIdentity : ∀ reference,
    reference.value.toNat ≤ prefixLength → map reference = reference
  rootsMap : destinationRoots = sourceRoots.map map
  rowPresent : ∀ reference,
    source.row? reference ≠ none → destination.row? (map reference) ≠ none
  sortMap : ∀ reference,
    destination.sort? (map reference) = (source.sort? reference).map map
  resolves : ∀ reference value,
    Resolves resolve source reference value ↔
      Resolves resolve destination (map reference) value
  structural : source.StructurallyValid → destination.StructurallyValid

namespace CopyResult

/-- Matching init-prefix references retain their numerical identity. -/
theorem init_reference_identity
    (copy : CopyResult resolve source destination) {reference : Ref}
    (inPrefix : reference.value.toNat ≤ copy.prefixLength) :
    copy.map reference = reference :=
  copy.prefixIdentity reference inPrefix

/-- Copied roots retain order and repetitions. -/
theorem roots_correspond (copy : CopyResult resolve source destination) :
    copy.destinationRoots = copy.sourceRoots.map copy.map :=
  copy.rootsMap

/-- Every mapped source lookup has a destination lookup. -/
theorem lookup_preserved (copy : CopyResult resolve source destination)
    {reference : Ref} {row : detail.Row}
    (lookup : source.row? reference = some row) :
    ∃ destinationRow,
      destination.row? (copy.map reference) = some destinationRow := by
  have present := copy.rowPresent reference (by simp [lookup])
  cases found : destination.row? (copy.map reference) with
  | none => exact False.elim (present found)
  | some destinationRow => exact ⟨destinationRow, rfl⟩

/-- A successful copy preserves acyclicity and all other raw structural
validity conditions. -/
theorem structural_validity_preserved
    (copy : CopyResult resolve source destination)
    (valid : source.StructurallyValid) : destination.StructurallyValid :=
  copy.structural valid

/-- Resolution is the denotation of a resident one-based row; copied rows
denote exactly the same classified Ethane value. -/
theorem denotation_preserved
    (copy : CopyResult resolve source destination)
    {reference : Ref} {value : Value}
    (denotes : Resolves resolve source reference value) :
    Resolves resolve destination (copy.map reference) value :=
  (copy.resolves reference value).mp denotes

/-- Logical well-formedness, hence kinding for families and typing for terms,
is preserved together with denotation. -/
theorem wellFormed_preserved
    (copy : CopyResult resolve source destination)
    {reference : Ref} {value : Value}
    (denotes : Resolves resolve source reference value)
    (wellFormed : value.WellFormed) :
    Resolves resolve destination (copy.map reference) value ∧ value.WellFormed :=
  ⟨copy.denotation_preserved denotes, wellFormed⟩

/-- Inline classifier lookup and its semantic typing judgment are preserved. -/
theorem typing_preserved
    (copy : CopyResult resolve source destination)
    {reference : Ref}
    (typed : SortingClaim resolve source reference) :
    SortingClaim resolve destination (copy.map reference) := by
  rcases typed with ⟨sort, value, classifier, sortLookup,
    valueDenotes, classifierDenotes, hasSort⟩
  refine ⟨copy.map sort, value, classifier, ?_, ?_, ?_, hasSort⟩
  · rw [copy.sortMap, sortLookup]
    rfl
  · exact copy.denotation_preserved valueDenotes
  · exact copy.denotation_preserved classifierDenotes

end CopyResult

end Nucleus.Hol.Ethane.OneBased
