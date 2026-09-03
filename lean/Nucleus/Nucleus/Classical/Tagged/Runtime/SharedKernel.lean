import Nucleus.Classical.Tagged.RewriteRules
import Nucleus.Classical.Tagged.Runtime.SemanticWire

/-!
# Sealed kernel boundary for shared classical arenas

This is the selected semantic contract for the Rust kernel.  A theorem stores
private constructor-built representation together with the sequents it
represents and their validity.  Allocator words, reference counts, and free
rings do not occur in the authority interface.
-/

namespace Nucleus.Classical.Tagged.Runtime.SharedKernel

open Nucleus.Classical
open Nucleus.Classical.Tagged
open Nucleus.Classical.Tagged.RewriteRules

universe u
variable {Representation : Type u}

def Valid (sequents : List (Sequent Nat)) : Prop :=
  ∀ sequent ∈ sequents, ∀ assignment, sequent.Holds assignment

/-- A sealed theorem fact constructed through the abstract arena API. -/
structure Theorem (api : SemanticWire.ConstructorApi Representation) where
  private mk ::
  representation : Representation
  sequents : List (Sequent Nat)
  represents : api.represents representation sequents
  sound : Valid sequents

namespace Theorem

variable {api : SemanticWire.ConstructorApi Representation}

private def seal? (sequents : List (Sequent Nat)) (sound : Valid sequents) :
    Option (Theorem api) :=
  match built : api.construct? sequents with
  | none => none
  | some representation => some ⟨representation, sequents,
      api.construct_sound built, sound⟩

private theorem singletonValid {sequent : Sequent Nat}
    (sound : ∀ assignment, sequent.Holds assignment) : Valid [sequent] := by
  intro selected member assignment
  have equal : selected = sequent := by simpa using member
  subst selected
  exact sound assignment

/-- `P ⊢ P`. -/
def identity? (formula : Formula Nat) : Option (Theorem api) :=
  seal? [⟨formula, formula⟩] (singletonValid fun _ premise ↦ premise)

/-- `and(A) ⊢ sat(A)`. -/
def satIntro? (children : List (Formula Nat)) : Option (Theorem api) :=
  seal? [⟨.and false children, .sat false children⟩]
    (singletonValid (satIntro children))

/-- Checked model evidence used by the two model-based introductions. -/
structure ModelWitness (children : List (Formula Nat)) where
  assignment : Assignment Nat
  holds : Formula.EvalAll children assignment

/-- `true ⊢ sat(A)` from an explicit checked assignment. -/
def proveSat? {children : List (Formula Nat)} (witness : ModelWitness children) :
    Option (Theorem api) :=
  seal? [⟨.and false [], .sat false children⟩]
    (singletonValid (proveSat children ⟨witness.assignment, witness.holds⟩))

/-- `sat(A) ⊢ sat(B)` when `B` has an explicit model.  The premise witness
accepted by Rust is redundant for soundness. -/
def modelSatImplication? {premise conclusion : List (Formula Nat)}
    (premiseWitness : ModelWitness premise)
    (conclusionWitness : ModelWitness conclusion) : Option (Theorem api) :=
  seal? [⟨.sat false premise, .sat false conclusion⟩]
    (singletonValid (modelSatImplication premise conclusion
      ⟨premiseWitness.assignment, premiseWitness.holds⟩
      ⟨conclusionWitness.assignment, conclusionWitness.holds⟩))

/-- `P ⊢ true`. -/
def truthIntro? (formula : Formula Nat) : Option (Theorem api) :=
  seal? [⟨formula, .and false []⟩] (singletonValid (truthIntro formula))

private theorem selectedSound (fact : Theorem api) {sequent : Sequent Nat}
    (member : sequent ∈ fact.sequents) : ∀ assignment, sequent.Holds assignment := by
  exact fact.sound sequent member

/-- `true ⊢ ¬sat(A)` yields `and(A) ⊢ false`. -/
def refutationToFalse? (fact : Theorem api) (children : List (Formula Nat))
    (member : ⟨.and false [], .sat true children⟩ ∈ fact.sequents) :
    Option (Theorem api) :=
  let source := selectedSound fact member
  seal? [⟨.and false children, .or false []⟩]
    (singletonValid fun assignment ↦
      Sequent.Holds.refutationToSequent assignment children (source assignment))

/-- Replacing a premise subformula by an equivalent formula is sound.
`context` is the representation-independent formula path. -/
def rewriteLeft? (fact : Theorem api) {premise conclusion left right : Formula Nat}
    (member : ⟨premise, conclusion⟩ ∈ fact.sequents)
    (context : Context Nat) (equivalent : Equivalent left right)
    (selected : premise = context.plug left) : Option (Theorem api) :=
  let target : Sequent Nat := ⟨context.plug right, conclusion⟩
  have contextual := context.congruent equivalent
  have source := selectedSound fact member
  have sound : ∀ assignment, target.Holds assignment := by
    intro assignment
    subst premise
    intro replacementTrue
    exact source assignment ((contextual assignment).mpr replacementTrue)
  seal? [target] (singletonValid sound)

/-- Replacing a conclusion subformula by an equivalent formula is sound. -/
def rewriteRight? (fact : Theorem api) {premise conclusion left right : Formula Nat}
    (member : ⟨premise, conclusion⟩ ∈ fact.sequents)
    (context : Context Nat) (equivalent : Equivalent left right)
    (selected : conclusion = context.plug left) : Option (Theorem api) :=
  let target : Sequent Nat := ⟨premise, context.plug right⟩
  have contextual := context.congruent equivalent
  have source := selectedSound fact member
  have sound : ∀ assignment, target.Holds assignment := by
    intro assignment
    subst conclusion
    intro premiseTrue
    exact (contextual assignment).mp (source assignment premiseTrue)
  seal? [target] (singletonValid sound)

/-- Bidirectional theorem facts establish formula equivalence. -/
theorem equivalentOfBothDirections (forward backward : Theorem api)
    {left right : Formula Nat}
    (forwardMember : ⟨left, right⟩ ∈ forward.sequents)
    (backwardMember : ⟨right, left⟩ ∈ backward.sequents) :
    Equivalent left right :=
  fromBothDirections (selectedSound forward forwardMember)
    (selectedSound backward backwardMember)

end Theorem

end Nucleus.Classical.Tagged.Runtime.SharedKernel
