import Nucleus.Classical.Alternating.Packed
import Nucleus.Classical.Alternating.Rules
import Nucleus.Classical.Tagged.Packed
import Nucleus.Classical.Tagged.Rules

/-!
# Certified packed mutations

The functions in `Classical.Packed.Memory` manipulate words and blocks, but a
successful call to one of them is not a theorem.  This module supplies the
separate checked boundary: both concrete states must decode exactly, and an
abstract theorem must preserve validity at every partial assignment.

`ExactTransition` is proof-carrying evidence.  Its constructor introduces no
primitive assumption and does not trust the mutation algorithm, a sort key, or
a claimed relationship between two word arrays.  A kernel checks the
representation equalities and the abstract preservation proof before the
transition can be used to carry a theorem fact forward.
-/

namespace Nucleus.Classical.Mutation

open Nucleus.Classical.Packed

universe u

variable {payloadWidth : Nat}

/-- Semantic validity of a concrete state through an exact representation.
The existential also prevents malformed packed states from being valid
vacuously. -/
def ConcreteEntailsAt {Abstract : Type u}
    (represents : Arena payloadWidth → Layout → Abstract → Prop)
    (entailsAt : PartialAssignment Nat → Abstract → Prop)
    (known : PartialAssignment Nat) (arena : Arena payloadWidth)
    (layout : Layout) : Prop :=
  ∃ abstract, represents arena layout abstract ∧ entailsAt known abstract

/-- Checked evidence for a concrete transition.  The semantic field is
uniform in the partial assignment, so the same certificate works for local
reasoning and for the null-assignment syllogism case. -/
structure ExactTransition {Abstract : Type u}
    (represents : Arena payloadWidth → Layout → Abstract → Prop)
    (entailsAt : PartialAssignment Nat → Abstract → Prop)
    (before : Arena payloadWidth) (beforeLayout : Layout)
    (after : Arena payloadWidth) (afterLayout : Layout) where
  beforeAbstract : Abstract
  afterAbstract : Abstract
  beforeRepresents : represents before beforeLayout beforeAbstract
  afterRepresents : represents after afterLayout afterAbstract
  preserves : ∀ known, entailsAt known beforeAbstract →
    entailsAt known afterAbstract

namespace ExactTransition

/-- Exact decoding plus representation functionality prevents a caller from
using a different abstract source when applying a checked transition. -/
theorem entailsAt {Abstract : Type u}
    {represents : Arena payloadWidth → Layout → Abstract → Prop}
    {abstractEntailsAt : PartialAssignment Nat → Abstract → Prop}
    {before after : Arena payloadWidth} {beforeLayout afterLayout : Layout}
    {known : PartialAssignment Nat}
    (functional : ∀ {arena : Arena payloadWidth} {layout : Layout}
      {left right : Abstract},
      represents arena layout left → represents arena layout right → left = right)
    (checked : ExactTransition represents abstractEntailsAt
      before beforeLayout after afterLayout)
    (source : ConcreteEntailsAt represents abstractEntailsAt
      known before beforeLayout) :
    ConcreteEntailsAt represents abstractEntailsAt known after afterLayout := by
  rcases source with ⟨abstract, abstractRepresents, abstractEntails⟩
  have equal := functional abstractRepresents checked.beforeRepresents
  subst abstract
  exact ⟨checked.afterAbstract, checked.afterRepresents,
    checked.preserves known abstractEntails⟩

end ExactTransition

namespace Alternating

/-- Concrete alternating validity at a partial assignment. -/
def EntailsAt (known : PartialAssignment Nat) (arena : Arena payloadWidth)
    (layout : Layout) : Prop :=
  ConcreteEntailsAt Classical.Alternating.Packed.Represents
    Classical.Alternating.Arena.EntailsAt known arena layout

/-- Concrete alternating syllogism validity: validity at the null assignment. -/
def Syllogistic (arena : Arena payloadWidth) (layout : Layout) : Prop :=
  EntailsAt bottom arena layout

/-- A checked transition between packed alternating states. -/
abbrev Checked (before : Arena payloadWidth) (beforeLayout : Layout)
    (after : Arena payloadWidth) (afterLayout : Layout) :=
  ExactTransition Classical.Alternating.Packed.Represents
    Classical.Alternating.Arena.EntailsAt
    before beforeLayout after afterLayout

namespace Checked

/-- Construct a checked transition from exact decoder results, allocator
validity, and an abstract mutation theorem.  The concrete mutation procedure
which produced `after` is deliberately absent from the trusted premises. -/
def ofDecoded {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    {source target : Classical.Alternating.Arena Nat}
    (beforeValid : beforeLayout.Valid before)
    (beforeDecoded : Classical.Alternating.Packed.decode? before beforeLayout =
      some source)
    (afterValid : afterLayout.Valid after)
    (afterDecoded : Classical.Alternating.Packed.decode? after afterLayout =
      some target)
    (preserves : ∀ known, source.EntailsAt known → target.EntailsAt known) :
    Checked before beforeLayout after afterLayout where
  beforeAbstract := source
  afterAbstract := target
  beforeRepresents := ⟨beforeValid, beforeDecoded⟩
  afterRepresents := ⟨afterValid, afterDecoded⟩
  preserves := preserves

/-- Carry alternating validity through a checked packed transition. -/
theorem entailsAt {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    {known : PartialAssignment Nat}
    (checked : Checked before beforeLayout after afterLayout)
    (source : EntailsAt known before beforeLayout) :
    EntailsAt known after afterLayout :=
  ExactTransition.entailsAt
    (fun left right ↦ Classical.Alternating.Packed.Represents.functional left right)
    checked source

/-- Null-assignment specialization of `entailsAt`. -/
theorem syllogistic {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    (checked : Checked before beforeLayout after afterLayout)
    (source : Syllogistic before beforeLayout) :
    Syllogistic after afterLayout :=
  checked.entailsAt source

/-- The target of a checked transition has passed the strict decoder and
allocator checks independently of any semantic premise. -/
theorem afterWellFormed {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    (checked : Checked before beforeLayout after afterLayout) :
    Classical.Alternating.Packed.WellFormed after afterLayout :=
  checked.afterRepresents.wellFormed

end Checked

end Alternating

namespace Tagged

/-- Concrete tagged validity at a partial assignment. -/
def EntailsAt (known : PartialAssignment Nat) (arena : Arena payloadWidth)
    (layout : Layout) : Prop :=
  ConcreteEntailsAt Classical.Tagged.Packed.Represents
    Classical.Tagged.EntailsAt known arena layout

/-- Concrete tagged syllogism validity: validity at the null assignment. -/
def Syllogism (arena : Arena payloadWidth) (layout : Layout) : Prop :=
  EntailsAt bottom arena layout

/-- A checked transition between packed tagged states. -/
abbrev Checked (before : Arena payloadWidth) (beforeLayout : Layout)
    (after : Arena payloadWidth) (afterLayout : Layout) :=
  ExactTransition Classical.Tagged.Packed.Represents
    Classical.Tagged.EntailsAt before beforeLayout after afterLayout

namespace Checked

/-- Construct a checked transition from exact decoder results, allocator
validity, and an abstract mutation theorem.  Executable `Memory` operations
remain untrusted until their output is connected by this evidence. -/
def ofDecoded {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    {source target : List (Classical.Tagged.Sequent Nat)}
    (beforeValid : beforeLayout.Valid before)
    (beforeDecoded : Classical.Tagged.Packed.decode? before beforeLayout =
      some source)
    (afterValid : afterLayout.Valid after)
    (afterDecoded : Classical.Tagged.Packed.decode? after afterLayout =
      some target)
    (preserves : ∀ known, Classical.Tagged.EntailsAt known source →
      Classical.Tagged.EntailsAt known target) :
    Checked before beforeLayout after afterLayout where
  beforeAbstract := source
  afterAbstract := target
  beforeRepresents := ⟨beforeValid, beforeDecoded⟩
  afterRepresents := ⟨afterValid, afterDecoded⟩
  preserves := preserves

/-- Carry tagged validity through a checked packed transition. -/
theorem entailsAt {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    {known : PartialAssignment Nat}
    (checked : Checked before beforeLayout after afterLayout)
    (source : EntailsAt known before beforeLayout) :
    EntailsAt known after afterLayout :=
  ExactTransition.entailsAt
    (fun left right ↦ Classical.Tagged.Packed.Represents.functional left right)
    checked source

/-- Null-assignment specialization of `entailsAt`. -/
theorem syllogism {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    (checked : Checked before beforeLayout after afterLayout)
    (source : Syllogism before beforeLayout) :
    Syllogism after afterLayout :=
  checked.entailsAt source

/-- The target of a checked transition has passed the strict decoder and
allocator checks independently of any semantic premise. -/
theorem afterWellFormed {before after : Arena payloadWidth}
    {beforeLayout afterLayout : Layout}
    (checked : Checked before beforeLayout after afterLayout) :
    Classical.Tagged.Packed.WellFormed after afterLayout :=
  checked.afterRepresents.wellFormed

end Checked

end Tagged

end Nucleus.Classical.Mutation
