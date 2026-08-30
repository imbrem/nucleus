import Nucleus.Classical.Tagged.Runtime.Canonical

/-!
# Direct/canonical runtime correspondence

The in-place mutators and the complete canonical fallback share one decoded
specification.  For functional edits, any successful direct result has exactly
the same abstract syntax as the canonical result.  Allocation addresses may
differ and are intentionally not observable through this relation.
-/

namespace Nucleus.Classical.Tagged.Runtime.Correspondence

open Nucleus.Classical.Tagged.Runtime

namespace Operations
export Nucleus.Classical.Mutation.Operations (Side EditedAt)
end Operations

namespace Abstract
export Nucleus.Classical.Mutation.Operations.Tagged
  (DedupesRoot PushesRoot CrossesRoot dedupesRoot_eq_true
    pushesRoot_eq_true crossesRoot_eq_true)
end Abstract

variable {payloadWidth : Nat}

/-- A pointwise functional edit remains functional when lifted to one exact
list position. -/
theorem EditedAt.eq_of_functional {relation : α → α → Prop}
    (functional : ∀ {source left right},
      relation source left → relation source right → left = right) :
    ∀ {index source left right},
      Operations.EditedAt relation index source left →
      Operations.EditedAt relation index source right → left = right
  | 0, _ :: sources, left :: lefts, right :: rights,
      ⟨leftRelated, leftTail⟩, ⟨rightRelated, rightTail⟩ => by
        subst lefts
        subst rights
        rw [functional leftRelated rightRelated]
  | index + 1, source :: sources, left :: lefts, right :: rights,
      ⟨leftHead, leftEdited⟩, ⟨rightHead, rightEdited⟩ => by
        subst left
        subst right
        congr
        exact @EditedAt.eq_of_functional α relation functional index sources
          lefts rights leftEdited rightEdited

private theorem optionRelation_functional {edit : α → Option α}
    {source left right : α}
    (leftResult : edit source = some left)
    (rightResult : edit source = some right) : left = right :=
  Option.some.inj (leftResult.symm.trans rightResult)

/-- Direct and canonical deduplication agree on decoded syntax. -/
theorem dedupeRoot?_agree {before fast canonical : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    (fastRan : Mutate.dedupeRoot? before index side = some fast)
    (canonicalRan : Canonical.dedupeRoot? before index side = some canonical) :
    fast.decoded.sequents = canonical.decoded.sequents := by
  have fastEdited := Mutate.checked?_decoded
    (Abstract.dedupesRoot_eq_true side)
    (by simpa [Mutate.dedupeRoot?] using fastRan)
  have canonicalEdited := Canonical.edit?_result
    (by simpa [Canonical.dedupeRoot?] using canonicalRan)
  exact EditedAt.eq_of_functional optionRelation_functional fastEdited
    canonicalEdited

/-- Direct literal push and canonical push agree on decoded syntax. -/
theorem pushRootLiteral?_agree {before fast canonical : Checked payloadWidth}
    {index : Nat} {side : Operations.Side}
    {reference : Nucleus.Classical.Packed.Word.Ref payloadWidth}
    (fastRan : Mutate.pushRootLiteral? before index side reference = some fast)
    (canonicalRan : Canonical.pushRoot? before index side
      (Mutate.literal reference) = some canonical) :
    fast.decoded.sequents = canonical.decoded.sequents := by
  have fastEdited := Mutate.checked?_decoded
    (Abstract.pushesRoot_eq_true (Mutate.literal reference) side)
    (by simpa [Mutate.pushRootLiteral?] using fastRan)
  have canonicalEdited := Canonical.edit?_result
    (by simpa [Canonical.pushRoot?] using canonicalRan)
  exact EditedAt.eq_of_functional optionRelation_functional fastEdited
    canonicalEdited

/-- Direct corrected crossing and canonical crossing agree on decoded syntax. -/
theorem crossRoot?_agree {before fast canonical : Checked payloadWidth}
    {index : Nat} {sourceSide : Operations.Side}
    (fastRan : Mutate.crossRoot? before index sourceSide = some fast)
    (canonicalRan : Canonical.crossRoot? before index sourceSide = some canonical) :
    fast.decoded.sequents = canonical.decoded.sequents := by
  have fastEdited := Mutate.checked?_decoded
    (Abstract.crossesRoot_eq_true sourceSide)
    (by simpa [Mutate.crossRoot?] using fastRan)
  have canonicalEdited := Canonical.edit?_result
    (by simpa [Canonical.crossRoot?] using canonicalRan)
  exact EditedAt.eq_of_functional optionRelation_functional fastEdited
    canonicalEdited

end Nucleus.Classical.Tagged.Runtime.Correspondence
