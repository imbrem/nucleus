import Nucleus.Cas.Basic

/-! # Whole-object CAS examples -/

namespace Nucleus.CasExamples

/-- A tiny naming function which makes collisions easy to exhibit. -/
def constantName (_ : Bytes) : O256 := 0

def emptyPair : CasPair constantName := CasPair.ofBlob constantName Bytes.empty

def oneBytePair : CasPair constantName :=
  CasPair.ofBlob constantName (Bytes.empty.push 1)

/-- Checked construction does not assume that the naming function is injective. -/
example : emptyPair.hash = oneBytePair.hash := rfl

example : emptyPair.blob ≠ oneBytePair.blob := by
  decide

/-- A relation-style CAS retains both witnesses to a collision. -/
example : ((Cas.singleton emptyPair).insert oneBytePair).HasCollision := by
  refine ⟨emptyPair, ?_, oneBytePair, ?_, rfl, ?_⟩
  · exact Cas.mem_insert.mpr (Or.inr (Cas.mem_singleton.mpr rfl))
  · exact Cas.mem_insert.mpr (Or.inl rfl)
  · decide

/-- Checking rejects no valid assertion and returns a checked LCF atom. -/
example :
    ∃ pair, emptyPair.assertion.check? constantName = some pair :=
  CasAssertion.check?_complete emptyPair.valid

/-- A singleton is collision-free, so its relational lookup is functional. -/
example {left right : Bytes}
    (leftLookup : (Cas.singleton emptyPair).Lookup emptyPair.hash left)
    (rightLookup : (Cas.singleton emptyPair).Lookup emptyPair.hash right) :
    left = right :=
  Cas.lookup_functional (Cas.collisionFree_singleton emptyPair) leftLookup rightLookup

end Nucleus.CasExamples
