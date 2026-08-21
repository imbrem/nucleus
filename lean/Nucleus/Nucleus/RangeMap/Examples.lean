import Nucleus.RangeMap

/-! # Range-map examples -/

namespace Nucleus.RangeMap.Examples

def sample : RangeMap String :=
  (ofList?
    [{ start := 2, length := 3, target := "left" },
     { start := 8, length := 2, target := "right" }]).get (by
      simp [Valid, Range.stop])

example : sample.lookupWithOffset? 3 = some ("left", 1) := by
  decide

example : sample.lookup? 6 = none := by
  decide

def shifted : RangeMap Nat :=
  singleton 10 4 20 (by decide)

example : shifted.natOffsetMap.lookup? 12 = some 22 := by
  decide

example : shifted.natOffsetMap.NoDuplicates := by
  rw [natOffsetMap, noDuplicates_toOffsetMap_iff]
  intro left right leftMember rightMember leftOffset rightOffset
    leftWithin rightWithin equality
  simp only [shifted, singleton, List.mem_cons, List.not_mem_nil, or_false] at leftMember
  simp only [shifted, singleton, List.mem_cons, List.not_mem_nil, or_false] at rightMember
  subst left
  subst right
  change 20 + leftOffset = 20 + rightOffset at equality
  omega

end Nucleus.RangeMap.Examples
