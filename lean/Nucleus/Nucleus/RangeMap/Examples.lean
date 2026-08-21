import Nucleus.RangeMap

/-! # Range-map examples -/

namespace Nucleus.RangeMap.Examples

def negative : RangeMap String :=
  singleton (-3) 2 40 "negative" (by decide)

example : negative.lookup? (-3) = some {
    target := "negative", sourceIndex := 40, localOffset := 0 } := by
  decide

example : negative.lookup? (-2) = some {
    target := "negative", sourceIndex := 41, localOffset := 1 } := by
  decide

example : negative.lookup? (-1) = none := by
  decide

def crossingZero : RangeMap String :=
  singleton (-3) 8 10 "crossing" (by decide)

example : crossingZero.lookup? 4 = some {
    target := "crossing", sourceIndex := 17, localOffset := 7 } := by
  decide

def positive : RangeMap String :=
  singleton 2 5 (-10) "positive" (by decide)

example : positive.lookup? 6 = some {
    target := "positive", sourceIndex := -6, localOffset := 4 } := by
  decide

def overlapping : Raw String where
  ranges :=
    [{ start := -3, length := 4, offset := 10, target := "first" },
     { start := -1, length := 5, offset := 20, target := "second" }]

example : overlapping.normalize.ranges =
    [{ start := -3, length := 4, offset := 10, target := "first" },
     { start := 1, length := 3, offset := 22, target := "second" }] := by
  decide

example : overlapping.normalize.lookup? 2 = some {
    target := "second", sourceIndex := 23, localOffset := 1 } := by
  decide

end Nucleus.RangeMap.Examples
