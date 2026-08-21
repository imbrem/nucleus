import Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor
import Nucleus.Hol.Ethane.Amber.Segment

/-! # Executable Amber specification examples -/

namespace Nucleus.Hol.Ethane.Amber.Examples

open Nucleus Nucleus.Hol.Ethane

private def zeroKey : O256 := fun _ => 0

private def truth : Syn Nucleus.HolE.EmptySig UInt64 := .bool true

/-- The concrete O256/CBOR specialization round-trips one canonical Ethane
expression. -/
example :
    Cbor.decodeExpression? (Key := O256) Arena.Cbor.uint64Names
      Arena.Cbor.emptySymbols
      (Cbor.encodeExpression (Key := O256) Arena.Cbor.uint64Names
        Arena.Cbor.emptySymbols truth) = some truth := by
  apply Cbor.decodeExpression?_encode
  change Cbor.FitsDense
    (⟨none, [Arena.Row.bool true]⟩ :
      SyntaxForest O256 Nucleus.HolE.EmptySig UInt64)
  simp [Cbor.FitsDense, Cbor.FitsParent, Cbor.FitsView,
    Row.view, Arena.Row.children]

private def parented : SyntaxForest O256 Nucleus.HolE.EmptySig UInt64 :=
  ⟨some ⟨zeroKey, 1⟩, [.bool true]⟩

/-- Parent metadata and syntax rows survive the concrete CBOR boundary. -/
example :
    Cbor.decodeSyntaxForest? Arena.Cbor.uint64Names Arena.Cbor.emptySymbols
      (Cbor.encodeSyntaxForest Arena.Cbor.uint64Names Arena.Cbor.emptySymbols parented) =
      some parented := by
  apply Cbor.decodeSyntaxForest?_encode
  simp [parented, Cbor.FitsDense, Cbor.FitsParent, Cbor.FitsView,
    Row.view, Arena.Row.children]

private def segmentRange : RangeMap.Range O256 :=
  ⟨-3, 2, -7, zeroKey⟩

private def segment : Arena.Segment.Syntax O256 Nucleus.HolE.EmptySig UInt64 :=
  ⟨RangeMap.singleton segmentRange.start segmentRange.length segmentRange.offset
      segmentRange.target (by simp [segmentRange]),
    1, [.bool false]⟩

/-- Signed destination and source coordinates are preserved by segment lookup. -/
example : segment.sourceAt? (-2) = some (zeroKey, -6) := by
  have member : segmentRange ∈ segment.imports.ranges := by
    simp [segment, segmentRange, RangeMap.singleton]
  have within : 1 < segmentRange.length := by simp [segmentRange]
  have found := RangeMap.lookup?_start_add (ranges := segment.imports)
    member within
  have lookup : segment.imports.lookup? (-2) = some {
      target := zeroKey
      sourceIndex := -6
      localOffset := 1
    } := by
    simpa [segmentRange] using found
  simp only [Arena.Segment.sourceAt?, Arena.Segment.importAt?, lookup,
    Option.map_some]

/-- The array-backed Rust model uses signed indices by default. -/
example :
    let arena : Amber.Arena.Dense.Syntax O256 Nucleus.HolE.EmptySig UInt64 :=
      ⟨none, 0, #[.bool true]⟩
    arena.Valid := by
  simp [Amber.Arena.Dense.Valid, Amber.Arena.Dense.RowsValid,
    Amber.Arena.Dense.RowValid, Nucleus.Hol.Ethane.Arena.Row.children]

private def signedDense :
    Amber.Arena.Dense.Cbor.Syntax O256 Nucleus.HolE.EmptySig UInt64 :=
  ⟨none, -3, #[.bool true]⟩

/-- Signed offsets and literal syntax names round-trip through the tagged
dictionary format. -/
example :
    Amber.Arena.Dense.Cbor.decodeSyntax?
      (S := Amber.Serialization.StringMapV0)
      Arena.Cbor.uint64Names Arena.Cbor.emptySymbols
      (Amber.Arena.Dense.Cbor.encodeSyntax
        (S := Amber.Serialization.StringMapV0)
        Arena.Cbor.uint64Names Arena.Cbor.emptySymbols signedDense) =
      some signedDense := by
  apply Amber.Arena.Dense.Cbor.decodeSyntax?_encode
  constructor
  · change 2 < 2 ^ 64
    norm_num
  · simp [signedDense, Amber.Arena.Dense.Cbor.FitsView,
      Row.view, Arena.Row.children]

end Nucleus.Hol.Ethane.Amber.Examples
