import Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor
import Nucleus.Hol.Ethane.Amber.Segment.Cbor

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

private def segmented : Segmented.Syntax O256 Nucleus.HolE.EmptySig UInt64 :=
  ⟨[⟨zeroKey, 3, 2⟩], [.bool false]⟩

/-- Segment slices have an independent, exact CBOR representation. -/
example :
    Cbor.decodeSegmentedSyntax? Arena.Cbor.uint64Names Arena.Cbor.emptySymbols
      (Cbor.encodeSegmentedSyntax Arena.Cbor.uint64Names Arena.Cbor.emptySymbols
        segmented) = some segmented := by
  apply Cbor.decodeSegmentedSyntax?_encode
  simp [segmented, Cbor.FitsSegmented, Cbor.FitsSegment, Cbor.FitsView,
    Row.view, Arena.Row.children]

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
