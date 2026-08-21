import Nucleus.Hol.Ethane.Amber.Memory
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

/-- The array-backed Rust model uses the same checked append invariant as the
mathematical forest. -/
example :
    let memory : Memory.Syntax O256 Nucleus.HolE.EmptySig UInt64 :=
      ⟨none, #[.bool true]⟩
    memory.Valid := by
  simp [Memory.Valid, Memory.toDense, Dense.Valid, Dense.RowsValid,
    Dense.RowValid, Dense.offset, Arena.Row.children]

end Nucleus.Hol.Ethane.Amber.Examples
