import Nucleus.Hol.Ethane.Amber.Cbor
import Nucleus.Hol.Ethane.Amber.Segment

/-! # CBOR representation of Amber segment forests -/

namespace Nucleus.Hol.Ethane.Amber.Cbor

open Nucleus Nucleus.Hol.Ethane
universe u
set_option relaxedAutoImplicit true

private def segmentArray? : Nucleus.Cbor → Option (List Nucleus.Cbor) :=
  Nucleus.Cbor.asArray?

private def segmentNat? : Nucleus.Cbor → Option Nat
  | .primitive (.integer (.unsigned value)) => some value.toNat
  | _ => none

private def segmentTraverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← segmentTraverse decode values)

@[simp] private theorem segmentArray?_array (values : List Nucleus.Cbor) :
    segmentArray? (array values) = some values := by
  exact Nucleus.Cbor.asArray?_arrayOfList values

@[simp] private theorem segmentNat?_unsigned (value : Nat)
    (fits : value < 2 ^ 64) : segmentNat? (unsigned value) = some value := by
  simpa [segmentNat?, unsigned] using fits

/-- A segment's indices fit the unsigned CBOR representation. -/
def FitsSegment (segment : Segment Key) : Prop :=
  segment.start < 2 ^ 64 ∧ segment.length < 2 ^ 64

def encodeSegment [CasKey Key] (segment : Segment Key) : Nucleus.Cbor :=
  array [CasKey.encode segment.key, unsigned segment.start, unsigned segment.length]

def decodeSegment? [CasKey Key] (value : Nucleus.Cbor) : Option (Segment Key) := do
  match ← segmentArray? value with
  | [key, start, length] =>
      return ⟨← CasKey.decode? key, ← segmentNat? start, ← segmentNat? length⟩
  | _ => none

@[simp] theorem decodeSegment?_encode [CasKey Key] (segment : Segment Key)
    (fits : FitsSegment segment) :
    decodeSegment? (encodeSegment segment) = some segment := by
  rcases fits with ⟨startFits, lengthFits⟩
  simp [decodeSegment?, encodeSegment, CasKey.decode_encode,
    segmentNat?_unsigned segment.start startFits,
    segmentNat?_unsigned segment.length lengthFits]

/-- Every segment field and local row reference fits CBOR. -/
def FitsSegmented [Row R Tag Nat Extra] (forest : Segmented Key R) : Prop :=
  (∀ segment ∈ forest.segments, FitsSegment segment) ∧
    ∀ row ∈ forest.rows, FitsView (Row.view row)

def encodeSegmented [CasKey Key] [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra)
    (forest : Segmented Key R) : Nucleus.Cbor :=
  array [text "ETHANE_AMBER_SEGMENTED",
    array (forest.segments.map encodeSegment),
    array (forest.rows.map fun row => encodeView tag extra (Row.view row))]

def decodeSegmented? [CasKey Key]
    (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (value : Nucleus.Cbor) : Option (Segmented Key R) := do
  match ← segmentArray? value with
  | [.primitive (.text "ETHANE_AMBER_SEGMENTED"), segments, rows] =>
      return ⟨← segmentTraverse decodeSegment? (← segmentArray? segments),
        ← segmentTraverse (fun value => (decodeView? tag extra value).bind ofView?)
          (← segmentArray? rows)⟩
  | _ => none

private theorem segmentTraverse_segments [CasKey Key]
    (segments : List (Segment Key))
    (fits : ∀ segment ∈ segments, FitsSegment segment) :
    segmentTraverse decodeSegment? (segments.map encodeSegment) = some segments := by
  induction segments with
  | nil => rfl
  | cons segment segments ih =>
      simp [segmentTraverse, decodeSegment?_encode segment (fits segment (by simp)),
        ih (fun item member => fits item (by simp [member]))]

private theorem segmentTraverse_rows [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (rows : List R) (fits : ∀ row ∈ rows, FitsView (Row.view row)) :
    segmentTraverse (fun value => (decodeView? tag extra value).bind ofView?)
      (rows.map fun row => encodeView tag extra (Row.view row)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [segmentTraverse, decodeView?_encode tag extra (Row.view row)
          (fits row (by simp)), ofView_view,
        ih (fun item member => fits item (by simp [member]))]

@[simp] theorem decodeSegmented?_encode [CasKey Key] [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (forest : Segmented Key R) (fits : FitsSegmented forest) :
    decodeSegmented? tag extra ofView? (encodeSegmented tag extra forest) =
      some forest := by
  rcases forest with ⟨segments, rows⟩
  rcases fits with ⟨segmentsFit, rowsFit⟩
  simp [decodeSegmented?, encodeSegmented, text,
    segmentTraverse_segments segments segmentsFit,
    segmentTraverse_rows tag extra ofView? ofView_view rows rowsFit]

def encodeSegmentedSyntax [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (forest : Segmented.Syntax Key Sig Name) : Nucleus.Cbor :=
  encodeSegmented syntaxTag (syntaxExtra names symbols) forest

def decodeSegmentedSyntax? [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Segmented.Syntax Key Sig Name) :=
  decodeSegmented? syntaxTag (syntaxExtra names symbols) SyntaxRow.ofView? value

@[simp] theorem decodeSegmentedSyntax?_encode [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (forest : Segmented.Syntax Key Sig Name) (fits : FitsSegmented forest) :
    decodeSegmentedSyntax? names symbols
      (encodeSegmentedSyntax names symbols forest) = some forest := by
  exact decodeSegmented?_encode syntaxTag (syntaxExtra names symbols)
    SyntaxRow.ofView? SyntaxRow.ofView?_view forest fits

/-- Decode, resolve every CAS slice, and elaborate a segmented Ethane forest. -/
def interpretSegmentedSyntax? [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (resolve : Dense.Resolver Key (Arena.Value Sig Name))
    (value : Nucleus.Cbor) : Option (Dense.Denotation (Arena.Value Sig Name)) :=
  match decodeSegmentedSyntax? (Key := Key) names symbols value with
  | none => none
  | some forest => Segmented.denote? resolve forest

/-- CBOR interpretation agrees with resolving the original segment forest. -/
@[simp] theorem interpretSegmentedSyntax?_encode [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (resolve : Dense.Resolver Key (Arena.Value Sig Name))
    (forest : Segmented.Syntax Key Sig Name) (fits : FitsSegmented forest) :
    interpretSegmentedSyntax? names symbols resolve
      (encodeSegmentedSyntax names symbols forest) = forest.denote? resolve := by
  unfold interpretSegmentedSyntax?
  rw [decodeSegmentedSyntax?_encode names symbols forest fits]

end Nucleus.Hol.Ethane.Amber.Cbor
