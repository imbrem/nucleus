import Nucleus.Hol.Ethane.Amber.Syntax

/-!
# Segment forests

A segmented Amber forest replaces one parent prefix with an ordered list of
CAS slices.  Each slice contributes a contiguous range from an independently
addressed forest.  The concatenated ranges form the absolute prefix seen by
local rows.
-/

namespace Nucleus.Hol.Ethane.Amber

open Nucleus.Hol.Ethane
universe u v
set_option relaxedAutoImplicit true

/-- One checked half-open slice of a CAS-addressed denotation. -/
structure Segment (Key : Type u) where
  key : Key
  start : Nat
  length : Nat
  deriving DecidableEq

/-- Multiple imported slices followed by a dense local suffix. -/
structure Segmented (Key : Type u) (R : Type v) where
  segments : List (Segment Key)
  rows : List R
  deriving DecidableEq

namespace Segment

/-- Resolve and bounds-check one slice. -/
def resolve? (resolve : Dense.Resolver Key Value) (segment : Segment Key) :
    Option (List Value) := do
  let values ← resolve segment.key
  if segment.start + segment.length ≤ values.length then
    some ((values.drop segment.start).take segment.length)
  else
    none

@[simp] theorem resolve?_length {resolve : Dense.Resolver Key Value}
    {segment : Segment Key} {values : List Value}
    (resolved : segment.resolve? resolve = some values) :
    values.length = segment.length := by
  unfold resolve? at resolved
  cases sourceEq : resolve segment.key with
  | none => rw [sourceEq] at resolved; contradiction
  | some source =>
      rw [sourceEq] at resolved
      simp only [Option.bind_eq_bind, Option.bind_some] at resolved
      by_cases inBounds : segment.start + segment.length ≤ source.length
      · rw [if_pos inBounds] at resolved
        injection resolved with valuesEq
        subst values
        simp [List.length_take, List.length_drop]
        omega
      · rw [if_neg inBounds] at resolved
        contradiction

end Segment

namespace Segmented

/-- Number of absolute indices supplied by all segments. -/
def offset (forest : Segmented Key R) : Nat :=
  (forest.segments.map Segment.length).sum

/-- First unallocated absolute index. -/
def next (forest : Segmented Key R) : Nat := forest.offset + forest.rows.length

/-- The same backward-edge invariant used by dense parent overlays. -/
def Valid [Row R Tag Nat Extra] (forest : Segmented Key R) : Prop :=
  Dense.RowsValid forest.offset forest.rows

/-- Resolve slices in order and concatenate their values. -/
def resolveSegments? (resolve : Dense.Resolver Key Value) :
    List (Segment Key) → Option (List Value)
  | [] => some []
  | segment :: segments =>
      return (← segment.resolve? resolve) ++ (← resolveSegments? resolve segments)

/-- Resolve all imports and elaborate the local suffix. -/
def denote? [Elaborates R Value] (resolve : Dense.Resolver Key Value)
    (forest : Segmented Key R) : Option (Dense.Denotation Value) := do
  let base ← resolveSegments? resolve forest.segments
  return ⟨base, Dense.elaborateLocal base forest.rows⟩

theorem resolveSegments?_length {resolve : Dense.Resolver Key Value}
    {segments : List (Segment Key)} {values : List Value}
    (resolved : resolveSegments? resolve segments = some values) :
    values.length = (segments.map Segment.length).sum := by
  induction segments generalizing values with
  | nil =>
      change some [] = some values at resolved
      injection resolved with valuesEq
      subst values
      rfl
  | cons segment segments ih =>
      simp only [resolveSegments?] at resolved
      cases segmentEq : segment.resolve? resolve with
      | none => rw [segmentEq] at resolved; contradiction
      | some segmentValues =>
          rw [segmentEq] at resolved
          cases restEq : resolveSegments? resolve segments with
          | none => rw [restEq] at resolved; contradiction
          | some rest =>
              rw [restEq] at resolved
              injection resolved with valuesEq
              subst values
              rw [List.length_append, Segment.resolve?_length segmentEq, ih restEq]
              simp

theorem denote?_size [Elaborates R Value]
    {resolve : Dense.Resolver Key Value} {forest : Segmented Key R}
    {denotation : Dense.Denotation Value}
    (denotes : forest.denote? resolve = some denotation) :
    denotation.size = forest.next := by
  unfold denote? at denotes
  cases segmentsEq : resolveSegments? resolve forest.segments with
  | none => rw [segmentsEq] at denotes; contradiction
  | some base =>
      rw [segmentsEq] at denotes
      have denotationEq :
          Dense.Denotation.mk base (Dense.elaborateLocal base forest.rows) = denotation :=
        Option.some.inj denotes
      subst denotation
      change base.length + (Dense.elaborateLocal base forest.rows).length =
        forest.offset + forest.rows.length
      rw [Dense.elaborateLocal_length, resolveSegments?_length segmentsEq]
      rfl

/-- Segmented Ethane syntax forest. -/
abbrev Syntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat) :=
  Segmented Key (Arena.Row Sig Name Nat)

end Segmented

end Nucleus.Hol.Ethane.Amber
