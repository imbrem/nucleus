import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Finite range maps

A `RangeMap α` is a canonical finite partial map from natural-number indices to
targets of type `α`. Its representation is a list of positive-length half-open
ranges, sorted by source position and with no overlaps. Looking up an index can
also return its offset from the beginning of the containing range.

Range maps are useful for describing arena overlays and segment tables, but this
module is independent of either application.
-/

namespace Nucleus

universe u v w

namespace RangeMap

/-- A target attached to the half-open source interval `[start, start + length)`. -/
structure Range (α : Type u) where
  start : Nat
  length : Nat
  target : α
  deriving Repr

namespace Range

/-- The exclusive upper bound of a range. -/
def stop (range : Range α) : Nat :=
  range.start + range.length

/-- Whether an index lies in the range's half-open source interval. -/
def Contains (range : Range α) (index : Nat) : Prop :=
  range.start ≤ index ∧ index < range.stop

instance (range : Range α) (index : Nat) : Decidable (range.Contains index) :=
  inferInstanceAs (Decidable (range.start ≤ index ∧ index < range.stop))

/-- The offset of an index from the start of a range, when it is contained. -/
def offset? (range : Range α) (index : Nat) : Option Nat :=
  if range.Contains index then some (index - range.start) else none

/-- Change a range's target without changing its source interval. -/
def mapTarget (f : α → β) (range : Range α) : Range β where
  start := range.start
  length := range.length
  target := f range.target

@[simp] theorem stop_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).stop = range.stop := rfl

@[simp] theorem start_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).start = range.start := rfl

@[simp] theorem length_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).length = range.length := rfl

@[simp] theorem target_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).target = f range.target := rfl

@[simp] theorem contains_mapTarget (f : α → β) (range : Range α) (index : Nat) :
    (range.mapTarget f).Contains index ↔ range.Contains index := by
  rfl

@[simp] theorem mapTarget_id (range : Range α) :
    range.mapTarget id = range := by
  cases range
  rfl

@[simp] theorem mapTarget_comp (g : β → γ) (f : α → β) (range : Range α) :
    (range.mapTarget f).mapTarget g = range.mapTarget (g ∘ f) := by
  cases range
  rfl

theorem offset_lt_length {range : Range α} {index : Nat}
    (contains : range.Contains index) :
    index - range.start < range.length := by
  simp only [Contains, stop] at contains
  omega

theorem start_add_offset {range : Range α} {index : Nat}
    (contains : range.Contains index) :
    range.start + (index - range.start) = index := by
  simp only [Contains, stop] at contains
  omega

@[simp] theorem offset?_eq_some_iff {range : Range α} {index offset : Nat} :
    range.offset? index = some offset ↔
      range.Contains index ∧ offset = index - range.start := by
  by_cases contains : range.Contains index <;> simp [offset?, contains, eq_comm]

end Range

/--
The representation invariant for a range map: every range is nonempty, and
earlier ranges finish no later than later ranges begin.
-/
def Valid (ranges : List (Range α)) : Prop :=
  (∀ range ∈ ranges, 0 < range.length) ∧
    ranges.Pairwise fun left right => left.stop ≤ right.start

instance (ranges : List (Range α)) : Decidable (Valid ranges) := by
  unfold Valid
  infer_instance

end RangeMap

/-- A sorted, nonoverlapping finite map from half-open natural ranges to targets. -/
structure RangeMap (α : Type u) where
  ranges : List (RangeMap.Range α)
  valid : RangeMap.Valid ranges

namespace RangeMap

variable {α : Type u} {β : Type v} {γ : Type w}

@[ext]
theorem ext {left right : RangeMap α} (ranges : left.ranges = right.ranges) :
    left = right := by
  cases left
  cases right
  cases ranges
  rfl

/-- The empty range map. -/
def empty : RangeMap α where
  ranges := []
  valid := by simp [Valid]

instance : EmptyCollection (RangeMap α) := ⟨empty⟩

@[simp] theorem ranges_empty : (∅ : RangeMap α).ranges = [] := rfl

/-- A range map containing one positive-length range. -/
def singleton (start length : Nat) (target : α) (positive : 0 < length) : RangeMap α where
  ranges := [{ start, length, target }]
  valid := by simp [Valid, positive]

/-- Check that a list is the canonical sorted representation of a range map. -/
def ofList? (ranges : List (Range α)) : Option (RangeMap α) :=
  if valid : Valid ranges then some ⟨ranges, valid⟩ else none

@[simp] theorem ofList?_eq_some_iff {ranges : List (Range α)} {map : RangeMap α} :
    ofList? ranges = some map ↔ map.ranges = ranges := by
  constructor
  · intro equality
    simp only [ofList?] at equality
    split at equality
    · cases equality
      rfl
    · contradiction
  · intro equality
    subst ranges
    simp [ofList?, map.valid]

@[simp] theorem ofList?_isSome_iff {ranges : List (Range α)} :
    (ofList? ranges).isSome ↔ Valid ranges := by
  simp [ofList?]

@[simp] theorem ofList?_ranges {ranges : List (Range α)} {map : RangeMap α}
    (decoded : ofList? ranges = some map) :
    map.ranges = ranges :=
  ofList?_eq_some_iff.mp decoded

/-- Map a function over the targets while retaining the source intervals. -/
def map (f : α → β) (ranges : RangeMap α) : RangeMap β where
  ranges := ranges.ranges.map (Range.mapTarget f)
  valid := by
    rcases ranges.valid with ⟨positive, ordered⟩
    constructor
    · intro mapped membership
      simp only [List.mem_map] at membership
      obtain ⟨range, membership, rfl⟩ := membership
      exact positive range membership
    · simpa only [List.pairwise_map, Range.stop_mapTarget,
        Range.start_mapTarget] using ordered

instance : Functor (RangeMap.{u}) where
  map := map

@[simp] theorem ranges_map (f : α → β) (ranges : RangeMap α) :
    (map f ranges).ranges = ranges.ranges.map (Range.mapTarget f) := rfl

@[simp] theorem map_id (ranges : RangeMap α) :
    map id ranges = ranges := by
  ext
  simp [map]

@[simp] theorem map_comp (g : β → γ) (f : α → β) (ranges : RangeMap α) :
    map g (map f ranges) = map (g ∘ f) ranges := by
  ext
  simp [map]

private def lookupRangesWithOffset? : List (Range α) → Nat → Option (α × Nat)
  | [], _ => none
  | range :: rest, index =>
      if range.Contains index then
        some (range.target, index - range.start)
      else
        lookupRangesWithOffset? rest index

private theorem lookupRangesWithOffset?_map
    (f : α → β) (raw : List (Range α)) (index : Nat) :
    lookupRangesWithOffset? (raw.map (Range.mapTarget f)) index =
      (lookupRangesWithOffset? raw index).map fun result => (f result.1, result.2) := by
  induction raw with
  | nil => rfl
  | cons range rest ih =>
      by_cases contains : range.Contains index
      · simp [lookupRangesWithOffset?, contains]
      · simp [lookupRangesWithOffset?, contains, ih]

/-- Find the target and the index's offset within its containing range. -/
def lookupWithOffset? (ranges : RangeMap α) (index : Nat) : Option (α × Nat) :=
  lookupRangesWithOffset? ranges.ranges index

/-- Find the target attached to an index. -/
def lookup? (ranges : RangeMap α) (index : Nat) : Option α :=
  (ranges.lookupWithOffset? index).map Prod.fst

/--
The integer-indexed view of `lookupWithOffset?`. Nonnegative integers delegate
to the canonical natural-number representation; negative indices are outside
the map. This does not assign an application-specific meaning to negatives.
-/
def lookupIntWithOffset? (ranges : RangeMap α) : Int → Option (α × Nat)
  | .ofNat index => ranges.lookupWithOffset? index
  | .negSucc _ => none

/-- The integer-indexed view of target lookup. -/
def lookupInt? (ranges : RangeMap α) (index : Int) : Option α :=
  (ranges.lookupIntWithOffset? index).map Prod.fst

@[simp] theorem lookupIntWithOffset?_ofNat (ranges : RangeMap α) (index : Nat) :
    ranges.lookupIntWithOffset? (Int.ofNat index) = ranges.lookupWithOffset? index := rfl

@[simp] theorem lookupIntWithOffset?_negSucc (ranges : RangeMap α) (index : Nat) :
    ranges.lookupIntWithOffset? (Int.negSucc index) = none := rfl

@[simp] theorem lookupInt?_ofNat (ranges : RangeMap α) (index : Nat) :
    ranges.lookupInt? (Int.ofNat index) = ranges.lookup? index := rfl

@[simp] theorem lookupInt?_negSucc (ranges : RangeMap α) (index : Nat) :
    ranges.lookupInt? (Int.negSucc index) = none := rfl

/-- Relational form of lookup, convenient for specifications and proofs. -/
def MapsTo (ranges : RangeMap α) (index : Nat) (target : α) (offset : Nat) : Prop :=
  ∃ range ∈ ranges.ranges,
    range.Contains index ∧ target = range.target ∧ offset = index - range.start

/-- An index belongs to a range map when lookup succeeds. -/
def Contains (ranges : RangeMap α) (index : Nat) : Prop :=
  ∃ target offset, ranges.MapsTo index target offset

private theorem lookupRangesWithOffset?_some_exists
    {raw : List (Range α)} {index : Nat} {result : α × Nat}
    (found : lookupRangesWithOffset? raw index = some result) :
    ∃ range ∈ raw,
      range.Contains index ∧ result.1 = range.target ∧ result.2 = index - range.start := by
  induction raw with
  | nil => simp [lookupRangesWithOffset?] at found
  | cons range rest ih =>
      simp only [lookupRangesWithOffset?] at found
      by_cases contains : range.Contains index
      · simp only [contains, ↓reduceIte, Option.some.injEq] at found
        rw [← found]
        exact ⟨range, by simp, contains, rfl, rfl⟩
      · simp only [contains, ↓reduceIte] at found
        obtain ⟨witness, member, covered, target, offset⟩ := ih found
        exact ⟨witness, by simp [member], covered, target, offset⟩

private theorem lookupRangesWithOffset?_of_mem
    {raw : List (Range α)} (valid : Valid raw)
    {range : Range α} (member : range ∈ raw)
    {index : Nat} (contains : range.Contains index) :
    lookupRangesWithOffset? raw index =
      some (range.target, index - range.start) := by
  induction raw with
  | nil => simp at member
  | cons head tail ih =>
      rcases valid with ⟨positive, ordered⟩
      have tailValid : Valid tail := by
        constructor
        · intro candidate candidateMember
          exact positive candidate (by simp [candidateMember])
        · exact ordered.tail
      rcases List.mem_cons.mp member with equality | tailMember
      · subst range
        simp [lookupRangesWithOffset?, contains]
      · have before : head.stop ≤ range.start :=
          ordered.rel_head_tail tailMember
        have headDoesNotContain : ¬head.Contains index := by
          intro headContains
          exact (Nat.not_lt_of_ge (before.trans contains.1)) headContains.2
        simp only [lookupRangesWithOffset?, headDoesNotContain, ↓reduceIte]
        exact ih tailValid tailMember

@[simp] theorem lookupWithOffset?_eq_some_iff
    {ranges : RangeMap α} {index : Nat} {target : α} {offset : Nat} :
    ranges.lookupWithOffset? index = some (target, offset) ↔
      ranges.MapsTo index target offset := by
  constructor
  · intro found
    obtain ⟨range, member, contains, targetEq, offsetEq⟩ :=
      lookupRangesWithOffset?_some_exists found
    exact ⟨range, member, contains, targetEq, offsetEq⟩
  · rintro ⟨range, member, contains, rfl, rfl⟩
    exact lookupRangesWithOffset?_of_mem ranges.valid member contains

theorem mapsTo_unique {ranges : RangeMap α} {index : Nat}
    {leftTarget rightTarget : α} {leftOffset rightOffset : Nat}
    (left : ranges.MapsTo index leftTarget leftOffset)
    (right : ranges.MapsTo index rightTarget rightOffset) :
    leftTarget = rightTarget ∧ leftOffset = rightOffset := by
  have equality : (leftTarget, leftOffset) = (rightTarget, rightOffset) := by
    apply Option.some.inj
    rw [← lookupWithOffset?_eq_some_iff.mpr left,
      ← lookupWithOffset?_eq_some_iff.mpr right]
  exact ⟨congrArg Prod.fst equality, congrArg Prod.snd equality⟩

@[simp] theorem lookupWithOffset?_start_add
    {ranges : RangeMap α} {range : Range α} (member : range ∈ ranges.ranges)
    {offset : Nat} (within : offset < range.length) :
    ranges.lookupWithOffset? (range.start + offset) = some (range.target, offset) := by
  rw [lookupWithOffset?_eq_some_iff]
  exact ⟨range, member, by simp [Range.Contains, Range.stop, within], rfl, by omega⟩

@[simp] theorem lookup?_eq_some_iff {ranges : RangeMap α} {index : Nat} {target : α} :
    ranges.lookup? index = some target ↔
      ∃ offset, ranges.MapsTo index target offset := by
  simp only [lookup?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨result, found, rfl⟩
    exact ⟨result.2, lookupWithOffset?_eq_some_iff.mp found⟩
  · rintro ⟨offset, mapsTo⟩
    exact ⟨(target, offset), lookupWithOffset?_eq_some_iff.mpr mapsTo, rfl⟩

@[simp] theorem contains_iff_lookup_isSome {ranges : RangeMap α} {index : Nat} :
    ranges.Contains index ↔ (ranges.lookup? index).isSome := by
  simp only [Contains, Option.isSome_iff_exists, lookup?_eq_some_iff]

@[simp] theorem contains_iff_exists_range {ranges : RangeMap α} {index : Nat} :
    ranges.Contains index ↔
      ∃ range ∈ ranges.ranges, range.Contains index := by
  constructor
  · rintro ⟨target, offset, range, member, contains, _, _⟩
    exact ⟨range, member, contains⟩
  · rintro ⟨range, member, contains⟩
    exact ⟨range.target, index - range.start,
      range, member, contains, rfl, rfl⟩

@[simp] theorem lookupWithOffset?_map (f : α → β) (ranges : RangeMap α) (index : Nat) :
    (map f ranges).lookupWithOffset? index =
      (ranges.lookupWithOffset? index).map fun result => (f result.1, result.2) := by
  exact lookupRangesWithOffset?_map f ranges.ranges index

/-! ## Offset maps -/

/-- A partial map whose successful outputs must be unique when `NoDuplicates` holds. -/
structure OffsetMap (ι : Type u) (α : Type v) where
  lookup? : ι → Option α

namespace OffsetMap

/-- No two inputs successfully map to the same output. Unmapped inputs are ignored. -/
def NoDuplicates (map : OffsetMap ι α) : Prop :=
  ∀ ⦃left right value⦄,
    map.lookup? left = some value → map.lookup? right = some value → left = right

theorem noDuplicates_iff_injectiveOn {map : OffsetMap ι α} :
    map.NoDuplicates ↔
      Set.InjOn map.lookup? {index | (map.lookup? index).isSome} := by
  constructor
  · intro noDuplicates left leftMember right rightMember equality
    obtain ⟨leftValue, leftFound⟩ := Option.isSome_iff_exists.mp leftMember
    obtain ⟨rightValue, rightFound⟩ := Option.isSome_iff_exists.mp rightMember
    rw [leftFound, rightFound] at equality
    cases equality
    exact noDuplicates leftFound rightFound
  · intro injective left right value leftFound rightFound
    apply injective
    · simp [leftFound]
    · simp [rightFound]
    · rw [leftFound, rightFound]

/-- Extend a natural-domain offset map to integers, leaving negatives unmapped. -/
def intDomain (map : OffsetMap Nat α) : OffsetMap Int α where
  lookup?
    | .ofNat index => map.lookup? index
    | .negSucc _ => none

@[simp] theorem intDomain_lookup?_ofNat (map : OffsetMap Nat α) (index : Nat) :
    map.intDomain.lookup? (Int.ofNat index) = map.lookup? index := rfl

@[simp] theorem intDomain_lookup?_negSucc (map : OffsetMap Nat α) (index : Nat) :
    map.intDomain.lookup? (Int.negSucc index) = none := rfl

@[simp] theorem noDuplicates_intDomain {map : OffsetMap Nat α} :
    map.intDomain.NoDuplicates ↔ map.NoDuplicates := by
  constructor
  · intro injective left right value leftFound rightFound
    exact Int.ofNat.inj (injective leftFound rightFound)
  · intro injective left right value leftFound rightFound
    cases left with
    | ofNat left =>
        cases right with
        | ofNat right =>
            exact congrArg Int.ofNat (injective leftFound rightFound)
        | negSucc right =>
            change none = some value at rightFound
            cases rightFound
    | negSucc left =>
        change none = some value at leftFound
        cases leftFound

end OffsetMap

/--
Interpret a target as the base of an output range and advance it by the local
offset of the source index.
-/
def toOffsetMap (ranges : RangeMap α) (advance : α → Nat → β) : OffsetMap Nat β where
  lookup? index :=
    (ranges.lookupWithOffset? index).map fun result => advance result.1 result.2

/-- The usual offset map when targets are natural-number bases. -/
def natOffsetMap (ranges : RangeMap Nat) : OffsetMap Nat Nat :=
  ranges.toOffsetMap (· + ·)

/-- The usual offset map when targets are integer bases. -/
def intOffsetMap (ranges : RangeMap Int) : OffsetMap Nat Int :=
  ranges.toOffsetMap fun target offset => target + Int.ofNat offset

/-- Natural targets with the integer-indexed source view. -/
def natOffsetMapOnInt (ranges : RangeMap Nat) : OffsetMap Int Nat :=
  ranges.natOffsetMap.intDomain

/-- Integer targets with the integer-indexed source view. -/
def intOffsetMapOnInt (ranges : RangeMap Int) : OffsetMap Int Int :=
  ranges.intOffsetMap.intDomain

/--
Range-level characterization of injectivity for an offset interpretation.
Offsets in two target ranges may coincide only when their source indices do.
-/
def TargetsInjectively (ranges : RangeMap α) (advance : α → Nat → β) : Prop :=
  ∀ ⦃left right : Range α⦄,
    left ∈ ranges.ranges → right ∈ ranges.ranges →
    ∀ ⦃leftOffset rightOffset : Nat⦄,
      leftOffset < left.length → rightOffset < right.length →
      advance left.target leftOffset = advance right.target rightOffset →
      left.start + leftOffset = right.start + rightOffset

theorem noDuplicates_toOffsetMap_iff
    {ranges : RangeMap α} {advance : α → Nat → β} :
    (ranges.toOffsetMap advance).NoDuplicates ↔ ranges.TargetsInjectively advance := by
  constructor
  · intro noDuplicates left right leftMember rightMember leftOffset rightOffset
      leftWithin rightWithin sameTarget
    exact noDuplicates
      (value := advance left.target leftOffset)
      (by simp [toOffsetMap, lookupWithOffset?_start_add leftMember leftWithin])
      (by rw [sameTarget]
          simp [toOffsetMap, lookupWithOffset?_start_add rightMember rightWithin])
  · intro targets leftIndex rightIndex value leftFound rightFound
    simp only [toOffsetMap, Option.map_eq_some_iff] at leftFound rightFound
    obtain ⟨leftResult, leftLookup, leftValue⟩ := leftFound
    obtain ⟨rightResult, rightLookup, rightValue⟩ := rightFound
    rw [lookupWithOffset?_eq_some_iff] at leftLookup rightLookup
    obtain ⟨left, leftMember, leftContains, leftTarget, leftOffset⟩ := leftLookup
    obtain ⟨right, rightMember, rightContains, rightTarget, rightOffset⟩ := rightLookup
    have targetEquality :
        advance left.target (leftIndex - left.start) =
          advance right.target (rightIndex - right.start) := by
      rw [← leftTarget, ← rightTarget, ← leftOffset, ← rightOffset,
        leftValue, rightValue]
    have sourceEquality := targets leftMember rightMember
      (Range.offset_lt_length leftContains) (Range.offset_lt_length rightContains)
      targetEquality
    simpa only [Range.start_add_offset leftContains,
      Range.start_add_offset rightContains] using sourceEquality

/-- Pairwise disjointness of the natural-number target intervals. -/
def TargetIntervalsDisjoint (ranges : RangeMap Nat) : Prop :=
  ∀ ⦃left right : Range Nat⦄,
    left ∈ ranges.ranges → right ∈ ranges.ranges →
    left = right ∨
      left.target + left.length ≤ right.target ∨
      right.target + right.length ≤ left.target

theorem TargetIntervalsDisjoint.noDuplicates {ranges : RangeMap Nat}
    (disjoint : ranges.TargetIntervalsDisjoint) :
    ranges.natOffsetMap.NoDuplicates := by
  rw [natOffsetMap, noDuplicates_toOffsetMap_iff]
  intro left right leftMember rightMember leftOffset rightOffset
    leftWithin rightWithin equality
  rcases disjoint leftMember rightMember with same | before | after
  · subst right
    have offsets : leftOffset = rightOffset := Nat.add_left_cancel equality
    simp [offsets]
  · change left.target + leftOffset = right.target + rightOffset at equality
    omega
  · change left.target + leftOffset = right.target + rightOffset at equality
    omega

/-! ## A small interface for range-map-like values -/

/-- A value with a distinguished canonical range-map representation. -/
class RangeMapLike (M : Type u) (α : outParam (Type v)) where
  toRangeMap : M → RangeMap α

def RangeMapLike.asRangeMap [RangeMapLike M α] (value : M) : RangeMap α :=
  RangeMapLike.toRangeMap value

instance : RangeMapLike (RangeMap α) α where
  toRangeMap := id

/-- A single positive-length segment, viewed canonically as a one-entry range map. -/
structure Single (α : Type u) where
  start : Nat
  length : Nat
  target : α
  positive : 0 < length

namespace Single

def toRangeMap (single : Single α) : RangeMap α :=
  singleton single.start single.length single.target single.positive

instance : RangeMapLike (Single α) α where
  toRangeMap := toRangeMap

@[simp] theorem ranges_toRangeMap (single : Single α) :
    single.toRangeMap.ranges =
      [{ start := single.start, length := single.length, target := single.target }] := rfl

end Single

end RangeMap

end Nucleus
