import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Finite integer range maps

This module separates three representations:

* `RangeMap.Raw` is an unchecked list of ranges.
* `RangeMap.Multimap` is positive-length and strictly sorted by `(start, offset)`;
  source intervals may overlap.
* `RangeMap α` is positive-length and nonoverlapping, so lookup is a partial
  function.

Ranges use signed source coordinates. A hit at `index` has natural local offset
`index - start` and translated source coordinate `offset + (index - start)`.
This matches segment tables whose payload is a source object and whose stored
offset is a coordinate in that object.
-/

namespace Nucleus

universe u v w

namespace RangeMap

/-- A payload attached to `[start, start + length)`, translated from `offset`. -/
structure Range (α : Type u) where
  start : Int
  length : Nat
  offset : Int
  target : α
  deriving Repr, DecidableEq

namespace Range

/-- Exclusive upper bound of the source interval. -/
def stop (range : Range α) : Int :=
  range.start + (range.length : Int)

/-- The SQL-style ordering key for a range row. -/
def key (range : Range α) : Int × Int :=
  (range.start, range.offset)

/-- Lexicographic non-strict ordering by `(start, offset)`. -/
def KeyLE (left right : Range α) : Prop :=
  left.start < right.start ∨
    left.start = right.start ∧ left.offset ≤ right.offset

/-- Lexicographic strict ordering by `(start, offset)`. -/
def KeyLT (left right : Range α) : Prop :=
  left.start < right.start ∨
    left.start = right.start ∧ left.offset < right.offset

instance : DecidableRel (@KeyLE α) := fun left right => by
  simp only [KeyLE]
  infer_instance

instance : DecidableRel (@KeyLT α) := fun left right => by
  simp only [KeyLT]
  infer_instance

instance : Std.Total (@KeyLE α) where
  total left right := by
    simp only [KeyLE]
    omega

instance : IsTrans (Range α) (@KeyLE α) where
  trans left middle right leftMiddle middleRight := by
    simp only [KeyLE] at leftMiddle middleRight ⊢
    omega

/-- Whether an integer lies in the half-open source interval. -/
def Contains (range : Range α) (index : Int) : Prop :=
  range.start ≤ index ∧ index < range.stop

instance (range : Range α) (index : Int) : Decidable (range.Contains index) :=
  inferInstanceAs (Decidable (range.start ≤ index ∧ index < range.stop))

/-- Natural offset of a contained index from the source interval's start. -/
def localOffset (range : Range α) (index : Int) : Nat :=
  (index - range.start).toNat

/-- Coordinate in the target selected by an index. -/
def sourceIndex (range : Range α) (index : Int) : Int :=
  range.offset + (range.localOffset index : Int)

@[ext]
theorem ext {left right : Range α}
    (start : left.start = right.start)
    (length : left.length = right.length)
    (offset : left.offset = right.offset)
    (target : left.target = right.target) : left = right := by
  cases left
  cases right
  simp_all

/-- Change only the payload. -/
def mapTarget (f : α → β) (range : Range α) : Range β where
  start := range.start
  length := range.length
  offset := range.offset
  target := f range.target

@[simp] theorem start_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).start = range.start := rfl

@[simp] theorem length_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).length = range.length := rfl

@[simp] theorem offset_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).offset = range.offset := rfl

@[simp] theorem target_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).target = f range.target := rfl

@[simp] theorem stop_mapTarget (f : α → β) (range : Range α) :
    (range.mapTarget f).stop = range.stop := rfl

@[simp] theorem contains_mapTarget (f : α → β) (range : Range α) (index : Int) :
    (range.mapTarget f).Contains index ↔ range.Contains index := by
  rfl

@[simp] theorem localOffset_mapTarget (f : α → β) (range : Range α) (index : Int) :
    (range.mapTarget f).localOffset index = range.localOffset index := rfl

@[simp] theorem sourceIndex_mapTarget (f : α → β) (range : Range α) (index : Int) :
    (range.mapTarget f).sourceIndex index = range.sourceIndex index := rfl

@[simp] theorem mapTarget_id (range : Range α) :
    range.mapTarget id = range := by
  cases range
  rfl

@[simp] theorem mapTarget_comp (g : β → γ) (f : α → β) (range : Range α) :
    (range.mapTarget f).mapTarget g = range.mapTarget (g ∘ f) := by
  cases range
  rfl

theorem localOffset_lt {range : Range α} {index : Int}
    (contains : range.Contains index) :
    range.localOffset index < range.length := by
  rw [localOffset, Int.toNat_lt (Int.sub_nonneg.mpr contains.1)]
  simp only [Contains, stop] at contains
  omega

theorem start_add_localOffset {range : Range α} {index : Int}
    (contains : range.Contains index) :
    range.start + Int.ofNat (range.localOffset index) = index := by
  change range.start + (↑(index - range.start).toNat : Int) = index
  rw [Int.toNat_of_nonneg (Int.sub_nonneg.mpr contains.1)]
  omega

theorem start_lt_stop {range : Range α} (positive : 0 < range.length) :
    range.start < range.stop := by
  simp [stop, positive]

end Range

/-- Unchecked range rows. -/
structure Raw (α : Type u) where
  ranges : List (Range α)

/-- Positive, strictly `(start, offset)`-sorted rows; overlaps are permitted. -/
def MultimapValid (ranges : List (Range α)) : Prop :=
  (∀ range ∈ ranges, 0 < range.length) ∧
    ranges.Pairwise Range.KeyLT

instance (ranges : List (Range α)) : Decidable (MultimapValid ranges) := by
  unfold MultimapValid
  infer_instance

/-- A sorted range multimap. Equal source indices may have several hits. -/
structure Multimap (α : Type u) where
  ranges : List (Range α)
  valid : MultimapValid ranges

/-- Nonoverlap of source intervals in list order. -/
def Nonoverlapping (ranges : List (Range α)) : Prop :=
  ranges.Pairwise fun left right => left.stop ≤ right.start

/-- The canonical invariant for a range map. -/
def Valid (ranges : List (Range α)) : Prop :=
  (∀ range ∈ ranges, 0 < range.length) ∧ Nonoverlapping ranges

instance (ranges : List (Range α)) : Decidable (Valid ranges) := by
  unfold Valid Nonoverlapping
  infer_instance

end RangeMap

/-- A positive-length, nonoverlapping partial map over integer intervals. -/
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

namespace Raw

/-- Map over unchecked range payloads. -/
def map (f : α → β) (raw : Raw α) : Raw β where
  ranges := raw.ranges.map (Range.mapTarget f)

instance : Functor (Raw.{u}) where
  map := map

end Raw

namespace Multimap

@[ext]
theorem ext {left right : Multimap α} (ranges : left.ranges = right.ranges) :
    left = right := by
  cases left
  cases right
  cases ranges
  rfl

/-- Check the multimap invariant. -/
def ofList? (ranges : List (Range α)) : Option (Multimap α) :=
  if valid : MultimapValid ranges then some ⟨ranges, valid⟩ else none

@[simp] theorem ofList?_eq_some_iff {ranges : List (Range α)} {map : Multimap α} :
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

/-- Map over sorted multimap payloads. -/
def map (f : α → β) (ranges : Multimap α) : Multimap β where
  ranges := ranges.ranges.map (Range.mapTarget f)
  valid := by
    rcases ranges.valid with ⟨positive, ordered⟩
    constructor
    · simpa only [List.forall_mem_map, Range.length_mapTarget] using positive
    · rw [List.pairwise_map]
      exact ordered.imp fun relation => relation

instance : Functor (Multimap.{u}) where
  map := map

end Multimap

/-! ## Canonical maps and normalization -/

/-- The empty range map. -/
def empty : RangeMap α where
  ranges := []
  valid := by simp [Valid, Nonoverlapping]

instance : EmptyCollection (RangeMap α) := ⟨empty⟩

/-- A one-row range map. -/
def singleton (start : Int) (length : Nat) (offset : Int) (target : α)
    (positive : 0 < length) : RangeMap α where
  ranges := [{ start, length, offset, target }]
  valid := by simp [Valid, Nonoverlapping, positive]

/-- Check the canonical range-map invariant. -/
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

/-- Map over canonical range payloads. -/
def map (f : α → β) (ranges : RangeMap α) : RangeMap β where
  ranges := ranges.ranges.map (Range.mapTarget f)
  valid := by
    rcases ranges.valid with ⟨positive, ordered⟩
    constructor
    · simpa only [List.forall_mem_map, Range.length_mapTarget] using positive
    · simpa only [Nonoverlapping, List.pairwise_map, Range.stop_mapTarget,
        Range.start_mapTarget] using ordered

instance : Functor (RangeMap.{u}) where
  map := map

@[simp] theorem map_id (ranges : RangeMap α) : map id ranges = ranges := by
  ext
  simp [map]

@[simp] theorem map_comp (g : β → γ) (f : α → β) (ranges : RangeMap α) :
    map g (map f ranges) = map (g ∘ f) ranges := by
  ext
  simp [map]

private def clip (cursor : Int) (range : Range α) : Option (Range α) :=
  let start := max cursor range.start
  if start < range.stop then
    some {
      start
      length := (range.stop - start).toNat
      offset := range.offset + (start - range.start)
      target := range.target
    }
  else
    none

private theorem clip_spec {cursor : Int} {range clipped : Range α}
    (clippedEq : clip cursor range = some clipped) :
    0 < clipped.length ∧ cursor ≤ clipped.start ∧ clipped.stop = range.stop := by
  simp only [clip] at clippedEq
  split at clippedEq
  · rename_i beforeStop
    cases clippedEq
    constructor
    · rw [Nat.pos_iff_ne_zero]
      intro zero
      rw [Int.toNat_eq_zero] at zero
      omega
    · constructor
      · simp
      · simp only [Range.stop]
        change max cursor range.start +
          (↑(range.stop - max cursor range.start).toNat : Int) = range.stop
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ range.stop - max cursor range.start)]
        omega
  · contradiction

private theorem clip_of_le_start {cursor : Int} {range : Range α}
    (before : cursor ≤ range.start) (positive : 0 < range.length) :
    clip cursor range = some range := by
  simp only [clip, max_eq_right before]
  have beforeStop := Range.start_lt_stop (range := range) positive
  simp only [beforeStop, if_true, Option.some.injEq]
  apply Range.ext <;> simp [Range.stop]

private def normalizeAfter (cursor : Int) : List (Range α) → List (Range α)
  | [] => []
  | range :: rest =>
      match clip cursor range with
      | none => normalizeAfter cursor rest
      | some clippedRange =>
          clippedRange :: normalizeAfter clippedRange.stop rest

private theorem normalizeAfter_spec (cursor : Int) (ranges : List (Range α)) :
    (∀ range ∈ normalizeAfter cursor ranges, 0 < range.length) ∧
    Nonoverlapping (normalizeAfter cursor ranges) ∧
    (∀ range ∈ normalizeAfter cursor ranges, cursor ≤ range.start) := by
  induction ranges generalizing cursor with
  | nil => simp [normalizeAfter, Nonoverlapping]
  | cons range rest ih =>
      simp only [normalizeAfter]
      split
      next clippedEq => simpa only using ih cursor
      next clipped clippedEq =>
        rcases clip_spec clippedEq with ⟨clippedPositive, cursorBefore, clippedStop⟩
        rcases ih clipped.stop with ⟨tailPositive, tailOrdered, tailAfter⟩
        constructor
        · intro candidate member
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact clippedPositive
          · exact tailPositive candidate tailMember
        · constructor
          · rw [Nonoverlapping, List.pairwise_cons]
            exact ⟨fun candidate member => tailAfter candidate member, tailOrdered⟩
          · intro candidate member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact cursorBefore
            · exact cursorBefore.trans ((Range.start_lt_stop clippedPositive).le.trans
                (tailAfter candidate tailMember))

private theorem normalizeAfter_eq_self
    {cursor : Int} {ranges : List (Range α)}
    (positive : ∀ range ∈ ranges, 0 < range.length)
    (ordered : Nonoverlapping ranges)
    (after : ∀ range ∈ ranges, cursor ≤ range.start) :
    normalizeAfter cursor ranges = ranges := by
  induction ranges generalizing cursor with
  | nil => rfl
  | cons range rest ih =>
      have rangePositive := positive range (by simp)
      have rangeAfter := after range (by simp)
      have tailPositive : ∀ candidate ∈ rest, 0 < candidate.length := by
        intro candidate member
        exact positive candidate (by simp [member])
      have tailOrdered : Nonoverlapping rest := ordered.tail
      have tailAfter : ∀ candidate ∈ rest, range.stop ≤ candidate.start := by
        intro candidate member
        exact ordered.rel_head_tail member
      rw [normalizeAfter, clip_of_le_start rangeAfter rangePositive]
      change range :: normalizeAfter range.stop rest = range :: rest
      rw [ih tailPositive tailOrdered tailAfter]

/-- Drop zero-length rows and stably sort by `(start, offset)`. -/
def Raw.prepare (raw : Raw α) : List (Range α) :=
  (raw.ranges.filter fun range => decide (0 < range.length)).insertionSort Range.KeyLE

theorem Raw.prepare_positive {raw : Raw α} {range : Range α}
    (member : range ∈ raw.prepare) : 0 < range.length := by
  have filteredMember :
      range ∈ raw.ranges.filter fun candidate => decide (0 < candidate.length) :=
    (List.mem_insertionSort Range.KeyLE).mp member
  exact of_decide_eq_true (List.mem_filter.mp filteredMember).2

theorem Raw.prepare_ordered (raw : Raw α) :
    raw.prepare.Pairwise Range.KeyLE := by
  exact List.pairwise_insertionSort Range.KeyLE _

private def normalizedRanges (raw : Raw α) : List (Range α) :=
  match raw.prepare with
  | [] => []
  | first :: rest => first :: normalizeAfter first.stop rest

private theorem normalizedRanges_valid (raw : Raw α) : Valid (normalizedRanges raw) := by
  unfold normalizedRanges
  split
  · simp [Valid, Nonoverlapping]
  · rename_i first rest preparedEq
    have firstPositive : 0 < first.length :=
      raw.prepare_positive (by simp [preparedEq])
    rcases normalizeAfter_spec first.stop rest with
      ⟨tailPositive, tailOrdered, tailAfter⟩
    constructor
    · intro range member
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact firstPositive
      · exact tailPositive range tailMember
    · rw [Nonoverlapping, List.pairwise_cons]
      exact ⟨fun range member => tailAfter range member, tailOrdered⟩

/--
Normalize arbitrary rows by stable `(start, offset)` sorting, then give earlier
rows precedence. A later overlapping prefix is clipped and its target offset is
advanced by the clipped amount; a wholly covered row is dropped.
-/
def Raw.normalize (raw : Raw α) : RangeMap α where
  ranges := normalizedRanges raw
  valid := normalizedRanges_valid raw

private theorem keyLT_pairwise_of_valid {ranges : List (Range α)}
    (positive : ∀ range ∈ ranges, 0 < range.length)
    (ordered : Nonoverlapping ranges) : ranges.Pairwise Range.KeyLT := by
  induction ranges with
  | nil => exact List.Pairwise.nil
  | cons range rest ih =>
      rw [List.pairwise_cons]
      constructor
      · intro candidate member
        left
        exact (Range.start_lt_stop (positive range (by simp))).trans_le
          (ordered.rel_head_tail member)
      · exact ih
          (fun candidate member => positive candidate (by simp [member]))
          ordered.tail

private theorem keyLE_pairwise_of_valid {ranges : List (Range α)}
    (positive : ∀ range ∈ ranges, 0 < range.length)
    (ordered : Nonoverlapping ranges) : ranges.Pairwise Range.KeyLE :=
  (keyLT_pairwise_of_valid positive ordered).imp fun relation => by
    rcases relation with before | ⟨same, offsetBefore⟩
    · exact Or.inl before
    · exact Or.inr ⟨same, offsetBefore.le⟩

private theorem Raw.prepare_eq_self {raw : Raw α} (valid : Valid raw.ranges) :
    raw.prepare = raw.ranges := by
  rcases valid with ⟨positive, ordered⟩
  unfold Raw.prepare
  have filtered :
      raw.ranges.filter (fun range => decide (0 < range.length)) = raw.ranges := by
    apply List.filter_eq_self.mpr
    intro range member
    simp [positive range member]
  rw [filtered]
  exact (keyLE_pairwise_of_valid positive ordered).insertionSort_eq

private theorem normalizedRanges_eq_self {raw : Raw α} (valid : Valid raw.ranges) :
    normalizedRanges raw = raw.ranges := by
  cases raw with
  | mk rawRanges =>
      cases rawRanges with
      | nil => rfl
      | cons first rest =>
          rw [normalizedRanges, Raw.prepare_eq_self valid]
          simp only
          rcases valid with ⟨positive, ordered⟩
          congr 1
          apply normalizeAfter_eq_self
          · intro range member
            exact positive range (by simp [member])
          · exact ordered.tail
          · intro range member
            exact ordered.rel_head_tail member

theorem Raw.normalize_eq_self_iff {raw : Raw α} :
    raw.normalize.ranges = raw.ranges ↔ Valid raw.ranges := by
  constructor
  · intro equality
    rw [← equality]
    exact raw.normalize.valid
  · exact normalizedRanges_eq_self

/-- Normalize a sorted multimap by resolving overlaps in row order. -/
def Multimap.normalize (ranges : Multimap α) : RangeMap α :=
  (Raw.mk ranges.ranges).normalize

theorem Multimap.normalize_eq_self_iff {ranges : Multimap α} :
    ranges.normalize.ranges = ranges.ranges ↔ Nonoverlapping ranges.ranges := by
  rw [Multimap.normalize, Raw.normalize_eq_self_iff]
  exact and_iff_right ranges.valid.1

/-- Every canonical range map is also a sorted range multimap. -/
def toMultimap (ranges : RangeMap α) : Multimap α where
  ranges := ranges.ranges
  valid := by
    rcases ranges.valid with ⟨positive, ordered⟩
    exact ⟨positive, keyLT_pairwise_of_valid positive ordered⟩

private theorem starts_nodup_of_valid {ranges : List (Range α)}
    (positive : ∀ range ∈ ranges, 0 < range.length)
    (ordered : Nonoverlapping ranges) :
    (ranges.map Range.start).Nodup := by
  induction ranges with
  | nil => simp
  | cons range rest ih =>
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨candidate, candidateMember, sameStart⟩ := List.mem_map.mp member
        have separated : range.stop ≤ candidate.start := by
          rw [Nonoverlapping, List.pairwise_cons] at ordered
          exact ordered.1 candidate candidateMember
        have grows := Range.start_lt_stop (positive range (by simp))
        omega
      · exact ih
          (fun candidate member => positive candidate (by simp [member]))
          ordered.tail

/-- Nonoverlap makes source starts unique; a separate `Nodup` invariant is unnecessary. -/
theorem starts_nodup (ranges : RangeMap α) :
    (ranges.ranges.map Range.start).Nodup :=
  starts_nodup_of_valid ranges.valid.1 ranges.valid.2

/-! ## Lookup -/

/-- Complete information returned by a range lookup. -/
structure Hit (α : Type u) where
  target : α
  sourceIndex : Int
  localOffset : Nat
  deriving Repr, DecidableEq

namespace Hit

@[ext]
theorem ext {left right : Hit α}
    (target : left.target = right.target)
    (sourceIndex : left.sourceIndex = right.sourceIndex)
    (localOffset : left.localOffset = right.localOffset) : left = right := by
  cases left
  cases right
  simp_all

def map (f : α → β) (hit : Hit α) : Hit β where
  target := f hit.target
  sourceIndex := hit.sourceIndex
  localOffset := hit.localOffset

end Hit

def Range.hit (range : Range α) (index : Int) : Hit α where
  target := range.target
  sourceIndex := range.sourceIndex index
  localOffset := range.localOffset index

private def lookupRanges? : List (Range α) → Int → Option (Hit α)
  | [], _ => none
  | range :: rest, index =>
      if range.Contains index then some (range.hit index) else lookupRanges? rest index

/-- Look up an integer source coordinate. -/
def lookup? (ranges : RangeMap α) (index : Int) : Option (Hit α) :=
  lookupRanges? ranges.ranges index

/-- Natural-domain specialization of lookup. -/
def lookupNat? (ranges : RangeMap α) (index : Nat) : Option (Hit α) :=
  ranges.lookup? (Int.ofNat index)

/-- Relational lookup specification. -/
def MapsTo (ranges : RangeMap α) (index : Int) (hit : Hit α) : Prop :=
  ∃ range ∈ ranges.ranges, range.Contains index ∧ hit = range.hit index

/-- Whether some row covers an index. -/
def Contains (ranges : RangeMap α) (index : Int) : Prop :=
  ∃ hit, ranges.MapsTo index hit

private theorem lookupRanges?_some_exists
    {raw : List (Range α)} {index : Int} {hit : Hit α}
    (found : lookupRanges? raw index = some hit) :
    ∃ range ∈ raw, range.Contains index ∧ hit = range.hit index := by
  induction raw with
  | nil => cases found
  | cons range rest ih =>
      by_cases contains : range.Contains index
      · have equality : range.hit index = hit := Option.some.inj (by
          simpa only [lookupRanges?, contains, if_true] using found)
        exact ⟨range, List.mem_cons_self, contains, equality.symm⟩
      · have tailFound : lookupRanges? rest index = some hit := by
          simpa only [lookupRanges?, contains, if_false] using found
        obtain ⟨witness, member, covered, equality⟩ := ih tailFound
        exact ⟨witness, List.mem_cons_of_mem range member, covered, equality⟩

private theorem lookupRanges?_of_mem
    {raw : List (Range α)} (valid : Valid raw)
    {range : Range α} (member : range ∈ raw)
    {index : Int} (contains : range.Contains index) :
    lookupRanges? raw index = some (range.hit index) := by
  induction raw with
  | nil => simp at member
  | cons head tail ih =>
      rcases valid with ⟨positive, ordered⟩
      rcases List.mem_cons.mp member with equality | tailMember
      · subst range
        simp [lookupRanges?, contains]
      · have before := ordered.rel_head_tail tailMember
        have headDoesNotContain : ¬head.Contains index := by
          intro headContains
          exact (not_lt_of_ge (before.trans contains.1)) headContains.2
        simp only [lookupRanges?, headDoesNotContain, ↓reduceIte]
        exact ih
          ⟨fun candidate candidateMember => positive candidate (by simp [candidateMember]),
            ordered.tail⟩
          tailMember

@[simp] theorem lookup?_eq_some_iff
    {ranges : RangeMap α} {index : Int} {hit : Hit α} :
    ranges.lookup? index = some hit ↔ ranges.MapsTo index hit := by
  constructor
  · exact lookupRanges?_some_exists
  · rintro ⟨range, member, contains, rfl⟩
    exact lookupRanges?_of_mem ranges.valid member contains

theorem mapsTo_unique {ranges : RangeMap α} {index : Int} {left right : Hit α}
    (leftMaps : ranges.MapsTo index left) (rightMaps : ranges.MapsTo index right) :
    left = right := by
  apply Option.some.inj
  rw [← lookup?_eq_some_iff.mpr leftMaps, ← lookup?_eq_some_iff.mpr rightMaps]

@[simp] theorem contains_iff_lookup_isSome {ranges : RangeMap α} {index : Int} :
    ranges.Contains index ↔ (ranges.lookup? index).isSome := by
  simp only [Contains, Option.isSome_iff_exists, lookup?_eq_some_iff]

@[simp] theorem contains_iff_exists_range {ranges : RangeMap α} {index : Int} :
    ranges.Contains index ↔ ∃ range ∈ ranges.ranges, range.Contains index := by
  constructor
  · rintro ⟨hit, range, member, contains, _⟩
    exact ⟨range, member, contains⟩
  · rintro ⟨range, member, contains⟩
    exact ⟨range.hit index, range, member, contains, rfl⟩

@[simp] theorem lookup?_start_add
    {ranges : RangeMap α} {range : Range α} (member : range ∈ ranges.ranges)
    {localOffset : Nat} (within : localOffset < range.length) :
    ranges.lookup? (range.start + Int.ofNat localOffset) = some {
      target := range.target
      sourceIndex := range.offset + Int.ofNat localOffset
      localOffset := localOffset
    } := by
  rw [lookup?_eq_some_iff]
  refine ⟨range, member, ?_, ?_⟩
  · simp [Range.Contains, Range.stop, within]
  · apply Hit.ext <;> simp [Range.hit, Range.sourceIndex, Range.localOffset]

private theorem lookupRanges?_map
    (f : α → β) (raw : List (Range α)) (index : Int) :
    lookupRanges? (raw.map (Range.mapTarget f)) index =
      (lookupRanges? raw index).map (Hit.map f) := by
  induction raw with
  | nil => rfl
  | cons range rest ih =>
      by_cases contains : range.Contains index <;>
        simp [lookupRanges?, contains, ih, Range.hit, Hit.map]

@[simp] theorem lookup?_map (f : α → β) (ranges : RangeMap α) (index : Int) :
    (map f ranges).lookup? index = (ranges.lookup? index).map (Hit.map f) := by
  exact lookupRanges?_map f ranges.ranges index

/-! ## Offset maps and duplicate outputs -/

/-- A partial function presented by lookup. -/
structure OffsetMap (ι : Type u) (α : Type v) where
  lookup? : ι → Option α

namespace OffsetMap

/-- Successful outputs uniquely determine their inputs. -/
def NoDuplicates (map : OffsetMap ι α) : Prop :=
  ∀ ⦃left right value⦄,
    map.lookup? left = some value → map.lookup? right = some value → left = right

/-- Restrict an integer-domain map to natural inputs. -/
def natDomain (map : OffsetMap Int α) : OffsetMap Nat α where
  lookup? index := map.lookup? (Int.ofNat index)

theorem NoDuplicates.natDomain {map : OffsetMap Int α}
    (noDuplicates : map.NoDuplicates) : map.natDomain.NoDuplicates := by
  intro left right value leftFound rightFound
  exact Int.ofNat.inj (noDuplicates leftFound rightFound)

end OffsetMap

/-- Project the payload and translated target coordinate of every hit. -/
def toOffsetMap (ranges : RangeMap α) (project : α → Int → β) : OffsetMap Int β where
  lookup? index :=
    (ranges.lookup? index).map fun hit => project hit.target hit.sourceIndex

/-- The direct `(payload, translated-coordinate)` offset map. -/
def entryOffsetMap (ranges : RangeMap α) : OffsetMap Int (α × Int) :=
  ranges.toOffsetMap fun target sourceIndex => (target, sourceIndex)

/-- Keep only the translated coordinate. -/
def sourceOffsetMap (ranges : RangeMap α) : OffsetMap Int Int :=
  ranges.toOffsetMap fun _ sourceIndex => sourceIndex

/-- Range-level characterization of an offset projection's injectivity. -/
def TargetsInjectively (ranges : RangeMap α) (project : α → Int → β) : Prop :=
  ∀ ⦃left right : Range α⦄,
    left ∈ ranges.ranges → right ∈ ranges.ranges →
    ∀ ⦃leftLocal rightLocal : Nat⦄,
      leftLocal < left.length → rightLocal < right.length →
      project left.target (left.offset + Int.ofNat leftLocal) =
        project right.target (right.offset + Int.ofNat rightLocal) →
      left.start + Int.ofNat leftLocal = right.start + Int.ofNat rightLocal

theorem noDuplicates_toOffsetMap_iff
    {ranges : RangeMap α} {project : α → Int → β} :
    (ranges.toOffsetMap project).NoDuplicates ↔ ranges.TargetsInjectively project := by
  constructor
  · intro noDuplicates left right leftMember rightMember leftLocal rightLocal
      leftWithin rightWithin sameTarget
    exact noDuplicates
      (value := project left.target (left.offset + Int.ofNat leftLocal))
      (by
        change (ranges.lookup? (left.start + Int.ofNat leftLocal)).map _ = some _
        rw [lookup?_start_add leftMember leftWithin]
        rfl)
      (by
        change (ranges.lookup? (right.start + Int.ofNat rightLocal)).map _ = some _
        rw [lookup?_start_add rightMember rightWithin]
        simp only [Option.map_some, Option.some.injEq]
        exact sameTarget.symm)
  · intro targets leftIndex rightIndex value leftFound rightFound
    simp only [toOffsetMap, Option.map_eq_some_iff] at leftFound rightFound
    obtain ⟨leftHit, leftLookup, leftValue⟩ := leftFound
    obtain ⟨rightHit, rightLookup, rightValue⟩ := rightFound
    rw [lookup?_eq_some_iff] at leftLookup rightLookup
    obtain ⟨left, leftMember, leftContains, rfl⟩ := leftLookup
    obtain ⟨right, rightMember, rightContains, rfl⟩ := rightLookup
    have projected :
        project left.target (left.sourceIndex leftIndex) =
          project right.target (right.sourceIndex rightIndex) := by
      change project left.target (left.sourceIndex leftIndex) = value at leftValue
      change project right.target (right.sourceIndex rightIndex) = value at rightValue
      exact leftValue.trans rightValue.symm
    have sourceEquality := targets leftMember rightMember
      (Range.localOffset_lt leftContains) (Range.localOffset_lt rightContains)
      (by simpa [Range.sourceIndex] using projected)
    simpa only [Range.start_add_localOffset leftContains,
      Range.start_add_localOffset rightContains] using sourceEquality

/-! ## A small interface for range-map-like values -/

/-- A value with a distinguished canonical range-map representation. -/
class RangeMapLike (M : Type u) (α : outParam (Type v)) where
  toRangeMap : M → RangeMap α

def RangeMapLike.asRangeMap [RangeMapLike M α] (value : M) : RangeMap α :=
  RangeMapLike.toRangeMap value

instance : RangeMapLike (RangeMap α) α where
  toRangeMap := id

/-- A single positive-length segment. -/
structure Single (α : Type u) where
  start : Int
  length : Nat
  offset : Int
  target : α
  positive : 0 < length

namespace Single

def toRangeMap (single : Single α) : RangeMap α :=
  singleton single.start single.length single.offset single.target single.positive

instance : RangeMapLike (Single α) α where
  toRangeMap := toRangeMap

end Single

end RangeMap

end Nucleus
