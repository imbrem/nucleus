import Nucleus.Json.Extensional

/-!
# Well-formed and ordered raw JSON

Two nested predicates on `RawJson` and the resulting canonical syntax:

- `RawJson.WellFormed`: every object has duplicate-free keys.  This is exactly
  the class of raw trees that denote an extensional `Json` value without a
  duplicate-key policy; `RawJson.toJson` performs that conversion.
- `RawJson.SortedKeys`: every object is in strictly increasing key order.
  This implies `WellFormed` and pins down a unique raw representative for each
  extensional value.

`OrderedJson` packages a raw tree with a `SortedKeys` proof.  Issue #541
considered two other formulations of sorted duplicate-free syntax; see
`Nucleus.Json.Alternatives` for the comparison and why this one is used.

Being propositions, both predicates add no data: `OrderedJson` equality is
equality of the underlying raw trees (`Subtype.ext`), and conversions carry
proofs by proof irrelevance.
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

namespace RawJson

/-- Every object in the tree has duplicate-free keys.  Such a tree denotes an
extensional `Json` value directly (`RawJson.toJson`); trees with duplicates
must first go through an explicit duplicate-key policy (`RawJson.validate`
rejects them). -/
inductive WellFormed : RawJson Scalar → Prop
  /-- Scalars are well-formed. -/
  | scalar (value : Scalar) : WellFormed (.scalar value)
  /-- A list is well-formed when all elements are. -/
  | list {elems : List (RawJson Scalar)} :
      (∀ e ∈ elems, WellFormed e) → WellFormed (.list elems)
  /-- A map is well-formed when its keys are duplicate-free and all values
  are well-formed. -/
  | map {entries : List (String × RawJson Scalar)} :
      (entries.map Prod.fst).Nodup →
      (∀ e ∈ entries, WellFormed e.2) → WellFormed (.map entries)

/-- Elements of a well-formed list are well-formed. -/
theorem WellFormed.list_elem {elems : List (RawJson Scalar)}
    (h : WellFormed (.list elems)) : ∀ e ∈ elems, WellFormed e := by
  cases h with | list h => exact h

/-- A well-formed map has duplicate-free keys. -/
theorem WellFormed.map_nodup {entries : List (String × RawJson Scalar)}
    (h : WellFormed (.map entries)) : (entries.map Prod.fst).Nodup := by
  cases h with | map hnd _ => exact hnd

/-- Values of a well-formed map are well-formed. -/
theorem WellFormed.map_elem {entries : List (String × RawJson Scalar)}
    (h : WellFormed (.map entries)) : ∀ e ∈ entries, WellFormed e.2 := by
  cases h with | map _ h => exact h

/-- Every object in the tree lists its members in strictly increasing key
order.  This is the canonical-representative invariant of `OrderedJson`. -/
inductive SortedKeys : RawJson Scalar → Prop
  /-- Scalars are trivially ordered. -/
  | scalar (value : Scalar) : SortedKeys (.scalar value)
  /-- A list is ordered when all elements are. -/
  | list {elems : List (RawJson Scalar)} :
      (∀ e ∈ elems, SortedKeys e) → SortedKeys (.list elems)
  /-- A map is ordered when its keys are strictly increasing and all values
  are ordered. -/
  | map {entries : List (String × RawJson Scalar)} :
      (entries.map Prod.fst).Pairwise (· < ·) →
      (∀ e ∈ entries, SortedKeys e.2) → SortedKeys (.map entries)

/-- Elements of an ordered list are ordered. -/
theorem SortedKeys.list_elem {elems : List (RawJson Scalar)}
    (h : SortedKeys (.list elems)) : ∀ e ∈ elems, SortedKeys e := by
  cases h with | list h => exact h

/-- An ordered map has strictly increasing keys. -/
theorem SortedKeys.map_pairwise {entries : List (String × RawJson Scalar)}
    (h : SortedKeys (.map entries)) : (entries.map Prod.fst).Pairwise (· < ·) := by
  cases h with | map hp _ => exact hp

/-- Values of an ordered map are ordered. -/
theorem SortedKeys.map_elem {entries : List (String × RawJson Scalar)}
    (h : SortedKeys (.map entries)) : ∀ e ∈ entries, SortedKeys e.2 := by
  cases h with | map _ h => exact h

/-- Strictly increasing keys are in particular duplicate-free. -/
theorem SortedKeys.wellFormed : ∀ {r : RawJson Scalar}, r.SortedKeys → r.WellFormed
  | .scalar _, _ => .scalar _
  | .list _, .list h => .list fun e he => (h e he).wellFormed
  | .map _, .map hp h => .map hp.nodup fun e he => (h e he).wellFormed
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- Convert a well-formed raw tree to its extensional value.  Object values
are recovered by key lookup, which is unambiguous because keys are
duplicate-free. -/
def toJson : (r : RawJson Scalar) → r.WellFormed → Json Scalar
  | .scalar v, _ => .scalar v
  | .list elems, h =>
      .list elems.length fun i => (elems.get i).toJson (h.list_elem _ (elems.get_mem i))
  | .map entries, h =>
      .map ⟨(entries.map Prod.fst : List String), h.map_nodup⟩ fun k =>
        have hfind : (entries.find? fun e => e.1 = k.1).isSome := by
          rw [List.find?_isSome]
          obtain ⟨e, he, hk⟩ := List.mem_map.mp (Multiset.mem_coe.mp k.2)
          exact ⟨e, he, by simp [hk]⟩
        have hmem : (entries.find? fun e => e.1 = k.1).get hfind ∈ entries :=
          List.get_find?_mem hfind
        ((entries.find? fun e => e.1 = k.1).get hfind).2.toJson (h.map_elem _ hmem)
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list (elems.get_mem _)
  · exact sizeOf_mem_map hmem

/-- Mapping over scalars preserves the ordering invariant: object keys are
untouched. -/
theorem SortedKeys.mapScalar {T : Type u} (f : Scalar → T) {r : RawJson Scalar}
    (h : r.SortedKeys) : (r.mapScalar f).SortedKeys := by
  induction h with
  | scalar v =>
      rw [RawJson.mapScalar_scalar]
      exact .scalar _
  | list _ ih =>
      rw [RawJson.mapScalar_list]
      exact .list fun e he => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact ih e' he'
  | map hp _ ih =>
      rw [RawJson.mapScalar_map]
      refine .map ?_ fun e he => ?_
      · simpa [List.map_map, Function.comp_def] using hp
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact ih e' he'

end RawJson

/-- The canonical raw representative is sorted: `Json.toRaw` emits every
object in strictly increasing key order. -/
theorem Json.toRaw_sortedKeys (j : Json Scalar) : j.toRaw.SortedKeys := by
  induction j with
  | scalar v => exact .scalar v
  | list n elems ih =>
      rw [Json.toRaw_list]
      refine .list fun e he => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact ih i
  | map keys vals ih =>
      rw [Json.toRaw_map]
      refine .map ?_ fun e he => ?_
      · have hkeys : (((keys.sort (· ≤ ·)).attach.map fun k =>
            (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw)).map Prod.fst)
            = keys.sort (· ≤ ·) := by
          simp [List.map_map, Function.comp_def]
        rw [hkeys]
        exact (Finset.sortedLT_sort keys).pairwise
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
        exact ih _

/-- Sorted duplicate-free JSON syntax: a raw tree together with a proof that
every object lists its members in strictly increasing key order.  This is the
canonical *data representative* of an extensional `Json` value
(`Nucleus.jsonEquivOrdered`); it does not impose a canonical byte encoding or
content hash. -/
def OrderedJson (Scalar : Type u) : Type u := {r : RawJson Scalar // r.SortedKeys}

namespace OrderedJson

/-- The underlying raw syntax tree.  Injective: an `OrderedJson` is determined
by its raw tree, the invariant being propositional. -/
def toRaw (o : OrderedJson Scalar) : RawJson Scalar := o.1

theorem toRaw_injective : Function.Injective (toRaw (Scalar := Scalar)) :=
  Subtype.coe_injective

/-- The extensional value an ordered tree represents. -/
def toJson (o : OrderedJson Scalar) : Json Scalar := o.1.toJson o.2.wellFormed

/-- Apply `f` to every scalar leaf. -/
def mapScalar {T : Type u} (f : Scalar → T) (o : OrderedJson Scalar) : OrderedJson T :=
  ⟨o.1.mapScalar f, o.2.mapScalar f⟩

end OrderedJson

/-- The canonical ordered representative of an extensional value, packaged
with its ordering invariant. -/
def Json.toOrdered (j : Json Scalar) : OrderedJson Scalar :=
  ⟨j.toRaw, j.toRaw_sortedKeys⟩

end Nucleus
