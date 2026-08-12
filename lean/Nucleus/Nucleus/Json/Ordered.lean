import Nucleus.Json.Extensional

/-!
# Well-formed and ordered raw JSON

Two structural predicates on the raw syntax and the resulting canonical form:

- `RawSyn.WellFormed`: every object has duplicate-free keys.  This is exactly
  the class of raw trees that denote an extensional `Json` value without a
  duplicate-key policy; `RawJson.toJson` performs that conversion.
- `RawSyn.SortedKeys`: every object is in strictly increasing key order.
  This implies `WellFormed` and pins down a unique raw representative for each
  extensional value.

`OrderedJson` packages a raw tree with a `SortedKeys` proof.  Issue #541
considered two other formulations of sorted duplicate-free syntax; see
`Nucleus.Json.Alternatives` for the comparison and why this one is used.

Being propositions, both predicates add no data: `OrderedJson` equality is
equality of the underlying raw trees (`Subtype.ext`), and conversions carry
proofs by proof irrelevance.  Both predicates and all conversions recurse
structurally over the indexed raw syntax.
-/

namespace Nucleus

universe u

variable {Key : Type} {Scalar : Type u} [LinearOrder Key]

namespace RawSyn

/-- Every object in the tree has duplicate-free keys.  Such a tree denotes an
extensional `Json` value directly (`RawJson.toJson`); trees with duplicates
must first go through an explicit duplicate-key policy (`RawJson.validate`
rejects them). -/
def WellFormed : ∀ {i : JsonIx}, RawSyn Key Scalar i → Prop
  | _, .scalar _ => True
  | _, .list elems => elems.WellFormed
  | _, .map entries => entries.keys.Nodup ∧ entries.WellFormed
  | _, .nil => True
  | _, .cons head tail => head.WellFormed ∧ tail.WellFormed
  | _, .objNil => True
  | _, .objCons _ value tail => value.WellFormed ∧ tail.WellFormed

/-- Every object in the tree lists its members in strictly increasing key
order.  This is the canonical-representative invariant of `OrderedJson`. -/
def SortedKeys : ∀ {i : JsonIx}, RawSyn Key Scalar i → Prop
  | _, .scalar _ => True
  | _, .list elems => elems.SortedKeys
  | _, .map entries => entries.keys.Pairwise (· < ·) ∧ entries.SortedKeys
  | _, .nil => True
  | _, .cons head tail => head.SortedKeys ∧ tail.SortedKeys
  | _, .objNil => True
  | _, .objCons _ value tail => value.SortedKeys ∧ tail.SortedKeys

omit [LinearOrder Key] in
@[simp] theorem wellFormed_scalar (value : Scalar) :
    (RawSyn.scalar (Key := Key) value).WellFormed := trivial

omit [LinearOrder Key] in
@[simp] theorem wellFormed_list_iff (elems : RawSyn Key Scalar .arr) :
    (RawSyn.list elems).WellFormed ↔ elems.WellFormed := Iff.rfl

omit [LinearOrder Key] in
@[simp] theorem wellFormed_map_iff (entries : RawSyn Key Scalar .obj) :
    (RawSyn.map entries).WellFormed ↔ entries.keys.Nodup ∧ entries.WellFormed := Iff.rfl

omit [LinearOrder Key] in
@[simp] theorem wellFormed_nil : (RawSyn.nil : RawSyn Key Scalar .arr).WellFormed := trivial

omit [LinearOrder Key] in
@[simp] theorem wellFormed_cons_iff (head : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .arr) :
    (RawSyn.cons head tail).WellFormed ↔ head.WellFormed ∧ tail.WellFormed := Iff.rfl

omit [LinearOrder Key] in
@[simp] theorem wellFormed_objNil : (RawSyn.objNil : RawSyn Key Scalar .obj).WellFormed := trivial

omit [LinearOrder Key] in
@[simp] theorem wellFormed_objCons_iff (key : Key) (value : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).WellFormed
      ↔ value.WellFormed ∧ tail.WellFormed := Iff.rfl

@[simp] theorem sortedKeys_scalar (value : Scalar) :
    (RawSyn.scalar (Key := Key) value).SortedKeys := trivial

@[simp] theorem sortedKeys_list_iff (elems : RawSyn Key Scalar .arr) :
    (RawSyn.list elems).SortedKeys ↔ elems.SortedKeys := Iff.rfl

@[simp] theorem sortedKeys_map_iff (entries : RawSyn Key Scalar .obj) :
    (RawSyn.map entries).SortedKeys
      ↔ entries.keys.Pairwise (· < ·) ∧ entries.SortedKeys := Iff.rfl

@[simp] theorem sortedKeys_nil : (RawSyn.nil : RawSyn Key Scalar .arr).SortedKeys := trivial

@[simp] theorem sortedKeys_cons_iff (head : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .arr) :
    (RawSyn.cons head tail).SortedKeys ↔ head.SortedKeys ∧ tail.SortedKeys := Iff.rfl

@[simp] theorem sortedKeys_objNil : (RawSyn.objNil : RawSyn Key Scalar .obj).SortedKeys := trivial

@[simp] theorem sortedKeys_objCons_iff (key : Key) (value : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).SortedKeys
      ↔ value.SortedKeys ∧ tail.SortedKeys := Iff.rfl

omit [LinearOrder Key] in
/-- An array tail is well-formed exactly when all its elements are. -/
theorem wellFormed_arr_iff : ∀ (a : RawSyn Key Scalar .arr),
    a.WellFormed ↔ ∀ e ∈ a.toList, e.WellFormed
  | .nil => by simp
  | .cons head tail => by simp [wellFormed_arr_iff tail]

omit [LinearOrder Key] in
/-- An object tail is well-formed exactly when all its entry values are. -/
theorem wellFormed_obj_iff : ∀ (o : RawSyn Key Scalar .obj),
    o.WellFormed ↔ ∀ e ∈ o.toEntries, e.2.WellFormed
  | .objNil => by simp
  | .objCons key value tail => by simp [wellFormed_obj_iff tail]

/-- An array tail is sorted exactly when all its elements are. -/
theorem sortedKeys_arr_iff : ∀ (a : RawSyn Key Scalar .arr),
    a.SortedKeys ↔ ∀ e ∈ a.toList, e.SortedKeys
  | .nil => by simp
  | .cons head tail => by simp [sortedKeys_arr_iff tail]

/-- An object tail is sorted exactly when all its entry values are. -/
theorem sortedKeys_obj_iff : ∀ (o : RawSyn Key Scalar .obj),
    o.SortedKeys ↔ ∀ e ∈ o.toEntries, e.2.SortedKeys
  | .objNil => by simp
  | .objCons key value tail => by simp [sortedKeys_obj_iff tail]

/-- Strictly increasing keys are in particular duplicate-free. -/
theorem SortedKeys.wellFormed {i : JsonIx} {r : RawSyn Key Scalar i}
    (h : r.SortedKeys) : r.WellFormed := by
  induction r with
  | scalar value => trivial
  | list elems ih => exact ih h
  | map entries ih => exact ⟨h.1.nodup, ih h.2⟩
  | nil => trivial
  | cons head tail ih ih' => exact ⟨ih h.1, ih' h.2⟩
  | objNil => trivial
  | objCons key value tail ih ih' => exact ⟨ih h.1, ih' h.2⟩

/-- Mapping over scalars preserves the ordering invariant: object keys are
untouched. -/
theorem SortedKeys.mapScalar {T : Type u} (f : Scalar → T) {i : JsonIx}
    {r : RawSyn Key Scalar i} (h : r.SortedKeys) : (r.mapScalar f).SortedKeys := by
  induction r with
  | scalar value => trivial
  | list elems ih => exact ih h
  | map entries ih =>
      refine ⟨?_, ih h.2⟩
      rw [keys_mapScalar]
      exact h.1
  | nil => trivial
  | cons head tail ih ih' => exact ⟨ih h.1, ih' h.2⟩
  | objNil => trivial
  | objCons key value tail ih ih' => exact ⟨ih h.1, ih' h.2⟩

/-! ## Conversion to the extensional form

The three functions below recurse structurally; `toJsonObj` carries the proof
that conversion preserves the key list, which discharges the duplicate-free
side condition of `Json.ofEntries` at `map` nodes. -/

mutual

/-- Convert a well-formed raw value to its extensional form.  Object values
are recovered by key lookup, which is unambiguous because keys are
duplicate-free. -/
def toJson : (r : KeyedRawJson Key Scalar) → r.WellFormed → Json Scalar Key
  | .scalar v, _ => .scalar v
  | .list elems, h =>
      .list (toJsonArr elems ((wellFormed_list_iff elems).mp h)).length
        (toJsonArr elems ((wellFormed_list_iff elems).mp h)).get
  | .map entries, h =>
      Json.ofEntries (toJsonObj entries ((wellFormed_map_iff entries).mp h).2).1 (by
        rw [(toJsonObj entries ((wellFormed_map_iff entries).mp h).2).2,
          ← keys_eq_toEntries_fst]
        exact ((wellFormed_map_iff entries).mp h).1)

/-- Convert the elements of a well-formed array tail. -/
def toJsonArr : (a : RawSyn Key Scalar .arr) → a.WellFormed → List (Json Scalar Key)
  | .nil, _ => []
  | .cons head tail, h => toJson head h.1 :: toJsonArr tail h.2

/-- Convert the entries of a well-formed object tail, keeping the fact that
keys are preserved. -/
def toJsonObj : (o : RawSyn Key Scalar .obj) → o.WellFormed →
    {l : List (Key × Json Scalar Key) // l.map Prod.fst = o.toEntries.map Prod.fst}
  | .objNil, _ => ⟨[], by simp⟩
  | .objCons key value tail, h =>
      ⟨(key, toJson value h.1) :: (toJsonObj tail h.2).1, by
        simp [(toJsonObj tail h.2).2]⟩

end

/-- The converted array elements are the converted elements of the list view;
membership proofs transport along `wellFormed_arr_iff`. -/
theorem toJsonArr_eq : ∀ (a : RawSyn Key Scalar .arr) (h : a.WellFormed),
    toJsonArr a h = a.toList.pmap (fun e he => e.toJson he)
      (fun e he => (wellFormed_arr_iff a).mp h e he)
  | .nil, _ => by simp [toJsonArr]
  | .cons head tail, h => by
      simp only [toJsonArr, toList_cons, List.pmap_cons]
      exact congrArg _ (toJsonArr_eq tail h.2)

/-- The converted object entries are the converted entries of the list view. -/
theorem toJsonObj_eq : ∀ (o : RawSyn Key Scalar .obj) (h : o.WellFormed),
    (toJsonObj o h).1 = o.toEntries.pmap (fun e he => (e.1, e.2.toJson he))
      (fun e he => (wellFormed_obj_iff o).mp h e he)
  | .objNil, _ => by simp [toJsonObj]
  | .objCons key value tail, h => by
      simp only [toJsonObj, toEntries_objCons, List.pmap_cons]
      exact congrArg _ (toJsonObj_eq tail h.2)

end RawSyn

/-- The canonical raw representative is sorted: `Json.toRaw` emits every
object in strictly increasing key order. -/
theorem Json.toRaw_sortedKeys (j : Json Scalar Key) : j.toRaw.SortedKeys := by
  induction j with
  | scalar v => trivial
  | list n elems ih =>
      rw [Json.toRaw_list, RawSyn.sortedKeys_list_iff, RawSyn.sortedKeys_arr_iff]
      intro e he
      rw [RawSyn.toList_ofList] at he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact ih i
  | map keys vals ih =>
      rw [Json.toRaw_map, RawSyn.sortedKeys_map_iff]
      constructor
      · rw [RawSyn.keys_eq_toEntries_fst, RawSyn.toEntries_ofEntries]
        have hkeys : (((keys.sort (· ≤ ·)).attach.map fun k =>
            (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw)).map Prod.fst)
            = keys.sort (· ≤ ·) := by
          simp [List.map_map, Function.comp_def]
        rw [hkeys]
        exact (Finset.sortedLT_sort keys).pairwise
      · rw [RawSyn.sortedKeys_obj_iff]
        intro e he
        rw [RawSyn.toEntries_ofEntries] at he
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
        exact ih _

/-- Sorted duplicate-free JSON syntax: a raw tree together with a proof that
every object lists its members in strictly increasing key order.  This is the
canonical *data representative* of an extensional `Json` value
(`Nucleus.jsonEquivOrdered`); it does not impose a canonical byte encoding or
content hash. -/
def OrderedJson (Scalar : Type u) (Key : Type := String) [LinearOrder Key] : Type u :=
  {r : KeyedRawJson Key Scalar // r.SortedKeys}

abbrev KeyedOrderedJson (Key : Type) (Scalar : Type u) [LinearOrder Key] :=
  OrderedJson Scalar Key

namespace OrderedJson

/-- The underlying raw syntax tree.  Injective: an `OrderedJson` is determined
by its raw tree, the invariant being propositional. -/
def toRaw (o : OrderedJson Scalar Key) : KeyedRawJson Key Scalar := o.1

theorem toRaw_injective : Function.Injective (toRaw (Key := Key) (Scalar := Scalar)) :=
  Subtype.coe_injective

/-- The extensional value an ordered tree represents. -/
def toJson (o : OrderedJson Scalar Key) : Json Scalar Key := o.1.toJson o.2.wellFormed

/-- Apply `f` to every scalar leaf. -/
def mapScalar {T : Type u} (f : Scalar → T) (o : OrderedJson Scalar Key) : OrderedJson T Key :=
  ⟨o.1.mapScalar f, o.2.mapScalar f⟩

end OrderedJson

/-- The canonical ordered representative of an extensional value, packaged
with its ordering invariant. -/
def Json.toOrdered (j : Json Scalar Key) : OrderedJson Scalar Key :=
  ⟨j.toRaw, j.toRaw_sortedKeys⟩

end Nucleus
