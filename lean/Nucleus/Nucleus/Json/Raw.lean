import Mathlib.Data.List.Basic

/-!
# Raw scalar-parametric JSON syntax

`RawJson` is the raw, RFC-8259-shaped JSON syntax layer, parametric over the type of
scalar values.  It records exactly what a JSON text says: object members are kept as an
ordered list of key–value entries, preserving both member order and duplicate keys.

Consequently, equality of `RawJson` values observes member order and duplicates: two
trees whose objects list the same members in a different order, or with different
duplicate structure, are distinct terms.  Profile validation — in particular, deciding
how duplicate keys are handled — happens explicitly when converting to the extensional
form (see the `Nucleus.Json` docs); nothing here collapses or reorders members.
-/

namespace Nucleus

universe u

/-- Raw JSON tree, parametric over the scalar type.  Objects are ordered lists of
key–value entries; duplicate keys are preserved, and equality observes both order and
duplicates.  Duplicate-key policy is applied only when converting to the extensional
form. -/
inductive RawJson (Scalar : Type u) : Type u where
  | scalar (value : Scalar)
  | list (elems : List (RawJson Scalar))
  | map (entries : List (String × RawJson Scalar))

/-- One step of a JSON path: a list index or an object key. -/
inductive JsonStep where
  | index (i : Nat)
  | key (k : String)
  deriving DecidableEq, Repr

/-- A path into a JSON tree. -/
abbrev JsonPath := List JsonStep

namespace RawJson

variable {Scalar : Type u}

/-- A list element is smaller than the `RawJson.list` node containing it; this powers
the termination proofs for recursion over `RawJson`. -/
theorem sizeOf_mem_list {elems : List (RawJson Scalar)} {e : RawJson Scalar}
    (h : e ∈ elems) : sizeOf e < sizeOf (RawJson.list elems) := by
  have := List.sizeOf_lt_of_mem h
  simp only [RawJson.list.sizeOf_spec]
  omega

/-- An entry's value is smaller than the `RawJson.map` node containing it; this powers
the termination proofs for recursion over `RawJson`. -/
theorem sizeOf_mem_map {entries : List (String × RawJson Scalar)}
    {e : String × RawJson Scalar} (h : e ∈ entries) :
    sizeOf e.2 < sizeOf (RawJson.map entries) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨k, v⟩ := e
  simp only [RawJson.map.sizeOf_spec, Prod.mk.sizeOf_spec] at *
  omega

/-- Total node count of a raw JSON tree. -/
def size : RawJson Scalar → Nat
  | .scalar _ => 1
  | .list elems => 1 + (elems.map fun e => e.size).sum
  | .map entries => 1 + (entries.map fun e => e.2.size).sum
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- Nesting depth of a raw JSON tree: scalars have depth `0`, and containers have one
more than the maximum depth of their children (`0` for an empty container). -/
def depth : RawJson Scalar → Nat
  | .scalar _ => 0
  | .list elems => 1 + (elems.map fun e => e.depth).foldr max 0
  | .map entries => 1 + (entries.map fun e => e.2.depth).foldr max 0
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- Pre-order list of the scalar leaves of a raw JSON tree, preserving order and
duplicates. -/
def scalars : RawJson Scalar → List Scalar
  | .scalar value => [value]
  | .list elems => (elems.map fun e => e.scalars).flatten
  | .map entries => (entries.map fun e => e.2.scalars).flatten
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- Apply `f` to every scalar leaf, preserving structure, member order, and duplicate
keys. -/
def mapScalar {T : Type u} (f : Scalar → T) : RawJson Scalar → RawJson T
  | .scalar value => .scalar (f value)
  | .list elems => .list (elems.map fun e => e.mapScalar f)
  | .map entries => .map (entries.map fun e => (e.1, e.2.mapScalar f))
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- Fold `f` over the scalar leaves of a raw JSON tree in pre-order. -/
def foldScalars {B : Type*} (f : B → Scalar → B) (init : B) (r : RawJson Scalar) : B :=
  r.scalars.foldl f init

/-- Look up a node by path.  The empty path returns the node itself; `.index i` indexes
into a `.list`, and `.key k` selects the FIRST entry with key `k` in a `.map`.
First-match lookup on duplicate keys is a lookup convention only — it does not collapse
duplicates semantically.  Any mismatch (index on a non-list, key on a non-map, index out
of range, or missing key) yields `none`. -/
def get? : RawJson Scalar → JsonPath → Option (RawJson Scalar)
  | r, [] => some r
  | .list elems, .index i :: rest =>
    match elems[i]? with
    | some e => e.get? rest
    | none => none
  | .map entries, .key k :: rest =>
    match entries.find? fun e => e.1 = k with
    | some e => e.2.get? rest
    | none => none
  | _, _ => none

/-- Induction principle for `RawJson` providing membership-indexed inductive hypotheses
for the children of `list` and `map` nodes. -/
@[induction_eliminator]
theorem inductionOn {motive : RawJson Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ entries, motive e.2) → motive (.map entries)) :
    ∀ r, motive r
  | .scalar value => scalar value
  | .list elems => list elems fun e _he => inductionOn scalar list map e
  | .map entries => map entries fun e _he => inductionOn scalar list map e.2
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_mem_list ‹_›
  · exact sizeOf_mem_map ‹_›

/-- `size` of a scalar leaf. -/
@[simp]
theorem size_scalar (value : Scalar) : (RawJson.scalar value).size = 1 := by
  rw [size]

/-- `size` of a list node. -/
@[simp]
theorem size_list (elems : List (RawJson Scalar)) :
    (RawJson.list elems).size = 1 + (elems.map fun e => e.size).sum := by
  rw [size]

/-- `size` of a map node. -/
@[simp]
theorem size_map (entries : List (String × RawJson Scalar)) :
    (RawJson.map entries).size = 1 + (entries.map fun e => e.2.size).sum := by
  rw [size]

/-- `depth` of a scalar leaf. -/
@[simp]
theorem depth_scalar (value : Scalar) : (RawJson.scalar value).depth = 0 := by
  rw [depth]

/-- `depth` of a list node. -/
@[simp]
theorem depth_list (elems : List (RawJson Scalar)) :
    (RawJson.list elems).depth = 1 + (elems.map fun e => e.depth).foldr max 0 := by
  rw [depth]

/-- `depth` of a map node. -/
@[simp]
theorem depth_map (entries : List (String × RawJson Scalar)) :
    (RawJson.map entries).depth = 1 + (entries.map fun e => e.2.depth).foldr max 0 := by
  rw [depth]

/-- `scalars` of a scalar leaf. -/
@[simp]
theorem scalars_scalar (value : Scalar) : (RawJson.scalar value).scalars = [value] := by
  rw [scalars]

/-- `scalars` of a list node. -/
@[simp]
theorem scalars_list (elems : List (RawJson Scalar)) :
    (RawJson.list elems).scalars = (elems.map fun e => e.scalars).flatten := by
  rw [scalars]

/-- `scalars` of a map node. -/
@[simp]
theorem scalars_map (entries : List (String × RawJson Scalar)) :
    (RawJson.map entries).scalars = (entries.map fun e => e.2.scalars).flatten := by
  rw [scalars]

/-- `mapScalar` on a scalar leaf. -/
@[simp]
theorem mapScalar_scalar {T : Type u} (f : Scalar → T) (value : Scalar) :
    (RawJson.scalar value).mapScalar f = .scalar (f value) := by
  rw [mapScalar]

/-- `mapScalar` on a list node. -/
@[simp]
theorem mapScalar_list {T : Type u} (f : Scalar → T) (elems : List (RawJson Scalar)) :
    (RawJson.list elems).mapScalar f = .list (elems.map fun e => e.mapScalar f) := by
  rw [mapScalar]

/-- `mapScalar` on a map node. -/
@[simp]
theorem mapScalar_map {T : Type u} (f : Scalar → T)
    (entries : List (String × RawJson Scalar)) :
    (RawJson.map entries).mapScalar f = .map (entries.map fun e => (e.1, e.2.mapScalar f)) := by
  rw [mapScalar]

/-- Mapping the identity over the scalar leaves is the identity. -/
@[simp]
theorem mapScalar_id (r : RawJson Scalar) : r.mapScalar id = r := by
  induction r with
  | scalar value => simp
  | list elems ih =>
    simp only [mapScalar_list]
    rw [List.map_congr_left ih, List.map_id']
  | map entries ih =>
    simp only [mapScalar_map]
    rw [List.map_congr_left fun e he => by rw [ih e he], List.map_id']

/-- Mapping over the scalar leaves composes. -/
theorem mapScalar_comp {T U : Type u} (f : Scalar → T) (g : T → U) (r : RawJson Scalar) :
    (r.mapScalar f).mapScalar g = r.mapScalar (g ∘ f) := by
  induction r with
  | scalar value => simp
  | list elems ih =>
    simp only [mapScalar_list, List.map_map]
    exact congrArg RawJson.list (List.map_congr_left fun e he => ih e he)
  | map entries ih =>
    simp only [mapScalar_map, List.map_map]
    exact congrArg RawJson.map (List.map_congr_left fun e he => by
      simp only [Function.comp_apply, ih e he])

/-- The scalar leaves of a mapped tree are the mapped scalar leaves. -/
theorem scalars_mapScalar {T : Type u} (f : Scalar → T) (r : RawJson Scalar) :
    (r.mapScalar f).scalars = r.scalars.map f := by
  induction r with
  | scalar value => simp
  | list elems ih =>
    simp only [mapScalar_list, scalars_list, List.map_map, List.map_flatten]
    exact congrArg List.flatten (List.map_congr_left fun e he => by
      simp only [Function.comp_apply, ih e he])
  | map entries ih =>
    simp only [mapScalar_map, scalars_map, List.map_map, List.map_flatten]
    exact congrArg List.flatten (List.map_congr_left fun e he => by
      simp only [Function.comp_apply, ih e he])

end RawJson

end Nucleus
