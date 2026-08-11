import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Raw scalar-parametric JSON syntax

`RawJson` is the raw, RFC-8259-shaped JSON syntax layer, parametric over the type of
scalar values.  It records exactly what a JSON text says: object members are kept as an
ordered sequence of key–value entries, preserving both member order and duplicate keys.

Consequently, equality of `RawJson` values observes member order and duplicates: two
trees whose objects list the same members in a different order, or with different
duplicate structure, are distinct terms.  Profile validation — in particular, deciding
how duplicate keys are handled — happens explicitly when converting to the extensional
form (see the `Nucleus.Json` docs); nothing here collapses or reorders members.

`RawJson` is the value sort of the three-sorted indexed family `RawSyn` (values, array
tails, object tails).  An indexed family is used instead of a nested inductive with
`List` children because indexed inductives support ordinary structural recursion: every
operation and proof below recurses structurally, with no `sizeOf` termination
arguments.  The array- and object-tail sorts are isomorphic to lists
(`RawSyn.arrEquivList`, `RawSyn.objEquivList`), and `RawSyn.toList` / `RawSyn.toEntries`
give the list views used to state key lemmas.
-/

namespace Nucleus

universe u

/-- Grammar sorts of the raw JSON syntax: a value, an array tail, or an object tail. -/
inductive JsonIx where
  /-- A single JSON value. -/
  | val
  /-- A (tail of an) array: a sequence of values. -/
  | arr
  /-- A (tail of an) object: a sequence of key–value entries. -/
  | obj
  deriving DecidableEq, Repr

/-- Raw JSON syntax, parametric over the scalar type and indexed by grammar sort.
Objects are ordered sequences of key–value entries; duplicate keys are preserved, and
equality observes both order and duplicates.  Duplicate-key policy is applied only when
converting to the extensional form. -/
inductive RawSyn (Scalar : Type u) : JsonIx → Type u where
  /-- A scalar leaf. -/
  | scalar (value : Scalar) : RawSyn Scalar .val
  /-- An array value, from an array tail. -/
  | list (elems : RawSyn Scalar .arr) : RawSyn Scalar .val
  /-- An object value, from an object tail. -/
  | map (entries : RawSyn Scalar .obj) : RawSyn Scalar .val
  /-- The empty array tail. -/
  | nil : RawSyn Scalar .arr
  /-- Prepend a value to an array tail. -/
  | cons (head : RawSyn Scalar .val) (tail : RawSyn Scalar .arr) : RawSyn Scalar .arr
  /-- The empty object tail. -/
  | objNil : RawSyn Scalar .obj
  /-- Prepend a key–value entry to an object tail.  No constraint relates `key` to the
  keys of `tail`: order and duplicates are preserved verbatim. -/
  | objCons (key : String) (value : RawSyn Scalar .val) (tail : RawSyn Scalar .obj) :
      RawSyn Scalar .obj

/-- A raw JSON value: the value sort of `RawSyn`. -/
abbrev RawJson (Scalar : Type u) := RawSyn Scalar .val

/-- One step of a JSON path: a list index or an object key. -/
inductive JsonStep where
  /-- Index into an array. -/
  | index (i : Nat)
  /-- Select an object member by key. -/
  | key (k : String)
  deriving DecidableEq, Repr

/-- A path into a JSON tree. -/
abbrev JsonPath := List JsonStep

namespace RawSyn

variable {Scalar : Type u}

/-! ## List views of the tail sorts -/

/-- The elements of an array tail, as a list. -/
def toList : RawSyn Scalar .arr → List (RawJson Scalar)
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- The entries of an object tail, as an ordered association list (duplicates and order
preserved). -/
def toEntries : RawSyn Scalar .obj → List (String × RawJson Scalar)
  | .objNil => []
  | .objCons key value tail => (key, value) :: tail.toEntries

/-- The keys of an object tail, in member order, with duplicates. -/
def keys : RawSyn Scalar .obj → List String
  | .objNil => []
  | .objCons key _ tail => key :: tail.keys

/-- Build an array tail from a list of values. -/
def ofList : List (RawJson Scalar) → RawSyn Scalar .arr
  | [] => .nil
  | head :: rest => .cons head (ofList rest)

/-- Build an object tail from an association list. -/
def ofEntries : List (String × RawJson Scalar) → RawSyn Scalar .obj
  | [] => .objNil
  | (key, value) :: rest => .objCons key value (ofEntries rest)

@[simp] theorem toList_nil : (RawSyn.nil : RawSyn Scalar .arr).toList = [] := by
  simp [toList]

@[simp] theorem toList_cons (head : RawJson Scalar) (tail : RawSyn Scalar .arr) :
    (RawSyn.cons head tail).toList = head :: tail.toList := by
  simp [toList]

@[simp] theorem toEntries_objNil : (RawSyn.objNil : RawSyn Scalar .obj).toEntries = [] := by
  simp [toEntries]

@[simp] theorem toEntries_objCons (key : String) (value : RawJson Scalar)
    (tail : RawSyn Scalar .obj) :
    (RawSyn.objCons key value tail).toEntries = (key, value) :: tail.toEntries := by
  simp [toEntries]

@[simp] theorem keys_objNil : (RawSyn.objNil : RawSyn Scalar .obj).keys = [] := by
  simp [keys]

@[simp] theorem keys_objCons (key : String) (value : RawJson Scalar)
    (tail : RawSyn Scalar .obj) :
    (RawSyn.objCons key value tail).keys = key :: tail.keys := by
  simp [keys]

@[simp] theorem ofList_nil : (ofList [] : RawSyn Scalar .arr) = .nil := by
  simp [ofList]

@[simp] theorem ofList_cons (head : RawJson Scalar) (rest : List (RawJson Scalar)) :
    ofList (head :: rest) = .cons head (ofList rest) := by
  simp [ofList]

@[simp] theorem ofEntries_nil : (ofEntries [] : RawSyn Scalar .obj) = .objNil := by
  simp [ofEntries]

@[simp] theorem ofEntries_cons (entry : String × RawJson Scalar)
    (rest : List (String × RawJson Scalar)) :
    ofEntries (entry :: rest) = .objCons entry.1 entry.2 (ofEntries rest) := by
  obtain ⟨key, value⟩ := entry
  simp [ofEntries]

/-- The keys of an object tail are the first components of its entries. -/
theorem keys_eq_toEntries_fst : ∀ (o : RawSyn Scalar .obj), o.keys = o.toEntries.map Prod.fst
  | .objNil => by simp
  | .objCons key value tail => by simp [keys_eq_toEntries_fst tail]

@[simp] theorem toList_ofList (l : List (RawJson Scalar)) : (ofList l).toList = l := by
  induction l with
  | nil => simp
  | cons head rest ih => simp [ih]

@[simp] theorem ofList_toList : ∀ (a : RawSyn Scalar .arr), ofList a.toList = a
  | .nil => by simp
  | .cons head tail => by simp [ofList_toList tail]

@[simp] theorem toEntries_ofEntries (l : List (String × RawJson Scalar)) :
    (ofEntries l).toEntries = l := by
  induction l with
  | nil => simp
  | cons entry rest ih => simp [ih]

@[simp] theorem ofEntries_toEntries : ∀ (o : RawSyn Scalar .obj), ofEntries o.toEntries = o
  | .objNil => by simp
  | .objCons key value tail => by simp [ofEntries_toEntries tail]

/-- An array tail is determined by its list of elements. -/
theorem toList_injective : Function.Injective (toList (Scalar := Scalar)) :=
  Function.LeftInverse.injective ofList_toList

/-- An object tail is determined by its entry list. -/
theorem toEntries_injective : Function.Injective (toEntries (Scalar := Scalar)) :=
  Function.LeftInverse.injective ofEntries_toEntries

/-- Array tails are exactly lists of raw values. -/
def arrEquivList : RawSyn Scalar .arr ≃ List (RawJson Scalar) where
  toFun := toList
  invFun := ofList
  left_inv := ofList_toList
  right_inv := toList_ofList

/-- Object tails are exactly ordered association lists. -/
def objEquivList : RawSyn Scalar .obj ≃ List (String × RawJson Scalar) where
  toFun := toEntries
  invFun := ofEntries
  left_inv := ofEntries_toEntries
  right_inv := toEntries_ofEntries

/-! ## Measures and scalar operations

All of these recurse structurally over the indexed family — no termination
arguments are needed. -/

/-- Total node count: each value node counts one, tails contribute their members. -/
def size {i : JsonIx} : RawSyn Scalar i → Nat
  | .scalar _ => 1
  | .list elems => 1 + elems.size
  | .map entries => 1 + entries.size
  | .nil => 0
  | .cons head tail => head.size + tail.size
  | .objNil => 0
  | .objCons _ value tail => value.size + tail.size

/-- Nesting depth: scalars have depth `0`, and containers have one more than the
maximum depth of their members (`0` for an empty container). -/
def depth {i : JsonIx} : RawSyn Scalar i → Nat
  | .scalar _ => 0
  | .list elems => 1 + elems.depth
  | .map entries => 1 + entries.depth
  | .nil => 0
  | .cons head tail => max head.depth tail.depth
  | .objNil => 0
  | .objCons _ value tail => max value.depth tail.depth

/-- Pre-order list of the scalar leaves, preserving order and duplicates. -/
def scalars {i : JsonIx} : RawSyn Scalar i → List Scalar
  | .scalar value => [value]
  | .list elems => elems.scalars
  | .map entries => entries.scalars
  | .nil => []
  | .cons head tail => head.scalars ++ tail.scalars
  | .objNil => []
  | .objCons _ value tail => value.scalars ++ tail.scalars

/-- Apply `f` to every scalar leaf, preserving structure, member order, and duplicate
keys. -/
def mapScalar {T : Type u} (f : Scalar → T) {i : JsonIx} : RawSyn Scalar i → RawSyn T i
  | .scalar value => .scalar (f value)
  | .list elems => .list (elems.mapScalar f)
  | .map entries => .map (entries.mapScalar f)
  | .nil => .nil
  | .cons head tail => .cons (head.mapScalar f) (tail.mapScalar f)
  | .objNil => .objNil
  | .objCons key value tail => .objCons key (value.mapScalar f) (tail.mapScalar f)

/-- Fold `f` over the scalar leaves in pre-order. -/
def foldScalars {B : Type*} (f : B → Scalar → B) (init : B) {i : JsonIx}
    (r : RawSyn Scalar i) : B :=
  r.scalars.foldl f init

@[simp] theorem mapScalar_scalar {T : Type u} (f : Scalar → T) (value : Scalar) :
    (RawSyn.scalar value).mapScalar f = .scalar (f value) := by
  simp [mapScalar]

@[simp] theorem mapScalar_list {T : Type u} (f : Scalar → T) (elems : RawSyn Scalar .arr) :
    (RawSyn.list elems).mapScalar f = .list (elems.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_map {T : Type u} (f : Scalar → T) (entries : RawSyn Scalar .obj) :
    (RawSyn.map entries).mapScalar f = .map (entries.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_nil {T : Type u} (f : Scalar → T) :
    (RawSyn.nil : RawSyn Scalar .arr).mapScalar f = .nil := by
  simp [mapScalar]

@[simp] theorem mapScalar_cons {T : Type u} (f : Scalar → T) (head : RawJson Scalar)
    (tail : RawSyn Scalar .arr) :
    (RawSyn.cons head tail).mapScalar f = .cons (head.mapScalar f) (tail.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_objNil {T : Type u} (f : Scalar → T) :
    (RawSyn.objNil : RawSyn Scalar .obj).mapScalar f = .objNil := by
  simp [mapScalar]

@[simp] theorem mapScalar_objCons {T : Type u} (f : Scalar → T) (key : String)
    (value : RawJson Scalar) (tail : RawSyn Scalar .obj) :
    (RawSyn.objCons key value tail).mapScalar f
      = .objCons key (value.mapScalar f) (tail.mapScalar f) := by
  simp [mapScalar]

/-- Mapping the identity over the scalar leaves is the identity. -/
@[simp] theorem mapScalar_id {i : JsonIx} (r : RawSyn Scalar i) : r.mapScalar id = r := by
  induction r <;> simp [*]

/-- Mapping over the scalar leaves composes. -/
theorem mapScalar_comp {T U : Type u} (f : Scalar → T) (g : T → U) {i : JsonIx}
    (r : RawSyn Scalar i) : (r.mapScalar f).mapScalar g = r.mapScalar (g ∘ f) := by
  induction r <;> simp [*]

/-- The scalar leaves of a mapped tree are the mapped scalar leaves. -/
theorem scalars_mapScalar {T : Type u} (f : Scalar → T) {i : JsonIx} (r : RawSyn Scalar i) :
    (r.mapScalar f).scalars = r.scalars.map f := by
  induction r <;> simp [scalars, *]

/-- The entries of a mapped object tail are the entries with mapped values. -/
theorem toEntries_mapScalar {T : Type u} (f : Scalar → T) :
    ∀ (o : RawSyn Scalar .obj),
      (o.mapScalar f).toEntries = o.toEntries.map fun e => (e.1, e.2.mapScalar f)
  | .objNil => by simp
  | .objCons key value tail => by simp [toEntries_mapScalar f tail]

/-- Mapping over scalars leaves object keys untouched. -/
@[simp] theorem keys_mapScalar {T : Type u} (f : Scalar → T) (o : RawSyn Scalar .obj) :
    (o.mapScalar f).keys = o.keys := by
  rw [keys_eq_toEntries_fst, keys_eq_toEntries_fst, toEntries_mapScalar]
  simp [List.map_map, Function.comp_def]

/-- The elements of a mapped array tail are the mapped elements. -/
theorem toList_mapScalar {T : Type u} (f : Scalar → T) :
    ∀ (a : RawSyn Scalar .arr), (a.mapScalar f).toList = a.toList.map (·.mapScalar f)
  | .nil => by simp
  | .cons head tail => by simp [toList_mapScalar f tail]

/-! ## Path lookup -/

/-- Look up a node by path.  The empty path returns the node itself; `.index i` indexes
into a `.list`, and `.key k` selects the FIRST entry with key `k` in a `.map`.
First-match lookup on duplicate keys is a lookup convention only — it does not collapse
duplicates semantically.  Any mismatch (index on a non-list, key on a non-map, index out
of range, or missing key) yields `none`. -/
def get? : RawJson Scalar → JsonPath → Option (RawJson Scalar)
  | r, [] => some r
  | .list elems, .index i :: rest =>
    match elems.toList[i]? with
    | some e => e.get? rest
    | none => none
  | .map entries, .key k :: rest =>
    match entries.toEntries.find? fun e => e.1 = k with
    | some e => e.2.get? rest
    | none => none
  | _, _ => none

/-! ## Induction with list-membership hypotheses -/

mutual

/-- Body of `RawSyn.inductionOn`; see the wrapper below for the
`@[induction_eliminator]` registration. -/
theorem inductionOnVal {motive : RawJson Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ r, motive r
  | .scalar value => scalar value
  | .list elems => list elems (inductionOnArr scalar list map elems)
  | .map entries => map entries (inductionOnObj scalar list map entries)

/-- Auxiliary induction for array tails: the motive holds for every element. -/
theorem inductionOnArr {motive : RawJson Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ a, ∀ e ∈ toList a, motive e
  | .cons head tail => by
      simp only [toList_cons, List.mem_cons]
      rintro e (rfl | he)
      · exact inductionOnVal scalar list map e
      · exact inductionOnArr scalar list map tail e he
  | .nil => by simp

/-- Auxiliary induction for object tails: the motive holds for every entry value. -/
theorem inductionOnObj {motive : RawJson Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ o, ∀ e ∈ toEntries o, motive e.2
  | .objCons key value tail => by
      simp only [toEntries_objCons, List.mem_cons]
      rintro e (rfl | he)
      · exact inductionOnVal scalar list map value
      · exact inductionOnObj scalar list map tail e he
  | .objNil => by simp

end

/-- Induction principle for raw JSON values providing list-membership-indexed inductive
hypotheses for the members of `list` and `map` nodes. -/
@[induction_eliminator]
theorem inductionOn {motive : RawJson Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ r, motive r :=
  inductionOnVal scalar list map

end RawSyn

namespace RawJson

variable {Scalar : Type u}

/-- Build an array value from a list of elements. -/
def listOf (elems : List (RawJson Scalar)) : RawJson Scalar :=
  .list (RawSyn.ofList elems)

/-- Build an object value from an ordered association list; duplicate keys are
preserved. -/
def mapOf (entries : List (String × RawJson Scalar)) : RawJson Scalar :=
  .map (RawSyn.ofEntries entries)

end RawJson

end Nucleus
