import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Raw key- and scalar-parametric JSON syntax

`KeyedRawJson` is raw JSON-shaped syntax, parametric over object keys and scalar
values. `RawJson` specializes keys to `String`. Object members are kept as an
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

universe u v

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
inductive RawSyn (Key : Type v) (Scalar : Type u) : JsonIx → Type (max u v) where
  /-- A scalar leaf. -/
  | scalar (value : Scalar) : RawSyn Key Scalar .val
  /-- An array value, from an array tail. -/
  | list (elems : RawSyn Key Scalar .arr) : RawSyn Key Scalar .val
  /-- An object value, from an object tail. -/
  | map (entries : RawSyn Key Scalar .obj) : RawSyn Key Scalar .val
  /-- The empty array tail. -/
  | nil : RawSyn Key Scalar .arr
  /-- Prepend a value to an array tail. -/
  | cons (head : RawSyn Key Scalar .val) (tail : RawSyn Key Scalar .arr) : RawSyn Key Scalar .arr
  /-- The empty object tail. -/
  | objNil : RawSyn Key Scalar .obj
  /-- Prepend a key–value entry to an object tail.  No constraint relates `key` to the
  keys of `tail`: order and duplicates are preserved verbatim. -/
  | objCons (key : Key) (value : RawSyn Key Scalar .val) (tail : RawSyn Key Scalar .obj) :
      RawSyn Key Scalar .obj

/-- A raw JSON value: the value sort of `RawSyn`. -/
abbrev KeyedRawJson (Key : Type v) (Scalar : Type u) := RawSyn Key Scalar .val

abbrev RawJson (Scalar : Type u) := KeyedRawJson String Scalar

/-- One step of a JSON path: a list index or an object key. -/
inductive KeyedJsonStep (Key : Type v) where
  /-- Index into an array. -/
  | index (i : Nat)
  /-- Select an object member by key. -/
  | key (k : Key)
  deriving DecidableEq, Repr

/-- A path into a JSON tree. -/
abbrev KeyedJsonPath (Key : Type v) := List (KeyedJsonStep Key)

abbrev JsonStep := KeyedJsonStep String
abbrev JsonPath := KeyedJsonPath String

namespace RawSyn

variable {Key : Type v} {Scalar : Type u}

/-! ## List views of the tail sorts -/

/-- The elements of an array tail, as a list. -/
def toList : RawSyn Key Scalar .arr → List (KeyedRawJson Key Scalar)
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- The entries of an object tail, as an ordered association list (duplicates and order
preserved). -/
def toEntries : RawSyn Key Scalar .obj → List (Key × KeyedRawJson Key Scalar)
  | .objNil => []
  | .objCons key value tail => (key, value) :: tail.toEntries

/-- The keys of an object tail, in member order, with duplicates. -/
def keys : RawSyn Key Scalar .obj → List Key
  | .objNil => []
  | .objCons key _ tail => key :: tail.keys

/-- Build an array tail from a list of values. -/
def ofList : List (KeyedRawJson Key Scalar) → RawSyn Key Scalar .arr
  | [] => .nil
  | head :: rest => .cons head (ofList rest)

/-- Build an object tail from an association list. -/
def ofEntries : List (Key × KeyedRawJson Key Scalar) → RawSyn Key Scalar .obj
  | [] => .objNil
  | (key, value) :: rest => .objCons key value (ofEntries rest)

@[simp] theorem toList_nil : (RawSyn.nil : RawSyn Key Scalar .arr).toList = [] := by
  simp [toList]

@[simp] theorem toList_cons (head : KeyedRawJson Key Scalar) (tail : RawSyn Key Scalar .arr) :
    (RawSyn.cons head tail).toList = head :: tail.toList := by
  simp [toList]

@[simp] theorem toEntries_objNil : (RawSyn.objNil : RawSyn Key Scalar .obj).toEntries = [] := by
  simp [toEntries]

@[simp] theorem toEntries_objCons (key : Key) (value : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).toEntries = (key, value) :: tail.toEntries := by
  simp [toEntries]

@[simp] theorem keys_objNil : (RawSyn.objNil : RawSyn Key Scalar .obj).keys = [] := by
  simp [keys]

@[simp] theorem keys_objCons (key : Key) (value : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).keys = key :: tail.keys := by
  simp [keys]

@[simp] theorem ofList_nil : (ofList [] : RawSyn Key Scalar .arr) = .nil := by
  simp [ofList]

@[simp] theorem ofList_cons (head : KeyedRawJson Key Scalar)
    (rest : List (KeyedRawJson Key Scalar)) :
    ofList (head :: rest) = .cons head (ofList rest) := by
  simp [ofList]

@[simp] theorem ofEntries_nil : (ofEntries [] : RawSyn Key Scalar .obj) = .objNil := by
  simp [ofEntries]

@[simp] theorem ofEntries_cons (entry : Key × KeyedRawJson Key Scalar)
    (rest : List (Key × KeyedRawJson Key Scalar)) :
    ofEntries (entry :: rest) = .objCons entry.1 entry.2 (ofEntries rest) := by
  obtain ⟨key, value⟩ := entry
  simp [ofEntries]

/-- The keys of an object tail are the first components of its entries. -/
theorem keys_eq_toEntries_fst : ∀ (o : RawSyn Key Scalar .obj), o.keys = o.toEntries.map Prod.fst
  | .objNil => by simp
  | .objCons key value tail => by simp [keys_eq_toEntries_fst tail]

@[simp] theorem toList_ofList (l : List (KeyedRawJson Key Scalar)) : (ofList l).toList = l := by
  induction l with
  | nil => simp
  | cons head rest ih => simp [ih]

@[simp] theorem ofList_toList : ∀ (a : RawSyn Key Scalar .arr), ofList a.toList = a
  | .nil => by simp
  | .cons head tail => by simp [ofList_toList tail]

@[simp] theorem toEntries_ofEntries (l : List (Key × KeyedRawJson Key Scalar)) :
    (ofEntries l).toEntries = l := by
  induction l with
  | nil => simp
  | cons entry rest ih => simp [ih]

@[simp] theorem ofEntries_toEntries : ∀ (o : RawSyn Key Scalar .obj), ofEntries o.toEntries = o
  | .objNil => by simp
  | .objCons key value tail => by simp [ofEntries_toEntries tail]

/-- An array tail is determined by its list of elements. -/
theorem toList_injective : Function.Injective (toList (Key := Key) (Scalar := Scalar)) :=
  Function.LeftInverse.injective ofList_toList

/-- An object tail is determined by its entry list. -/
theorem toEntries_injective : Function.Injective (toEntries (Key := Key) (Scalar := Scalar)) :=
  Function.LeftInverse.injective ofEntries_toEntries

/-- Array tails are exactly lists of raw values. -/
def arrEquivList : RawSyn Key Scalar .arr ≃ List (KeyedRawJson Key Scalar) where
  toFun := toList
  invFun := ofList
  left_inv := ofList_toList
  right_inv := toList_ofList

/-- Object tails are exactly ordered association lists. -/
def objEquivList : RawSyn Key Scalar .obj ≃ List (Key × KeyedRawJson Key Scalar) where
  toFun := toEntries
  invFun := ofEntries
  left_inv := ofEntries_toEntries
  right_inv := toEntries_ofEntries

/-! ## Measures and scalar operations

All of these recurse structurally over the indexed family — no termination
arguments are needed. -/

/-- Total node count: each value node counts one, tails contribute their members. -/
def size {i : JsonIx} : RawSyn Key Scalar i → Nat
  | .scalar _ => 1
  | .list elems => 1 + elems.size
  | .map entries => 1 + entries.size
  | .nil => 0
  | .cons head tail => head.size + tail.size
  | .objNil => 0
  | .objCons _ value tail => value.size + tail.size

/-- Nesting depth: scalars have depth `0`, and containers have one more than the
maximum depth of their members (`0` for an empty container). -/
def depth {i : JsonIx} : RawSyn Key Scalar i → Nat
  | .scalar _ => 0
  | .list elems => 1 + elems.depth
  | .map entries => 1 + entries.depth
  | .nil => 0
  | .cons head tail => max head.depth tail.depth
  | .objNil => 0
  | .objCons _ value tail => max value.depth tail.depth

/-- Pre-order list of the scalar leaves, preserving order and duplicates. -/
def scalars {i : JsonIx} : RawSyn Key Scalar i → List Scalar
  | .scalar value => [value]
  | .list elems => elems.scalars
  | .map entries => entries.scalars
  | .nil => []
  | .cons head tail => head.scalars ++ tail.scalars
  | .objNil => []
  | .objCons _ value tail => value.scalars ++ tail.scalars

/-- Apply `f` to every scalar leaf, preserving structure, member order, and duplicate
keys. -/
def mapScalar {T : Type u} (f : Scalar → T) {i : JsonIx} : RawSyn Key Scalar i → RawSyn Key T i
  | .scalar value => .scalar (f value)
  | .list elems => .list (elems.mapScalar f)
  | .map entries => .map (entries.mapScalar f)
  | .nil => .nil
  | .cons head tail => .cons (head.mapScalar f) (tail.mapScalar f)
  | .objNil => .objNil
  | .objCons key value tail => .objCons key (value.mapScalar f) (tail.mapScalar f)

/-- Fold `f` over the scalar leaves in pre-order. -/
def foldScalars {B : Type*} (f : B → Scalar → B) (init : B) {i : JsonIx}
    (r : RawSyn Key Scalar i) : B :=
  r.scalars.foldl f init

@[simp] theorem mapScalar_scalar {T : Type u} (f : Scalar → T) (value : Scalar) :
    (RawSyn.scalar (Key := Key) value).mapScalar f = .scalar (f value) := by
  simp [mapScalar]

@[simp] theorem mapScalar_list {T : Type u} (f : Scalar → T) (elems : RawSyn Key Scalar .arr) :
    (RawSyn.list elems).mapScalar f = .list (elems.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_map {T : Type u} (f : Scalar → T) (entries : RawSyn Key Scalar .obj) :
    (RawSyn.map entries).mapScalar f = .map (entries.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_nil {T : Type u} (f : Scalar → T) :
    (RawSyn.nil : RawSyn Key Scalar .arr).mapScalar f = .nil := by
  simp [mapScalar]

@[simp] theorem mapScalar_cons {T : Type u} (f : Scalar → T) (head : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .arr) :
    (RawSyn.cons head tail).mapScalar f = .cons (head.mapScalar f) (tail.mapScalar f) := by
  simp [mapScalar]

@[simp] theorem mapScalar_objNil {T : Type u} (f : Scalar → T) :
    (RawSyn.objNil : RawSyn Key Scalar .obj).mapScalar f = .objNil := by
  simp [mapScalar]

@[simp] theorem mapScalar_objCons {T : Type u} (f : Scalar → T) (key : Key)
    (value : KeyedRawJson Key Scalar) (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).mapScalar f
      = .objCons key (value.mapScalar f) (tail.mapScalar f) := by
  simp [mapScalar]

/-- Mapping the identity over the scalar leaves is the identity. -/
@[simp] theorem mapScalar_id {i : JsonIx} (r : RawSyn Key Scalar i) : r.mapScalar id = r := by
  induction r <;> simp [*]

/-- Mapping over the scalar leaves composes. -/
theorem mapScalar_comp {T U : Type u} (f : Scalar → T) (g : T → U) {i : JsonIx}
    (r : RawSyn Key Scalar i) : (r.mapScalar f).mapScalar g = r.mapScalar (g ∘ f) := by
  induction r <;> simp [*]

/-- The scalar leaves of a mapped tree are the mapped scalar leaves. -/
theorem scalars_mapScalar {T : Type u} (f : Scalar → T) {i : JsonIx} (r : RawSyn Key Scalar i) :
    (r.mapScalar f).scalars = r.scalars.map f := by
  induction r <;> simp [scalars, *]

/-- The entries of a mapped object tail are the entries with mapped values. -/
theorem toEntries_mapScalar {T : Type u} (f : Scalar → T) :
    ∀ (o : RawSyn Key Scalar .obj),
      (o.mapScalar f).toEntries = o.toEntries.map fun e => (e.1, e.2.mapScalar f)
  | .objNil => by simp
  | .objCons key value tail => by simp [toEntries_mapScalar f tail]

/-- Mapping over scalars leaves object keys untouched. -/
@[simp] theorem keys_mapScalar {T : Type u} (f : Scalar → T) (o : RawSyn Key Scalar .obj) :
    (o.mapScalar f).keys = o.keys := by
  rw [keys_eq_toEntries_fst, keys_eq_toEntries_fst, toEntries_mapScalar]
  simp [List.map_map, Function.comp_def]

/-- The elements of a mapped array tail are the mapped elements. -/
theorem toList_mapScalar {T : Type u} (f : Scalar → T) :
    ∀ (a : RawSyn Key Scalar .arr), (a.mapScalar f).toList = a.toList.map (·.mapScalar f)
  | .nil => by simp
  | .cons head tail => by simp [toList_mapScalar f tail]

/-! ## Monad structure

Substituting raw values for scalar leaves makes the value sort a monad — the
free monad on the JSON container signature — with `RawSyn.scalar` as `pure`
and `RawSyn.bind` as bind.  The tail sorts are modules over that monad: `bind`
is defined at every sort, and the `bind_pure` and `bind_assoc` laws hold
family-wide, while `pure` (and hence the `pure_bind` law) exists only at the
value sort. -/

/-- Substitute every scalar leaf by a raw JSON value, preserving structure,
member order, and duplicate keys. -/
def bind {T : Type u} {i : JsonIx} :
    RawSyn Key Scalar i → (Scalar → KeyedRawJson Key T) → RawSyn Key T i
  | .scalar value, f => f value
  | .list elems, f => .list (elems.bind f)
  | .map entries, f => .map (entries.bind f)
  | .nil, _ => .nil
  | .cons head tail, f => .cons (head.bind f) (tail.bind f)
  | .objNil, _ => .objNil
  | .objCons key value tail, f => .objCons key (value.bind f) (tail.bind f)

@[simp] theorem bind_scalar {T : Type u} (f : Scalar → KeyedRawJson Key T) (value : Scalar) :
    (RawSyn.scalar value).bind f = f value := by
  simp [bind]

@[simp] theorem bind_list {T : Type u} (f : Scalar → KeyedRawJson Key T)
    (elems : RawSyn Key Scalar .arr) :
    (RawSyn.list elems).bind f = .list (elems.bind f) := by
  simp [bind]

@[simp] theorem bind_map {T : Type u} (f : Scalar → KeyedRawJson Key T)
    (entries : RawSyn Key Scalar .obj) :
    (RawSyn.map entries).bind f = .map (entries.bind f) := by
  simp [bind]

@[simp] theorem bind_nil {T : Type u} (f : Scalar → KeyedRawJson Key T) :
    (RawSyn.nil : RawSyn Key Scalar .arr).bind f = .nil := by
  simp [bind]

@[simp] theorem bind_cons {T : Type u} (f : Scalar → KeyedRawJson Key T)
    (head : KeyedRawJson Key Scalar)
    (tail : RawSyn Key Scalar .arr) :
    (RawSyn.cons head tail).bind f = .cons (head.bind f) (tail.bind f) := by
  simp [bind]

@[simp] theorem bind_objNil {T : Type u} (f : Scalar → KeyedRawJson Key T) :
    (RawSyn.objNil : RawSyn Key Scalar .obj).bind f = .objNil := by
  simp [bind]

@[simp] theorem bind_objCons {T : Type u} (f : Scalar → KeyedRawJson Key T) (key : Key)
    (value : KeyedRawJson Key Scalar) (tail : RawSyn Key Scalar .obj) :
    (RawSyn.objCons key value tail).bind f
      = .objCons key (value.bind f) (tail.bind f) := by
  simp [bind]

/-- Right identity: substituting each leaf by itself changes nothing.  Holds
at every sort of the family. -/
@[simp] theorem bind_pure {i : JsonIx} (r : RawSyn Key Scalar i) :
    r.bind RawSyn.scalar = r := by
  induction r <;> simp [*]

/-- Associativity of substitution.  Holds at every sort of the family. -/
theorem bind_assoc {T U : Type u} {i : JsonIx} (r : RawSyn Key Scalar i)
    (f : Scalar → KeyedRawJson Key T) (g : T → KeyedRawJson Key U) :
    (r.bind f).bind g = r.bind fun s => (f s).bind g := by
  induction r <;> simp [*]

/-- `mapScalar` is the functorial action induced by `bind`. -/
theorem mapScalar_eq_bind {T : Type u} (f : Scalar → T) {i : JsonIx} (r : RawSyn Key Scalar i) :
    r.mapScalar f = r.bind fun s => .scalar (f s) := by
  induction r <;> simp [*]

end RawSyn

/-- Raw JSON values form a monad over their scalars: `pure` is a scalar leaf
and `bind` substitutes leaves. -/
instance : Monad (RawJson : Type u → Type u) where
  pure := RawSyn.scalar
  bind := RawSyn.bind

instance : LawfulMonad (RawJson : Type u → Type u) :=
  LawfulMonad.mk' _
    (fun r => by
      change r.bind (fun s => RawSyn.scalar (id s)) = r
      simp)
    (fun v f => by
      change (RawSyn.scalar v).bind f = f v
      simp)
    (fun r f g => by
      change (r.bind f).bind g = r.bind fun s => (f s).bind g
      exact RawSyn.bind_assoc r f g)

/-- The `Functor` map of `RawJson` is `RawSyn.mapScalar`. -/
theorem RawJson.map_eq_mapScalar {S T : Type u} (f : S → T) (r : RawJson S) :
    f <$> r = r.mapScalar f := by
  change r.bind (fun s => RawSyn.scalar (f s)) = r.mapScalar f
  exact (RawSyn.mapScalar_eq_bind f r).symm

namespace RawSyn

variable {Key : Type v} {Scalar : Type u}

/-! ## Path lookup -/

/-- Look up a node by path.  The empty path returns the node itself; `.index i` indexes
into a `.list`, and `.key k` selects the FIRST entry with key `k` in a `.map`.
First-match lookup on duplicate keys is a lookup convention only — it does not collapse
duplicates semantically.  Any mismatch (index on a non-list, key on a non-map, index out
of range, or missing key) yields `none`. -/
def get? [BEq Key] : KeyedRawJson Key Scalar → KeyedJsonPath Key → Option (KeyedRawJson Key Scalar)
  | r, [] => some r
  | .list elems, .index i :: rest =>
    match elems.toList[i]? with
    | some e => e.get? rest
    | none => none
  | .map entries, .key k :: rest =>
    match entries.toEntries.find? fun e => e.1 == k with
    | some e => e.2.get? rest
    | none => none
  | _, _ => none

/-! ## Induction with list-membership hypotheses -/

mutual

/-- Body of `RawSyn.inductionOn`; see the wrapper below for the
`@[induction_eliminator]` registration. -/
theorem inductionOnVal {motive : KeyedRawJson Key Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ r, motive r
  | .scalar value => scalar value
  | .list elems => list elems (inductionOnArr scalar list map elems)
  | .map entries => map entries (inductionOnObj scalar list map entries)

/-- Auxiliary induction for array tails: the motive holds for every element. -/
theorem inductionOnArr {motive : KeyedRawJson Key Scalar → Prop}
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
theorem inductionOnObj {motive : KeyedRawJson Key Scalar → Prop}
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
theorem inductionOn {motive : KeyedRawJson Key Scalar → Prop}
    (scalar : ∀ value, motive (.scalar value))
    (list : ∀ elems, (∀ e ∈ toList elems, motive e) → motive (.list elems))
    (map : ∀ entries, (∀ e ∈ toEntries entries, motive e.2) → motive (.map entries)) :
    ∀ r, motive r :=
  inductionOnVal scalar list map

end RawSyn

namespace KeyedRawJson

variable {Key : Type v} {Scalar : Type u}

/-- Build an array value from a list of elements. -/
def listOf (elems : List (KeyedRawJson Key Scalar)) : KeyedRawJson Key Scalar :=
  .list (RawSyn.ofList elems)

/-- Build an object value from an ordered association list; duplicate keys are
preserved. -/
def mapOf (entries : List (Key × KeyedRawJson Key Scalar)) : KeyedRawJson Key Scalar :=
  .map (RawSyn.ofEntries entries)

end KeyedRawJson

namespace RawJson

variable {Scalar : Type u}

/-- Build an ordinary String-keyed raw array value. -/
abbrev listOf (elems : List (RawJson Scalar)) : RawJson Scalar :=
  KeyedRawJson.listOf elems

/-- Build an ordinary String-keyed raw object value. -/
abbrev mapOf (entries : List (String × RawJson Scalar)) : RawJson Scalar :=
  KeyedRawJson.mapOf entries

end RawJson

end Nucleus
