import Mathlib.Data.Finset.Sort
import Mathlib.Data.String.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Nucleus.Json.Raw

/-!
# Extensional JSON values

`Json Scalar Key` is the extensional form of a JSON tree: arrays are finite
indexed families and objects are value families indexed by a `Finset Key`.
Object equality therefore ignores member ordering by
construction — two maps are equal exactly when they have the same key set and
propositionally equal value families (via function extensionality) — while
duplicate keys are unrepresentable.

Scalars stay generic: null/Boolean representation, string decoding, and exact
numeral semantics are deliberately not fixed here (see the `Nucleus.Json`
module documentation). Ordinary JSON defaults object keys to `String`;
this does not constrain how string *values* are represented inside `Scalar`.

`Json.toRaw` picks the canonical ordered data representative: it enumerates
each object in strictly increasing key order.  This is a data-level choice
only; it does not impose a canonical byte encoding, and equal extensional
values are not required to have equal content hashes.
-/

namespace Nucleus

universe u

/-- An extensional JSON tree over scalar values `Scalar` and object keys `Key`.
Keys default to `String`. Arrays are finite indexed families and objects are value
families over a finite key set, so array/object contents are compared
extensionally and duplicate keys cannot be represented. -/
inductive Json (Scalar : Type u) (Key : Type := String) : Type u where
  /-- A scalar leaf. -/
  | scalar (value : Scalar)
  /-- An array of `n` children, as a finite indexed family. -/
  | list (n : Nat) (elems : Fin n → Json Scalar Key)
  /-- An object: a finite set of keys together with a value for each key. -/
  | map (keys : Finset Key) (vals : {k // k ∈ keys} → Json Scalar Key)

/-- A key-parametric JSON tree, with the key parameter written first. -/
abbrev KeyedJson (Key : Type) (Scalar : Type u) := Json Scalar Key

namespace Json

variable {Key : Type} {Scalar : Type u}

/-- Total node count. -/
def size : Json Scalar Key → Nat
  | .scalar _ => 1
  | .list _n elems => 1 + ∑ i, (elems i).size
  | .map _keys vals => 1 + ∑ k, (vals k).size

/-- Nesting depth: scalars have depth `0`, arrays and objects are one deeper
than their deepest child (`1` when empty). -/
def depth : Json Scalar Key → Nat
  | .scalar _ => 0
  | .list _n elems => 1 + Finset.univ.sup fun i => (elems i).depth
  | .map keys vals => 1 + keys.attach.sup fun k => (vals k).depth

/-- The multiset of scalar leaves.  A multiset rather than a list: the
extensional form has no canonical traversal order for object members. -/
def scalars : Json Scalar Key → Multiset Scalar
  | .scalar v => {v}
  | .list _n elems => ∑ i, (elems i).scalars
  | .map _keys vals => ∑ k, (vals k).scalars

/-- Apply `f` to every scalar leaf, preserving the tree structure. -/
def mapScalar {T : Type u} (f : Scalar → T) : Json Scalar Key → Json T Key
  | .scalar v => .scalar (f v)
  | .list n elems => .list n fun i => (elems i).mapScalar f
  | .map keys vals => .map keys fun k => (vals k).mapScalar f

/-- Look up a descendant by a path of array indices and object keys.  Returns
`none` on any mismatch: an index step at a non-array, a key step at a
non-object, an out-of-range index, or a missing key. -/
def get? [DecidableEq Key] : Json Scalar Key → KeyedJsonPath Key → Option (Json Scalar Key)
  | j, [] => some j
  | .list n elems, .index i :: rest =>
      if h : i < n then (elems ⟨i, h⟩).get? rest else none
  | .map keys vals, .key k :: rest =>
      if h : k ∈ keys then (vals ⟨k, h⟩).get? rest else none
  | _, _ => none

/-- Congruence for `Json.list` across an equality of lengths, avoiding direct
`HEq` manipulation at use sites. -/
theorem list_congr {n n' : Nat} (h : n = n')
    {elems : Fin n → Json Scalar Key} {elems' : Fin n' → Json Scalar Key}
    (hv : ∀ (i : Nat) (hi : i < n) (hi' : i < n'), elems ⟨i, hi⟩ = elems' ⟨i, hi'⟩) :
    Json.list n elems = Json.list n' elems' := by
  subst h
  have : elems = elems' := funext fun i => by
    obtain ⟨i, hi⟩ := i
    exact hv i hi hi
  rw [this]

/-- Congruence for `Json.map` across an equality of key sets, avoiding direct
`HEq` manipulation at use sites. -/
theorem map_congr {keys keys' : Finset Key} (hk : keys = keys')
    {vals : {k // k ∈ keys} → Json Scalar Key} {vals' : {k // k ∈ keys'} → Json Scalar Key}
    (hv : ∀ (k : Key) (h : k ∈ keys) (h' : k ∈ keys'), vals ⟨k, h⟩ = vals' ⟨k, h'⟩) :
    Json.map keys vals = Json.map keys' vals' := by
  subst hk
  have : vals = vals' := funext fun k => by
    obtain ⟨k, h⟩ := k
    exact hv k h h
  rw [this]

@[simp]
theorem mapScalar_id (j : Json Scalar Key) : j.mapScalar id = j := by
  induction j with
  | scalar v => rfl
  | list n elems ih =>
      simp only [mapScalar]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [mapScalar]
      congr 1
      exact funext ih

theorem mapScalar_comp {T U : Type u} (f : Scalar → T) (g : T → U) (j : Json Scalar Key) :
    (j.mapScalar f).mapScalar g = j.mapScalar (g ∘ f) := by
  induction j with
  | scalar v => rfl
  | list n elems ih =>
      simp only [mapScalar]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [mapScalar]
      congr 1
      exact funext ih

/-- Monadic bind: substitute every scalar leaf by a JSON tree.  `Json` is the
free monad on scalar leaves over the extensional JSON container signature. -/
def bind {T : Type u} : Json Scalar Key → (Scalar → Json T Key) → Json T Key
  | .scalar v, f => f v
  | .list n elems, f => .list n fun i => (elems i).bind f
  | .map keys vals, f => .map keys fun k => (vals k).bind f

@[simp]
theorem bind_scalar {T : Type u} (v : Scalar) (f : Scalar → Json T Key) :
    (Json.scalar v).bind f = f v := rfl

@[simp]
theorem bind_list {T : Type u} (n : Nat) (elems : Fin n → Json Scalar Key)
    (f : Scalar → Json T Key) :
    (Json.list n elems).bind f = .list n fun i => (elems i).bind f := rfl

@[simp]
theorem bind_map {T : Type u} (keys : Finset Key)
    (vals : {k // k ∈ keys} → Json Scalar Key) (f : Scalar → Json T Key) :
    (Json.map keys vals).bind f = .map keys fun k => (vals k).bind f := rfl

/-- Right identity: substituting each leaf by itself changes nothing. -/
@[simp]
theorem bind_pure (j : Json Scalar Key) : j.bind Json.scalar = j := by
  induction j with
  | scalar v => rfl
  | list n elems ih =>
      simp only [bind_list]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [bind_map]
      congr 1
      exact funext ih

/-- Associativity of substitution. -/
theorem bind_assoc {T U : Type u} (j : Json Scalar Key) (f : Scalar → Json T Key)
    (g : T → Json U Key) : (j.bind f).bind g = j.bind fun s => (f s).bind g := by
  induction j with
  | scalar v => rfl
  | list n elems ih =>
      simp only [bind_list]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [bind_map]
      congr 1
      exact funext ih

/-- `mapScalar` is the functorial action induced by `bind`. -/
theorem mapScalar_eq_bind {T : Type u} (f : Scalar → T) (j : Json Scalar Key) :
    j.mapScalar f = j.bind fun s => .scalar (f s) := by
  induction j with
  | scalar v => rfl
  | list n elems ih =>
      simp only [mapScalar, bind_list]
      congr 1
      exact funext ih
  | map keys vals ih =>
      simp only [mapScalar, bind_map]
      congr 1
      exact funext ih

/-- Build an object from an association list with duplicate-free keys; values
are recovered by (unambiguous) key lookup. -/
def ofEntries [DecidableEq Key] (entries : List (Key × Json Scalar Key))
    (h : (entries.map Prod.fst).Nodup) : Json Scalar Key :=
  .map ⟨(entries.map Prod.fst : List Key), h⟩ fun k =>
    ((entries.find? fun e => decide (e.1 = k.1)).get (by
      rw [List.find?_isSome]
      obtain ⟨e, he, hk⟩ := List.mem_map.mp (Multiset.mem_coe.mp k.2)
      exact ⟨e, he, by simp [hk]⟩)).2

/-- The canonical ordered raw representative: arrays are enumerated in index
order and objects in strictly increasing key order.  This is a data-level
choice of representative, not a byte-encoding or hashing requirement. -/
def toRaw [LinearOrder Key] : Json Scalar Key → KeyedRawJson Key Scalar
  | .scalar v => .scalar v
  | .list _n elems => .list (RawSyn.ofList (List.ofFn fun i => (elems i).toRaw))
  | .map keys vals =>
      .map (RawSyn.ofEntries ((keys.sort (· ≤ ·)).attach.map fun k =>
        (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw)))

@[simp]
theorem toRaw_scalar [LinearOrder Key] (v : Scalar) :
    (Json.scalar (Key := Key) v).toRaw = .scalar v := rfl

@[simp]
theorem toRaw_list [LinearOrder Key] (n : Nat) (elems : Fin n → Json Scalar Key) :
    (Json.list n elems).toRaw
      = .list (RawSyn.ofList (List.ofFn fun i => (elems i).toRaw)) := rfl

@[simp]
theorem toRaw_map [LinearOrder Key] (keys : Finset Key)
    (vals : {k // k ∈ keys} → Json Scalar Key) :
    (Json.map keys vals).toRaw
      = .map (RawSyn.ofEntries ((keys.sort (· ≤ ·)).attach.map fun k =>
          (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw))) := rfl

end Json

/-- Extensional JSON values form a monad over their scalars: `pure` is a
scalar leaf and `bind` substitutes leaves. -/
instance : Monad (fun Scalar : Type u => Json Scalar String) where
  pure := Json.scalar
  bind := Json.bind

instance : LawfulMonad (fun Scalar : Type u => Json Scalar String) :=
  LawfulMonad.mk' _
    (fun j => by
      change j.bind (fun s => Json.scalar (id s)) = j
      simp)
    (fun v f => by
      change (Json.scalar v).bind f = f v
      simp)
    (fun j f g => by
      change (j.bind f).bind g = j.bind fun s => (f s).bind g
      exact Json.bind_assoc j f g)

/-- The `Functor` map of `Json` is `Json.mapScalar`. -/
theorem Json.map_eq_mapScalar {S T : Type u} (f : S → T) (j : Json S String) :
    @Functor.map (fun X : Type u => Json X String) _ S T f j =
      Json.mapScalar (Key := String) f j := by
  change j.bind (fun s => Json.scalar (f s)) = j.mapScalar f
  exact (Json.mapScalar_eq_bind f j).symm

/-- On an association list with duplicate-free keys, `find?` at the key of a
member returns exactly that member. -/
theorem find?_entry_of_nodup_keys {Key α : Type*} [DecidableEq Key]
    {entries : List (Key × α)} (hnd : (entries.map Prod.fst).Nodup)
    {e : Key × α} (he : e ∈ entries) :
    (entries.find? fun x => decide (x.1 = e.1)) = some e := by
  induction entries with
  | nil => cases he
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp he with rfl | hmem
      · simp
      · have hne : ¬(a.1 = e.1) := fun hEq =>
          hnd.1 (hEq ▸ List.mem_map.mpr ⟨e, hmem, rfl⟩)
        rw [List.find?_cons_of_neg (by simpa using hne)]
        exact ih hnd.2 hmem

/-- On an association list with duplicate-free keys, extracting the found
entry at the key of a member yields exactly that member. -/
theorem find?_get_entry_of_nodup_keys {Key α : Type*} [DecidableEq Key]
    {entries : List (Key × α)} (hnd : (entries.map Prod.fst).Nodup)
    {e : Key × α} (he : e ∈ entries)
    {p : (entries.find? fun x => decide (x.1 = e.1)).isSome = true} :
    (entries.find? fun x => decide (x.1 = e.1)).get p = e := by
  simp [find?_entry_of_nodup_keys hnd he]

end Nucleus
