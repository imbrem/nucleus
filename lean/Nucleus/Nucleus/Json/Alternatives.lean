import Nucleus.Json.Ordered

/-!
# Alternative formulations of sorted duplicate-free JSON syntax

Issue #541 asks for a small Lean prototype comparing formulations of JSON syntax whose
objects are sorted (hence duplicate-free) *by construction*.  Three candidates:

## (a) Constructor-level proof-carrying sorted list — rejected by the kernel

The naive transcription attaches the sortedness proof directly to the `map` constructor:

```
inductive OrderedJson (Scalar : Type u) : Type u where
  | scalar (value : Scalar)
  | list (elems : List (OrderedJson Scalar))
  | map (entries : List (String × OrderedJson Scalar))
      (sorted : entries.Pairwise (fun a b => a.1 < b.1))
```

This is REJECTED BY THE LEAN KERNEL on this exact toolchain
(leanprover/lean4:v4.33.0-rc1): the nested-inductive compilation fails with
"(kernel) unknown constant" / "(kernel) application type mismatch".  The `sorted` field's
type mentions the recursive type through `List.Pairwise`'s implicit arguments, and the
auxiliary `_nested.*` types produced by the nested-inductive translation do not line up.
A keys-only variant `(sorted : (entries.map Prod.fst).Pairwise (· < ·))` fails the same
way, since the type of `entries.map Prod.fst` still mentions the recursive type.  (Both
failures were verified experimentally on this exact toolchain.)

## (b) Indexed grammar `JsonSyn` — works, defined and exercised below

Constructor-level enforcement via an index carrying a strict lower bound on object keys.
The grammar has three sorts (`JsonSynIx`): a value, an array tail, and an object tail
indexed by an `Option String` lower bound that every remaining key must exceed.  Because
the children of each sort are again `JsonSyn` terms (not `List`s of them), the inductive
is indexed but *not* nested, and the kernel accepts it.

It works, but at a cost: an index type, three grammar sorts, and conversion boilerplate;
recursion principles quantify over indices, and every lemma about object tails must be
stated for an arbitrary lower bound.  Using `Option String` as the bound avoids assuming
`String` has a bottom sentinel — a last-key index over bare `String` would need one.

## (c) Subtype of the raw syntax — the chosen form

`Nucleus.OrderedJson Scalar := {r : RawJson Scalar // r.SortedKeys}` (see
`Nucleus.Json.Ordered`): a raw tree plus a propositional invariant.  It reuses
`RawJson`'s recursion/induction and all its operations, `toRaw` is `Subtype.val`
(trivially injective), and proofs transport by proof irrelevance.  Chosen because it
yields the cleanest recursion and round-trip proofs against the extensional form.

## Verdict

Formulation (a) is unavailable outright.  Formulations (b) and (c) are equivalent in
expressive power: `JsonSyn.toRaw_sortedKeys` below shows the index invariant of (b)
yields exactly the `SortedKeys` invariant of (c), so a bundling equivalence
`JsonSyn Scalar .val ≃ OrderedJson Scalar` is routine — the forward map is
`fun s => ⟨s.toRaw, s.toRaw_sortedKeys⟩`, and an inverse follows by recursion over
`SortedKeys` derivations.  That equivalence is intentionally left out of scope for this
prototype; (c) was adopted for the main development because it avoids (b)'s index
plumbing while keeping the same guarantees.
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

/-- Grammar sorts for the indexed syntax: a value, an array tail, or an object
tail whose keys must all exceed the given strict lower bound. -/
inductive JsonSynIx where
  /-- A single JSON value. -/
  | val
  /-- A (tail of an) array of values. -/
  | arr
  /-- A (tail of an) object whose remaining keys must all strictly exceed `low`;
  `none` imposes no bound. -/
  | obj (low : Option String)
  deriving DecidableEq, Repr

/-- Indexed sorted-object JSON syntax: objects enforce strictly increasing keys
through the `obj low` index.  Formulation (b) of the module docstring. -/
inductive JsonSyn (Scalar : Type u) : JsonSynIx → Type u where
  /-- A scalar leaf. -/
  | scalar (value : Scalar) : JsonSyn Scalar .val
  /-- An array value, built from an array tail. -/
  | list (elems : JsonSyn Scalar .arr) : JsonSyn Scalar .val
  /-- An object value, built from an unbounded object tail. -/
  | map (entries : JsonSyn Scalar (.obj none)) : JsonSyn Scalar .val
  /-- The empty array tail. -/
  | nil : JsonSyn Scalar .arr
  /-- Prepend a value to an array tail. -/
  | cons (head : JsonSyn Scalar .val) (tail : JsonSyn Scalar .arr) : JsonSyn Scalar .arr
  /-- The empty object tail, at any lower bound. -/
  | empty {low : Option String} : JsonSyn Scalar (.obj low)
  /-- Prepend an entry to an object tail: the new key must exceed the current lower
  bound, and the rest of the tail is bounded below by the new key.  This is where
  sortedness is enforced by construction. -/
  | insert {low : Option String} (key : String)
      (bound : ∀ l ∈ low, l < key)
      (value : JsonSyn Scalar .val) (rest : JsonSyn Scalar (.obj (some key))) :
      JsonSyn Scalar (.obj low)

namespace JsonSyn

mutual

/-- Convert an indexed value to the main development's raw syntax tree. -/
def toRaw : JsonSyn Scalar .val → RawJson Scalar
  | .scalar value => .scalar value
  | .list elems => .list (toRawList elems)
  | .map entries => .map (toRawEntries entries)

/-- Convert an array tail to its list of raw elements. -/
def toRawList : JsonSyn Scalar .arr → List (RawJson Scalar)
  | .nil => []
  | .cons head tail => toRaw head :: toRawList tail

/-- Convert an object tail to its list of raw key–value entries. -/
def toRawEntries : {low : Option String} → JsonSyn Scalar (.obj low) →
    List (String × RawJson Scalar)
  | _, .empty => []
  | _, .insert key _bound value rest => (key, toRaw value) :: toRawEntries rest

end

/-- The keys emitted by an object tail are strictly increasing, and every emitted
entry's key strictly exceeds the index's lower bound.  The second conjunct is the
strengthening that makes the induction go through. -/
theorem toRawEntries_keys : ∀ {low : Option String} (t : JsonSyn Scalar (.obj low)),
    (t.toRawEntries.map Prod.fst).Pairwise (· < ·) ∧
      ∀ l ∈ low, ∀ p ∈ t.toRawEntries, l < p.1
  | _, .empty => by simp [toRawEntries]
  | _, .insert key bound value rest => by
      obtain ⟨ihp, ihb⟩ := toRawEntries_keys rest
      constructor
      · simp only [toRawEntries, List.map_cons, List.pairwise_cons]
        refine ⟨fun k hk => ?_, ihp⟩
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
        exact ihb key rfl p hp
      · simp only [toRawEntries, List.mem_cons]
        rintro l hl p (rfl | hp)
        · exact bound l hl
        · exact lt_trans (bound l hl) (ihb key rfl p hp)

mutual

/-- Adequacy of the indexed grammar: the raw tree produced by `toRaw` satisfies the
`SortedKeys` invariant of the chosen formulation (c).  Together with an inverse by
recursion over `SortedKeys`, this yields `JsonSyn Scalar .val ≃ OrderedJson Scalar`. -/
theorem toRaw_sortedKeys : ∀ (s : JsonSyn Scalar .val), s.toRaw.SortedKeys
  | .scalar value => by
      simp only [toRaw]
      exact .scalar value
  | .list elems => by
      simp only [toRaw]
      exact .list (toRawList_sortedKeys elems)
  | .map entries => by
      simp only [toRaw]
      exact .map (toRawEntries_keys entries).1 (toRawEntries_sortedKeys entries)

/-- Every raw element produced from an array tail satisfies `SortedKeys`. -/
theorem toRawList_sortedKeys : ∀ (t : JsonSyn Scalar .arr), ∀ e ∈ t.toRawList, e.SortedKeys
  | .nil => by simp [toRawList]
  | .cons head tail => by
      simp only [toRawList, List.mem_cons]
      rintro e (rfl | he)
      · exact toRaw_sortedKeys head
      · exact toRawList_sortedKeys tail e he

/-- Every raw entry value produced from an object tail satisfies `SortedKeys`. -/
theorem toRawEntries_sortedKeys : ∀ {low : Option String} (t : JsonSyn Scalar (.obj low)),
    ∀ e ∈ t.toRawEntries, e.2.SortedKeys
  | _, .empty => by simp [toRawEntries]
  | _, .insert key _bound value rest => by
      simp only [toRawEntries, List.mem_cons]
      rintro e (rfl | he)
      · exact toRaw_sortedKeys value
      · exact toRawEntries_sortedKeys rest e he

end

end JsonSyn

end Nucleus
