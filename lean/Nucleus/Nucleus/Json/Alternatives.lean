import Nucleus.Json.Ordered

/-!
# Alternative formulations of sorted duplicate-free JSON syntax

Issue #541 asks for a small Lean prototype comparing formulations of JSON syntax whose
objects are sorted (hence duplicate-free) *by construction*.  Four candidates:

## (a) Nested inductive with `List` children — abandoned

The transcription in the issue's text represents container children as `List`s:

```
inductive RawJson (Scalar : Type u) : Type u where
  | scalar (value : Scalar)
  | list (elems : List (KeyedRawJson String Scalar))
  | map (entries : List (String × KeyedRawJson String Scalar))
```

This works as a plain type, but on this toolchain structural recursion is not inferred
for it: every operation and proof falls back to `sizeOf`-based well-founded recursion,
with the attendant termination annotations.  Worse, its constructor-level proof-carrying
sorted variant

```
inductive OrderedJson (Scalar : Type u) : Type u where
  | scalar (value : Scalar)
  | list (elems : List (OrderedJson Scalar))
  | map (entries : List (String × OrderedJson Scalar))
      (sorted : entries.Pairwise (fun a b => a.1 < b.1))
```

is REJECTED BY THE LEAN KERNEL on this exact toolchain
(leanprover/lean4:v4.33.0-rc1): the nested-inductive compilation fails with
"(kernel) unknown constant" / "(kernel) application type mismatch".  The `sorted` field's
type mentions the recursive type through `List.Pairwise`'s implicit arguments, and the
auxiliary `_nested.*` types produced by the nested-inductive translation do not line up.
A keys-only variant `(sorted : (entries.map Prod.fst).Pairwise (· < ·))` fails the same
way, since the type of `entries.map Prod.fst` still mentions the recursive type.  (Both
failures were verified experimentally on this exact toolchain.)  The main development
originally used this nested form for `RawJson` and was refactored away from it.

## (b) Indexed three-sorted family — the adopted raw representation

`RawSyn` (see `Nucleus.Json.Raw`) replaces the `List` children with two extra grammar
sorts, indexed by `JsonIx`: a value, an array tail, and an object tail.  The children of
each sort are again `RawSyn` terms, so the inductive is indexed but *not* nested, and
ordinary structural recursion works everywhere — no termination boilerplate anywhere in
the development.  The tail sorts are isomorphic to lists (`RawSyn.arrEquivList`,
`RawSyn.objEquivList`), recovering the list views when convenient.  Nothing about the
family constrains keys: member order and duplicate keys are preserved verbatim, matching
RFC 8259 raw syntax.

## (c) Indexed grammar with a sortedness index — works, defined and exercised below

`JsonSyn` below (the issue's `.empty`/`.insert` sketch) takes the same indexed idea as
(b) and additionally threads a strict lower bound `Option String` through the object-tail
sort: every remaining key must exceed the bound, so objects are sorted and duplicate-free
by construction.  It works — adequacy is proved below — and using `Option String` as the
bound avoids assuming `String` has a bottom sentinel, which a last-key index over bare
`String` would need.

## (d) Subtype of the raw syntax — the adopted ordered representation

`Nucleus.OrderedJson Scalar := {r : KeyedRawJson String Scalar // r.SortedKeys}` (see
`Nucleus.Json.Ordered`): a raw tree plus a propositional invariant.  It reuses all of
`RawSyn`'s operations and recursion, `toRaw` is `Subtype.val` (trivially injective), and
proofs transport by proof irrelevance.

## Verdict

Formulation (a) is unavailable outright, and (b) is the adopted raw layer.  Between (c)
and (d) for the ordered form, (d) was adopted because it yields the cleanest round-trip
proofs against the extensional form, while (c) remains equivalent in expressive power:
`JsonSyn.toRaw_sortedKeys` below shows the index invariant of (c) yields exactly the
`SortedKeys` invariant of (d), and is the adequacy half of a routine equivalence
`JsonSyn Scalar .val ≃ OrderedJson Scalar` — the forward map is
`fun s => ⟨s.toRaw, s.toRaw_sortedKeys⟩`, and an inverse follows by recursion over
`SortedKeys` derivations.  That equivalence is intentionally left out of scope for this
prototype.
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
through the `obj low` index.  Formulation (c) of the module docstring. -/
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

/-! ## Functor and monad structure

Like the raw family, `JsonSyn` is a functor and a monad over its scalars —
at every member of the family: substituting scalar leaves never touches keys
or their bound proofs, so the sortedness index is preserved verbatim.  As with
`RawSyn`, `pure` (a scalar leaf) exists only at the value sort, so the
`pure_bind` law is `bind_scalar`; the `bind_pure` and `bind_assoc` laws hold
at every sort, making the array and object tails modules over the value-sort
monad.  A `Monad`/`LawfulMonad` instance for the value sort would mirror the
one on `RawJson`; it is omitted from this prototype. -/

/-- Apply `f` to every scalar leaf, at every sort of the family.  Keys and
their ordering proofs are untouched. -/
def mapScalar {T : Type u} (f : Scalar → T) :
    ∀ {ix : JsonSynIx}, JsonSyn Scalar ix → JsonSyn T ix
  | _, .scalar value => .scalar (f value)
  | _, .list elems => .list (elems.mapScalar f)
  | _, .map entries => .map (entries.mapScalar f)
  | _, .nil => .nil
  | _, .cons head tail => .cons (head.mapScalar f) (tail.mapScalar f)
  | _, .empty => .empty
  | _, .insert key bound value rest => .insert key bound (value.mapScalar f)
      (rest.mapScalar f)

/-- Substitute every scalar leaf by a value, at every sort of the family.  The
sortedness index is preserved because keys are untouched. -/
def bind {T : Type u} :
    ∀ {ix : JsonSynIx}, JsonSyn Scalar ix → (Scalar → JsonSyn T .val) → JsonSyn T ix
  | _, .scalar value, f => f value
  | _, .list elems, f => .list (elems.bind f)
  | _, .map entries, f => .map (entries.bind f)
  | _, .nil, _ => .nil
  | _, .cons head tail, f => .cons (head.bind f) (tail.bind f)
  | _, .empty, _ => .empty
  | _, .insert key bound value rest, f => .insert key bound (value.bind f) (rest.bind f)

/-- Mapping the identity is the identity, at every sort. -/
@[simp] theorem mapScalar_id {ix : JsonSynIx} (s : JsonSyn Scalar ix) :
    s.mapScalar id = s := by
  induction s <;> simp [mapScalar, *]

/-- Mapping composes, at every sort. -/
theorem mapScalar_comp {T U : Type u} (f : Scalar → T) (g : T → U) {ix : JsonSynIx}
    (s : JsonSyn Scalar ix) : (s.mapScalar f).mapScalar g = s.mapScalar (g ∘ f) := by
  induction s <;> simp [mapScalar, *]

/-- Left identity (`pure_bind`), at the value sort where `pure` lives. -/
@[simp] theorem bind_scalar {T : Type u} (value : Scalar) (f : Scalar → JsonSyn T .val) :
    (JsonSyn.scalar value).bind f = f value := by
  simp [bind]

/-- Right identity: substituting each leaf by itself changes nothing, at every
sort. -/
@[simp] theorem bind_pure {ix : JsonSynIx} (s : JsonSyn Scalar ix) :
    s.bind JsonSyn.scalar = s := by
  induction s <;> simp [bind, *]

/-- Associativity of substitution, at every sort. -/
theorem bind_assoc {T U : Type u} {ix : JsonSynIx} (s : JsonSyn Scalar ix)
    (f : Scalar → JsonSyn T .val) (g : T → JsonSyn U .val) :
    (s.bind f).bind g = s.bind fun v => (f v).bind g := by
  induction s <;> simp [bind, *]

/-- `mapScalar` is the functorial action induced by `bind`. -/
theorem mapScalar_eq_bind {T : Type u} (f : Scalar → T) {ix : JsonSynIx}
    (s : JsonSyn Scalar ix) : s.mapScalar f = s.bind fun v => .scalar (f v) := by
  induction s <;> simp [mapScalar, bind, *]

mutual

/-- Convert an indexed value to the main development's raw syntax tree.  The
conversion is sort-by-sort, so each constructor maps directly onto its `RawSyn`
counterpart. -/
def toRaw : JsonSyn Scalar .val → KeyedRawJson String Scalar
  | .scalar value => .scalar value
  | .list elems => .list (toRawArr elems)
  | .map entries => .map (toRawObj entries)

/-- Convert an array tail to a raw array tail. -/
def toRawArr : JsonSyn Scalar .arr → RawSyn String Scalar .arr
  | .nil => .nil
  | .cons head tail => .cons (toRaw head) (toRawArr tail)

/-- Convert an object tail to a raw object tail, forgetting the lower-bound index. -/
def toRawObj : {low : Option String} → JsonSyn Scalar (.obj low) → RawSyn String Scalar .obj
  | _, .empty => .objNil
  | _, .insert key _bound value rest => .objCons key (toRaw value) (toRawObj rest)

end

/-- The keys emitted by an object tail are strictly increasing, and every emitted
key strictly exceeds the index's lower bound.  The second conjunct is the
strengthening that makes the induction go through. -/
theorem toRawObj_keys : ∀ {low : Option String} (t : JsonSyn Scalar (.obj low)),
    (toRawObj t).keys.Pairwise (· < ·) ∧ ∀ l ∈ low, ∀ k ∈ (toRawObj t).keys, l < k
  | _, .empty => by simp [toRawObj]
  | _, .insert key bound value rest => by
      obtain ⟨ihp, ihb⟩ := toRawObj_keys rest
      constructor
      · simp only [toRawObj, RawSyn.keys_objCons, List.pairwise_cons]
        exact ⟨fun k hk => ihb key rfl k hk, ihp⟩
      · simp only [toRawObj, RawSyn.keys_objCons, List.mem_cons]
        rintro l hl k (rfl | hk)
        · exact bound l hl
        · exact lt_trans (bound l hl) (ihb key rfl k hk)

mutual

/-- Adequacy of the sortedness-indexed grammar: the raw tree produced by `toRaw`
satisfies the `SortedKeys` invariant of the adopted formulation (d).  Together with
an inverse by recursion over `SortedKeys` derivations, this yields
`JsonSyn Scalar .val ≃ OrderedJson Scalar`. -/
theorem toRaw_sortedKeys : ∀ (s : JsonSyn Scalar .val), s.toRaw.SortedKeys
  | .scalar value => by simp [toRaw]
  | .list elems => by
      simp only [toRaw, RawSyn.sortedKeys_list_iff]
      exact toRawArr_sortedKeys elems
  | .map entries => by
      simp only [toRaw, RawSyn.sortedKeys_map_iff]
      exact ⟨(toRawObj_keys entries).1, toRawObj_sortedKeys entries⟩

/-- The raw array tail produced from an array tail satisfies `SortedKeys`. -/
theorem toRawArr_sortedKeys : ∀ (t : JsonSyn Scalar .arr), (toRawArr t).SortedKeys
  | .nil => by simp [toRawArr]
  | .cons head tail => by
      simp only [toRawArr, RawSyn.sortedKeys_cons_iff]
      exact ⟨toRaw_sortedKeys head, toRawArr_sortedKeys tail⟩

/-- The raw object tail produced from an object tail satisfies `SortedKeys`. -/
theorem toRawObj_sortedKeys : ∀ {low : Option String} (t : JsonSyn Scalar (.obj low)),
    (toRawObj t).SortedKeys
  | _, .empty => by simp [toRawObj]
  | _, .insert key _bound value rest => by
      simp only [toRawObj, RawSyn.sortedKeys_objCons_iff]
      exact ⟨toRaw_sortedKeys value, toRawObj_sortedKeys rest⟩

end

end JsonSyn

end Nucleus
