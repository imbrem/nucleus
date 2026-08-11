import Nucleus.Json.Ordered

/-!
# The data-level equivalence between extensional and ordered JSON

The two headline equivalences of issue #541:

- `Σ n, Fin n → A ≃ List A` (`sigmaFinEquivList`, Mathlib's
  `List.equivSigmaTuple`), relating the finite indexed child families of
  `Json` to the list children of `RawJson`;
- `Json Scalar ≃ OrderedJson Scalar` (`jsonEquivOrdered`): sorted
  duplicate-free syntax is a faithful data representative of the extensional
  form.  The forward map enumerates key sets in sorted order
  (`Json.toOrdered`); the inverse rebuilds the finite key set and value family
  (`OrderedJson.toJson`).

Both are *data-level* isomorphisms.  They do not canonicalize byte encodings:
an encoder may serialize either raw or ordered syntax, and content hashes
identify the exact chosen bytes, so equal extensional values need not have
equal hashes.
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

/-- Arrays-as-families and arrays-as-lists are equivalent; this is Mathlib's
`List.equivSigmaTuple`, restated in the direction used by issue #541. -/
def sigmaFinEquivList (α : Type u) : (Σ n, Fin n → α) ≃ List α :=
  List.equivSigmaTuple.symm

/-- Sorting the `Finset` carried by an already sorted duplicate-free list
returns that list. -/
theorem sort_mk_eq {l : List String} (hnd : l.Nodup) (hp : l.Pairwise (· ≤ ·)) :
    Finset.sort (⟨(↑l : Multiset String), (Multiset.coe_nodup).mpr hnd⟩ : Finset String)
      (· ≤ ·) = l := by
  rw [Finset.sort_mk, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hp

/-- An association list is recovered from its key list and a lookup function
that agrees with it on members. -/
theorem pmap_keys_eq {α : Type*} {p : String → Prop} :
    ∀ {entries : List (String × α)} (g : ∀ k, p k → α)
      (H : ∀ k ∈ entries.map Prod.fst, p k),
      (∀ e ∈ entries, ∀ hk, g e.1 hk = e.2) →
      (entries.map Prod.fst).pmap (fun k hk => (k, g k hk)) H = entries
  | [], _, _, _ => rfl
  | e :: rest, g, H, hg => by
      simp only [List.map_cons, List.pmap_cons, List.cons.injEq]
      refine ⟨Prod.ext rfl (hg e List.mem_cons_self _), ?_⟩
      exact pmap_keys_eq g (fun k hk => H k (List.mem_cons_of_mem _ hk))
        (fun e' he' hk' => hg e' (List.mem_cons_of_mem _ he') hk')

/-- `RawJson.toJson` only depends on the raw tree, not the well-formedness
proof (which is irrelevant). -/
theorem RawJson.toJson_congr {r r' : RawJson Scalar} (h : r = r')
    (hr : r.WellFormed) (hr' : r'.WellFormed) : r.toJson hr = r'.toJson hr' := by
  subst h; rfl

/-- Round trip: converting the canonical raw representative back to the
extensional form is the identity. -/
theorem Json.toJson_toRaw :
    ∀ (j : Json Scalar) (h : j.toRaw.WellFormed), j.toRaw.toJson h = j := by
  intro j
  induction j with
  | scalar v =>
      intro h
      rw [RawJson.toJson_congr (Json.toRaw_scalar v) h (by exact .scalar v),
        RawJson.toJson.eq_def]
  | list n elems ih =>
      intro h
      rw [RawJson.toJson_congr (Json.toRaw_list n elems) h (Json.toRaw_list n elems ▸ h),
        RawJson.toJson.eq_def]
      refine Json.list_congr (by simp) fun i hi hi' => ?_
      have hwf : (elems ⟨i, hi'⟩).toRaw.WellFormed := (Json.toRaw_sortedKeys _).wellFormed
      have hEq : (List.ofFn fun j => (elems j).toRaw).get ⟨i, hi⟩ = (elems ⟨i, hi'⟩).toRaw := by
        simp
      exact (RawJson.toJson_congr hEq _ hwf).trans (ih ⟨i, hi'⟩ hwf)
  | map keys vals ih =>
      intro h
      rw [RawJson.toJson_congr (Json.toRaw_map keys vals) h (Json.toRaw_map keys vals ▸ h),
        RawJson.toJson.eq_def]
      have hfst : (((keys.sort (· ≤ ·)).attach.map fun k =>
          (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw)).map Prod.fst)
          = keys.sort (· ≤ ·) := by
        simp [List.map_map, Function.comp_def]
      refine Json.map_congr ?_ ?_
      · apply Finset.val_inj.mp
        change (↑(_ : List String) : Multiset String) = keys.1
        rw [hfst]
        exact Finset.sort_eq _ _
      · intro k hk hk'
        have hks : k ∈ keys.sort (· ≤ ·) := (Finset.mem_sort _).mpr hk'
        have hmem : (k, (vals ⟨k, (Finset.mem_sort _).mp hks⟩).toRaw)
            ∈ (keys.sort (· ≤ ·)).attach.map fun x =>
              (x.1, (vals ⟨x.1, (Finset.mem_sort _).mp x.2⟩).toRaw) :=
          List.mem_map.mpr ⟨⟨k, hks⟩, List.mem_attach _ _, rfl⟩
        have hnd : (((keys.sort (· ≤ ·)).attach.map fun x =>
            (x.1, (vals ⟨x.1, (Finset.mem_sort _).mp x.2⟩).toRaw)).map Prod.fst).Nodup := by
          rw [hfst]; exact Finset.sort_nodup _ _
        have hfind := find?_entry_of_nodup_keys hnd hmem
        simp only [hfind, Option.get_some]
        exact ih _ _

/-- `List.pmap` only depends on the underlying list, not the membership
proofs. -/
theorem pmap_congr_list {α β : Type*} {p : α → Prop} {l l' : List α} (h : l = l')
    {f : ∀ a, p a → β} {H : ∀ a ∈ l, p a} {H' : ∀ a ∈ l', p a} :
    l.pmap f H = l'.pmap f H' := by
  subst h; rfl

/-- Round trip: an ordered raw tree is recovered from its extensional value by
re-sorting. -/
theorem RawJson.toRaw_toJson :
    ∀ (r : RawJson Scalar), r.SortedKeys → ∀ (h : r.WellFormed), (r.toJson h).toRaw = r := by
  intro r
  induction r with
  | scalar v =>
      intro _hs h
      rw [RawJson.toJson.eq_def]
      rfl
  | list elems ih =>
      intro hs h
      rw [RawJson.toJson.eq_def, Json.toRaw_list]
      refine congrArg RawJson.list (List.ext_getElem (by simp) fun i h1 h2 => ?_)
      simp only [List.getElem_ofFn]
      refine ((ih _ (List.get_mem _ _) (hs.list_elem _ (List.get_mem _ _)) _).trans ?_)
      simp
  | map entries ih =>
      intro hs h
      rw [RawJson.toJson.eq_def, Json.toRaw_map]
      refine congrArg RawJson.map ?_
      have hsort : Finset.sort
          (⟨(↑(entries.map Prod.fst) : Multiset String), _⟩ : Finset String) (· ≤ ·)
          = entries.map Prod.fst :=
        sort_mk_eq h.map_nodup (hs.map_pairwise.imp le_of_lt)
      rw [List.map_attach_eq_pmap,
        pmap_congr_list hsort (H' := fun a ha => by rw [hsort]; exact ha)]
      refine pmap_keys_eq _ _ fun e he hk => ?_
      have hfind := find?_entry_of_nodup_keys h.map_nodup he
      simp only [hfind, Option.get_some]
      exact ih e he (hs.map_elem e he) _

/-- The two directions of `jsonEquivOrdered`, stated for the bundled
`OrderedJson`. -/
theorem Json.toOrdered_toJson (j : Json Scalar) : j.toOrdered.toJson = j :=
  Json.toJson_toRaw j _

/-- Converting an ordered tree to its extensional value and re-sorting is the
identity. -/
theorem OrderedJson.toOrdered_toJson (o : OrderedJson Scalar) : o.toJson.toOrdered = o :=
  Subtype.ext (RawJson.toRaw_toJson o.1 o.2 _)

/-- Extensional JSON values and sorted duplicate-free syntax trees are
equivalent: `OrderedJson` is a faithful data representative of `Json`.  This
is a data-level isomorphism only — it imposes no canonical byte encoding, and
equal extensional values need not have equal content hashes. -/
def jsonEquivOrdered (Scalar : Type u) : Json Scalar ≃ OrderedJson Scalar where
  toFun := Json.toOrdered
  invFun := OrderedJson.toJson
  left_inv := Json.toOrdered_toJson
  right_inv := OrderedJson.toOrdered_toJson

/-- The canonical raw representative determines the extensional value. -/
theorem Json.toRaw_injective : Function.Injective (Json.toRaw (Scalar := Scalar)) :=
  fun a b h => by
    rw [← Json.toOrdered_toJson a, ← Json.toOrdered_toJson b]
    exact congrArg OrderedJson.toJson (Subtype.ext h)

end Nucleus
