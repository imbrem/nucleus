import Nucleus.Json.Ordered

/-!
# The data-level equivalence between extensional and ordered JSON

The two headline equivalences of issue #541:

- `Σ n, Fin n → A ≃ List A` (`sigmaFinEquivList`, Mathlib's
  `List.equivSigmaTuple`), relating the finite indexed child families of
  `Json` to the sequence children of `RawJson`;
- `Json Scalar Key ≃ OrderedJson Scalar Key Key` (`jsonEquivOrdered`): sorted
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

variable {Key : Type} {Scalar : Type u} [LinearOrder Key]

/-- Arrays-as-families and arrays-as-lists are equivalent; this is Mathlib's
`List.equivSigmaTuple`, restated in the direction used by issue #541. -/
def sigmaFinEquivList (α : Type u) : (Σ n, Fin n → α) ≃ List α :=
  List.equivSigmaTuple.symm

/-- Sorting the `Finset` carried by an already sorted duplicate-free list
returns that list. -/
theorem sort_mk_eq {l : List Key} (hnd : l.Nodup) (hp : l.Pairwise (· ≤ ·)) :
    Finset.sort (⟨(↑l : Multiset Key), (Multiset.coe_nodup).mpr hnd⟩ : Finset Key)
      (· ≤ ·) = l := by
  rw [Finset.sort_mk, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hp

omit [LinearOrder Key] in
/-- An association list is recovered from its key list and a lookup function
that agrees with it on members. -/
theorem pmap_keys_eq {α : Type*} {p : Key → Prop} :
    ∀ {entries : List (Key × α)} (g : ∀ k, p k → α)
      (H : ∀ k ∈ entries.map Prod.fst, p k),
      (∀ e ∈ entries, ∀ hk, g e.1 hk = e.2) →
      (entries.map Prod.fst).pmap (fun k hk => (k, g k hk)) H = entries
  | [], _, _, _ => rfl
  | e :: rest, g, H, hg => by
      simp only [List.map_cons, List.pmap_cons, List.cons.injEq]
      refine ⟨Prod.ext rfl (hg e List.mem_cons_self _), ?_⟩
      exact pmap_keys_eq g (fun k hk => H k (List.mem_cons_of_mem _ hk))
        (fun e' he' hk' => hg e' (List.mem_cons_of_mem _ he') hk')

/-- `List.pmap` only depends on the underlying list, not the membership
proofs. -/
theorem pmap_congr_list {α β : Type*} {p : α → Prop} {l l' : List α} (h : l = l')
    {f : ∀ a, p a → β} {H : ∀ a ∈ l, p a} {H' : ∀ a ∈ l', p a} :
    l.pmap f H = l'.pmap f H' := by
  subst h; rfl

namespace RawSyn

/-- `RawSyn.toJson` only depends on the raw tree, not the well-formedness
proof (which is irrelevant). -/
theorem toJson_congr {r r' : KeyedRawJson Key Scalar} (h : r = r')
    (hr : r.WellFormed) (hr' : r'.WellFormed) : r.toJson hr = r'.toJson hr' := by
  subst h; rfl

end RawSyn

/-- Round trip: converting the canonical raw representative back to the
extensional form is the identity. -/
theorem Json.toJson_toRaw :
    ∀ (j : Json Scalar Key) (h : j.toRaw.WellFormed), j.toRaw.toJson h = j := by
  intro j
  induction j with
  | scalar v =>
      intro h
      simp [RawSyn.toJson]
  | list n elems ih =>
      intro h
      have hW : (RawSyn.list (RawSyn.ofList (List.ofFn fun i =>
          (elems i).toRaw))).WellFormed := Json.toRaw_list n elems ▸ h
      rw [RawSyn.toJson_congr (Json.toRaw_list n elems) h hW, RawSyn.toJson,
        RawSyn.toJsonArr_eq]
      refine Json.list_congr (by simp) fun i hi hi' => ?_
      simp only [List.get_eq_getElem, List.getElem_pmap]
      have hwf : (elems ⟨i, hi'⟩).toRaw.WellFormed := (Json.toRaw_sortedKeys _).wellFormed
      refine (RawSyn.toJson_congr ?_ _ hwf).trans (ih ⟨i, hi'⟩ hwf)
      simp [RawSyn.toList_ofList]
  | map keys vals ih =>
      intro h
      have hW : (RawSyn.map (RawSyn.ofEntries ((keys.sort (· ≤ ·)).attach.map fun k =>
          (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw)))).WellFormed :=
        Json.toRaw_map keys vals ▸ h
      rw [RawSyn.toJson_congr (Json.toRaw_map keys vals) h hW, RawSyn.toJson]
      set E := (keys.sort (· ≤ ·)).attach.map fun k =>
        (k.1, (vals ⟨k.1, (Finset.mem_sort _).mp k.2⟩).toRaw) with hE
      set hWo := ((RawSyn.wellFormed_map_iff (RawSyn.ofEntries E)).mp hW).2 with hhWo
      have hfst : E.map Prod.fst = keys.sort (· ≤ ·) := by
        simp [hE, List.map_map, Function.comp_def]
      have hobj : ((RawSyn.toJsonObj (RawSyn.ofEntries E) hWo).1).map Prod.fst
          = E.map Prod.fst := by
        rw [(RawSyn.toJsonObj _ _).2, RawSyn.toEntries_ofEntries]
      simp only [Json.ofEntries]
      refine Json.map_congr ?_ ?_
      · apply Finset.val_inj.mp
        change (↑(_ : List Key) : Multiset Key) = keys.1
        rw [hobj, hfst]
        exact Finset.sort_eq _ _
      · intro k hk hk'
        have hks : k ∈ keys.sort (· ≤ ·) := (Finset.mem_sort _).mpr hk'
        have hmemE : (k, (vals ⟨k, (Finset.mem_sort _).mp hks⟩).toRaw) ∈ E :=
          List.mem_map.mpr ⟨⟨k, hks⟩, List.mem_attach _ _, rfl⟩
        have hwf : (vals ⟨k, (Finset.mem_sort _).mp hks⟩).toRaw.WellFormed :=
          (Json.toRaw_sortedKeys _).wellFormed
        have hmem : (k, ((vals ⟨k, (Finset.mem_sort _).mp hks⟩).toRaw).toJson hwf)
            ∈ (RawSyn.toJsonObj (RawSyn.ofEntries E) hWo).1 := by
          rw [RawSyn.toJsonObj_eq]
          refine List.mem_pmap.mpr
            ⟨(k, (vals ⟨k, (Finset.mem_sort _).mp hks⟩).toRaw), ?_, rfl⟩
          rw [RawSyn.toEntries_ofEntries]
          exact hmemE
        have hnd : (((RawSyn.toJsonObj (RawSyn.ofEntries E) hWo).1).map Prod.fst).Nodup := by
          rw [hobj, hfst]
          exact Finset.sort_nodup _ _
        exact (congrArg Prod.snd (find?_get_entry_of_nodup_keys hnd hmem)).trans (ih _ hwf)

/-- Round trip: an ordered raw tree is recovered from its extensional value by
re-sorting. -/
theorem RawSyn.toRaw_toJson :
    ∀ (r : KeyedRawJson Key Scalar), r.SortedKeys →
      ∀ (h : r.WellFormed), (r.toJson h).toRaw = r := by
  intro r
  induction r with
  | scalar v =>
      intro _hs h
      simp [RawSyn.toJson]
  | list elems ih =>
      intro hs h
      rw [RawSyn.toJson, Json.toRaw_list]
      refine congrArg RawSyn.list (RawSyn.toList_injective ?_)
      rw [RawSyn.toList_ofList]
      refine List.ext_getElem (by simp [RawSyn.toJsonArr_eq]) fun i h1 h2 => ?_
      simp only [List.getElem_ofFn, RawSyn.toJsonArr_eq, List.get_eq_getElem,
        List.getElem_pmap]
      exact ih _ (List.getElem_mem _)
        ((RawSyn.sortedKeys_arr_iff elems).mp hs _ (List.getElem_mem _)) _
  | map entries ih =>
      intro hs h
      rw [RawSyn.toJson, Json.ofEntries, Json.toRaw_map]
      refine congrArg RawSyn.map (RawSyn.toEntries_injective ?_)
      rw [RawSyn.toEntries_ofEntries]
      set hWo := ((RawSyn.wellFormed_map_iff entries).mp h).2 with hhWo
      set L := (RawSyn.toJsonObj entries hWo).1 with hL
      have hkeysL : L.map Prod.fst = entries.toEntries.map Prod.fst :=
        (RawSyn.toJsonObj entries hWo).2
      have hnd : (L.map Prod.fst).Nodup := by
        rw [hkeysL, ← RawSyn.keys_eq_toEntries_fst]
        exact ((RawSyn.wellFormed_map_iff entries).mp h).1
      have hsort : Finset.sort
          (⟨(↑(L.map Prod.fst) : Multiset Key), (Multiset.coe_nodup).mpr hnd⟩ :
            Finset Key) (· ≤ ·)
          = entries.toEntries.map Prod.fst := by
        rw [Finset.sort_mk]
        conv_lhs => rw [hkeysL]
        rw [Multiset.coe_sort]
        refine List.mergeSort_eq_self _ ?_
        rw [← RawSyn.keys_eq_toEntries_fst]
        exact (((RawSyn.sortedKeys_map_iff entries).mp hs).1).imp le_of_lt
      rw [List.map_attach_eq_pmap, pmap_congr_list hsort (H' := fun a ha => by
        rw [hsort]; exact ha)]
      refine pmap_keys_eq _ _ fun e he hk => ?_
      have hwf : e.2.WellFormed := (RawSyn.wellFormed_obj_iff entries).mp
        ((RawSyn.wellFormed_map_iff entries).mp h).2 e he
      have hmem : (e.1, e.2.toJson hwf) ∈ L := by
        rw [hL, RawSyn.toJsonObj_eq]
        exact List.mem_pmap.mpr ⟨e, he, rfl⟩
      refine (congrArg (fun j => Json.toRaw j.2)
        (find?_get_entry_of_nodup_keys hnd hmem)).trans ?_
      exact ih e he ((RawSyn.sortedKeys_obj_iff entries).mp
        ((RawSyn.sortedKeys_map_iff entries).mp hs).2 e he) hwf

/-- Converting to the canonical ordered representative and back is the
identity. -/
theorem Json.toOrdered_toJson (j : Json Scalar Key) : j.toOrdered.toJson = j :=
  Json.toJson_toRaw j _

/-- Converting an ordered tree to its extensional value and re-sorting is the
identity. -/
theorem OrderedJson.toOrdered_toJson (o : OrderedJson Scalar Key) : o.toJson.toOrdered = o :=
  Subtype.ext (RawSyn.toRaw_toJson o.1 o.2 _)

/-- Extensional JSON values and sorted duplicate-free syntax trees are
equivalent: `OrderedJson` is a faithful data representative of `Json`.  This
is a data-level isomorphism only — it imposes no canonical byte encoding, and
equal extensional values need not have equal content hashes. -/
def jsonEquivOrdered (Scalar : Type u) (Key : Type := String) [LinearOrder Key] :
    Json Scalar Key ≃ OrderedJson Scalar Key where
  toFun := Json.toOrdered
  invFun := OrderedJson.toJson
  left_inv := Json.toOrdered_toJson
  right_inv := OrderedJson.toOrdered_toJson

/-- The canonical raw representative determines the extensional value. -/
theorem Json.toRaw_injective :
    Function.Injective (Json.toRaw (Key := Key) (Scalar := Scalar)) :=
  fun a b h => by
    rw [← Json.toOrdered_toJson a, ← Json.toOrdered_toJson b]
    exact congrArg OrderedJson.toJson (Subtype.ext h)

end Nucleus
