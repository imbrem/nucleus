import Nucleus.HolE.Named.Dense.Indexed

/-!
# Finite representations of named expressions

These first representation results deliberately use the generic `HolE` entry
instance.  They establish the list/offset/finite-forest bookkeeping without
committing the later node encoder to a numbering strategy.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u
set_option relaxedAutoImplicit true

def emptyForest : Forest Nat α := ⟨fun _ => none⟩

/-- A tree is a valid one-entry dense arena through the generic tree instance. -/
def singleton (tree : HolE Sig Name) : List (Option (HolE Sig Name)) := [some tree]

@[simp] theorem elaborateList_singleton (tree : HolE Sig Name) (offset : Nat) :
    elaborateList emptyForest (singleton tree) offset = [some tree] := rfl

/-- A list of trees is already a dense arena through the same generic instance. -/
def ofTrees (trees : List (HolE Sig Name)) : List (Option (HolE Sig Name)) :=
  trees.map some

/-- The roots corresponding to a list of trees in an arena at `offset`. -/
def roots (offset : Nat) (trees : List (HolE Sig Name)) : List Nat :=
  (List.range trees.length).map (offset + ·)

theorem roots_length (offset : Nat) (trees : List (HolE Sig Name)) :
    (roots offset trees).length = trees.length := by simp [roots]

/-- The finite forest directly induced by a list. -/
def finiteForestOfTrees (trees : List (HolE Sig Name)) (offset : Nat) :
    FiniteForest Nat (HolE Sig Name) := by
  refine ⟨⟨fun index => if offset ≤ index then trees[index - offset]? else none⟩,
    ⟨List.range (offset + trees.length), ?_⟩⟩
  intro index value lookup
  dsimp only at lookup
  split at lookup
  · rename_i above
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp lookup
    apply List.mem_range.mpr
    have shifted := Nat.add_lt_add_left bounded offset
    simpa [Nat.add_sub_of_le above] using shifted
  · contradiction

/-- Every unsorted named tree has a finite-support forest representation and a
root index which retrieves it. -/
theorem exists_tree_finite_representation (tree : HolE Sig Name) :
    ∃ forest : FiniteForest Nat (HolE Sig Name), ∃ root, forest root = some tree := by
  refine ⟨finiteForestOfTrees [tree] 0, 0, ?_⟩
  rfl

/-- In particular, every sorted named expression has such a representation
after erasing its sort index. -/
theorem Named.exists_finite_representation
    (expression : Named.Expr Sig Name sort) :
    ∃ forest : FiniteForest Nat (HolE Sig Name), ∃ root,
      forest root = some (Unsorted.erase expression) :=
  exists_tree_finite_representation (Unsorted.erase expression)

/-- A whole list is represented by one larger arena together with one root per
input tree. -/
theorem exists_list_representation (trees : List (HolE Sig Name)) :
    ∃ _forest : FiniteForest Nat (HolE Sig Name), ∃ indices : List Nat,
      indices.length = trees.length := by
  exact ⟨finiteForestOfTrees trees 0, roots 0 trees, roots_length 0 trees⟩

end Nucleus.HolE.Named.Unsorted.Dense
