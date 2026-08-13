import Nucleus.SExpr.Basic
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Generic cons cells and indexed cell tables

`ConsCell ι` records exactly two pointers. `Cell2 ι α` adds atom cells.
Functional tables permit arbitrary, infinite, or domain-specific index types.
List tables are preferable for compact storage and canonical enumeration; a
functional table becomes a list only after choosing a finite ordering.
-/

namespace Nucleus.SExpr2

universe u v

/-- A binary cell containing two indices of the same pointer type. -/
structure ConsCell (ι : Type u) where
  car : ι
  cdr : ι
  deriving DecidableEq, Repr

/-- An atom or a cons cell over an arbitrary index type. -/
inductive Cell2 (ι : Type u) (α : Type v) where
  | atom (value : α)
  | cons (cell : ConsCell ι)
  deriving DecidableEq, Repr

namespace Cell2

def mapIndex (f : ι → κ) : Cell2 ι α → Cell2 κ α
  | .atom value => .atom value
  | .cons cell => .cons ⟨f cell.car, f cell.cdr⟩

def mapAtom (f : α → β) : Cell2 ι α → Cell2 ι β
  | .atom value => .atom (f value)
  | .cons cell => .cons cell

end Cell2

/-- A total table over an arbitrary index space. -/
abbrev CellTable (ι : Type u) (α : Type v) := ι → Cell2 ι α

/-- An atomless total table. Every index denotes a cons cell, so its natural
semantics lives only in the greatest fixpoint. -/
abbrev ConsTable (ι : Type u) := ι → ConsCell ι

namespace CellTable

/-- Fuelled least-fixpoint interpretation of a total indexed table. Cycles do
not produce finite trees and therefore exhaust every finite gas supply. -/
def deref (table : CellTable ι α) : Nat → ι → Option (Tree2 α)
  | 0, _ => none
  | gas + 1, index =>
      match table index with
      | .atom value => some (.atom value)
      | .cons cell => .cons <$> deref table gas cell.car <*> deref table gas cell.cdr

/-- Reindex a total cell table along an index equivalence. -/
def reindex (equiv : ι ≃ κ) (table : CellTable ι α) : CellTable κ α :=
  fun index => (table (equiv.symm index)).mapIndex equiv

@[simp] theorem reindex_refl (table : CellTable ι α) :
    reindex (Equiv.refl ι) table = table := by
  funext index
  cases h : table index with
  | atom => simp [reindex, Cell2.mapIndex, h]
  | cons cell => cases cell; simp [reindex, Cell2.mapIndex, h]

/-- Reindexing is an equivalence of functional-table representations. -/
def reindexEquiv (equiv : ι ≃ κ) : CellTable ι α ≃ CellTable κ α where
  toFun := reindex equiv
  invFun := reindex equiv.symm
  left_inv table := by
    funext index
    cases h : table index with
    | atom => simp [reindex, Cell2.mapIndex, h]
    | cons cell => cases cell; simp [reindex, Cell2.mapIndex, h]
  right_inv table := by
    funext index
    cases h : table index with
    | atom => simp [reindex, Cell2.mapIndex, h]
    | cons cell => cases cell; simp [reindex, Cell2.mapIndex, h]

/-- With a chosen enumeration `ι ≃ Fin n`, a functional table is equivalent
to a length-indexed list. Different enumerations generally produce different
list layouts with isomorphic pointer semantics. -/
def equivVector (equiv : ι ≃ Fin n) :
    CellTable ι α ≃ List.Vector (Cell2 (Fin n) α) n :=
  (reindexEquiv equiv).trans {
    toFun := fun table => ⟨List.ofFn table, by simp⟩
    invFun := fun values i => values.1[i.1]'(by
      rw [values.2]
      exact i.2)
    left_inv := by intro table; funext i; simp
    right_inv := by
      intro values
      apply Subtype.ext
      simpa [values.2] using List.ofFn_get (l := values.1) }

end CellTable
end Nucleus.SExpr2
