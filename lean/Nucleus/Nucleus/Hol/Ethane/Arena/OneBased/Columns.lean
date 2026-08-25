import Nucleus.Hol.Ethane.Arena.OneBased
import Mathlib.Logic.Relation

/-!
# Dense optional arena columns

This is the representation model for the behavior-preserving column
refactor. Expression rows contain syntax only.  Classifiers and the three
nested equality relations are independent, trailing-null-eliding columns.
The existing `SynFact` arena remains unchanged and is named `subst1` by the
wire view; columns cache only direct relations admitted by checked rules.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

/-- A dense optional column. A missing entry, including every position past
the stored prefix, denotes `none`. -/
abbrev Column (α : Type) := List (Option α)

namespace Column

def get? (column : Column α) (reference : Ref) : Option α :=
  column[(reference.value.toNat - 1)]?.bind id

@[simp] theorem get?_nil (reference : Ref) :
    get? ([] : Column α) reference = none := by
  simp [get?]

/-- Removing trailing nulls is the canonical wire normalization. -/
def normalize : Column α → Column α
  | [] => []
  | none :: tail =>
      let normalized := normalize tail
      if normalized.isEmpty then [] else none :: normalized
  | some value :: tail => some value :: normalize tail

@[simp] theorem normalize_nil : normalize ([] : Column α) = [] := rfl

theorem normalize_cons_some (value : α) (tail : Column α) :
    normalize (some value :: tail) = some value :: normalize tail := rfl

@[simp] theorem normalize_idempotent (column : Column α) :
    normalize (normalize column) = normalize column := by
  induction column with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | some value => simp [normalize, ih]
      | none =>
          simp only [normalize]
          split <;> simp_all [normalize]

end Column

/-- The five optional columns of the first refactor PR. `sort` is deliberately
separate from `conv`; the stacked fusion PR changes only this representation,
not the checked rules that justify its entries. -/
structure Dense where
  defs : List detail.Expr
  eq : Column Ref := []
  synEq : Column Ref := []
  conv : Column Ref := []
  sort : Column Ref := []
  deriving DecidableEq, Repr

namespace Dense

def expr? (dense : Dense) (reference : Ref) : Option detail.Expr :=
  dense.defs[(reference.value.toNat - 1)]?

def row? (dense : Dense) (reference : Ref) : Option detail.Row := do
  let expr ← dense.expr? reference
  return {
    expr
    eq := dense.eq.get? reference
    sort := dense.sort.get? reference
  }

/-- The semantic row view consumed by the pre-column kernel proofs.  This is
not stored or serialized: it is reconstructed by zipping expression-only
`defs` with the semantic-equality and classifier columns.  Syntactic equality
and conversion are separate proof caches and therefore do not occur in a
logical row. -/
def rows (dense : Dense) : List detail.Row :=
  dense.defs.mapIdx fun position expr => {
    expr
    eq := dense.eq[position]?.bind id
    sort := dense.sort[position]?.bind id
  }

@[simp] theorem rows_length (dense : Dense) : dense.rows.length = dense.defs.length := by
  simp [rows]

/-- Positional materialization is observationally identical to separately
looking up the expression, semantic equality, and classifier columns. -/
theorem rows_get? (dense : Dense) (position : Nat) :
    dense.rows[position]? = do
      let expr ← dense.defs[position]?
      return {
        expr
        eq := dense.eq[position]?.bind id
        sort := dense.sort[position]?.bind id
      } := by
  simp only [rows, List.getElem?_mapIdx]
  cases dense.defs[position]? <;> rfl

theorem rows_row? (dense : Dense) (reference : Ref) :
    dense.rows[(reference.value.toNat - 1)]? = dense.row? reference := by
  rw [rows_get?]
  rfl

@[simp] theorem row?_eq (dense : Dense) (reference : Ref)
    (resident : dense.expr? reference ≠ none) :
    (dense.row? reference).bind (·.eq) = dense.eq.get? reference := by
  simp only [row?]
  cases found : dense.expr? reference with
  | none => contradiction
  | some expr => simp

@[simp] theorem row?_sort (dense : Dense) (reference : Ref)
    (resident : dense.expr? reference ≠ none) :
    (dense.row? reference).bind (·.sort) = dense.sort.get? reference := by
  simp only [row?]
  cases found : dense.expr? reference with
  | none => contradiction
  | some expr => simp

/-- A column is resident when it has no non-null member beyond `defs`. Short
columns are valid and mean null for the omitted suffix. -/
def Resident (dense : Dense) (column : Column Ref) : Prop :=
  ∀ position value, column[position]? = some (some value) → position < dense.defs.length

structure WellFormed (dense : Dense) : Prop where
  eq : dense.Resident dense.eq
  synEq : dense.Resident dense.synEq
  conv : dense.Resident dense.conv
  sort : dense.Resident dense.sort

/-- Checked kernels additionally require every equality target to be a local
definition. Raw arena decoding checks only source-column residency; dangling
targets remain harmless raw data because they cannot enter a checked kernel. -/
def TargetsResident (dense : Dense) (column : Column Ref) : Prop :=
  ∀ left right, column.get? left = some right →
    dense.expr? left ≠ none ∧ dense.expr? right ≠ none

structure Checked (dense : Dense) extends dense.WellFormed where
  eqTargets : dense.TargetsResident dense.eq
  synEqTargets : dense.TargetsResident dense.synEq
  convTargets : dense.TargetsResident dense.conv
  sortTargets : dense.TargetsResident dense.sort

end Dense

inductive EqualityColumn
  | syn
  | conv
  | semantic
  deriving DecidableEq, Repr

def Dense.column (dense : Dense) : EqualityColumn → Column Ref
  | .syn => dense.synEq
  | .conv => dense.conv
  | .semantic => dense.eq

def Edge (dense : Dense) (column : EqualityColumn) (left right : Ref) : Prop :=
  (dense.column column).get? left = some right

def Class (dense : Dense) (column : EqualityColumn) : Ref → Ref → Prop :=
  Relation.EqvGen (Edge dense column)

namespace Class

@[refl] theorem refl (reference : Ref) : Class dense column reference reference :=
  Relation.EqvGen.refl reference

@[symm] theorem symm (connected : Class dense column left right) :
    Class dense column right left := Relation.EqvGen.symm _ _ connected

@[trans] theorem trans (leftMiddle : Class dense column left middle)
    (middleRight : Class dense column middle right) :
    Class dense column left right :=
  Relation.EqvGen.trans _ _ _ leftMiddle middleRight

/-- The shared proof obligation for all three Rust union-find columns. -/
theorem sound {R : Ref → Ref → Prop}
    (edgeSound : ∀ {left right}, Edge dense column left right → R left right)
    (refl : ∀ reference, R reference reference)
    (symm : ∀ {left right}, R left right → R right left)
    (trans : ∀ {left middle right}, R left middle → R middle right → R left right)
    (connected : Class dense column left right) : R left right := by
  induction connected with
  | rel left right edge => exact edgeSound edge
  | refl reference => exact refl reference
  | symm left right _ ih => exact symm ih
  | trans left middle right _ _ leftRight middleRight =>
      exact trans leftRight middleRight

end Class

/-- Semantic inclusion of the three cached equivalence relations. -/
structure Refines (dense : Dense) : Prop where
  syn_conv : ∀ {left right}, Class dense .syn left right → Class dense .conv left right
  conv_semantic : ∀ {left right}, Class dense .conv left right →
    Class dense .semantic left right

theorem Refines.syn_semantic (refines : Refines dense)
    (related : Class dense .syn left right) :
    Class dense .semantic left right :=
  refines.conv_semantic (refines.syn_conv related)

/-- Proof-cache storage is representation-orthogonal: column changes do not
alter any occupied, free, or reusable `subst1` slot. -/
structure Arena where
  dense : Dense
  subst1 : List SynSlot := []
  subst1Free : Option SynFactId := none
  deriving DecidableEq, Repr

def Arena.withDense (arena : Arena) (dense : Dense) : Arena :=
  { arena with dense }

@[simp] theorem Arena.withDense_subst1 (arena : Arena) (dense : Dense) :
    (arena.withDense dense).subst1 = arena.subst1 := rfl

@[simp] theorem Arena.withDense_subst1Free (arena : Arena) (dense : Dense) :
    (arena.withDense dense).subst1Free = arena.subst1Free := rfl

end Nucleus.Hol.Ethane.OneBased.Columns
