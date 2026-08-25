import Nucleus.Hol.Ethane.Arena.OneBased
import Mathlib.Logic.Relation

/-!
# Dense optional arena columns

This is the representation model for the behavior-preserving column
refactor. Expression rows contain syntax only.  The conversion column fuses
same-category union-find parents with cross-category classifiers; semantic
and syntactic equality remain independent, trailing-null-eliding columns.
The existing `SynFact` arena remains unchanged and is named `subst1` by the
wire view; columns cache only direct relations admitted by checked rules.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

/-- A dense optional column. A missing entry, including every position past
the stored prefix, denotes `none`. -/
abbrev Column := Nucleus.Hol.Ethane.OneBased.Column

namespace Column

abbrev get? (column : Column α) (reference : Ref) : Option α :=
  Nucleus.Hol.Ethane.OneBased.Column.get? column reference
abbrev Decreases (column : Column Ref) : Prop :=
  Nucleus.Hol.Ethane.OneBased.Column.Decreases column
abbrev normalize (column : Column α) : Column α :=
  Nucleus.Hol.Ethane.OneBased.Column.normalize column

theorem normalize_nil : normalize ([] : Column α) = [] :=
  Nucleus.Hol.Ethane.OneBased.Column.normalize_nil

theorem normalize_cons_some (value : α) (tail : Column α) :
    normalize (some value :: tail) = some value :: normalize tail :=
  Nucleus.Hol.Ethane.OneBased.Column.normalize_cons_some value tail

theorem normalize_idempotent (column : Column α) :
    normalize (normalize column) = normalize column :=
  Nucleus.Hol.Ethane.OneBased.Column.normalize_idempotent column

theorem getElem?_normalize_bind (column : Column α) (position : Nat) :
    (normalize column)[position]?.bind id = column[position]?.bind id :=
  Nucleus.Hol.Ethane.OneBased.Column.getElem?_normalize_bind column position

theorem get?_normalize (column : Column α) (reference : Ref) :
    get? (normalize column) reference = get? column reference :=
  Nucleus.Hol.Ethane.OneBased.Column.get?_normalize column reference

end Column

/-- Compatibility namespace for invariants over the base arena's storage. -/
abbrev Dense := Nucleus.Hol.Ethane.OneBased.Dense

namespace Dense

abbrev expr? (dense : Dense) (reference : Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.expr? dense reference
abbrev tagSort? (dense : Dense) (reference : Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense reference
abbrev classifierSort? (sort : TagSort) :=
  Nucleus.Hol.Ethane.OneBased.Dense.classifierSort? sort
abbrev classifierAt? (dense : Dense) (fuel : Nat) (reference : Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? dense fuel reference
abbrev classifier? (dense : Dense) (reference : Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.classifier? dense reference
abbrev classifierFrom? (dense : Dense) (fuel : Nat) (sort : TagSort)
    (target : Option Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.classifierFrom? dense fuel sort target
abbrev row? (dense : Dense) (reference : Ref) :=
  Nucleus.Hol.Ethane.OneBased.Dense.row? dense reference
abbrev rows (dense : Dense) := Nucleus.Hol.Ethane.OneBased.Dense.rows dense

theorem classifierAt?_eq_classifierFrom? (dense : Dense) (fuel : Nat)
    (reference : Ref) (expr : detail.Expr)
    (found : dense.expr? reference = some expr) :
    dense.classifierAt? fuel reference =
      dense.classifierFrom? fuel expr.tag.sort (dense.conv.get? reference) :=
  Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?_eq_classifierFrom?
    dense fuel reference expr found

@[simp] theorem rows_length (dense : Dense) : dense.rows.length = dense.defs.length := by
  exact Nucleus.Hol.Ethane.OneBased.Dense.rows_length dense

/-- Positional syntax lookup is the underlying definition lookup. -/
theorem rows_get? (dense : Dense) (position : Nat) :
    dense.rows[position]? = dense.defs[position]? :=
  Nucleus.Hol.Ethane.OneBased.Dense.rows_get? dense position

theorem rows_row? (dense : Dense) (reference : Ref) :
    dense.rows[(reference.value.toNat - 1)]? = dense.row? reference :=
  Nucleus.Hol.Ethane.OneBased.Dense.rows_row? dense reference

/-- A column is resident when it has no non-null member beyond `defs`. Short
columns are valid and mean null for the omitted suffix. -/
def Resident (dense : Dense) (column : Column Ref) : Prop :=
  ∀ position value, column[position]? = some (some value) → position < dense.defs.length

structure WellFormed (dense : Dense) : Prop where
  eq : dense.Resident dense.eq
  synEq : dense.Resident dense.synEq
  conv : dense.Resident dense.conv

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

end Dense

/-! ## Category-sensitive meaning of the fused conversion column -/

def SameCategory (dense : Dense) (left right : Ref) : Prop :=
  ∃ category, dense.tagSort? left = some category ∧ dense.tagSort? right = some category

/-- The raw cell has one representation but two disjoint meanings. -/
inductive RawLink (dense : Dense) (left right : Ref) : Prop
  | conversion (raw : dense.conv.get? left = some right)
      (same : SameCategory dense left right)
  | classifier (raw : dense.conv.get? left = some right)
      (different : ¬ SameCategory dense left right)

def ConvEdge (dense : Dense) (left right : Ref) : Prop :=
  dense.conv.get? left = some right ∧ SameCategory dense left right

def ClassifierEdge (dense : Dense) (value classifier : Ref) : Prop :=
  dense.conv.get? value = some classifier ∧ ¬ SameCategory dense value classifier

theorem convEdge_classifierEdge_disjoint :
    ¬ (ConvEdge dense left right ∧ ClassifierEdge dense left right) := by
  rintro ⟨⟨_, same⟩, ⟨_, different⟩⟩
  exact different same

def ConvClass (dense : Dense) : Ref → Ref → Prop :=
  Relation.EqvGen (ConvEdge dense)

/-- A classifier belongs to a conversion class when one member's root cell
points across the category boundary to it. This relational definition is
independent of path-compression shape. -/
def HasClassifier (dense : Dense) (value classifier : Ref) : Prop :=
  ∃ root, ConvClass dense value root ∧ ClassifierEdge dense root classifier

theorem HasClassifier.of_edge (edge : ClassifierEdge dense value classifier) :
    HasClassifier dense value classifier :=
  ⟨value, Relation.EqvGen.refl value, edge⟩

theorem HasClassifier.of_conv (connected : ConvClass dense left right)
    (classified : HasClassifier dense right classifier) :
    HasClassifier dense left classifier := by
  obtain ⟨root, rightRoot, edge⟩ := classified
  exact ⟨root, Relation.EqvGen.trans _ _ _ connected rightRoot, edge⟩

/-- Executable classifier traversal is intrinsically sound: whenever it
returns a classifier, the fused graph relationally classifies the source by
that reference. This direction needs no checked-kernel invariant. -/
theorem Dense.classifierAt?_sound (dense : Dense) (fuel : Nat)
    (value classifier : Ref)
    (checked : dense.Checked) (resident : dense.expr? value ≠ none)
    (found : dense.classifierAt? fuel value = some classifier) :
    HasClassifier dense value classifier := by
  induction fuel generalizing value with
  | zero => simp [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?] at found
  | succ fuel ih =>
      simp only [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?] at found
      cases raw : dense.conv.get? value with
      | none => simp [raw] at found
      | some target =>
          rw [raw] at found
          change (if dense.tagSort? value = dense.tagSort? target then
            dense.classifierAt? fuel target
          else if (dense.tagSort? value).bind
            Nucleus.Hol.Ethane.OneBased.Dense.classifierSort? = dense.tagSort? target then
            some target else none) = some classifier at found
          have targetResident := (checked.convTargets value target raw).2
          by_cases same : dense.tagSort? value = dense.tagSort? target
          · rw [if_pos same] at found
            apply HasClassifier.of_conv (Relation.EqvGen.rel _ _ ⟨raw, ?_⟩)
              (ih target targetResident found)
            cases sourceCategory : dense.tagSort? value with
            | none =>
                have missing : dense.expr? value = none := by
                  cases expression : dense.expr? value with
                  | none => rfl
                  | some expr =>
                      simp [Nucleus.Hol.Ethane.OneBased.Dense.tagSort?, expression]
                        at sourceCategory
                exact (resident missing).elim
            | some category =>
                exact ⟨category, sourceCategory, same ▸ sourceCategory⟩
          · rw [if_neg same] at found
            split at found
            · rename_i classifierShape
              have classifierEq : target = classifier := Option.some.inj found
              subst target
              exact HasClassifier.of_edge ⟨raw, fun sameCategory => same <| by
                obtain ⟨category, valueCategory, classifierCategory⟩ := sameCategory
                rw [valueCategory, classifierCategory]⟩
            · simp at found

theorem Dense.classifier?_sound (dense : Dense) (value classifier : Ref)
    (checked : dense.Checked) (resident : dense.expr? value ≠ none)
    (found : dense.classifier? value = some classifier) :
    HasClassifier dense value classifier :=
  dense.classifierAt?_sound (dense.defs.length + 1) value classifier
    checked resident found

/-- Category transition discipline of the fused cell: conversion links stay
within a category; classifiers are exactly `tm → ty` or `ty → kind`.
Kinds therefore never carry classifiers. -/
def ClassifierShape (dense : Dense) (value classifier : Ref) : Prop :=
  (dense.tagSort? value = some .tm ∧ dense.tagSort? classifier = some .ty) ∨
  (dense.tagSort? value = some .ty ∧ dense.tagSort? classifier = some .kind)

structure FusedChecked (dense : Dense) extends dense.Checked where
  eqDecreases : dense.eq.Decreases
  synEqDecreases : dense.synEq.Decreases
  convDecreases : dense.conv.Decreases
  classifierShape : ∀ {value classifier}, ClassifierEdge dense value classifier →
    ClassifierShape dense value classifier

theorem ConvClass.category_eq (connected : ConvClass dense left right) :
    dense.tagSort? left = dense.tagSort? right := by
  induction connected with
  | rel left right edge =>
      rcases edge.2 with ⟨category, leftCategory, rightCategory⟩
      rw [leftCategory, rightCategory]
  | refl => rfl
  | symm left right _ ih => exact ih.symm
  | trans left middle right _ _ leftMiddle middleRight =>
      exact leftMiddle.trans middleRight

theorem FusedChecked.kind_has_no_classifier (checked : FusedChecked dense)
    (kind : dense.tagSort? value = some .kind) :
    ¬ HasClassifier dense value classifier := by
  rintro ⟨root, connected, edge⟩
  have rootKind : dense.tagSort? root = some .kind := by
    rw [← connected.category_eq]
    exact kind
  rcases checked.classifierShape edge with shape | shape
  · rw [rootKind] at shape
    cases shape.1
  · rw [rootKind] at shape
    cases shape.1

/-- A kind is inhabited in the arena exactly when some type-family class is
classified by it. This is the fused replacement for a dedicated kind-sort
bit/column. -/
def ValidKind (dense : Dense) (kind : Ref) : Prop :=
  ∃ family, HasClassifier dense family kind

theorem validKind_iff_exists_classifier :
    ValidKind dense kind ↔ ∃ family, HasClassifier dense family kind := Iff.rfl

theorem ConvClass.mono
    (edges : ∀ {left right}, ConvEdge before left right → ConvClass after left right)
    (connected : ConvClass before left right) : ConvClass after left right := by
  induction connected with
  | rel left right relation => exact edges relation
  | refl reference => exact Relation.EqvGen.refl reference
  | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right _ _ leftMiddle middleRight =>
      exact Relation.EqvGen.trans _ _ _ leftMiddle middleRight

/-- Abstract path compression theorem: replacing parent edges by edges inside
the same old conversion classes, while retaining classifier edges, preserves
all old classifications. This is the exact obligation of the mutable Rust
compression loop. -/
theorem compression_preserves_classifier
    (classes : ∀ {left right}, ConvEdge before left right →
      ConvClass after left right)
    (classifiers : ∀ {value classifier}, ClassifierEdge before value classifier →
      ClassifierEdge after value classifier)
    (classified : HasClassifier before value classifier) :
    HasClassifier after value classifier := by
  obtain ⟨root, connected, edge⟩ := classified
  exact ⟨root, connected.mono classes, classifiers edge⟩

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
  match column with
  | .syn => dense.synEq.get? left = some right
  | .conv => ConvEdge dense left right
  | .semantic => dense.eq.get? left = some right

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
