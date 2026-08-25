import Nucleus.Hol.Ethane.Arena.OneBased.FusedConvUnionProofs

/-!
# Ordered direct-fact cache union

`Kernel::union_syn_fact` mutates three increasingly fine equality caches in
this exact order:

1. semantic equality;
2. fused conversion/classification;
3. syntactic equality, only for a `SynRel.syn` fact.

The order is logically significant because Rust mutations are observable even
when a later fallible step returns an error.  This file gives each stage an
explicit transition certificate and proves that the checked representation and
the refinement chain survive every successful or failed prefix.  The concrete
union-find/path proofs discharge these certificates; this layer proves their
composition once, independently of storage details.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

/-- The callback used by fused conversion union may answer `true` only for a
pair already connected in the semantic column of the state being queried. -/
def EquivalentSound (dense : Dense) (equivalent : Dense.Equivalent) : Prop :=
  ∀ left right, equivalent left right = true →
    Class dense .semantic left right

/-- Soundness is required only for the classifier pair actually queried by
`union_conv`, not for every pair the callback could hypothetically receive. -/
def EquivalentPairSound (dense : Dense) (equivalent : Dense.Equivalent)
    (left right : Ref) : Prop :=
  ∀ {leftClassifier rightClassifier},
    dense.checkedClassifier? left = some leftClassifier →
    dense.checkedClassifier? right = some rightClassifier →
    equivalent leftClassifier rightClassifier = true →
    Class dense .semantic leftClassifier rightClassifier

/-- A classifier route which does not enter the overwritten conversion
component can be read backwards through a one-cell update. -/
private theorem Dense.RootedClassifierRoute.restore_of_not_connected
    (update : Dense.ConvCellUpdate before after child (some parent))
    (route : Dense.RootedClassifierRoute after classifier root value length)
    (outside : ¬ ConvClass before value child) :
    Dense.RootedClassifierRoute before classifier root value length := by
  revert outside
  induction route with
  | terminal edge =>
      intro outside
      have rootNe : root ≠ child := by
        intro rootEq
        subst root
        exact outside (Relation.EqvGen.refl _)
      exact .terminal (update.classifierEdge_before_of_ne rootNe edge)
  | @step source next tailLength edge tail ih =>
      intro outside
      have sourceNe : source ≠ child := by
        intro sourceEq
        subst source
        exact outside (Relation.EqvGen.refl _)
      have oldEdge := update.convEdge_before_of_ne sourceNe edge
      have tailOutside : ¬ ConvClass before next child := by
        intro connected
        exact outside (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ oldEdge) connected)
      exact .step oldEdge (ih tailOutside)

/-- Linking two same-category roots preserves whether each resident value has
a classifier, provided both components already expose their terminal
classifier edges. -/
private theorem Dense.ConvCellUpdate.hasClassifier_exists_iff
    (update : Dense.ConvCellUpdate before after child (some parent))
    (same : SameCategory before child parent)
    (beforeChecked : FusedChecked before)
    (afterChecked : FusedChecked after)
    (resident : before.expr? value ≠ none)
    (childEdge : ClassifierEdge before child childClassifier)
    (parentEdge : ClassifierEdge after parent parentClassifier) :
    (∃ classifier, HasClassifier after value classifier) ↔
      ∃ classifier, HasClassifier before value classifier := by
  constructor
  · rintro ⟨classifier, classified⟩
    by_cases inside : ConvClass before value child
    · exact ⟨childClassifier,
        HasClassifier.of_conv inside (HasClassifier.of_edge childEdge)⟩
    · have afterResident : after.expr? value ≠ none := by
        simpa [update.expr?_eq] using resident
      obtain ⟨length, _bound, route⟩ :=
        HasClassifier.route afterChecked afterResident classified
      obtain ⟨root, route⟩ := route.rooted
      exact ⟨classifier,
        (route.restore_of_not_connected update inside).hasClassifier⟩
  · rintro ⟨classifier, classified⟩
    by_cases inside : ConvClass before value child
    · obtain ⟨length, _bound, route⟩ :=
        HasClassifier.route beforeChecked resident classified
      have rooted := route.rooted_at_of_connected inside childEdge
      obtain ⟨newLength, _bound, spliced⟩ :=
        Dense.RootedClassifierRoute.splice_child update same childEdge
          (.terminal parentEdge) rooted
      exact ⟨parentClassifier, spliced.hasClassifier⟩
    · obtain ⟨length, _bound, route⟩ :=
        HasClassifier.route beforeChecked resident classified
      obtain ⟨root, rooted⟩ := route.rooted
      exact ⟨classifier,
        (rooted.preserve_of_not_connected update inside).hasClassifier⟩

/-- Joining a kind root cannot create or destroy classifier availability:
values in the kind component cannot be classified, and every other route is
cell-for-cell unchanged. -/
private theorem Dense.ConvCellUpdate.hasClassifier_exists_iff_of_kind
    (update : Dense.ConvCellUpdate before after child (some parent))
    (beforeChecked : FusedChecked before) (afterChecked : FusedChecked after)
    (resident : before.expr? value ≠ none)
    (childKind : before.tagSort? child = some .kind) :
    (∃ classifier, HasClassifier after value classifier) ↔
      ∃ classifier, HasClassifier before value classifier := by
  have afterResident : after.expr? value ≠ none := by
    simpa [update.expr?_eq] using resident
  constructor
  · rintro ⟨classifier, classified⟩
    have outside : ¬ ConvClass before value child := by
      intro inside
      have valueKind : after.tagSort? value = some .kind := by
        rw [update.tagSort?_eq, inside.category_eq, childKind]
      exact afterChecked.kind_has_no_classifier valueKind classified
    obtain ⟨length, _bound, route⟩ :=
      HasClassifier.route afterChecked afterResident classified
    obtain ⟨root, rooted⟩ := route.rooted
    exact ⟨classifier,
      (rooted.restore_of_not_connected update outside).hasClassifier⟩
  · rintro ⟨classifier, classified⟩
    have outside : ¬ ConvClass before value child := by
      intro inside
      have valueKind : before.tagSort? value = some .kind := by
        rw [inside.category_eq, childKind]
      exact beforeChecked.kind_has_no_classifier valueKind classified
    obtain ⟨length, _bound, route⟩ :=
      HasClassifier.route beforeChecked resident classified
    obtain ⟨root, rooted⟩ := route.rooted
    exact ⟨classifier,
      (rooted.preserve_of_not_connected update outside).hasClassifier⟩

private theorem Dense.classifierEqEarly (before after : Dense)
    (defs : after.defs = before.defs) (conv : after.conv = before.conv)
    (value : Ref) : after.classifier? value = before.classifier? value := by
  have tagEq : ∀ reference,
      Nucleus.Hol.Ethane.OneBased.Dense.tagSort? after reference =
        Nucleus.Hol.Ethane.OneBased.Dense.tagSort? before reference := by
    intro reference
    change (after.defs[(reference.value.toNat - 1)]?).map (·.tag.sort) =
      (before.defs[(reference.value.toNat - 1)]?).map (·.tag.sort)
    rw [defs]
  have lookupEq : ∀ fuel reference,
      Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? after fuel reference =
        Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? before fuel reference := by
    intro fuel
    induction fuel with
    | zero => intro reference; rfl
    | succ fuel ih =>
        intro reference
        simp only [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?]
        rw [conv]
        split
        · rfl
        · rename_i _ target _
          rw [tagEq reference, tagEq target]
          split
          · exact ih target
          · split <;> rfl
  change Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?
      after (after.defs.length + 1) value = _
  rw [defs]
  exact lookupEq _ _

private theorem Dense.checkedClassifierEqEarly (before after : Dense)
    (defs : after.defs = before.defs) (conv : after.conv = before.conv)
    (value : Ref) : after.checkedClassifier? value = before.checkedClassifier? value := by
  unfold Dense.checkedClassifier?
  have exprEq : after.expr? value = before.expr? value := by
    change after.defs[(value.value.toNat - 1)]? =
      before.defs[(value.value.toNat - 1)]?
    rw [defs]
  rw [exprEq, Dense.classifierEqEarly before after defs conv value]

theorem Dense.ConvPathWitness.root_no_convEdge
    (witness : Dense.ConvPathWitness dense category path)
    (order : Dense.ConvPathOrder path)
    (decreases : dense.conv.Decreases) :
    ¬ConvEdge dense path.root target := by
  intro edge
  have targetIn := witness.successorClosed path.root witness.rootMember edge
  have rootLe := order.root_le target targetIn
  exact (Nat.not_lt_of_ge rootLe) (decreases edge.1)

/-! ## Executable plain-column unions

This is the exact non-conversion branch of Rust `union_in`: validate both
read-only paths, compress both paths, then join their least roots. -/

inductive PlainColumn
  | semantic
  | syntactic
  deriving DecidableEq, Repr

def PlainColumn.relation : PlainColumn → EqualityColumn
  | .semantic => .semantic
  | .syntactic => .syn

def Dense.plainColumn (dense : Dense) : PlainColumn → Column Ref
  | .semantic => dense.eq
  | .syntactic => dense.synEq

def Dense.withPlainColumn (dense : Dense) : PlainColumn → Column Ref → Dense
  | .semantic, column => { dense with eq := column }
  | .syntactic, column => { dense with synEq := column }

def Dense.setPlain? (dense : Dense) (column : PlainColumn)
    (reference : Ref) (value : Option Ref) : Option Dense :=
  let position := reference.value.toNat - 1
  if position < dense.defs.length then
    some (dense.withPlainColumn column
      (Dense.setColumnNormalized (dense.plainColumn column) position value))
  else none

theorem Dense.setPlain?_exists_of_resident (dense : Dense)
    (column : PlainColumn) (reference : Ref) (value : Option Ref)
    (resident : dense.expr? reference ≠ none) :
    ∃ after, dense.setPlain? column reference value = some after := by
  unfold Dense.setPlain?
  dsimp only
  have position : reference.value.toNat - 1 < dense.defs.length := by
    change dense.defs[(reference.value.toNat - 1)]? ≠ none at resident
    simpa [List.getElem?_eq_none_iff] using resident
  rw [if_pos position]
  exact ⟨_, rfl⟩

private theorem plainRefPosition_injective :
    Function.Injective (fun reference : Ref => reference.1.toNat - 1) := by
  intro left right positions
  change left.1.toNat - 1 = right.1.toNat - 1 at positions
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  have leftPositive : 0 < left.1.toNat := Nat.pos_of_ne_zero fun zero =>
    left.property.1 (UInt64.toNat_inj.mp (by simpa using zero))
  have rightPositive : 0 < right.1.toNat := Nat.pos_of_ne_zero fun zero =>
    right.property.1 (UInt64.toNat_inj.mp (by simpa using zero))
  omega

structure PlainFrame (before after : Dense) (column : PlainColumn) : Prop where
  defs : after.defs = before.defs
  conv : after.conv = before.conv
  other : match column with
    | .semantic => after.synEq = before.synEq
    | .syntactic => after.eq = before.eq

theorem PlainFrame.expr?_eq (frame : PlainFrame before after column)
    (reference : Ref) : after.expr? reference = before.expr? reference := by
  change after.defs[(reference.value.toNat - 1)]? =
    before.defs[(reference.value.toNat - 1)]?
  rw [frame.defs]

theorem PlainFrame.tagSort?_eq (frame : PlainFrame before after column)
    (reference : Ref) : after.tagSort? reference = before.tagSort? reference := by
  change (after.expr? reference).map (·.tag.sort) =
    (before.expr? reference).map (·.tag.sort)
  rw [frame.expr?_eq]

theorem Dense.setPlain?_frame (before after : Dense) (column : PlainColumn)
    (reference : Ref) (value : Option Ref)
    (result : before.setPlain? column reference value = some after) :
    PlainFrame before after column := by
  unfold Dense.setPlain? at result
  dsimp only at result
  split at result
  · simp only [Option.some.injEq] at result
    subst after
    cases column <;> exact ⟨rfl, rfl, rfl⟩
  · simp at result

structure PlainCellUpdate (before after : Dense) (column : PlainColumn)
    (reference : Ref) (value : Option Ref) : Prop extends
    PlainFrame before after column where
  updated : (after.plainColumn column).get? reference = value
  unchanged : ∀ other, other ≠ reference →
    (after.plainColumn column).get? other =
      (before.plainColumn column).get? other

theorem Dense.setPlain?_spec (before after : Dense) (column : PlainColumn)
    (reference : Ref) (value : Option Ref)
    (result : before.setPlain? column reference value = some after) :
    PlainCellUpdate before after column reference value := by
  have frame := before.setPlain?_frame after column reference value result
  unfold Dense.setPlain? at result
  dsimp only at result
  split at result
  · simp only [Option.some.injEq] at result
    subst after
    refine { toPlainFrame := frame, updated := ?_, unchanged := ?_ }
    · cases column <;>
        exact getElem?_setColumnNormalized_self _
          (reference.value.toNat - 1) value
    · intro other different
      cases column <;>
        exact getElem?_setColumnNormalized_of_ne _
          (reference.value.toNat - 1) (other.value.toNat - 1) value
          (fun equal => different (plainRefPosition_injective equal).symm)
  · simp at result

theorem Dense.setPlain?_selectedResident (before after : Dense)
    (column : PlainColumn) (reference : Ref) (value : Option Ref)
    (beforeResident : before.Resident (before.plainColumn column))
    (result : before.setPlain? column reference value = some after) :
    after.Resident (after.plainColumn column) := by
  unfold Dense.setPlain? at result
  dsimp only at result
  split at result
  · simp only [Option.some.injEq] at result
    subst after
    intro position target cell
    have flat :
        (setColumnNormalized (before.plainColumn column)
          (reference.value.toNat - 1) value)[position]?.bind id = some target := by
      have bound := congrArg (fun entry => entry.bind id) cell
      cases column <;>
        simpa [Dense.withPlainColumn, Dense.plainColumn] using bound
    rw [setColumnNormalized, Column.getElem?_normalize_bind] at flat
    by_cases same : position = reference.value.toNat - 1
    · subst position
      cases column <;> assumption
    · rw [List.getElem?_set, if_neg (Ne.symm same)] at flat
      by_cases inside : position < (before.plainColumn column).length
      · rw [List.getElem?_append_left inside] at flat
        have original : (before.plainColumn column)[position]? = some (some target) := by
          cases found : (before.plainColumn column)[position]? <;> simp_all
        cases column <;> exact beforeResident position target original
      · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at flat
        simp only [List.getElem?_replicate] at flat
        split at flat <;> simp_all
  · simp at result

theorem Dense.setPlain?_selectedTargets (before after : Dense)
    (column : PlainColumn) (reference : Ref) (value : Option Ref)
    (beforeTargets : before.TargetsResident (before.plainColumn column))
    (targetResident : ∀ target, value = some target → before.expr? target ≠ none)
    (result : before.setPlain? column reference value = some after) :
    after.TargetsResident (after.plainColumn column) := by
  have update := before.setPlain?_spec after column reference value result
  have sourceResident : before.expr? reference ≠ none := by
    simp only [Dense.setPlain?] at result
    split at result
    · rename_i inside
      intro missing
      have outside : ¬(reference.value.toNat - 1 < before.defs.length) := by
        change before.defs[(reference.value.toNat - 1)]? = none at missing
        simpa [List.getElem?_eq_none_iff] using missing
      contradiction
    · simp at result
  intro left right edge
  by_cases same : left = reference
  · subst left
    rw [update.updated] at edge
    obtain rfl : value = some right := edge
    exact ⟨update.toPlainFrame.expr?_eq reference ▸ sourceResident,
      update.toPlainFrame.expr?_eq right ▸ targetResident right rfl⟩
  · rw [update.unchanged left same] at edge
    obtain ⟨leftResident, rightResident⟩ := beforeTargets left right edge
    exact ⟨update.toPlainFrame.expr?_eq left ▸ leftResident,
      update.toPlainFrame.expr?_eq right ▸ rightResident⟩

theorem Dense.setPlain?_checked (before after : Dense) (column : PlainColumn)
    (reference : Ref) (value : Option Ref) (beforeChecked : before.Checked)
    (targetResident : ∀ target, value = some target → before.expr? target ≠ none)
    (result : before.setPlain? column reference value = some after) :
    after.Checked := by
  have frame := before.setPlain?_frame after column reference value result
  have selectedResident := before.setPlain?_selectedResident after column reference
    value (by
      cases column
      · exact beforeChecked.toWellFormed.eq
      · exact beforeChecked.toWellFormed.synEq) result
  have selectedTargets := before.setPlain?_selectedTargets after column reference
    value (by
      cases column
      · exact beforeChecked.eqTargets
      · exact beforeChecked.synEqTargets) targetResident result
  cases column with
  | semantic =>
      refine {
        toWellFormed := {
          eq := selectedResident
          synEq := by
            intro position target cell
            rw [frame.other] at cell
            rw [frame.defs]
            exact beforeChecked.toWellFormed.synEq position target cell
          conv := by
            intro position target cell
            rw [frame.conv] at cell
            rw [frame.defs]
            exact beforeChecked.toWellFormed.conv position target cell
        }
        eqTargets := selectedTargets
        synEqTargets := ?_
        convTargets := ?_
      }
      · intro left right edge
        have oldEdge : before.synEq.get? left = some right := by
          simpa [Dense.plainColumn] using frame.other ▸ edge
        obtain ⟨leftResident, rightResident⟩ :=
          beforeChecked.synEqTargets left right oldEdge
        exact ⟨frame.expr?_eq left ▸ leftResident,
          frame.expr?_eq right ▸ rightResident⟩
      · intro left right edge
        have oldEdge : before.conv.get? left = some right := frame.conv ▸ edge
        obtain ⟨leftResident, rightResident⟩ :=
          beforeChecked.convTargets left right oldEdge
        exact ⟨frame.expr?_eq left ▸ leftResident,
          frame.expr?_eq right ▸ rightResident⟩
  | syntactic =>
      refine {
        toWellFormed := {
          eq := by
            intro position target cell
            rw [frame.other] at cell
            rw [frame.defs]
            exact beforeChecked.toWellFormed.eq position target cell
          synEq := selectedResident
          conv := by
            intro position target cell
            rw [frame.conv] at cell
            rw [frame.defs]
            exact beforeChecked.toWellFormed.conv position target cell
        }
        eqTargets := ?_
        synEqTargets := selectedTargets
        convTargets := ?_
      }
      · intro left right edge
        have oldEdge : before.eq.get? left = some right := by
          simpa [Dense.plainColumn] using frame.other ▸ edge
        obtain ⟨leftResident, rightResident⟩ :=
          beforeChecked.eqTargets left right oldEdge
        exact ⟨frame.expr?_eq left ▸ leftResident,
          frame.expr?_eq right ▸ rightResident⟩
      · intro left right edge
        have oldEdge : before.conv.get? left = some right := frame.conv ▸ edge
        obtain ⟨leftResident, rightResident⟩ :=
          beforeChecked.convTargets left right oldEdge
        exact ⟨frame.expr?_eq left ▸ leftResident,
          frame.expr?_eq right ▸ rightResident⟩

theorem PlainCellUpdate.edge_of_ne
    (update : PlainCellUpdate before after column reference value)
    (different : left ≠ reference)
    (edge : Edge before column.relation left right) :
    Edge after column.relation left right := by
  have unchanged := update.unchanged left different
  cases column with
  | semantic =>
      change after.eq.get? left = before.eq.get? left at unchanged
      change before.eq.get? left = some right at edge
      change after.eq.get? left = some right
      rw [unchanged]
      exact edge
  | syntactic =>
      change after.synEq.get? left = before.synEq.get? left at unchanged
      change before.synEq.get? left = some right at edge
      change after.synEq.get? left = some right
      rw [unchanged]
      exact edge

theorem PlainCellUpdate.edge_before_of_ne
    (update : PlainCellUpdate before after column reference value)
    (different : left ≠ reference)
    (edge : Edge after column.relation left right) :
    Edge before column.relation left right := by
  have unchanged := update.unchanged left different
  cases column with
  | semantic =>
      change after.eq.get? left = before.eq.get? left at unchanged
      change after.eq.get? left = some right at edge
      change before.eq.get? left = some right
      rw [← unchanged]
      exact edge
  | syntactic =>
      change after.synEq.get? left = before.synEq.get? left at unchanged
      change after.synEq.get? left = some right at edge
      change before.synEq.get? left = some right
      rw [← unchanged]
      exact edge

theorem PlainCellUpdate.decreases
    (update : PlainCellUpdate before after column reference value)
    (beforeDecreases : (before.plainColumn column).Decreases)
    (valueDecreases : ∀ target, value = some target → target < reference) :
    (after.plainColumn column).Decreases := by
  intro source target edge
  by_cases same : source = reference
  · subst source
    have updated := update.updated
    change Column.get? (after.plainColumn column) reference = value at updated
    change Column.get? (after.plainColumn column) reference = some target at edge
    rw [updated] at edge
    exact valueDecreases target edge
  · have unchanged := update.unchanged source same
    change Column.get? (after.plainColumn column) source =
      Column.get? (before.plainColumn column) source at unchanged
    change Column.get? (after.plainColumn column) source = some target at edge
    apply beforeDecreases
    change Column.get? (before.plainColumn column) source = some target
    exact unchanged.symm ▸ edge

theorem PlainCellUpdate.class_mono
    (update : PlainCellUpdate before after column reference value)
    (overwritten : ∀ {right}, Edge before column.relation reference right →
      Class after column.relation reference right)
    (connected : Class before column.relation left right) :
    Class after column.relation left right := by
  induction connected with
  | rel edgeLeft edgeRight edge =>
      by_cases same : edgeLeft = reference
      · subst edgeLeft; exact overwritten edge
      · exact Relation.EqvGen.rel _ _ (update.edge_of_ne same edge)
  | refl selected => exact Class.refl selected
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem PlainCellUpdate.class_before_mono
    (update : PlainCellUpdate before after column reference value)
    (replacement : ∀ {right}, Edge after column.relation reference right →
      Class before column.relation reference right)
    (connected : Class after column.relation left right) :
    Class before column.relation left right := by
  induction connected with
  | rel edgeLeft edgeRight edge =>
      by_cases same : edgeLeft = reference
      · subst edgeLeft; exact replacement edge
      · exact Relation.EqvGen.rel _ _ (update.edge_before_of_ne same edge)
  | refl selected => exact Class.refl selected
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- The equivalence relation obtained by merging exactly the two old ordinary
column classes containing `child` and `parent`. -/
def PlainJoinedClass (dense : Dense) (column : PlainColumn)
    (child parent left right : Ref) : Prop :=
  Class dense column.relation left right ∨
    ((Class dense column.relation left child ∨
        Class dense column.relation left parent) ∧
      (Class dense column.relation right child ∨
        Class dense column.relation right parent))

theorem PlainJoinedClass.class_congr
    (classes : ∀ {x y}, Class first column.relation x y ↔
      Class second column.relation x y) :
    PlainJoinedClass first column child parent left right ↔
      PlainJoinedClass second column child parent left right := by
  simp only [PlainJoinedClass, classes]

theorem PlainJoinedClass.generator_congr
    (leftConnected : Class dense column.relation left leftRoot)
    (rightConnected : Class dense column.relation right rightRoot) :
    PlainJoinedClass dense column leftRoot rightRoot a b ↔
      PlainJoinedClass dense column left right a b := by
  have leftIff : ∀ x, Class dense column.relation x leftRoot ↔
      Class dense column.relation x left := fun x => ⟨
    fun connected => connected.trans leftConnected.symm,
    fun connected => connected.trans leftConnected⟩
  have rightIff : ∀ x, Class dense column.relation x rightRoot ↔
      Class dense column.relation x right := fun x => ⟨
    fun connected => connected.trans rightConnected.symm,
    fun connected => connected.trans rightConnected⟩
  simp only [PlainJoinedClass, leftIff, rightIff]

theorem PlainJoinedClass.of_connected_iff
    (generators : Class dense column.relation left right) :
    PlainJoinedClass dense column left right a b ↔
      Class dense column.relation a b := by
  constructor
  · rintro (old | ⟨aSide, bSide⟩)
    · exact old
    · rcases aSide with aLeft | aRight <;>
        rcases bSide with bLeft | bRight
      · exact aLeft.trans bLeft.symm
      · exact (aLeft.trans generators).trans bRight.symm
      · exact aRight.trans (bLeft.trans generators).symm
      · exact aRight.trans bRight.symm
  · exact Or.inl

/-- A functional one-cell update can add no connectivity beyond joining the
old classes of its source and target. This decomposition is independent of
forest well-formedness and therefore also covers defensive cyclic inputs. -/
theorem PlainCellUpdate.class_decompose
    (update : PlainCellUpdate before after column child (some parent))
    (related : Class after column.relation left right) :
    PlainJoinedClass before column child parent left right := by
  induction related with
  | rel edgeLeft edgeRight edge =>
      by_cases source : edgeLeft = child
      · subst edgeLeft
        have target : edgeRight = parent := by
          cases column <;>
            exact Option.some.inj (by
              simpa [Edge, PlainColumn.relation, Dense.plainColumn] using
                edge.symm.trans update.updated)
        subst edgeRight
        right
        exact ⟨Or.inl (Class.refl _), Or.inr (Class.refl _)⟩
      · left
        exact Relation.EqvGen.rel _ _ (update.edge_before_of_ne source edge)
  | refl reference => exact Or.inl (Class.refl reference)
  | symm left right _ ih =>
      rcases ih with old | ⟨leftMerged, rightMerged⟩
      · exact Or.inl old.symm
      · exact Or.inr ⟨rightMerged, leftMerged⟩
  | trans left middle right _ _ leftMiddle middleRight =>
      rcases leftMiddle with oldLeft | ⟨leftMerged, middleMerged⟩
      · rcases middleRight with oldRight | ⟨middleMerged', rightMerged⟩
        · exact Or.inl (oldLeft.trans oldRight)
        · right
          refine ⟨?_, rightMerged⟩
          rcases middleMerged' with middleChild | middleParent
          · exact Or.inl (oldLeft.trans middleChild)
          · exact Or.inr (oldLeft.trans middleParent)
      · rcases middleRight with oldRight | ⟨middleMerged', rightMerged⟩
        · right
          refine ⟨leftMerged, ?_⟩
          rcases middleMerged with middleChild | middleParent
          · exact Or.inl (oldRight.symm.trans middleChild)
          · exact Or.inr (oldRight.symm.trans middleParent)
        · exact Or.inr ⟨leftMerged, rightMerged⟩

theorem PlainCellUpdate.class_iff_joined
    (update : PlainCellUpdate before after column child (some parent))
    (overwritten : ∀ {right}, Edge before column.relation child right →
      Class after column.relation child right) :
    Class after column.relation left right ↔
      PlainJoinedClass before column child parent left right := by
  constructor
  · exact update.class_decompose
  · intro joined
    have oldMono : ∀ {a b}, Class before column.relation a b →
        Class after column.relation a b := update.class_mono overwritten
    rcases joined with old | ⟨leftMerged, rightMerged⟩
    · exact oldMono old
    · have childParent : Class after column.relation child parent := by
        apply Relation.EqvGen.rel _ _
        cases column <;>
          simpa [Edge, PlainColumn.relation, Dense.plainColumn] using update.updated
      have leftChildOrParent :
          Class after column.relation left child ∨
            Class after column.relation left parent := leftMerged.elim
        (Or.inl ∘ oldMono) (Or.inr ∘ oldMono)
      have rightChildOrParent :
          Class after column.relation right child ∨
            Class after column.relation right parent := rightMerged.elim
        (Or.inl ∘ oldMono) (Or.inr ∘ oldMono)
      rcases leftChildOrParent with leftChild | leftParent <;>
        rcases rightChildOrParent with rightChild | rightParent
      · exact leftChild.trans rightChild.symm
      · exact (leftChild.trans childParent).trans rightParent.symm
      · exact leftParent.trans (rightChild.trans childParent).symm
      · exact leftParent.trans rightParent.symm

theorem PlainFrame.trans (first : PlainFrame before middle column)
    (second : PlainFrame middle after column) : PlainFrame before after column := by
  constructor
  · exact second.defs.trans first.defs
  · exact second.conv.trans first.conv
  · cases column
    · exact second.other.trans first.other
    · exact second.other.trans first.other

theorem class_congr (edges : ∀ {left right},
    Edge before column left right ↔ Edge after column left right) :
    Class before column left right ↔ Class after column left right := by
  constructor <;> intro connected
  · induction connected with
    | rel left right edge => exact Relation.EqvGen.rel _ _ (edges.mp edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr
  · induction connected with
    | rel left right edge => exact Relation.EqvGen.rel _ _ (edges.mpr edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr

theorem PlainFrame.syn_class_iff (frame : PlainFrame before after .semantic) :
    Class after .syn left right ↔ Class before .syn left right := by
  apply class_congr
  simp [Edge, frame.other]

theorem PlainFrame.semantic_class_iff
    (frame : PlainFrame before after .syntactic) :
    Class after .semantic left right ↔ Class before .semantic left right := by
  apply class_congr
  simp [Edge, frame.other]

theorem PlainFrame.conv_class_iff (frame : PlainFrame before after column) :
    Class after .conv left right ↔ Class before .conv left right := by
  apply class_congr
  intro a b
  constructor <;> intro edge
  · rcases edge with ⟨raw, category, leftCategory, rightCategory⟩
    exact ⟨frame.conv ▸ raw, category,
      frame.tagSort?_eq a ▸ leftCategory,
      frame.tagSort?_eq b ▸ rightCategory⟩
  · rcases edge with ⟨raw, category, leftCategory, rightCategory⟩
    exact ⟨frame.conv.symm ▸ raw, category,
      (frame.tagSort?_eq a).symm ▸ leftCategory,
      (frame.tagSort?_eq b).symm ▸ rightCategory⟩

structure PlainPath where
  root : Ref
  members : List Ref
  deriving DecidableEq, Repr

/-- Exact successful branch trace for ordinary equality traversal.  Unlike
the fused traversal there is no classifier exit: every followed edge must
remain in the source category. -/
inductive PlainPathTrace (dense : Dense) (column : PlainColumn)
    (category : TagSort) : Nat → List Ref → Ref → PlainPath → Prop
  | cycle {fuel members current} (seen : current ∈ members) :
      PlainPathTrace dense column category (fuel + 1) members current {
        root := Dense.cycleRoot current members, members }
  | root {fuel members current}
      (fresh : current ∉ members)
      (empty : (dense.plainColumn column).get? current = none) :
      PlainPathTrace dense column category (fuel + 1) members current {
        root := current, members := members ++ [current] }
  | step {fuel members current target path}
      (fresh : current ∉ members)
      (raw : (dense.plainColumn column).get? current = some target)
      (same : dense.tagSort? target = some category)
      (tail : PlainPathTrace dense column category fuel
        (members ++ [current]) target path) :
      PlainPathTrace dense column category (fuel + 1) members current path

def Dense.plainPathLoop (dense : Dense) (column : PlainColumn)
    (category : TagSort) : Nat → List Ref → Ref → Except Dense.ConvError PlainPath
  | 0, _, _ => .error .exhausted
  | fuel + 1, members, current =>
      if current ∈ members then
        .ok { root := Dense.cycleRoot current members, members }
      else
        let members := members ++ [current]
        match (dense.plainColumn column).get? current with
        | none => .ok { root := current, members }
        | some parent =>
            match dense.tagSort? parent with
            | none => .error (.missing parent)
            | some parentCategory =>
                if parentCategory = category then
                  dense.plainPathLoop column category fuel members parent
                else .error (.wrongCategory parent category parentCategory)

theorem Dense.plainPathLoop_ok_trace (dense : Dense) (column : PlainColumn)
    (category : TagSort) (fuel : Nat) (members : List Ref) (current : Ref)
    (path : PlainPath)
    (found : dense.plainPathLoop column category fuel members current = .ok path) :
    PlainPathTrace dense column category fuel members current path := by
  fun_induction Dense.plainPathLoop generalizing path <;>
    simp_all only [Except.ok.injEq, reduceCtorEq]
  case case2 =>
    subst path
    exact .cycle ‹_›
  case case3 =>
    subst path
    exact .root ‹_› ‹_›
  case case5 =>
    exact .step ‹_› ‹_› ‹_› (by apply ‹∀ _, _›; rfl)

private theorem plain_cycleRoot_mem {current : Ref} {members : List Ref}
    (seen : current ∈ members) : Dense.cycleRoot current members ∈ members := by
  have nonempty : members.dropWhile (· != current) ≠ [] := by
    induction members with
    | nil => simp at seen
    | cons head tail ih =>
        by_cases equal : head = current
        · subst head; simp
        · simp only [List.mem_cons] at seen
          have tailSeen : current ∈ tail := seen.resolve_left (Ne.symm equal)
          rw [List.dropWhile, show (head != current) = true by simpa [bne_iff_ne]]
          exact ih tailSeen
  cases found : (members.dropWhile (· != current)).min? with
  | none => exact False.elim (nonempty (List.min?_eq_none_iff.mp found))
  | some least =>
      rw [Dense.cycleRoot, found]
      exact (List.dropWhile_sublist (· != current)).mem (List.min?_mem found)

structure PlainAccumulator (dense : Dense) (column : PlainColumn)
    (members : List Ref) (current : Ref) : Prop where
  currentResident : dense.expr? current ≠ none
  memberResident : ∀ member ∈ members, dense.expr? member ≠ none
  memberConnected : ∀ member ∈ members,
    Class dense column.relation member current
  successorClosed : ∀ member ∈ members, ∀ {target},
    Edge dense column.relation member target →
      target ∈ members ∨ target = current

structure PlainPathWitness (dense : Dense) (column : PlainColumn)
    (path : PlainPath) : Prop where
  rootMember : path.root ∈ path.members
  memberResident : ∀ member ∈ path.members, dense.expr? member ≠ none
  memberConnected : ∀ member ∈ path.members,
    Class dense column.relation member path.root
  successorClosed : ∀ member ∈ path.members, ∀ {target},
    Edge dense column.relation member target → target ∈ path.members

structure PlainPathOrder (path : PlainPath) : Prop where
  root_le : ∀ member ∈ path.members, path.root ≤ member

private structure PlainOrderAccumulator (members : List Ref) (current : Ref) : Prop where
  current_lt : ∀ member ∈ members, current < member

private theorem PlainPathTrace.order
    (trace : PlainPathTrace dense column category fuel members current path)
    (decreases : (dense.plainColumn column).Decreases)
    (accumulator : PlainOrderAccumulator members current) :
    PlainPathOrder path := by
  cases trace with
  | cycle seen =>
      exact (lt_irrefl current (accumulator.current_lt current seen)).elim
  | root fresh empty =>
      refine ⟨?_⟩
      intro member memberIn
      rcases List.mem_append.mp memberIn with prior | last
      · exact (accumulator.current_lt member prior).le
      · simp only [List.mem_singleton] at last
        subst member
        exact le_rfl
  | step fresh raw same tail =>
      apply tail.order decreases
      refine ⟨?_⟩
      intro member memberIn
      rcases List.mem_append.mp memberIn with prior | last
      · exact (decreases raw).trans (accumulator.current_lt member prior)
      · simp only [List.mem_singleton] at last
        subst member
        exact decreases raw
termination_by fuel

theorem PlainPathTrace.witness
    (trace : PlainPathTrace dense column category fuel members current path)
    (accumulator : PlainAccumulator dense column members current) :
    PlainPathWitness dense column path := by
  induction trace with
  | cycle seen =>
      have rootMember := plain_cycleRoot_mem seen
      exact {
        rootMember
        memberResident := accumulator.memberResident
        memberConnected := fun member memberIn =>
          (accumulator.memberConnected member memberIn).trans
            (accumulator.memberConnected _ rootMember).symm
        successorClosed := by
          intro member memberIn target edge
          rcases accumulator.successorClosed member memberIn edge with inside | current
          · exact inside
          · subst target; exact seen }
  | root fresh empty =>
      exact {
        rootMember := by simp
        memberResident := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | current
          · exact accumulator.memberResident member prior
          · simp only [List.mem_singleton] at current
            subst member
            exact accumulator.currentResident
        memberConnected := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | current
          · simpa using accumulator.memberConnected member prior
          · simp only [List.mem_singleton] at current
            subst member
            exact Class.refl _
        successorClosed := by
          intro member memberIn target edge
          rcases List.mem_append.mp memberIn with prior | selected
          · rcases accumulator.successorClosed member prior edge with inside | current
            · exact List.mem_append_left _ inside
            · subst target; simp
          · simp only [List.mem_singleton] at selected
            subst member
            cases column
            · simp only [Dense.plainColumn] at empty
              simp only [Edge, PlainColumn.relation] at edge
              change dense.eq.get? _ = none at empty
              rw [empty] at edge
              contradiction
            · simp only [Dense.plainColumn] at empty
              simp only [Edge, PlainColumn.relation] at edge
              change dense.synEq.get? _ = none at empty
              rw [empty] at edge
              contradiction }
  | @step fuel members current target path fresh raw same tail ih =>
      apply ih
      have edge : Edge dense column.relation current target := by
        cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using raw
      exact {
        currentResident := by
          intro missing
          have : dense.tagSort? target = none := by
            change (dense.expr? target).map (·.tag.sort) = none
            rw [missing]
            rfl
          rw [same] at this
          contradiction
        memberResident := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | current
          · exact accumulator.memberResident member prior
          · simp only [List.mem_singleton] at current
            subst member
            exact accumulator.currentResident
        memberConnected := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | current
          · exact (accumulator.memberConnected member prior).trans
              (Relation.EqvGen.rel _ _ edge)
          · simp only [List.mem_singleton] at current
            subst member
            exact Relation.EqvGen.rel _ _ edge
        successorClosed := by
          intro member memberIn successor successorEdge
          rcases List.mem_append.mp memberIn with prior | selected
          · rcases accumulator.successorClosed member prior successorEdge with inside | current
            · exact Or.inl (List.mem_append_left _ inside)
            · subst successor; exact Or.inl (by simp)
          · simp only [List.mem_singleton] at selected
            subst member
            have successorEq : successor = target := by
              cases column <;>
                exact Option.some.inj (by
                  simpa [Edge, PlainColumn.relation, Dense.plainColumn] using
                    successorEdge.symm.trans raw)
            exact Or.inr successorEq }

private theorem PlainPathTrace.empty_member_eq_root
    (trace : PlainPathTrace dense column category fuel members current path)
    (priorNonempty : ∀ member ∈ members,
      (dense.plainColumn column).get? member ≠ none)
    (selected : Ref) (selectedIn : selected ∈ path.members)
    (selectedEmpty : (dense.plainColumn column).get? selected = none) :
    selected = path.root := by
  cases trace with
  | cycle seen =>
      exact (priorNonempty selected selectedIn selectedEmpty).elim
  | root fresh empty =>
      rcases List.mem_append.mp selectedIn with prior | last
      · exact (priorNonempty selected prior selectedEmpty).elim
      · simpa only [List.mem_singleton] using last
  | step fresh raw same tail =>
      apply tail.empty_member_eq_root
        (priorNonempty := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | last
          · exact priorNonempty member prior
          · simp only [List.mem_singleton] at last
            subst member
            simp [raw])
        selected selectedIn selectedEmpty
termination_by fuel

private structure PlainMembershipAccumulator (members : List Ref)
    (current origin : Ref) : Prop where
  seen : origin = current ∨ origin ∈ members

private theorem PlainPathTrace.origin_mem
    (trace : PlainPathTrace dense column category fuel members current path)
    (accumulator : PlainMembershipAccumulator members current origin) :
    origin ∈ path.members := by
  cases trace with
  | cycle currentSeen =>
      rcases accumulator.seen with rfl | seen
      · exact currentSeen
      · exact seen
  | root fresh empty =>
      rcases accumulator.seen with rfl | seen
      · simp
      · exact List.mem_append_left _ seen
  | step fresh raw same tail =>
      apply tail.origin_mem
      refine ⟨?_⟩
      rcases accumulator.seen with rfl | seen
      · exact Or.inr (by simp)
      · exact Or.inr (List.mem_append_left _ seen)
termination_by fuel

def Dense.plainPath (dense : Dense) (column : PlainColumn) (reference : Ref) :
    Except Dense.ConvError PlainPath :=
  match dense.tagSort? reference with
  | none => .error (.missing reference)
  | some category =>
      dense.plainPathLoop column category (dense.defs.length + 1) [] reference

/-- The implementation fuel is only a structural device for Lean.  On an
ordered column, a resident traversal can never observe `exhausted`: each edge
strictly lowers the positive one-based reference, while the initial reference
is bounded by the number of resident rows. -/
private theorem Dense.plainPathLoop_ne_exhausted (dense : Dense)
    (column : PlainColumn) (category : TagSort) (fuel : Nat)
    (members : List Ref) (current : Ref)
    (decreases : (dense.plainColumn column).Decreases)
    (bound : current.value.toNat < fuel) :
    dense.plainPathLoop column category fuel members current ≠
      .error .exhausted := by
  induction fuel generalizing members current with
  | zero => omega
  | succ fuel ih =>
      simp only [Dense.plainPathLoop]
      split
      · simp
      · split
        · simp
        · rename_i parent raw
          split
          · simp
          · rename_i parentCategory parentCategoryEq
            split
            · apply ih
              have lower := decreases raw
              change parent.value.toNat < current.value.toNat at lower
              omega
            · simp

theorem Dense.plainPath_ne_exhausted (dense : Dense) (column : PlainColumn)
    (reference : Ref) (decreases : (dense.plainColumn column).Decreases) :
    dense.plainPath column reference ≠ .error .exhausted := by
  unfold Dense.plainPath
  cases categoryEq : dense.tagSort? reference with
  | none => simp
  | some category =>
      apply dense.plainPathLoop_ne_exhausted column category
        (dense.defs.length + 1) [] reference decreases
      have resident : dense.expr? reference ≠ none := by
        intro missing
        change (dense.expr? reference).map (·.tag.sort) = some category at categoryEq
        rw [missing] at categoryEq
        contradiction
      have position : reference.value.toNat - 1 < dense.defs.length := by
        change dense.defs[(reference.value.toNat - 1)]? ≠ none at resident
        simpa [List.getElem?_eq_none_iff] using resident
      have positive : 0 < reference.value.toNat := by
        apply Nat.pos_of_ne_zero
        intro zero
        change reference.1.toNat = 0 at zero
        exact reference.property.1 (UInt64.toNat_inj.mp zero)
      omega

/-- Read-only semantic equivalence query matching Rust `equivalent_as`: reject
missing endpoints, return `false` before traversal for unlike categories, and
otherwise compare the canonical roots of the two semantic paths. -/
def Dense.equivalentAs (dense : Dense) (left right : Ref) :
    Except Dense.ConvError Bool :=
  match dense.tagSort? left with
  | none => .error (.missing left)
  | some leftCategory =>
      match dense.tagSort? right with
      | none => .error (.missing right)
      | some rightCategory =>
          if rightCategory != leftCategory then .ok false
          else
            match dense.plainPath .semantic left with
            | .error error => .error error
            | .ok leftPath =>
                match dense.plainPath .semantic right with
                | .error error => .error error
                | .ok rightPath => .ok (leftPath.root == rightPath.root)

theorem Dense.plainPath_ok_witness (dense : Dense) (column : PlainColumn)
    (reference : Ref) (path : PlainPath)
    (found : dense.plainPath column reference = .ok path) :
    ∃ category, dense.tagSort? reference = some category ∧
      PlainPathWitness dense column path := by
  unfold Dense.plainPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      have resident : dense.expr? reference ≠ none := by
        intro missing
        change (dense.expr? reference).map (·.tag.sort) = some category at categoryEq
        rw [missing] at categoryEq
        contradiction
      rw [categoryEq] at found
      have trace := dense.plainPathLoop_ok_trace column category
        (dense.defs.length + 1) [] reference path found
      refine ⟨category, rfl, trace.witness ?_⟩
      exact {
        currentResident := resident
        memberResident := by simp
        memberConnected := by simp
        successorClosed := by simp }

theorem Dense.plainPath_ok_order (dense : Dense) (column : PlainColumn)
    (reference : Ref) (path : PlainPath)
    (decreases : (dense.plainColumn column).Decreases)
    (found : dense.plainPath column reference = .ok path) : PlainPathOrder path := by
  unfold Dense.plainPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      rw [categoryEq] at found
      have trace := dense.plainPathLoop_ok_trace column category
        (dense.defs.length + 1) [] reference path found
      exact trace.order decreases ⟨by simp⟩

theorem Dense.plainPath_ok_source_mem (dense : Dense) (column : PlainColumn)
    (reference : Ref) (path : PlainPath)
    (found : dense.plainPath column reference = .ok path) :
    reference ∈ path.members := by
  unfold Dense.plainPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      rw [categoryEq] at found
      have trace := dense.plainPathLoop_ok_trace column category
        (dense.defs.length + 1) [] reference path found
      exact trace.origin_mem ⟨Or.inl rfl⟩

/-- A positive executable root comparison is a semantic equality class. -/
theorem Dense.equivalentAs_true_sound (dense : Dense) (left right : Ref)
    (found : dense.equivalentAs left right = .ok true) :
    Class dense .semantic left right := by
  cases leftCategoryEq : dense.tagSort? left with
  | none => simp_all [Dense.equivalentAs]
  | some leftCategory =>
      cases rightCategoryEq : dense.tagSort? right with
      | none => simp_all [Dense.equivalentAs]
      | some rightCategory =>
          by_cases same : rightCategory = leftCategory
          · subst rightCategory
            cases leftPathEq : dense.plainPath .semantic left with
            | error error => simp_all [Dense.equivalentAs]
            | ok leftPath =>
                cases rightPathEq : dense.plainPath .semantic right with
                | error error => simp_all [Dense.equivalentAs]
                | ok rightPath =>
                    have roots : leftPath.root = rightPath.root := by
                      simpa [Dense.equivalentAs, leftCategoryEq,
                        rightCategoryEq, leftPathEq, rightPathEq] using found
                    obtain ⟨_, _, leftWitness⟩ :=
                      dense.plainPath_ok_witness .semantic left leftPath leftPathEq
                    obtain ⟨_, _, rightWitness⟩ :=
                      dense.plainPath_ok_witness .semantic right rightPath rightPathEq
                    have leftConnected := leftWitness.memberConnected left <|
                      dense.plainPath_ok_source_mem .semantic left leftPath leftPathEq
                    have rightConnected := rightWitness.memberConnected right <|
                      dense.plainPath_ok_source_mem .semantic right rightPath rightPathEq
                    rw [roots] at leftConnected
                    exact leftConnected.trans rightConnected.symm
          · simp_all [Dense.equivalentAs]

/-- Total callback view used by the existing abstract conversion-union layer.
Errors map to `false`; the fallible API above remains the exact Rust query. -/
def Dense.equivalentAsBool (dense : Dense) : Dense.Equivalent :=
  fun left right =>
    match dense.equivalentAs left right with
    | .ok answer => answer
    | .error _ => false

theorem Dense.equivalentAsBool_sound (dense : Dense) :
    EquivalentSound dense dense.equivalentAsBool := by
  intro left right accepted
  unfold Dense.equivalentAsBool at accepted
  cases found : dense.equivalentAs left right with
  | error error => simp [found] at accepted
  | ok answer =>
      simp only [found] at accepted
      subst answer
      exact dense.equivalentAs_true_sound left right found

/-- Fallible, state-aware conversion union matching Rust's observed callback:
the semantic query is evaluated against the state at the instant immediately
before conversion-path mutation, and its error is propagated unchanged. -/
def Dense.unionConvExact (dense : Dense) (left right : Ref) :
    Except Dense.ConvError Dense := do
  let leftCategory ← Dense.require (.missing left) (dense.tagSort? left)
  let rightCategory ← Dense.require (.missing right) (dense.tagSort? right)
  if rightCategory != leftCategory then
    throw (.wrongCategory right leftCategory rightCategory)
  if leftCategory = .kind then
    dense.unionConv (fun _ _ => false) left right
  else
    let leftClassifier ← Dense.require (.noClassifier left)
      (dense.checkedClassifier? left)
    let rightClassifier ← Dense.require (.noClassifier right)
      (dense.checkedClassifier? right)
    let answer ← dense.equivalentAs leftClassifier rightClassifier
    dense.unionConv
      (fun queriedLeft queriedRight =>
        queriedLeft == leftClassifier && queriedRight == rightClassifier && answer)
      left right

/-- A successful exact Rust conversion union is an instance of the abstract
conversion transition with a callback that is sound for the one classifier
pair the operation can query.  The callback is existential because the exact
operation captures the classifiers and semantic answer read from this state. -/
theorem Dense.unionConvExact_ok_certificate (dense after : Dense)
    (left right : Ref) (found : dense.unionConvExact left right = .ok after) :
    ∃ equivalent,
      EquivalentPairSound dense equivalent left right ∧
      dense.unionConv equivalent left right = .ok after := by
  unfold Dense.unionConvExact at found
  cases leftCategoryFound : dense.tagSort? left with
  | none =>
      rw [leftCategoryFound] at found
      simp only [Dense.require, bind, Except.bind] at found
      cases found
  | some leftCategory =>
      rw [leftCategoryFound] at found
      simp only [Dense.require] at found
      cases rightCategoryFound : dense.tagSort? right with
      | none =>
          rw [rightCategoryFound] at found
          simp only [bind, Except.bind] at found
          cases found
      | some rightCategory =>
          rw [rightCategoryFound] at found
          simp only [bind, Except.bind] at found
          by_cases categories : rightCategory = leftCategory
          · subst rightCategory
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at found
            by_cases kind : leftCategory = TagSort.kind
            · rw [if_pos kind] at found
              let equivalent : Dense.Equivalent := fun _ _ => false
              refine ⟨equivalent, ?_, found⟩
              intro _ _ _ _ accepted
              simp [equivalent] at accepted
            · rw [if_neg kind] at found
              cases leftClassifierFound : dense.checkedClassifier? left with
              | none => simp [leftClassifierFound] at found
              | some leftClassifier =>
                  rw [leftClassifierFound] at found
                  simp only at found
                  cases rightClassifierFound : dense.checkedClassifier? right with
                  | none => simp [rightClassifierFound] at found
                  | some rightClassifier =>
                      rw [rightClassifierFound] at found
                      simp only at found
                      cases answerFound : dense.equivalentAs leftClassifier rightClassifier with
                      | error error => simp [answerFound] at found
                      | ok answer =>
                          rw [answerFound] at found
                          simp only at found
                          let equivalent : Dense.Equivalent :=
                            fun queriedLeft queriedRight =>
                              queriedLeft == leftClassifier &&
                                queriedRight == rightClassifier && answer
                          refine ⟨equivalent, ?_, found⟩
                          intro queriedLeft queriedRight queriedLeftFound
                            queriedRightFound accepted
                          simp only [equivalent, Bool.and_eq_true, beq_iff_eq]
                            at accepted
                          obtain ⟨⟨leftEq, rightEq⟩, answerTrue⟩ := accepted
                          subst queriedLeft
                          subst queriedRight
                          subst answer
                          exact dense.equivalentAs_true_sound leftClassifier
                            rightClassifier answerFound
          · have categoriesBool : (rightCategory != leftCategory) = true := by
              simpa [bne_iff_ne] using categories
            rw [if_pos categoriesBool] at found
            simp at found

theorem Dense.plainPath_ok_empty_member_eq_root
    (dense : Dense) (column : PlainColumn) (reference selected : Ref)
    (path : PlainPath) (found : dense.plainPath column reference = .ok path)
    (selectedIn : selected ∈ path.members)
    (selectedEmpty : (dense.plainColumn column).get? selected = none) :
    selected = path.root := by
  unfold Dense.plainPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      rw [categoryEq] at found
      have trace := dense.plainPathLoop_ok_trace column category
        (dense.defs.length + 1) [] reference path found
      exact trace.empty_member_eq_root (by simp) selected selectedIn selectedEmpty

def Dense.compressPlain (dense : Dense) (column : PlainColumn)
    (path : PlainPath) : Option Dense :=
  path.members.foldlM (m := Option) (fun state member =>
    state.setPlain? column member
      (if member = path.root then none else some path.root)) dense

private theorem compressPlainFold_exists (path : PlainPath)
    (original current : Dense) (column : PlainColumn) (members : List Ref)
    (resident : ∀ member ∈ members, original.expr? member ≠ none)
    (sameDefs : current.defs = original.defs) :
    ∃ after, members.foldlM (m := Option) (fun state member =>
      state.setPlain? column member
        (if member = path.root then none else some path.root)) current = some after := by
  induction members generalizing current with
  | nil => exact ⟨current, rfl⟩
  | cons member tail ih =>
      have currentResident : current.expr? member ≠ none := by
        change current.defs[(member.value.toNat - 1)]? ≠ none
        rw [sameDefs]
        exact resident member (by simp)
      obtain ⟨middle, first⟩ := current.setPlain?_exists_of_resident column member
        (if member = path.root then none else some path.root) currentResident
      have frame := current.setPlain?_frame middle column member _ first
      obtain ⟨after, rest⟩ := ih middle
        (fun selected selectedIn => resident selected (by simp [selectedIn]))
        (frame.defs.trans sameDefs)
      refine ⟨after, ?_⟩
      simp only [List.foldlM_cons, first]
      exact rest

theorem Dense.compressPlain_exists (dense : Dense) (column : PlainColumn)
    (path : PlainPath) (resident : ∀ member ∈ path.members,
      dense.expr? member ≠ none) :
    ∃ after, dense.compressPlain column path = some after := by
  exact compressPlainFold_exists path dense dense column path.members resident rfl

/-- Exact model of Rust `find_mut_in` for the ordinary semantic and syntactic
columns.  The returned pair records both the representative returned to the
caller and the complete post-compression dense state. -/
def Dense.findPlainExact (dense : Dense) (column : PlainColumn)
    (reference : Ref) : Except Dense.ConvError (Ref × Dense) :=
  match dense.plainPath column reference with
  | .error error => .error error
  | .ok path =>
      match dense.compressPlain column path with
      | none => .error (.missing reference)
      | some after => .ok (path.root, after)

theorem Dense.findPlainExact_ok (before after : Dense) (column : PlainColumn)
    (reference root : Ref)
    (result : before.findPlainExact column reference = .ok (root, after)) :
    ∃ path,
      before.plainPath column reference = .ok path ∧
      root = path.root ∧
      before.compressPlain column path = some after := by
  unfold Dense.findPlainExact at result
  cases pathResult : before.plainPath column reference with
  | error error => simp [pathResult] at result
  | ok path =>
      rw [pathResult] at result
      simp only at result
      cases compressed : before.compressPlain column path with
      | none => simp [compressed] at result
      | some final =>
          rw [compressed] at result
          simp only [Except.ok.injEq, Prod.mk.injEq] at result
          rcases result with ⟨rfl, rfl⟩
          exact ⟨path, rfl, rfl, compressed⟩

/-- The optional setter used to model Rust's internal `debug_assert!` cannot
fail on a path returned by traversal.  Consequently the exact mutable query
has precisely the same error behavior as its read-only Rust preflight. -/
theorem Dense.findPlainExact_error_iff (dense : Dense) (column : PlainColumn)
    (reference : Ref) (error : Dense.ConvError) :
    dense.findPlainExact column reference = .error error ↔
      dense.plainPath column reference = .error error := by
  unfold Dense.findPlainExact
  cases pathResult : dense.plainPath column reference with
  | error found => simp
  | ok path =>
      obtain ⟨after, compressed⟩ := dense.compressPlain_exists column path
        (by
          obtain ⟨_category, _categoryFound, witness⟩ :=
            dense.plainPath_ok_witness column reference path pathResult
          exact witness.memberResident)
      simp only
      rw [compressed]
      simp

theorem Dense.findPlainExact_ne_exhausted (dense : Dense)
    (column : PlainColumn) (reference : Ref)
    (decreases : (dense.plainColumn column).Decreases) :
    dense.findPlainExact column reference ≠ .error .exhausted := by
  intro exhausted
  have := (dense.findPlainExact_error_iff column reference .exhausted).mp exhausted
  exact dense.plainPath_ne_exhausted column reference decreases this

structure PlainCompressionUpdate (before after : Dense) (column : PlainColumn)
    (path : PlainPath) : Prop extends PlainFrame before after column where
  updated : ∀ member ∈ path.members,
    (after.plainColumn column).get? member =
      if member = path.root then none else some path.root
  unchanged : ∀ other, other ∉ path.members →
    (after.plainColumn column).get? other =
      (before.plainColumn column).get? other

private theorem compressPlainFold_spec (path : PlainPath) (column : PlainColumn)
    (members : List Ref) (before after : Dense)
    (result : members.foldlM (m := Option) (fun state member =>
      state.setPlain? column member
        (if member = path.root then none else some path.root)) before = some after) :
    PlainFrame before after column ∧
      (∀ member ∈ members, (after.plainColumn column).get? member =
        if member = path.root then none else some path.root) ∧
      (∀ other, other ∉ members → (after.plainColumn column).get? other =
        (before.plainColumn column).get? other) := by
  induction members generalizing before with
  | nil =>
      simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq] at result
      subst after
      exact ⟨by cases column <;> exact ⟨rfl, rfl, rfl⟩, by simp, by simp⟩
  | cons member tail ih =>
      simp only [List.foldlM_cons] at result
      cases firstResult : before.setPlain? column member
          (if member = path.root then none else some path.root) with
      | none =>
          rw [firstResult] at result
          contradiction
      | some middle =>
          rw [firstResult] at result
          have first := before.setPlain?_spec middle column member _ firstResult
          obtain ⟨tailFrame, tailUpdated, tailUnchanged⟩ := ih middle result
          refine ⟨first.toPlainFrame.trans tailFrame, ?_, ?_⟩
          · intro selected selectedIn
            simp only [List.mem_cons] at selectedIn
            rcases selectedIn with equal | inTail
            · subst selected
              by_cases again : member ∈ tail
              · exact tailUpdated member again
              · rw [tailUnchanged member again]
                exact first.updated
            · exact tailUpdated selected inTail
          · intro other outside
            simp only [List.mem_cons, not_or] at outside
            rw [tailUnchanged other outside.2]
            exact first.unchanged other outside.1

theorem Dense.compressPlain_spec (before after : Dense) (column : PlainColumn)
    (path : PlainPath) (result : before.compressPlain column path = some after) :
    PlainCompressionUpdate before after column path := by
  obtain ⟨frame, updated, unchanged⟩ :=
    compressPlainFold_spec path column path.members before after result
  exact ⟨frame, updated, unchanged⟩

theorem PlainCompressionUpdate.member_class_root
    (update : PlainCompressionUpdate before after column path)
    (memberIn : member ∈ path.members) :
    Class after column.relation member path.root := by
  by_cases root : member = path.root
  · subst member
    exact Class.refl _
  · apply Relation.EqvGen.rel _ _
    have raw := update.updated member memberIn
    rw [if_neg root] at raw
    cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using raw

theorem PlainCompressionUpdate.class_iff
    (update : PlainCompressionUpdate before after column path)
    (witness : PlainPathWitness before column path) :
    Class after column.relation left right ↔
      Class before column.relation left right := by
  have edgeForward : ∀ {source target}, Edge before column.relation source target →
      Class after column.relation source target := by
    intro source target edge
    by_cases inside : source ∈ path.members
    · have targetIn := witness.successorClosed source inside edge
      exact (update.member_class_root inside).trans
        (update.member_class_root targetIn).symm
    · apply Relation.EqvGen.rel _ _
      have unchanged := update.unchanged source inside
      have rawBefore : (before.plainColumn column).get? source = some target := by
        cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using edge
      have rawAfter : (after.plainColumn column).get? source = some target :=
        unchanged ▸ rawBefore
      cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using rawAfter
  have edgeBackward : ∀ {source target}, Edge after column.relation source target →
      Class before column.relation source target := by
    intro source target edge
    by_cases inside : source ∈ path.members
    · have raw : (after.plainColumn column).get? source = some target := by
        cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using edge
      rw [update.updated source inside] at raw
      by_cases root : source = path.root
      · simp [root] at raw
      · have targetEq : target = path.root := by
          rw [if_neg root] at raw
          exact (Option.some.inj raw).symm
        subst target
        exact witness.memberConnected source inside
    · apply Relation.EqvGen.rel _ _
      have unchanged := update.unchanged source inside
      have rawAfter : (after.plainColumn column).get? source = some target := by
        cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using edge
      have rawBefore : (before.plainColumn column).get? source = some target :=
        unchanged.symm ▸ rawAfter
      cases column <;> simpa [Edge, PlainColumn.relation, Dense.plainColumn] using rawBefore
  constructor <;> intro connected
  · induction connected with
    | rel _ _ edge => exact edgeBackward edge
    | refl reference => exact Class.refl reference
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · induction connected with
    | rel _ _ edge => exact edgeForward edge
    | refl reference => exact Class.refl reference
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second

theorem Dense.compressPlain_frame (before after : Dense) (column : PlainColumn)
    (path : PlainPath) (result : before.compressPlain column path = some after) :
    PlainFrame before after column :=
  (before.compressPlain_spec after column path result).toPlainFrame

private theorem compressPlainFold_decreases (path : PlainPath)
    (order : PlainPathOrder path) (column : PlainColumn) (members : List Ref)
    (membersIn : ∀ member ∈ members, member ∈ path.members)
    (before after : Dense)
    (beforeDecreases : (before.plainColumn column).Decreases)
    (result : members.foldlM (m := Option) (fun state member =>
      state.setPlain? column member
        (if member = path.root then none else some path.root)) before = some after) :
    (after.plainColumn column).Decreases := by
  induction members generalizing before with
  | nil =>
      simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq] at result
      subst after
      exact beforeDecreases
  | cons member tail ih =>
      simp only [List.foldlM_cons] at result
      let value := if member = path.root then none else some path.root
      cases firstResult : before.setPlain? column member value with
      | none =>
          change before.setPlain? column member
            (if member = path.root then none else some path.root) = none at firstResult
          rw [firstResult] at result
          contradiction
      | some middle =>
          change before.setPlain? column member
            (if member = path.root then none else some path.root) = some middle at firstResult
          rw [firstResult] at result
          have update := before.setPlain?_spec middle column member value firstResult
          have valueDecreases : ∀ target, value = some target → target < member := by
            intro target found
            by_cases root : member = path.root
            · simp [value, root] at found
            · have targetEq : target = path.root := by
                simp only [value, if_neg root] at found
                exact (Option.some.inj found).symm
              subst target
              exact lt_of_le_of_ne (order.root_le member (membersIn member (by simp)))
                (Ne.symm root)
          have middleDecreases : (middle.plainColumn column).Decreases :=
            update.decreases beforeDecreases valueDecreases
          have finalDecreases : (after.plainColumn column).Decreases :=
            ih (fun selected selectedIn =>
            membersIn selected (by simp [selectedIn])) middle middleDecreases result
          intro source target edge
          exact finalDecreases edge

theorem Dense.compressPlain_decreases (before after : Dense) (column : PlainColumn)
    (path : PlainPath) (order : PlainPathOrder path)
    (beforeDecreases : (before.plainColumn column).Decreases)
    (result : before.compressPlain column path = some after) :
    (after.plainColumn column).Decreases := by
  exact compressPlainFold_decreases path order column path.members (by simp)
    before after beforeDecreases result

private theorem compressPlainFold_checked (path : PlainPath) (original : Dense)
    (rootResident : original.expr? path.root ≠ none) (members : List Ref)
    (membersIn : ∀ member ∈ members, member ∈ path.members)
    (current after : Dense) (currentChecked : current.Checked)
    (sameDefs : current.defs = original.defs)
    (result : members.foldlM (m := Option) (fun state member =>
      state.setPlain? column member
        (if member = path.root then none else some path.root)) current = some after) :
    after.Checked := by
  induction members generalizing current with
  | nil =>
      simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq] at result
      subst after
      exact currentChecked
  | cons member tail ih =>
      simp only [List.foldlM_cons] at result
      cases firstResult : current.setPlain? column member
          (if member = path.root then none else some path.root) with
      | none =>
          rw [firstResult] at result
          contradiction
      | some middle =>
          rw [firstResult] at result
          have targetResident : ∀ target,
              (if member = path.root then none else some path.root) = some target →
                current.expr? target ≠ none := by
            intro target found
            by_cases root : member = path.root
            · simp [root] at found
            · simp only [if_neg root, Option.some.injEq] at found
              subst target
              change current.defs[(path.root.value.toNat - 1)]? ≠ none
              change original.defs[(path.root.value.toNat - 1)]? ≠ none at rootResident
              rw [sameDefs]
              exact rootResident
          have middleChecked := current.setPlain?_checked middle column member _
            currentChecked targetResident firstResult
          have frame := current.setPlain?_frame middle column member _ firstResult
          apply ih (fun selected selectedIn =>
              membersIn selected (by simp [selectedIn])) middle middleChecked
            (frame.defs.trans sameDefs) result

theorem Dense.compressPlain_checked_of_root (before after : Dense)
    (column : PlainColumn) (path : PlainPath)
    (rootResident : before.expr? path.root ≠ none)
    (beforeChecked : before.Checked)
    (result : before.compressPlain column path = some after) : after.Checked := by
  exact compressPlainFold_checked path before rootResident path.members (by simp)
    before after beforeChecked rfl result

theorem Dense.compressPlain_checked (before after : Dense) (column : PlainColumn)
    (path : PlainPath) (witness : PlainPathWitness before column path)
    (beforeChecked : before.Checked)
    (result : before.compressPlain column path = some after) : after.Checked := by
  exact before.compressPlain_checked_of_root after column path
    (witness.memberResident path.root witness.rootMember) beforeChecked result

theorem Dense.compressPlain_fusedChecked (before after : Dense)
    (column : PlainColumn) (path : PlainPath)
    (witness : PlainPathWitness before column path)
    (order : PlainPathOrder path) (beforeChecked : FusedChecked before)
    (result : before.compressPlain column path = some after) :
    FusedChecked after := by
  have frame := before.compressPlain_frame after column path result
  have afterChecked := before.compressPlain_checked after column path witness
    beforeChecked.toChecked result
  have selectedDecreases : (after.plainColumn column).Decreases :=
    before.compressPlain_decreases after column path order
      (by
        cases column
        · exact beforeChecked.eqDecreases
        · exact beforeChecked.synEqDecreases)
      result
  refine {
    toChecked := afterChecked
    eqDecreases := ?_
    synEqDecreases := ?_
    convDecreases := ?_
    classifierShape := ?_
  }
  · cases column with
    | semantic => exact selectedDecreases
    | syntactic =>
        intro source target edge
        apply beforeChecked.eqDecreases
        simpa [Dense.plainColumn] using frame.other ▸ edge
  · cases column with
    | semantic =>
        intro source target edge
        apply beforeChecked.synEqDecreases
        simpa [Dense.plainColumn] using frame.other ▸ edge
    | syntactic => exact selectedDecreases
  · intro source target edge
    apply beforeChecked.convDecreases
    exact frame.conv ▸ edge
  · intro value classifier edge
    have oldEdge : ClassifierEdge before value classifier := by
      refine ⟨frame.conv ▸ edge.1, ?_⟩
      intro same
      apply edge.2
      obtain ⟨category, valueCategory, classifierCategory⟩ := same
      exact ⟨category, frame.tagSort?_eq value ▸ valueCategory,
        frame.tagSort?_eq classifier ▸ classifierCategory⟩
    have shape := beforeChecked.classifierShape oldEdge
    rcases shape with shape | shape
    · exact Or.inl ⟨frame.tagSort?_eq value ▸ shape.1,
        frame.tagSort?_eq classifier ▸ shape.2⟩
    · exact Or.inr ⟨frame.tagSort?_eq value ▸ shape.1,
        frame.tagSort?_eq classifier ▸ shape.2⟩

/-- A successful exact `find_mut_in` transition is precisely path compression:
it returns the path representative, preserves every equivalence class, and
preserves the complete fused checked invariant. -/
theorem Dense.findPlainExact_ok_preserves (before after : Dense)
    (column : PlainColumn) (reference root : Ref)
    (beforeChecked : FusedChecked before)
    (result : before.findPlainExact column reference = .ok (root, after)) :
    FusedChecked after ∧
      (∀ left right,
        Class after column.relation left right ↔
          Class before column.relation left right) ∧
      Class before column.relation reference root := by
  obtain ⟨path, pathFound, rfl, compressed⟩ :=
    before.findPlainExact_ok after column reference root result
  obtain ⟨_category, _categoryFound, witness⟩ :=
    before.plainPath_ok_witness column reference path pathFound
  have order := before.plainPath_ok_order column reference path
    (by
      cases column
      · exact beforeChecked.eqDecreases
      · exact beforeChecked.synEqDecreases)
    pathFound
  have afterChecked := before.compressPlain_fusedChecked after column path
    witness order beforeChecked compressed
  have update := before.compressPlain_spec after column path compressed
  have sourceIn := before.plainPath_ok_source_mem column reference path pathFound
  exact ⟨afterChecked, fun left right => update.class_iff witness,
    witness.memberConnected reference sourceIn⟩

private def requireValue (error : Dense.ConvError) : Option α → Except Dense.ConvError α
  | none => .error error
  | some value => .ok value

private theorem exceptDoError (error : ε) (next : α → Except ε β) :
    (do let value ← (Except.error error : Except ε α); next value) =
      Except.error error := rfl

private theorem exceptDoOk (value : α) (next : α → Except ε β) :
    (do let result ← (Except.ok value : Except ε α); next result) = next value := rfl

def Dense.unionPlain (dense : Dense) (column : PlainColumn) (left right : Ref) :
    Except Dense.ConvError Dense := do
  let leftPath ← dense.plainPath column left
  let _ ← dense.plainPath column right
  let dense ← requireValue (.missing left) (dense.compressPlain column leftPath)
  let rightPath ← dense.plainPath column right
  let dense ← requireValue (.missing right) (dense.compressPlain column rightPath)
  if leftPath.root = rightPath.root then return dense
  let child := max leftPath.root rightPath.root
  let parent := min leftPath.root rightPath.root
  requireValue (.missing child) (dense.setPlain? column child (some parent))

theorem Dense.unionPlain_frame (before after : Dense) (column : PlainColumn)
    (left right : Ref) (result : before.unionPlain column left right = .ok after) :
    PlainFrame before after column := by
  unfold Dense.unionPlain at result
  cases leftResult : before.plainPath column left with
  | error error =>
      rw [leftResult, exceptDoError] at result
      contradiction
  | ok leftPath =>
      rw [leftResult, exceptDoOk] at result
      cases rightResult : before.plainPath column right with
      | error error =>
          rw [rightResult, exceptDoError] at result
          contradiction
      | ok rightPreflight =>
          rw [rightResult, exceptDoOk] at result
          cases leftCompressed : before.compressPlain column leftPath with
          | none =>
              rw [leftCompressed, requireValue, exceptDoError] at result
              contradiction
          | some leftState =>
              rw [leftCompressed, requireValue, exceptDoOk] at result
              cases rightFound : leftState.plainPath column right with
              | error error =>
                  rw [rightFound, exceptDoError] at result
                  contradiction
              | ok rightPath =>
                  rw [rightFound, exceptDoOk] at result
                  cases rightCompressed : leftState.compressPlain column rightPath with
                  | none =>
                      rw [rightCompressed, requireValue, exceptDoError] at result
                      contradiction
                  | some rightState =>
                      rw [rightCompressed, requireValue, exceptDoOk] at result
                      have first := before.compressPlain_frame leftState column
                        leftPath leftCompressed
                      have second := leftState.compressPlain_frame rightState column
                        rightPath rightCompressed
                      by_cases same : leftPath.root = rightPath.root
                      · rw [if_pos same] at result
                        change Except.ok rightState = Except.ok after at result
                        cases result
                        exact first.trans second
                      · rw [if_neg same] at result
                        let child := max leftPath.root rightPath.root
                        let parent := min leftPath.root rightPath.root
                        dsimp only at result
                        cases joined : rightState.setPlain? column child (some parent) with
                        | none =>
                            rw [joined, requireValue] at result
                            contradiction
                        | some final =>
                            rw [joined, requireValue] at result
                            simp only [Except.ok.injEq] at result
                            subst final
                            exact (first.trans second).trans
                              (rightState.setPlain?_frame after column child
                                (some parent) joined)

theorem Dense.unionPlain_decreases (before after : Dense) (column : PlainColumn)
    (left right : Ref) (beforeDecreases : (before.plainColumn column).Decreases)
    (result : before.unionPlain column left right = .ok after) :
    (after.plainColumn column).Decreases := by
  intro finalSource finalTarget finalEdge
  unfold Dense.unionPlain at result
  cases leftResult : before.plainPath column left with
  | error error =>
      rw [leftResult, exceptDoError] at result
      contradiction
  | ok leftPath =>
      rw [leftResult, exceptDoOk] at result
      cases rightResult : before.plainPath column right with
      | error error =>
          rw [rightResult, exceptDoError] at result
          contradiction
      | ok rightPreflight =>
          rw [rightResult, exceptDoOk] at result
          have leftOrder := before.plainPath_ok_order column left leftPath
            beforeDecreases leftResult
          cases leftCompressed : before.compressPlain column leftPath with
          | none =>
              rw [leftCompressed, requireValue, exceptDoError] at result
              contradiction
          | some leftState =>
              rw [leftCompressed, requireValue, exceptDoOk] at result
              have leftDecreases : (leftState.plainColumn column).Decreases :=
                before.compressPlain_decreases leftState column leftPath leftOrder
                  beforeDecreases leftCompressed
              cases rightFound : leftState.plainPath column right with
              | error error =>
                  rw [rightFound, exceptDoError] at result
                  contradiction
              | ok rightPath =>
                  rw [rightFound, exceptDoOk] at result
                  have rightOrder := leftState.plainPath_ok_order column right
                    rightPath leftDecreases rightFound
                  cases rightCompressed : leftState.compressPlain column rightPath with
                  | none =>
                      rw [rightCompressed, requireValue, exceptDoError] at result
                      contradiction
                  | some rightState =>
                    rw [rightCompressed, requireValue, exceptDoOk] at result
                    have rightDecreases : (rightState.plainColumn column).Decreases :=
                      leftState.compressPlain_decreases rightState column rightPath
                        rightOrder leftDecreases rightCompressed
                    by_cases same : leftPath.root = rightPath.root
                    · rw [if_pos same] at result
                      change Except.ok rightState = Except.ok after at result
                      cases result
                      exact rightDecreases finalEdge
                    · rw [if_neg same] at result
                      let child := max leftPath.root rightPath.root
                      let parent := min leftPath.root rightPath.root
                      dsimp only at result
                      cases joined : rightState.setPlain? column child (some parent) with
                      | none =>
                          rw [joined, requireValue] at result
                          contradiction
                      | some final =>
                          rw [joined, requireValue] at result
                          simp only [Except.ok.injEq] at result
                          subst final
                          have update := rightState.setPlain?_spec after column child
                            (some parent) joined
                          have joinedDecreases :
                              (after.plainColumn column).Decreases := by
                            apply update.decreases rightDecreases
                            intro target equality
                            have targetEq : target = parent :=
                              (Option.some.inj equality).symm
                            subst target
                            exact min_lt_max.mpr same
                          exact joinedDecreases finalEdge

theorem Dense.unionPlain_checked (before after : Dense) (column : PlainColumn)
    (left right : Ref) (beforeChecked : before.Checked)
    (result : before.unionPlain column left right = .ok after) : after.Checked := by
  unfold Dense.unionPlain at result
  cases leftResult : before.plainPath column left with
  | error error =>
      rw [leftResult, exceptDoError] at result
      contradiction
  | ok leftPath =>
      rw [leftResult, exceptDoOk] at result
      obtain ⟨_, _, leftWitness⟩ :=
        before.plainPath_ok_witness column left leftPath leftResult
      cases rightResult : before.plainPath column right with
      | error error =>
          rw [rightResult, exceptDoError] at result
          contradiction
      | ok rightPreflight =>
          rw [rightResult, exceptDoOk] at result
          cases leftCompressed : before.compressPlain column leftPath with
          | none =>
              rw [leftCompressed, requireValue, exceptDoError] at result
              contradiction
          | some leftState =>
              rw [leftCompressed, requireValue, exceptDoOk] at result
              have leftChecked := before.compressPlain_checked leftState column
                leftPath leftWitness beforeChecked leftCompressed
              have leftFrame := before.compressPlain_frame leftState column leftPath
                leftCompressed
              cases rightFound : leftState.plainPath column right with
              | error error =>
                  rw [rightFound, exceptDoError] at result
                  contradiction
              | ok rightPath =>
                rw [rightFound, exceptDoOk] at result
                obtain ⟨_, _, rightWitness⟩ :=
                  leftState.plainPath_ok_witness column right rightPath rightFound
                cases rightCompressed : leftState.compressPlain column rightPath with
                | none =>
                  rw [rightCompressed, requireValue, exceptDoError] at result
                  contradiction
                | some rightState =>
                  rw [rightCompressed, requireValue, exceptDoOk] at result
                  have rightChecked := leftState.compressPlain_checked rightState
                    column rightPath rightWitness leftChecked rightCompressed
                  have rightFrame := leftState.compressPlain_frame rightState column
                    rightPath rightCompressed
                  by_cases same : leftPath.root = rightPath.root
                  · rw [if_pos same] at result
                    change Except.ok rightState = Except.ok after at result
                    cases result
                    exact rightChecked
                  · rw [if_neg same] at result
                    let child := max leftPath.root rightPath.root
                    let parent := min leftPath.root rightPath.root
                    dsimp only at result
                    cases joined : rightState.setPlain? column child (some parent) with
                    | none =>
                        rw [joined, requireValue] at result
                        contradiction
                    | some final =>
                        rw [joined, requireValue] at result
                        simp only [Except.ok.injEq] at result
                        subst final
                        have parentResident : rightState.expr? parent ≠ none := by
                          have beforeResident : before.expr? parent ≠ none := by
                            dsimp only [parent]
                            rcases min_choice leftPath.root rightPath.root with minimum | minimum
                            · rw [minimum]
                              exact leftWitness.memberResident leftPath.root
                                leftWitness.rootMember
                            · rw [minimum]
                              have resident' := rightWitness.memberResident rightPath.root
                                rightWitness.rootMember
                              change leftState.defs[
                                (rightPath.root.value.toNat - 1)]? ≠ none at resident'
                              change before.defs[(rightPath.root.value.toNat - 1)]? ≠ none
                              rw [leftFrame.defs] at resident'
                              exact resident'
                          change rightState.defs[(parent.value.toNat - 1)]? ≠ none
                          change before.defs[(parent.value.toNat - 1)]? ≠ none at beforeResident
                          rw [rightFrame.defs, leftFrame.defs]
                          exact beforeResident
                        exact rightState.setPlain?_checked after column child
                          (some parent) rightChecked (by
                            intro target equality
                            cases Option.some.inj equality
                            exact parentResident) joined

theorem Dense.unionPlain_fusedChecked (before after : Dense)
    (column : PlainColumn) (left right : Ref) (beforeChecked : FusedChecked before)
    (result : before.unionPlain column left right = .ok after) :
    FusedChecked after := by
  have frame := before.unionPlain_frame after column left right result
  have afterChecked := before.unionPlain_checked after column left right
    beforeChecked.toChecked result
  have selectedDecreases : (after.plainColumn column).Decreases :=
    before.unionPlain_decreases after column left right
    (by
      cases column
      · exact beforeChecked.eqDecreases
      · exact beforeChecked.synEqDecreases) result
  refine {
    toChecked := afterChecked
    eqDecreases := ?_
    synEqDecreases := ?_
    convDecreases := ?_
    classifierShape := ?_
  }
  · cases column with
    | semantic => exact selectedDecreases
    | syntactic =>
        intro source target edge
        apply beforeChecked.eqDecreases
        simpa [Dense.plainColumn] using frame.other ▸ edge
  · cases column with
    | semantic =>
        intro source target edge
        apply beforeChecked.synEqDecreases
        simpa [Dense.plainColumn] using frame.other ▸ edge
    | syntactic => exact selectedDecreases
  · intro source target edge
    apply beforeChecked.convDecreases
    exact frame.conv ▸ edge
  · intro value classifier edge
    have oldEdge : ClassifierEdge before value classifier := by
      refine ⟨frame.conv ▸ edge.1, ?_⟩
      intro same
      apply edge.2
      obtain ⟨category, valueCategory, classifierCategory⟩ := same
      exact ⟨category, frame.tagSort?_eq value ▸ valueCategory,
        frame.tagSort?_eq classifier ▸ classifierCategory⟩
    have shape := beforeChecked.classifierShape oldEdge
    rcases shape with shape | shape
    · exact Or.inl ⟨frame.tagSort?_eq value ▸ shape.1,
        frame.tagSort?_eq classifier ▸ shape.2⟩
    · exact Or.inr ⟨frame.tagSort?_eq value ▸ shape.1,
        frame.tagSort?_eq classifier ▸ shape.2⟩

/-- A successful ordinary union preserves every old class and adds exactly
the single join between the original classes of its two arguments. -/
theorem Dense.unionPlain_class_iff_joined (before after : Dense)
    (column : PlainColumn) (left right : Ref)
    (result : before.unionPlain column left right = .ok after) :
    Class after column.relation a b ↔
      PlainJoinedClass before column left right a b := by
  unfold Dense.unionPlain at result
  cases leftResult : before.plainPath column left with
  | error error => rw [leftResult, exceptDoError] at result; contradiction
  | ok leftPath =>
    rw [leftResult, exceptDoOk] at result
    obtain ⟨_, _, leftWitness⟩ :=
      before.plainPath_ok_witness column left leftPath leftResult
    have leftIn := before.plainPath_ok_source_mem column left leftPath leftResult
    have leftConnected := leftWitness.memberConnected left leftIn
    cases preflight : before.plainPath column right with
    | error error => rw [preflight, exceptDoError] at result; contradiction
    | ok rightPreflight =>
      rw [preflight, exceptDoOk] at result
      cases leftCompressed : before.compressPlain column leftPath with
      | none => rw [leftCompressed, requireValue, exceptDoError] at result; contradiction
      | some leftState =>
        rw [leftCompressed, requireValue, exceptDoOk] at result
        have leftUpdate := before.compressPlain_spec leftState column leftPath leftCompressed
        cases rightFound : leftState.plainPath column right with
        | error error => rw [rightFound, exceptDoError] at result; contradiction
        | ok rightPath =>
          rw [rightFound, exceptDoOk] at result
          obtain ⟨_, _, rightWitness⟩ :=
            leftState.plainPath_ok_witness column right rightPath rightFound
          have rightIn := leftState.plainPath_ok_source_mem column right rightPath rightFound
          have rightConnectedState := rightWitness.memberConnected right rightIn
          cases rightCompressed : leftState.compressPlain column rightPath with
          | none => rw [rightCompressed, requireValue, exceptDoError] at result; contradiction
          | some rightState =>
            rw [rightCompressed, requireValue, exceptDoOk] at result
            have rightUpdate := leftState.compressPlain_spec rightState column
              rightPath rightCompressed
            have compressionIff : ∀ {x y},
                Class rightState column.relation x y ↔
                  Class before column.relation x y := by
              intro x y
              exact (rightUpdate.class_iff rightWitness).trans
                (leftUpdate.class_iff leftWitness)
            have rightConnected : Class before column.relation right rightPath.root :=
              (leftUpdate.class_iff leftWitness).mp rightConnectedState
            by_cases same : leftPath.root = rightPath.root
            · rw [if_pos same] at result
              change Except.ok rightState = Except.ok after at result
              cases result
              have generators : Class before column.relation left right :=
                leftConnected.trans (same ▸ rightConnected.symm)
              exact compressionIff.trans
                (PlainJoinedClass.of_connected_iff generators).symm
            · rw [if_neg same] at result
              let child := max leftPath.root rightPath.root
              let parent := min leftPath.root rightPath.root
              dsimp only at result
              cases joined : rightState.setPlain? column child (some parent) with
              | none => rw [joined, requireValue] at result; contradiction
              | some final =>
                rw [joined, requireValue] at result
                simp only [Except.ok.injEq] at result
                subst final
                have cell := rightState.setPlain?_spec after column child
                  (some parent) joined
                have leftRootEmpty :
                    (rightState.plainColumn column).get? leftPath.root = none := by
                  by_cases inRight : leftPath.root ∈ rightPath.members
                  · have leftEmpty := leftUpdate.updated leftPath.root leftWitness.rootMember
                    simp only at leftEmpty
                    have preserved := rightUpdate.toPlainFrame
                    have emptyInLeftState :
                        (leftState.plainColumn column).get? leftPath.root = none := leftEmpty
                    have eqRoot := leftState.plainPath_ok_empty_member_eq_root column right
                      leftPath.root rightPath rightFound inRight emptyInLeftState
                    exact (same eqRoot).elim
                  · rw [rightUpdate.unchanged leftPath.root inRight]
                    simpa using leftUpdate.updated leftPath.root leftWitness.rootMember
                have rightRootEmpty :
                    (rightState.plainColumn column).get? rightPath.root = none := by
                  simpa using rightUpdate.updated rightPath.root rightWitness.rootMember
                have overwritten : ∀ {target},
                    Edge rightState column.relation child target →
                      Class after column.relation child target := by
                  intro target edge
                  have empty : (rightState.plainColumn column).get? child = none := by
                    rcases max_choice leftPath.root rightPath.root with choice | choice
                    · simpa [child, choice] using leftRootEmpty
                    · simpa [child, choice] using rightRootEmpty
                  cases column
                  · simp only [Dense.plainColumn] at empty
                    simp only [Edge, PlainColumn.relation] at edge
                    change Column.get? rightState.eq child = some target at edge
                    rw [empty] at edge
                    contradiction
                  · simp only [Dense.plainColumn] at empty
                    simp only [Edge, PlainColumn.relation] at edge
                    change Column.get? rightState.synEq child = some target at edge
                    rw [empty] at edge
                    contradiction
                have joinedIff := cell.class_iff_joined overwritten (left := a) (right := b)
                have rootsIff : PlainJoinedClass rightState column child parent a b ↔
                    PlainJoinedClass rightState column leftPath.root rightPath.root a b := by
                  have equalOfMaxMin
                      (equal : max leftPath.root rightPath.root =
                        min leftPath.root rightPath.root) :
                      leftPath.root = rightPath.root := by
                    apply le_antisymm
                    · exact (le_max_left _ _).trans
                        (equal ▸ min_le_right _ _)
                    · exact (le_max_right _ _).trans
                        (equal ▸ min_le_left _ _)
                  rcases max_choice leftPath.root rightPath.root with maxEq | maxEq <;>
                    rcases min_choice leftPath.root rightPath.root with minEq | minEq
                  · exact (same (equalOfMaxMin (maxEq.trans minEq.symm))).elim
                  · simp [child, parent, maxEq, minEq]
                  · simp [child, parent, maxEq, minEq, PlainJoinedClass,
                      or_comm]
                  · exact (same (equalOfMaxMin (maxEq.trans minEq.symm))).elim
                exact joinedIff.trans <| rootsIff.trans <|
                  (PlainJoinedClass.class_congr compressionIff).trans <|
                  PlainJoinedClass.generator_congr leftConnected rightConnected

theorem Dense.unionPlain_connected (before after : Dense)
    (column : PlainColumn) (left right : Ref)
    (result : before.unionPlain column left right = .ok after) :
    Class after column.relation left right := by
  rw [before.unionPlain_class_iff_joined after column left right result]
  right
  exact ⟨Or.inl (Class.refl _), Or.inr (Class.refl _)⟩

/-- Observable checked-kernel result of the three calls. An error carries the
state left by the already-completed coarser stages. Ordinary unions are fully
transactional. Conversion preflight errors are transactional; its defensive
post-compression path-recomputation error can expose compression only for a
malformed private Rust state and is proved unreachable from `FusedChecked`.
The pure `Except` model intentionally does not represent that raw state. -/
inductive UnionSynResult
  | success (state : Dense)
  | failure (state : Dense) (error : Dense.ConvError)
  deriving DecidableEq, Repr

def Dense.unionSynFact (equivalent : Dense.Equivalent) (dense : Dense)
    (left right : Ref) (relation : SynRel) : UnionSynResult :=
  match dense.unionPlain .semantic left right with
  | .error error => .failure dense error
  | .ok semanticState =>
      match semanticState.unionConv equivalent left right with
      | .error error => .failure semanticState error
      | .ok conversionState =>
          if relation = .syn then
            match conversionState.unionPlain .syntactic left right with
            | .error error => .failure conversionState error
            | .ok syntacticState => .success syntacticState
          else .success conversionState

/-- Exact state-aware counterpart of Rust `union_syn_fact`. In particular,
an error from the post-semantic classifier equivalence query retains the
already-mutated semantic state. -/
def Dense.unionSynFactExact (dense : Dense) (left right : Ref)
    (relation : SynRel) : UnionSynResult :=
  match dense.unionPlain .semantic left right with
  | .error error => .failure dense error
  | .ok semanticState =>
      match semanticState.unionConvExact left right with
      | .error error => .failure semanticState error
      | .ok conversionState =>
          if relation = .syn then
            match conversionState.unionPlain .syntactic left right with
            | .error error => .failure conversionState error
            | .ok syntacticState => .success syntacticState
          else .success conversionState

theorem Dense.unionSynFact_semantic_failure
    (dense : Dense) (equivalent : Dense.Equivalent) (left right : Ref)
    (relation : SynRel) (error : Dense.ConvError)
    (semantic : dense.unionPlain .semantic left right = Except.error error) :
    dense.unionSynFact equivalent left right relation =
      UnionSynResult.failure dense error := by
  simp [Dense.unionSynFact, semantic]

theorem Dense.unionSynFact_conversion_failure
    (dense semanticState : Dense) (equivalent : Dense.Equivalent) (left right : Ref)
    (relation : SynRel) (error : Dense.ConvError)
    (semantic : dense.unionPlain .semantic left right = Except.ok semanticState)
    (conversion : semanticState.unionConv equivalent left right = Except.error error) :
    dense.unionSynFact equivalent left right relation =
      UnionSynResult.failure semanticState error := by
  simp [Dense.unionSynFact, semantic, conversion]

theorem Dense.unionSynFact_syntactic_failure
    (dense semanticState conversionState : Dense) (equivalent : Dense.Equivalent)
    (left right : Ref) (relation : SynRel) (error : Dense.ConvError)
    (semantic : dense.unionPlain .semantic left right = Except.ok semanticState)
    (conversion : semanticState.unionConv equivalent left right = Except.ok conversionState)
    (syntacticRelation : relation = SynRel.syn)
    (syntactic : conversionState.unionPlain .syntactic left right = Except.error error) :
    dense.unionSynFact equivalent left right relation =
      UnionSynResult.failure conversionState error := by
  simp [Dense.unionSynFact, semantic, conversion, syntacticRelation, syntactic]

/-- Preconditions established by `direct_fact` and checked row lookup before
the first mutation. Authorization to add the coarse equality comes from the
proof-producing HOL rule and is outside this cache-refinement layer. -/
structure DirectFactPreconditions (dense : Dense) (equivalent : Dense.Equivalent)
    (left right : Ref) (relation : SynRel) : Prop where
  leftResident : dense.expr? left ≠ none
  rightResident : dense.expr? right ≠ none
  sameCategory : SameCategory dense left right

inductive StageOutcome
  | success
  | failure
  deriving DecidableEq, Repr

/-- Exact logical footprint of the first, semantic, union attempt. Path
compression or joining may change `eq`, but expression, syntactic, and fused
conversion storage are unchanged. A failed attempt may have compressed a
prefix, so preservation is stated by semantic-class monotonicity rather than
raw-column equality. -/
structure SemanticUnion (before after : Dense) (left right : Ref)
    (outcome : StageOutcome) : Prop where
  defs : after.defs = before.defs
  synEq : after.synEq = before.synEq
  conv : after.conv = before.conv
  synIff : ∀ {a b}, Class after .syn a b ↔ Class before .syn a b
  convIff : ∀ {a b}, Class after .conv a b ↔ Class before .conv a b
  checked : FusedChecked before → FusedChecked after
  semanticMono : ∀ {a b}, Class before .semantic a b →
    Class after .semantic a b
  semanticCases : ∀ {a b}, Class after .semantic a b →
    PlainJoinedClass before .semantic left right a b
  connected : outcome = .success → Class after .semantic left right

/-- Exact logical footprint of the fused conversion attempt. Semantic and
syntactic columns are unchanged. `supported` is the local obligation proved by
the classifier-equality check plus the concrete path/update theorems: every
conversion class visible after the attempt is semantically supported. -/
structure ConversionUnion (before after : Dense) (left right : Ref)
    (outcome : StageOutcome) : Prop where
  defs : after.defs = before.defs
  eq : after.eq = before.eq
  synEq : after.synEq = before.synEq
  checked : FusedChecked before → FusedChecked after
  semanticIff : ∀ {a b}, Class after .semantic a b ↔
    Class before .semantic a b
  synIff : ∀ {a b}, Class after .syn a b ↔ Class before .syn a b
  convMono : ∀ {a b}, Class before .conv a b → Class after .conv a b
  supported : ∀ {a b}, Class after .conv a b → Class after .semantic a b
  classifierSupported : FusedChecked before →
    ∀ {value oldClassifier newClassifier}, before.expr? value ≠ none →
      before.classifier? value = some oldClassifier →
      after.classifier? value = some newClassifier →
      Class before .semantic oldClassifier newClassifier
  classifierOptionality : FusedChecked before →
    ∀ {value}, before.expr? value ≠ none →
      ((∃ classifier, HasClassifier after value classifier) ↔
        ∃ classifier, HasClassifier before value classifier)
  connected : outcome = .success → Class after .conv left right

/-- Exact logical footprint of the optional final syntactic union. The fused
conversion and semantic columns are unchanged. -/
structure SyntacticUnion (before after : Dense) (left right : Ref)
    (outcome : StageOutcome) : Prop where
  defs : after.defs = before.defs
  eq : after.eq = before.eq
  conv : after.conv = before.conv
  checked : FusedChecked before → FusedChecked after
  semanticIff : ∀ {a b}, Class after .semantic a b ↔
    Class before .semantic a b
  convIff : ∀ {a b}, Class after .conv a b ↔ Class before .conv a b
  supported : ∀ {a b}, Class after .syn a b → Class after .conv a b
  connected : outcome = .success → Class after .syn left right

theorem semanticUnion_of_unionPlain_ok
    (found : before.unionPlain .semantic left right = .ok after) :
    SemanticUnion before after left right .success := by
  have frame := before.unionPlain_frame after .semantic left right found
  exact {
    defs := frame.defs
    synEq := frame.other
    conv := frame.conv
    synIff := frame.syn_class_iff
    convIff := frame.conv_class_iff
    checked := fun checked =>
      before.unionPlain_fusedChecked after .semantic left right checked found
    semanticMono := by
      intro a b connected
      apply (before.unionPlain_class_iff_joined after .semantic left right found).mpr
      exact Or.inl connected
    semanticCases := fun connected =>
      (before.unionPlain_class_iff_joined after .semantic left right found).mp connected
    connected := fun _ => before.unionPlain_connected after .semantic left right found
  }

theorem syntacticUnion_of_unionPlain_ok
    (beforeRefines : Refines before)
    (endpoints : Class before .conv left right)
    (found : before.unionPlain .syntactic left right = .ok after) :
    SyntacticUnion before after left right .success := by
  have frame := before.unionPlain_frame after .syntactic left right found
  exact {
    defs := frame.defs
    eq := frame.other
    conv := frame.conv
    checked := fun checked =>
      before.unionPlain_fusedChecked after .syntactic left right checked found
    semanticIff := frame.semantic_class_iff
    convIff := frame.conv_class_iff
    supported := by
      intro a b related
      rcases (before.unionPlain_class_iff_joined after .syntactic left right
        (a := a) (b := b) found).mp related with old | ⟨aSide, bSide⟩
      · exact frame.conv_class_iff.mpr (beforeRefines.syn_conv old)
      · have lift : ∀ {x},
            (Class before .syn x left ∨ Class before .syn x right) →
              Class before .conv x left ∨ Class before .conv x right := by
          intro x side
          rcases side with xLeft | xRight
          · exact Or.inl (beforeRefines.syn_conv xLeft)
          · exact Or.inr (beforeRefines.syn_conv xRight)
        rcases lift aSide with aLeft | aRight <;>
          rcases lift bSide with bLeft | bRight
        · exact frame.conv_class_iff.mpr (aLeft.trans bLeft.symm)
        · exact frame.conv_class_iff.mpr
            ((aLeft.trans endpoints).trans bRight.symm)
        · exact frame.conv_class_iff.mpr
            (aRight.trans (bLeft.trans endpoints).symm)
        · exact frame.conv_class_iff.mpr (aRight.trans bRight.symm)
    connected := fun _ =>
      before.unionPlain_connected after .syntactic left right found
  }

private theorem Dense.UnionConvTrace.classifier_exists_iff
    (trace : Dense.UnionConvTrace equivalent before left right after)
    (checked : FusedChecked before) (resident : before.expr? value ≠ none) :
    (∃ classifier, HasClassifier after value classifier) ↔
      ∃ classifier, HasClassifier before value classifier := by
  have afterChecked := trace.fusedChecked checked
  cases trace with
  | @sameRoot category leftPath rightPreflight rightPath leftCompressed after
      _ _ _ leftFound _ leftCompression rightFound rightCompression _ =>
      have leftUpdate := Dense.compressMembers_spec leftPath before leftCompressed
        leftCompression
      have rightUpdate := Dense.compressMembers_spec rightPath leftCompressed after
        rightCompression
      obtain ⟨_, _, leftWitness⟩ :=
        Dense.convPath_ok_witness before left leftPath leftFound
      obtain ⟨_, _, rightWitness⟩ :=
        Dense.convPath_ok_witness leftCompressed right rightPath rightFound
      constructor <;> rintro ⟨classifier, classified⟩
      · exact ⟨classifier, (leftUpdate.has_classifier_iff leftWitness).mp <|
          (rightUpdate.has_classifier_iff rightWitness).mp classified⟩
      · exact ⟨classifier, (rightUpdate.has_classifier_iff rightWitness).mpr <|
          (leftUpdate.has_classifier_iff leftWitness).mpr classified⟩
  | @joined category leftPath rightPreflight rightPath leftCompressed compressed
      child parent after leftCategoryFound rightCategoryFound agreement leftFound
      rightPreflightFound leftCompression rightFound rightCompression different
      childEq parentEq joined =>
      have leftUpdate := Dense.compressMembers_spec leftPath before leftCompressed
        leftCompression
      have rightUpdate := Dense.compressMembers_spec rightPath leftCompressed compressed
        rightCompression
      have cell := Dense.setConv?_spec compressed after child (some parent) joined
      obtain ⟨leftCategory, leftSourceCategory, leftWitness⟩ :=
        Dense.convPath_ok_witness before left leftPath leftFound
      have leftCategoryEq : leftCategory = category :=
        Option.some.inj (leftSourceCategory.symm.trans leftCategoryFound)
      subst leftCategory
      have leftChecked := Dense.compressMembers_fusedChecked leftPath before
        leftCompressed category leftWitness
        (Dense.convPath_ok_order before left leftPath checked.convDecreases leftFound)
        checked leftCompression
      obtain ⟨rightCategory, rightSourceCategory, rightWitness⟩ :=
        Dense.convPath_ok_witness leftCompressed right rightPath rightFound
      have rightCategoryEq : rightCategory = category := by
        have original : before.tagSort? right = some rightCategory := by
          simpa [leftUpdate.tagSort?_eq] using rightSourceCategory
        exact Option.some.inj (original.symm.trans rightCategoryFound)
      subst rightCategory
      have compressedChecked := Dense.compressMembers_fusedChecked rightPath
        leftCompressed compressed category rightWitness
        (Dense.convPath_ok_order leftCompressed right rightPath
          leftChecked.convDecreases rightFound) leftChecked rightCompression
      have compressedResident : compressed.expr? value ≠ none := by
        simpa [rightUpdate.expr?_eq, leftUpdate.expr?_eq] using resident
      have leftRootCategory : compressed.tagSort? leftPath.root = some category := by
        simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
          leftWitness.rootCategory
      have rightRootCategory : compressed.tagSort? rightPath.root = some category := by
        simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory
      have same : SameCategory compressed child parent := by
        rw [childEq, parentEq]
        rcases lt_or_gt_of_ne different with order | order
        · rw [max_eq_right order.le, min_eq_left order.le]
          exact ⟨category, rightRootCategory, leftRootCategory⟩
        · rw [max_eq_left order.le, min_eq_right order.le]
          exact ⟨category, leftRootCategory, rightRootCategory⟩
      have compressionIff :
          (∃ classifier, HasClassifier compressed value classifier) ↔
            ∃ classifier, HasClassifier before value classifier := by
        constructor <;> rintro ⟨classifier, classified⟩
        · exact ⟨classifier, (leftUpdate.has_classifier_iff leftWitness).mp <|
            (rightUpdate.has_classifier_iff rightWitness).mp classified⟩
        · exact ⟨classifier, (rightUpdate.has_classifier_iff rightWitness).mpr <|
            (leftUpdate.has_classifier_iff leftWitness).mpr classified⟩
      rcases agreement with kindCategory | classifierAgreement
      · have childKind : compressed.tagSort? child = some .kind := by
          rw [childEq]
          rcases max_choice leftPath.root rightPath.root with maximum | maximum
          · rw [maximum]
            simpa [kindCategory] using leftRootCategory
          · rw [maximum]
            simpa [kindCategory] using rightRootCategory
        exact (cell.hasClassifier_exists_iff_of_kind compressedChecked afterChecked
          compressedResident childKind).trans compressionIff
      · obtain ⟨leftClassifier, rightClassifier, leftClassifierFound,
            rightClassifierFound, _⟩ := classifierAgreement
        have leftResident := Dense.convPath_ok_source_resident before left leftPath leftFound
        have rightResident := Dense.convPath_ok_source_resident before right
          rightPreflight rightPreflightFound
        have leftLookup : before.classifier? left = some leftClassifier := by
          simpa [Dense.checkedClassifier?, leftResident] using leftClassifierFound
        have rightLookup : before.classifier? right = some rightClassifier := by
          simpa [Dense.checkedClassifier?, rightResident] using rightClassifierFound
        have leftClassified := (checked.classifierLookup leftResident).mp leftLookup
        have rightClassified := (checked.classifierLookup rightResident).mp rightLookup
        obtain ⟨_, _, leftRoute⟩ := HasClassifier.route checked leftResident leftClassified
        have leftAtRoot := leftRoute.inside_classifier leftWitness
          (Dense.convPath_ok_source_mem before left leftPath leftFound)
        have rightClassifiedLeft : HasClassifier leftCompressed right rightClassifier :=
          (leftUpdate.has_classifier_iff leftWitness).mpr rightClassified
        have rightResidentLeft : leftCompressed.expr? right ≠ none := by
          simpa [leftUpdate.expr?_eq] using rightResident
        obtain ⟨_, _, rightRoute⟩ :=
          HasClassifier.route leftChecked rightResidentLeft rightClassifiedLeft
        have rightAtRoot := rightRoute.inside_classifier rightWitness
          (Dense.convPath_ok_source_mem leftCompressed right rightPath rightFound)
        have leftEdge : ClassifierEdge compressed leftPath.root leftClassifier :=
          (rightUpdate.classifier_edge_iff rightWitness).mpr <|
            (leftUpdate.classifier_edge_iff leftWitness).mpr
              (leftWitness.classifier leftClassifier leftAtRoot).1
        have rightEdge : ClassifierEdge compressed rightPath.root rightClassifier :=
          (rightUpdate.classifier_edge_iff rightWitness).mpr
            (rightWitness.classifier rightClassifier rightAtRoot).1
        rcases lt_or_gt_of_ne different with order | order
        · have childIs : child = rightPath.root := childEq.trans (max_eq_right order.le)
          have parentIs : parent = leftPath.root := parentEq.trans (min_eq_left order.le)
          have cell' : Dense.ConvCellUpdate compressed after rightPath.root
              (some leftPath.root) := by simpa [childIs, parentIs] using cell
          have parentEdge : ClassifierEdge after leftPath.root leftClassifier :=
            cell'.classifierEdge_of_ne different leftEdge
          have same' : SameCategory compressed rightPath.root leftPath.root := by
            simpa [childIs, parentIs] using same
          exact (cell'.hasClassifier_exists_iff same' compressedChecked afterChecked
            compressedResident rightEdge parentEdge).trans compressionIff
        · have childIs : child = leftPath.root := childEq.trans (max_eq_left order.le)
          have parentIs : parent = rightPath.root := parentEq.trans (min_eq_right order.le)
          have cell' : Dense.ConvCellUpdate compressed after leftPath.root
              (some rightPath.root) := by simpa [childIs, parentIs] using cell
          have parentEdge : ClassifierEdge after rightPath.root rightClassifier :=
            cell'.classifierEdge_of_ne different.symm rightEdge
          have same' : SameCategory compressed leftPath.root rightPath.root := by
            simpa [childIs, parentIs] using same
          exact (cell'.hasClassifier_exists_iff same' compressedChecked afterChecked
            compressedResident leftEdge parentEdge).trans compressionIff

theorem conversionUnion_of_unionConv_ok
    (beforeRefines : Refines before)
    (equivalentSound : EquivalentPairSound before equivalent left right)
    (endpoints : Class before .semantic left right)
    (found : before.unionConv equivalent left right = .ok after) :
    ConversionUnion before after left right .success := by
  have trace := before.unionConv_ok_trace equivalent after left right found
  cases trace with
  | @sameRoot category leftPath rightPreflight rightPath leftCompressed after
      leftCategoryFound rightCategoryFound _ leftFound _ leftCompression rightFound
      rightCompression same =>
      have leftUpdate := Dense.compressMembers_spec leftPath before leftCompressed leftCompression
      have rightUpdate := Dense.compressMembers_spec rightPath leftCompressed after rightCompression
      obtain ⟨leftCategory, leftSourceCategory, leftWitness⟩ :=
        Dense.convPath_ok_witness before left leftPath leftFound
      obtain ⟨rightCategory, rightSourceCategory, rightWitness⟩ :=
        Dense.convPath_ok_witness leftCompressed right rightPath rightFound
      have classes : ∀ {a b}, Class after .conv a b ↔ Class before .conv a b := by
        intro a b
        exact (rightUpdate.conv_class_iff rightWitness).trans
          (leftUpdate.conv_class_iff leftWitness)
      have afterRefines := rightUpdate.refines rightWitness
        (leftUpdate.refines leftWitness beforeRefines)
      exact {
        defs := rightUpdate.defs.trans leftUpdate.defs
        eq := rightUpdate.eq.trans leftUpdate.eq
        synEq := rightUpdate.synEq.trans leftUpdate.synEq
        checked := fun checked =>
          (before.unionConv_ok_trace equivalent after left right found).fusedChecked checked
        semanticIff := rightUpdate.semantic_class_iff.trans leftUpdate.semantic_class_iff
        synIff := rightUpdate.syn_class_iff.trans leftUpdate.syn_class_iff
        convMono := fun related => classes.mpr related
        supported := afterRefines.conv_semantic
        classifierSupported := by
          intro checked value oldClassifier newClassifier resident oldFound newFound
          exact (before.unionConv_ok_trace equivalent after left right found).classifier_supported
            equivalentSound checked resident oldFound newFound
        classifierOptionality := by
          intro checked value resident
          exact (before.unionConv_ok_trace equivalent after left right found)
            |>.classifier_exists_iff checked resident
        connected := by
          intro _
          apply classes.mpr
          have leftConnected := leftWitness.memberConnected left
            (before.convPath_ok_source_mem left leftPath leftFound)
          have rightConnected := (leftUpdate.conv_class_iff leftWitness).mp
            (rightWitness.memberConnected right
              (leftCompressed.convPath_ok_source_mem right rightPath rightFound))
          exact Relation.EqvGen.trans _ _ _ leftConnected
            (same ▸ rightConnected.symm)
      }
  | @joined category leftPath rightPreflight rightPath leftCompressed compressed
      child parent after leftCategoryFound rightCategoryFound _ leftFound _
      leftCompression rightFound rightCompression different childEq parentEq joined =>
      have leftUpdate := Dense.compressMembers_spec leftPath before leftCompressed
        leftCompression
      have rightUpdate := Dense.compressMembers_spec rightPath leftCompressed compressed
        rightCompression
      have cell := Dense.setConv?_spec compressed after child (some parent) joined
      obtain ⟨leftCategory, leftSourceCategory, leftWitness⟩ :=
        Dense.convPath_ok_witness before left leftPath leftFound
      obtain ⟨rightCategory, rightSourceCategory, rightWitness⟩ :=
        Dense.convPath_ok_witness leftCompressed right rightPath rightFound
      have leftRootNo : ∀ {target},
          ¬ConvEdge leftCompressed leftPath.root target :=
        leftUpdate.root_no_convEdge leftWitness
      have leftRootNoCompressed : ∀ {target},
          ¬ConvEdge compressed leftPath.root target :=
        rightUpdate.preserve_distinct_root_no_convEdge rightFound different leftRootNo
      have rightRootNoCompressed : ∀ {target},
          ¬ConvEdge compressed rightPath.root target :=
        rightUpdate.root_no_convEdge rightWitness
      have childNo : ∀ {target}, ¬ConvEdge compressed child target := by
        intro target
        rw [childEq]
        rcases max_choice leftPath.root rightPath.root with maximum | maximum
        · rw [maximum]
          exact leftRootNoCompressed
        · rw [maximum]
          exact rightRootNoCompressed
      have overwritten : ∀ {target}, ConvEdge compressed child target →
          ConvClass after child target := by
        intro target edge
        exact (childNo edge).elim
      have leftConnected : ConvClass before left leftPath.root :=
        leftWitness.memberConnected left
          (before.convPath_ok_source_mem left leftPath leftFound)
      have rightConnectedLeft : ConvClass leftCompressed right rightPath.root :=
        rightWitness.memberConnected right
          (leftCompressed.convPath_ok_source_mem right rightPath rightFound)
      have rightConnected : ConvClass before right rightPath.root :=
        (leftUpdate.conv_class_iff leftWitness).mp rightConnectedLeft
      have rootsSemanticBefore : Class before .semantic leftPath.root rightPath.root :=
        (beforeRefines.conv_semantic leftConnected).symm |>.trans <|
          endpoints.trans (beforeRefines.conv_semantic rightConnected)
      have rootsSemanticCompressed :
          Class compressed .semantic leftPath.root rightPath.root :=
        rightUpdate.semantic_class_iff.mpr <|
          leftUpdate.semantic_class_iff.mpr rootsSemanticBefore
      have rootOrder : leftPath.root < rightPath.root ∨
          rightPath.root < leftPath.root := lt_or_gt_of_ne different
      have childParentSemantic : Class compressed .semantic child parent := by
        rw [childEq, parentEq]
        rcases rootOrder with order | order
        · rw [max_eq_right (le_of_lt order), min_eq_left (le_of_lt order)]
          exact rootsSemanticCompressed.symm
        · rw [max_eq_left (le_of_lt order), min_eq_right (le_of_lt order)]
          exact rootsSemanticCompressed
      have newSound : ∀ {target}, ConvEdge after child target →
          Class after .semantic child target := by
        intro target edge
        have targetEq : target = parent :=
          Option.some.inj (edge.1.symm.trans cell.updated)
        subst target
        exact cell.semantic_class_iff.mpr childParentSemantic
      have compressedRefines := rightUpdate.refines rightWitness
        (leftUpdate.refines leftWitness beforeRefines)
      have afterRefines := compressedRefines.afterConvCellUpdate cell overwritten newSound
      have leftRootCategory : compressed.tagSort? leftPath.root = some category := by
        have categoryEq : leftCategory = category :=
          Option.some.inj (leftSourceCategory.symm.trans leftCategoryFound)
        subst leftCategory
        simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
          leftWitness.rootCategory
      have rightRootCategory : compressed.tagSort? rightPath.root = some category := by
        have originalRight : before.tagSort? right = some rightCategory := by
          simpa [leftUpdate.tagSort?_eq] using rightSourceCategory
        have categoryEq : rightCategory = category :=
          Option.some.inj (originalRight.symm.trans rightCategoryFound)
        subst rightCategory
        simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory
      have childParentCategory : SameCategory compressed child parent := by
        rw [childEq, parentEq]
        rcases rootOrder with order | order
        · rw [max_eq_right (le_of_lt order), min_eq_left (le_of_lt order)]
          exact ⟨category, rightRootCategory, leftRootCategory⟩
        · rw [max_eq_left (le_of_lt order), min_eq_right (le_of_lt order)]
          exact ⟨category, leftRootCategory, rightRootCategory⟩
      have joinedEdge : ConvEdge after child parent := by
        refine ⟨cell.updated, ?_⟩
        obtain ⟨edgeCategory, childCategory, parentCategory⟩ := childParentCategory
        exact ⟨edgeCategory, cell.tagSort?_eq child ▸ childCategory,
          cell.tagSort?_eq parent ▸ parentCategory⟩
      have rootsConnectedAfter : ConvClass after leftPath.root rightPath.root := by
        have linked : ConvClass after child parent := Relation.EqvGen.rel _ _ joinedEdge
        rw [childEq, parentEq] at linked
        rcases rootOrder with order | order
        · rw [max_eq_right (le_of_lt order), min_eq_left (le_of_lt order)] at linked
          exact linked.symm
        · rw [max_eq_left (le_of_lt order), min_eq_right (le_of_lt order)] at linked
          exact linked
      have leftConnectedCompressed : ConvClass compressed left leftPath.root :=
        rightUpdate.conv_class_iff rightWitness |>.mpr <|
          leftUpdate.conv_class_iff leftWitness |>.mpr leftConnected
      have rightConnectedCompressed : ConvClass compressed right rightPath.root :=
        rightUpdate.conv_class_iff rightWitness |>.mpr rightConnectedLeft
      exact {
        defs := cell.defs.trans (rightUpdate.defs.trans leftUpdate.defs)
        eq := cell.eq.trans (rightUpdate.eq.trans leftUpdate.eq)
        synEq := cell.synEq.trans (rightUpdate.synEq.trans leftUpdate.synEq)
        checked := fun checked =>
          (before.unionConv_ok_trace equivalent after left right found).fusedChecked checked
        semanticIff := cell.semantic_class_iff.trans <|
          rightUpdate.semantic_class_iff.trans leftUpdate.semantic_class_iff
        synIff := cell.syn_class_iff.trans <|
          rightUpdate.syn_class_iff.trans leftUpdate.syn_class_iff
        convMono := fun related => cell.convClass_mono overwritten <|
          rightUpdate.conv_class_iff rightWitness |>.mpr <|
            leftUpdate.conv_class_iff leftWitness |>.mpr related
        supported := afterRefines.conv_semantic
        classifierSupported := by
          intro checked value oldClassifier newClassifier resident oldFound newFound
          exact (before.unionConv_ok_trace equivalent after left right found).classifier_supported
            equivalentSound checked resident oldFound newFound
        classifierOptionality := by
          intro checked value resident
          exact (before.unionConv_ok_trace equivalent after left right found)
            |>.classifier_exists_iff checked resident
        connected := by
          intro _
          have leftAfter := cell.convClass_mono overwritten leftConnectedCompressed
          have rightAfter := cell.convClass_mono overwritten rightConnectedCompressed
          exact Relation.EqvGen.trans _ _ _ leftAfter <|
            Relation.EqvGen.trans _ _ _ rootsConnectedAfter rightAfter.symm
      }

theorem semanticUnion_failure_identity (dense : Dense) (left right : Ref) :
    SemanticUnion dense dense left right .failure := {
  defs := rfl
  synEq := rfl
  conv := rfl
  synIff := Iff.rfl
  convIff := Iff.rfl
  checked := id
  semanticMono := id
  semanticCases := fun connected => Or.inl connected
  connected := by simp
}

theorem conversionUnion_failure_identity (dense : Dense) (left right : Ref)
    (refines : Refines dense) :
    ConversionUnion dense dense left right .failure := {
  defs := rfl
  eq := rfl
  synEq := rfl
  checked := id
  semanticIff := Iff.rfl
  synIff := Iff.rfl
  convMono := id
  supported := refines.conv_semantic
  classifierSupported := by
    intro _ value oldClassifier newClassifier _ oldFound newFound
    have same : oldClassifier = newClassifier :=
      Option.some.inj (oldFound.symm.trans newFound)
    subst newClassifier
    exact Class.refl _
  classifierOptionality := fun _ _ _ => Iff.rfl
  connected := by simp
}

theorem syntacticUnion_failure_identity (dense : Dense) (left right : Ref)
    (refines : Refines dense) :
    SyntacticUnion dense dense left right .failure := {
  defs := rfl
  eq := rfl
  conv := rfl
  checked := id
  semanticIff := Iff.rfl
  convIff := Iff.rfl
  supported := refines.syn_conv
  connected := by simp
}

theorem SemanticUnion.refines (transition : SemanticUnion before after left right outcome)
    (refines : Refines before) : Refines after := by
  constructor
  · intro a b related
    have beforeSyn : Class before .syn a b := transition.synIff.mp related
    have beforeConv := refines.syn_conv beforeSyn
    exact transition.convIff.mpr beforeConv
  · intro a b related
    have beforeConv : Class before .conv a b := transition.convIff.mp related
    exact transition.semanticMono (refines.conv_semantic beforeConv)

theorem ConversionUnion.refines
    (transition : ConversionUnion before after left right outcome)
    (_refines : Refines before) : Refines after := by
  constructor
  · intro a b related
    exact transition.convMono <| _refines.syn_conv (transition.synIff.mp related)
  · exact transition.supported

theorem SyntacticUnion.refines
    (transition : SyntacticUnion before after left right outcome)
    (_refines : Refines before) : Refines after := by
  constructor
  · exact transition.supported
  · intro a b related
    exact transition.semanticIff.mpr <|
      _refines.conv_semantic (transition.convIff.mp related)

/-- A proof-relevant trace of the exact Rust statement order. Every error
constructor records the mutated state which remains observable to the caller. -/
inductive EqualitySequence (equivalent : Dense.Equivalent) (before : Dense)
    (left right : Ref) (relation : SynRel) : Dense → StageOutcome → Prop
  | semanticFailure
      (pre : DirectFactPreconditions before equivalent left right relation)
      (semantic : SemanticUnion before after left right .failure) :
      EqualitySequence equivalent before left right relation after .failure
  | conversionFailure
      (pre : DirectFactPreconditions before equivalent left right relation)
      (semantic : SemanticUnion before semanticState left right .success)
      (conversion : ConversionUnion semanticState after left right .failure) :
      EqualitySequence equivalent before left right relation after .failure
  | conversionSuccess
      (notSyntactic : relation ≠ .syn)
      (pre : DirectFactPreconditions before equivalent left right relation)
      (semantic : SemanticUnion before semanticState left right .success)
      (conversion : ConversionUnion semanticState after left right .success) :
      EqualitySequence equivalent before left right relation after .success
  | syntacticFailure
      (relationSyntactic : relation = .syn)
      (pre : DirectFactPreconditions before equivalent left right relation)
      (semantic : SemanticUnion before semanticState left right .success)
      (conversion : ConversionUnion semanticState conversionState left right .success)
      (syntactic : SyntacticUnion conversionState after left right .failure) :
      EqualitySequence equivalent before left right relation after .failure
  | syntacticSuccess
      (relationSyntactic : relation = .syn)
      (pre : DirectFactPreconditions before equivalent left right relation)
      (semantic : SemanticUnion before semanticState left right .success)
      (conversion : ConversionUnion semanticState conversionState left right .success)
      (syntactic : SyntacticUnion conversionState after left right .success) :
      EqualitySequence equivalent before left right relation after .success

/-- The refinement invariant holds after every observable prefix, including
all three possible error returns. -/
theorem EqualitySequence.refines
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    (refines : Refines before) : Refines after := by
  cases sequence with
  | semanticFailure _ semantic => exact semantic.refines refines
  | conversionFailure _ semantic conversion =>
      exact conversion.refines (semantic.refines refines)
  | conversionSuccess _ _ semantic conversion =>
      exact conversion.refines (semantic.refines refines)
  | syntacticFailure _ _ semantic conversion syntactic =>
      exact syntactic.refines (conversion.refines (semantic.refines refines))
  | syntacticSuccess _ _ semantic conversion syntactic =>
      exact syntactic.refines (conversion.refines (semantic.refines refines))

/-- Checked structural invariants likewise survive every observable prefix. -/
theorem EqualitySequence.checked
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    (checked : FusedChecked before) : FusedChecked after := by
  cases sequence with
  | semanticFailure _ semantic => exact semantic.checked checked
  | conversionFailure _ semantic conversion =>
      exact conversion.checked (semantic.checked checked)
  | conversionSuccess _ _ semantic conversion =>
      exact conversion.checked (semantic.checked checked)
  | syntacticFailure _ _ semantic conversion syntactic =>
      exact syntactic.checked (conversion.checked (semantic.checked checked))
  | syntacticSuccess _ _ semantic conversion syntactic =>
      exact syntactic.checked (conversion.checked (semantic.checked checked))

/-- Executable equality insertion never changes the syntax-row allocation. -/
theorem EqualitySequence.defs
    (sequence : EqualitySequence equivalent before left right relation after outcome) :
    after.defs = before.defs := by
  cases sequence with
  | semanticFailure _ semantic => exact semantic.defs
  | conversionFailure _ semantic conversion =>
      exact conversion.defs.trans semantic.defs
  | conversionSuccess _ _ semantic conversion =>
      exact conversion.defs.trans semantic.defs
  | syntacticFailure _ _ semantic conversion syntactic =>
      exact syntactic.defs.trans (conversion.defs.trans semantic.defs)
  | syntacticSuccess _ _ semantic conversion syntactic =>
      exact syntactic.defs.trans (conversion.defs.trans semantic.defs)

/-- Every semantic class after an executable prefix is generated by an old
class and the one endpoint equality authorized by the caller. -/
theorem EqualitySequence.semanticCases
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    (connected : Class after .semantic a b) :
    PlainJoinedClass before .semantic left right a b := by
  cases sequence with
  | semanticFailure _ semantic => exact semantic.semanticCases connected
  | conversionFailure _ semantic conversion =>
      exact semantic.semanticCases (conversion.semanticIff.mp connected)
  | conversionSuccess _ _ semantic conversion =>
      exact semantic.semanticCases (conversion.semanticIff.mp connected)
  | syntacticFailure _ _ semantic conversion syntactic =>
      exact semantic.semanticCases <|
        conversion.semanticIff.mp (syntactic.semanticIff.mp connected)
  | syntacticSuccess _ _ semantic conversion syntactic =>
      exact semantic.semanticCases <|
        conversion.semanticIff.mp (syntactic.semanticIff.mp connected)

/-- Eliminate a post-union semantic class into any equivalence relation which
already validates the old cache and the newly authorized endpoint fact. -/
theorem EqualitySequence.semanticSound
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    {R : Ref → Ref → Prop}
    (oldSound : ∀ {a b}, Class before .semantic a b → R a b)
    (endpoint : R left right)
    (symm : ∀ {a b}, R a b → R b a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (connected : Class after .semantic a b) : R a b := by
  rcases sequence.semanticCases connected with old | ⟨aSide, bSide⟩
  · exact oldSound old
  · have aLeftOrRight : R a left ∨ R a right := by
      rcases aSide with aLeft | aRight
      · exact Or.inl (oldSound aLeft)
      · exact Or.inr (oldSound aRight)
    have bLeftOrRight : R b left ∨ R b right := by
      rcases bSide with bLeft | bRight
      · exact Or.inl (oldSound bLeft)
      · exact Or.inr (oldSound bRight)
    rcases aLeftOrRight with aLeft | aRight <;>
      rcases bLeftOrRight with bLeft | bRight
    · exact trans aLeft (symm bLeft)
    · exact trans (trans aLeft endpoint) (symm bRight)
    · exact trans (trans aRight (symm endpoint)) (symm bLeft)
    · exact trans aRight (symm bRight)

private theorem Dense.classifier?_eq_of_defs_conv
    (before after : Dense)
    (defs : after.defs = before.defs) (conv : after.conv = before.conv)
    (value : Ref) : after.classifier? value = before.classifier? value := by
  have tagEq : ∀ reference,
      Nucleus.Hol.Ethane.OneBased.Dense.tagSort? after reference =
        Nucleus.Hol.Ethane.OneBased.Dense.tagSort? before reference := by
    intro reference
    change (after.defs[(reference.value.toNat - 1)]?).map (·.tag.sort) =
      (before.defs[(reference.value.toNat - 1)]?).map (·.tag.sort)
    rw [defs]
  have lookupEq : ∀ fuel reference,
      Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? after fuel reference =
        Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? before fuel reference := by
    intro fuel
    induction fuel with
    | zero => intro reference; rfl
    | succ fuel ih =>
        intro reference
        simp only [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?]
        rw [conv]
        split
        · rfl
        · rename_i _ target _
          rw [tagEq reference, tagEq target]
          split
          · exact ih target
          · split <;> rfl
  change Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?
      after (after.defs.length + 1) value = _
  rw [defs]
  exact lookupEq _ _

private theorem Dense.expr?_neq_of_defs
    (before after : Dense) (defs : after.defs = before.defs)
    (resident : before.expr? value ≠ none) : after.expr? value ≠ none := by
  change after.defs[(value.value.toNat - 1)]? ≠ none
  change before.defs[(value.value.toNat - 1)]? ≠ none at resident
  rw [defs]
  exact resident

private theorem Dense.hasClassifier_exists_iff_of_defs_conv
    (beforeChecked : FusedChecked before) (afterChecked : FusedChecked after)
    (defs : after.defs = before.defs) (conv : after.conv = before.conv)
    (resident : before.expr? value ≠ none) :
    (∃ classifier, HasClassifier after value classifier) ↔
      ∃ classifier, HasClassifier before value classifier := by
  have afterResident := Dense.expr?_neq_of_defs before after defs resident
  have lookupEq := Dense.classifier?_eq_of_defs_conv before after defs conv value
  constructor <;> rintro ⟨classifier, classified⟩
  · have found := afterChecked.classifierComplete afterResident classified
    rw [lookupEq] at found
    exact ⟨classifier, (beforeChecked.classifierLookup resident).mp found⟩
  · have found := beforeChecked.classifierComplete resident classified
    rw [← lookupEq] at found
    exact ⟨classifier, (afterChecked.classifierLookup afterResident).mp found⟩

/-- Equality insertion preserves classifier optionality for every resident
syntax row, even when conversion path compression changes its classifier id. -/
theorem EqualitySequence.classifierOptionality
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    (checked : FusedChecked before) (resident : before.expr? value ≠ none) :
    (∃ classifier, HasClassifier after value classifier) ↔
      ∃ classifier, HasClassifier before value classifier := by
  cases sequence with
  | semanticFailure _ semantic =>
      exact Dense.hasClassifier_exists_iff_of_defs_conv checked
        (semantic.checked checked) semantic.defs semantic.conv resident
  | conversionFailure _ semantic conversion =>
      have semanticChecked := semantic.checked checked
      have semanticResident := Dense.expr?_neq_of_defs _ _ semantic.defs resident
      exact (conversion.classifierOptionality semanticChecked semanticResident).trans <|
        Dense.hasClassifier_exists_iff_of_defs_conv checked semanticChecked
          semantic.defs semantic.conv resident
  | conversionSuccess _ _ semantic conversion =>
      have semanticChecked := semantic.checked checked
      have semanticResident := Dense.expr?_neq_of_defs _ _ semantic.defs resident
      exact (conversion.classifierOptionality semanticChecked semanticResident).trans <|
        Dense.hasClassifier_exists_iff_of_defs_conv checked semanticChecked
          semantic.defs semantic.conv resident
  | syntacticFailure _ _ semantic conversion syntactic =>
      have semanticChecked := semantic.checked checked
      have conversionChecked := conversion.checked semanticChecked
      have semanticResident := Dense.expr?_neq_of_defs _ _ semantic.defs resident
      have conversionResident := Dense.expr?_neq_of_defs _ _ conversion.defs semanticResident
      exact (Dense.hasClassifier_exists_iff_of_defs_conv conversionChecked
        (syntactic.checked conversionChecked) syntactic.defs syntactic.conv
        conversionResident).trans <| (conversion.classifierOptionality semanticChecked
          semanticResident).trans <| Dense.hasClassifier_exists_iff_of_defs_conv
            checked semanticChecked semantic.defs semantic.conv resident
  | syntacticSuccess _ _ semantic conversion syntactic =>
      have semanticChecked := semantic.checked checked
      have conversionChecked := conversion.checked semanticChecked
      have semanticResident := Dense.expr?_neq_of_defs _ _ semantic.defs resident
      have conversionResident := Dense.expr?_neq_of_defs _ _ conversion.defs semanticResident
      exact (Dense.hasClassifier_exists_iff_of_defs_conv conversionChecked
        (syntactic.checked conversionChecked) syntactic.defs syntactic.conv
        conversionResident).trans <| (conversion.classifierOptionality semanticChecked
          semanticResident).trans <| Dense.hasClassifier_exists_iff_of_defs_conv
            checked semanticChecked semantic.defs semantic.conv resident

/-- Classifier changes made by the executable conversion stage are justified
by the old semantic relation and the one semantic equality inserted first. -/
theorem EqualitySequence.classifierCases
    (sequence : EqualitySequence equivalent before left right relation after outcome)
    (checked : FusedChecked before) (resident : before.expr? value ≠ none)
    (oldFound : before.classifier? value = some oldClassifier)
    (newFound : after.classifier? value = some newClassifier) :
    PlainJoinedClass before .semantic left right oldClassifier newClassifier := by
  cases sequence with
  | semanticFailure _ semantic =>
      have unchanged := Dense.classifier?_eq_of_defs_conv _ _ semantic.defs semantic.conv value
      have same : oldClassifier = newClassifier :=
        Option.some.inj (oldFound.symm.trans (unchanged.symm.trans newFound))
      subst newClassifier
      exact Or.inl (Class.refl _)
  | conversionFailure _ semantic conversion =>
      have semanticLookup := oldFound
      rw [← Dense.classifier?_eq_of_defs_conv _ _ semantic.defs semantic.conv value]
        at semanticLookup
      exact semantic.semanticCases <| conversion.classifierSupported
        (semantic.checked checked) (Dense.expr?_neq_of_defs _ _ semantic.defs resident)
        semanticLookup newFound
  | conversionSuccess _ _ semantic conversion =>
      have semanticLookup := oldFound
      rw [← Dense.classifier?_eq_of_defs_conv _ _ semantic.defs semantic.conv value]
        at semanticLookup
      exact semantic.semanticCases <| conversion.classifierSupported
        (semantic.checked checked) (Dense.expr?_neq_of_defs _ _ semantic.defs resident)
        semanticLookup newFound
  | syntacticFailure _ _ semantic conversion syntactic =>
      have semanticLookup := oldFound
      rw [← Dense.classifier?_eq_of_defs_conv _ _ semantic.defs semantic.conv value]
        at semanticLookup
      have conversionLookup := newFound
      rw [Dense.classifier?_eq_of_defs_conv _ _ syntactic.defs syntactic.conv value]
        at conversionLookup
      exact semantic.semanticCases <| conversion.classifierSupported
        (semantic.checked checked) (Dense.expr?_neq_of_defs _ _ semantic.defs resident)
        semanticLookup conversionLookup
  | syntacticSuccess _ _ semantic conversion syntactic =>
      have semanticLookup := oldFound
      rw [← Dense.classifier?_eq_of_defs_conv _ _ semantic.defs semantic.conv value]
        at semanticLookup
      have conversionLookup := newFound
      rw [Dense.classifier?_eq_of_defs_conv _ _ syntactic.defs syntactic.conv value]
        at conversionLookup
      exact semantic.semanticCases <| conversion.classifierSupported
        (semantic.checked checked) (Dense.expr?_neq_of_defs _ _ semantic.defs resident)
        semanticLookup conversionLookup

/-- A late error cannot invalidate the checked kernel cache. This is the
formal reason for installing the coarsest relation first. -/
theorem EqualitySequence.failure_safe
    (sequence : EqualitySequence equivalent before left right relation after .failure)
    (checked : FusedChecked before) (refines : Refines before) :
    FusedChecked after ∧ Refines after :=
  ⟨sequence.checked checked, sequence.refines refines⟩

theorem unionSynFact_semantic_failure_sequence
    (pre : DirectFactPreconditions dense equivalent left right relation)
    (error : Dense.ConvError)
    (failed : dense.unionPlain .semantic left right = .error error) :
    dense.unionSynFact equivalent left right relation =
        .failure dense error ∧
      EqualitySequence equivalent dense left right relation dense .failure := by
  exact ⟨dense.unionSynFact_semantic_failure equivalent left right relation error failed,
    .semanticFailure pre (semanticUnion_failure_identity dense left right)⟩

theorem unionSynFact_conversion_failure_sequence
    (pre : DirectFactPreconditions dense equivalent left right relation)
    (beforeRefines : Refines dense)
    (semanticFound : dense.unionPlain .semantic left right = .ok semanticState)
    (error : Dense.ConvError)
    (conversionFailed : semanticState.unionConv equivalent left right = .error error) :
    dense.unionSynFact equivalent left right relation =
        .failure semanticState error ∧
      EqualitySequence equivalent dense left right relation semanticState .failure := by
  have semantic := semanticUnion_of_unionPlain_ok semanticFound
  have semanticRefines := semantic.refines beforeRefines
  exact ⟨dense.unionSynFact_conversion_failure semanticState equivalent left right
      relation error semanticFound conversionFailed,
    .conversionFailure pre semantic
      (conversionUnion_failure_identity semanticState left right semanticRefines)⟩

theorem unionSynFact_syntactic_failure_sequence
    (pre : DirectFactPreconditions dense equivalent left right relation)
    (pairSound : EquivalentPairSound dense equivalent left right)
    (beforeRefines : Refines dense)
    (semanticFound : dense.unionPlain .semantic left right = .ok semanticState)
    (conversionFound : semanticState.unionConv equivalent left right =
      .ok conversionState)
    (relationSyntactic : relation = .syn)
    (error : Dense.ConvError)
    (syntacticFailed : conversionState.unionPlain .syntactic left right =
      .error error) :
    dense.unionSynFact equivalent left right relation =
        .failure conversionState error ∧
      EqualitySequence equivalent dense left right relation conversionState .failure := by
  have semantic := semanticUnion_of_unionPlain_ok semanticFound
  have semanticRefines := semantic.refines beforeRefines
  have conversion := conversionUnion_of_unionConv_ok semanticRefines
    (by
      intro leftClassifier rightClassifier leftFound rightFound accepted
      apply semantic.semanticMono
      apply pairSound
      · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs semantic.conv]
      · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs semantic.conv]
      · exact accepted)
    (semantic.connected rfl) conversionFound
  have conversionRefines := conversion.refines semanticRefines
  exact ⟨dense.unionSynFact_syntactic_failure semanticState conversionState equivalent
      left right relation error semanticFound conversionFound relationSyntactic syntacticFailed,
    .syntacticFailure relationSyntactic pre semantic conversion
      (syntacticUnion_failure_identity conversionState left right conversionRefines)⟩

/-- A successful executable call yields the proof-relevant trace of the exact
semantic, conversion, and optional syntactic mutations which produced it. -/
theorem unionSynFact_success_sequence
    (pre : DirectFactPreconditions before equivalent left right relation)
    (pairSound : EquivalentPairSound before equivalent left right)
    (beforeRefines : Refines before)
    (result : before.unionSynFact equivalent left right relation = .success after) :
    EqualitySequence equivalent before left right relation after .success := by
  unfold Dense.unionSynFact at result
  cases semanticFound : before.unionPlain .semantic left right with
  | error error => simp [semanticFound] at result
  | ok semanticState =>
      rw [semanticFound] at result
      simp only at result
      cases conversionFound : semanticState.unionConv equivalent left right with
      | error error => simp [conversionFound] at result
      | ok conversionState =>
          rw [conversionFound] at result
          simp only at result
          have semantic := semanticUnion_of_unionPlain_ok semanticFound
          have semanticRefines := semantic.refines beforeRefines
          have conversion := conversionUnion_of_unionConv_ok semanticRefines
            (by
              intro leftClassifier rightClassifier leftFound rightFound accepted
              apply semantic.semanticMono
              apply pairSound
              · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs semantic.conv]
              · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs semantic.conv]
              · exact accepted)
            (semantic.connected rfl) conversionFound
          by_cases relationSyntactic : relation = .syn
          · rw [if_pos relationSyntactic] at result
            cases syntacticFound : conversionState.unionPlain .syntactic left right with
            | error error => simp [syntacticFound] at result
            | ok syntacticState =>
                rw [syntacticFound] at result
                cases result
                exact .syntacticSuccess relationSyntactic pre semantic conversion <|
                  syntacticUnion_of_unionPlain_ok (conversion.refines semanticRefines)
                    (conversion.connected rfl) syntacticFound
          · rw [if_neg relationSyntactic] at result
            cases result
            exact .conversionSuccess relationSyntactic pre semantic conversion

/-- Every observable result of the executable three-stage model carries its
exact proof-relevant prefix certificate. -/
theorem unionSynFact_result_sequence
    (pre : DirectFactPreconditions before equivalent left right relation)
    (pairSound : EquivalentPairSound before equivalent left right)
    (beforeRefines : Refines before) (result : UnionSynResult)
    (found : before.unionSynFact equivalent left right relation = result) :
    match result with
    | .success after =>
        EqualitySequence equivalent before left right relation after .success
    | .failure after _ =>
        EqualitySequence equivalent before left right relation after .failure := by
  cases result with
  | success after => exact unionSynFact_success_sequence pre pairSound beforeRefines found
  | failure failedState error =>
      unfold Dense.unionSynFact at found
      cases semanticFound : before.unionPlain .semantic left right with
      | error semanticError =>
          rw [semanticFound] at found
          simp only at found
          cases found
          exact .semanticFailure pre
            (semanticUnion_failure_identity before left right)
      | ok semanticState =>
          rw [semanticFound] at found
          simp only at found
          cases conversionFound : semanticState.unionConv equivalent left right with
          | error conversionError =>
              rw [conversionFound] at found
              simp only at found
              have semantic := semanticUnion_of_unionPlain_ok semanticFound
              have failure := conversionUnion_failure_identity semanticState left right <|
                semantic.refines beforeRefines
              cases found
              exact .conversionFailure pre semantic failure
          | ok conversionState =>
              rw [conversionFound] at found
              simp only at found
              by_cases relationSyntactic : relation = .syn
              · rw [if_pos relationSyntactic] at found
                cases syntacticFound : conversionState.unionPlain .syntactic left right with
                | error syntacticError =>
                    rw [syntacticFound] at found
                    have semantic := semanticUnion_of_unionPlain_ok semanticFound
                    have semanticRefines := semantic.refines beforeRefines
                    have conversion := conversionUnion_of_unionConv_ok semanticRefines
                      (by
                        intro leftClassifier rightClassifier leftFound rightFound accepted
                        apply semantic.semanticMono
                        apply pairSound
                        · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs
                            semantic.conv]
                        · rwa [← Dense.checkedClassifierEqEarly _ _ semantic.defs
                            semantic.conv]
                        · exact accepted)
                      (semantic.connected rfl) conversionFound
                    have failure := syntacticUnion_failure_identity conversionState
                      left right (conversion.refines semanticRefines)
                    cases found
                    exact .syntacticFailure relationSyntactic pre semantic conversion failure
                | ok syntacticState =>
                    rw [syntacticFound] at found
                    contradiction
              · rw [if_neg relationSyntactic] at found
                contradiction

/-- The exact state-aware model of Rust `union_syn_fact` produces the same
proof-relevant transition sequence as the abstract cache layer.  The witness
callback is chosen after the semantic stage because Rust queries classifier
equality in that already-mutated state. -/
theorem unionSynFactExact_result_sequence
    (leftResident : before.expr? left ≠ none)
    (rightResident : before.expr? right ≠ none)
    (sameCategory : SameCategory before left right)
    (beforeRefines : Refines before) (result : UnionSynResult)
    (found : before.unionSynFactExact left right relation = result) :
    ∃ equivalent,
      match result with
      | .success after =>
          EqualitySequence equivalent before left right relation after .success
      | .failure after _ =>
          EqualitySequence equivalent before left right relation after .failure := by
  let pre (equivalent : Dense.Equivalent) :
      DirectFactPreconditions before equivalent left right relation := {
    leftResident
    rightResident
    sameCategory
  }
  cases result with
  | success after =>
      unfold Dense.unionSynFactExact at found
      cases semanticFound : before.unionPlain .semantic left right with
      | error error => simp [semanticFound] at found
      | ok semanticState =>
          rw [semanticFound] at found
          simp only at found
          cases conversionFound : semanticState.unionConvExact left right with
          | error error => simp [conversionFound] at found
          | ok conversionState =>
              rw [conversionFound] at found
              simp only at found
              obtain ⟨equivalent, pairSound, abstractFound⟩ :=
                semanticState.unionConvExact_ok_certificate conversionState
                  left right conversionFound
              have semantic := semanticUnion_of_unionPlain_ok semanticFound
              have semanticRefines := semantic.refines beforeRefines
              have conversion := conversionUnion_of_unionConv_ok semanticRefines
                pairSound (semantic.connected rfl) abstractFound
              by_cases relationSyntactic : relation = .syn
              · rw [if_pos relationSyntactic] at found
                cases syntacticFound : conversionState.unionPlain .syntactic left right with
                | error error => simp [syntacticFound] at found
                | ok syntacticState =>
                    rw [syntacticFound] at found
                    cases found
                    exact ⟨equivalent, .syntacticSuccess relationSyntactic
                      (pre equivalent) semantic conversion <|
                        syntacticUnion_of_unionPlain_ok
                          (conversion.refines semanticRefines)
                          (conversion.connected rfl) syntacticFound⟩
              · rw [if_neg relationSyntactic] at found
                cases found
                exact ⟨equivalent, .conversionSuccess relationSyntactic
                  (pre equivalent) semantic conversion⟩
  | failure failedState error =>
      unfold Dense.unionSynFactExact at found
      cases semanticFound : before.unionPlain .semantic left right with
      | error semanticError =>
          rw [semanticFound] at found
          simp only at found
          cases found
          let equivalent : Dense.Equivalent := fun _ _ => false
          exact ⟨equivalent, .semanticFailure (pre equivalent)
            (semanticUnion_failure_identity before left right)⟩
      | ok semanticState =>
          rw [semanticFound] at found
          simp only at found
          have semantic := semanticUnion_of_unionPlain_ok semanticFound
          have semanticRefines := semantic.refines beforeRefines
          cases conversionFound : semanticState.unionConvExact left right with
          | error conversionError =>
              rw [conversionFound] at found
              simp only at found
              cases found
              let equivalent : Dense.Equivalent := fun _ _ => false
              exact ⟨equivalent, .conversionFailure (pre equivalent) semantic
                (conversionUnion_failure_identity failedState left right
                  semanticRefines)⟩
          | ok conversionState =>
              rw [conversionFound] at found
              simp only at found
              obtain ⟨equivalent, pairSound, abstractFound⟩ :=
                semanticState.unionConvExact_ok_certificate conversionState
                  left right conversionFound
              have conversion := conversionUnion_of_unionConv_ok semanticRefines
                pairSound (semantic.connected rfl) abstractFound
              by_cases relationSyntactic : relation = .syn
              · rw [if_pos relationSyntactic] at found
                cases syntacticFound : conversionState.unionPlain .syntactic left right with
                | error syntacticError =>
                    rw [syntacticFound] at found
                    cases found
                    exact ⟨equivalent, .syntacticFailure relationSyntactic
                      (pre equivalent) semantic conversion
                        (syntacticUnion_failure_identity failedState left right
                          (conversion.refines semanticRefines))⟩
                | ok syntacticState =>
                    rw [syntacticFound] at found
                    contradiction
              · rw [if_neg relationSyntactic] at found
                contradiction

/-- Assemble the successful Rust path. Alpha/conversion facts stop after the
fused conversion stage; literal-syntax facts perform the third union. -/
theorem unionSynFact_ok_sequence
    (pre : DirectFactPreconditions before equivalent left right relation)
    (semantic : SemanticUnion before semanticState left right .success)
    (conversion : ConversionUnion semanticState conversionState left right .success)
    (syntactic : relation = .syn →
      ∃ after, SyntacticUnion conversionState after left right .success) :
    ∃ after, EqualitySequence equivalent before left right relation after .success := by
  by_cases relationSyntactic : relation = .syn
  · obtain ⟨after, final⟩ := syntactic relationSyntactic
    exact ⟨after, .syntacticSuccess relationSyntactic pre semantic conversion final⟩
  · exact ⟨conversionState,
      .conversionSuccess relationSyntactic pre semantic conversion⟩

end Nucleus.Hol.Ethane.OneBased.Columns
