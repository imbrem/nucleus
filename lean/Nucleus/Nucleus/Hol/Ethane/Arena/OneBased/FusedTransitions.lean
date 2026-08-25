import Nucleus.Hol.Ethane.Arena.OneBased.Columns

/-!
# Executable fused conversion transitions

This file is the functional model of the category-sensitive conversion forest
in `logic/hol/src/kernel.rs`.  It is deliberately separate from the wire
layout: decoded columns are inert data, while these are the only shapes of
mutation performed by a checked kernel.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

namespace Dense

private theorem refPosition_injective :
    Function.Injective (fun reference : Ref => reference.1.toNat - 1) := by
  intro left right positions
  change left.1.toNat - 1 = right.1.toNat - 1 at positions
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  have leftPositive : 0 < left.1.toNat := Nat.pos_of_ne_zero fun zero =>
    left.property.1 (UInt64.toNat_inj.mp (show left.1.toNat = (0 : UInt64).toNat by
      simpa using zero))
  have rightPositive : 0 < right.1.toNat := Nat.pos_of_ne_zero fun zero =>
    right.property.1 (UInt64.toNat_inj.mp (show right.1.toNat = (0 : UInt64).toNat by
      simpa using zero))
  omega

/-- The successful result of Rust's `conv_path`. `members` includes the root.
For a malformed cycle, `root` is the least member of the cycle and
`classifier` is absent, exactly as in Rust. -/
structure ConvPath where
  root : Ref
  classifier : Option Ref
  members : List Ref
  deriving DecidableEq, Repr

inductive ConvError where
  | missing (reference : Ref)
  | noClassifier (reference : Ref)
  | wrongCategory (reference : Ref) (expected actual : TagSort)
  | classifierMismatch (expected actual : Ref)
  | exhausted
  deriving DecidableEq, Repr

def expectedClassifier : TagSort → Option TagSort
  | .kind => none
  | .ty => some .kind
  | .tm => some .ty

def cycleRoot (current : Ref) (members : List Ref) : Ref :=
  ((members.dropWhile (· != current)).min?).getD current

/-- Fuelled executable counterpart of the Rust loop.  On resident columns,
`defs.length + 1` is sufficient: every same-category step visits a fresh
resident definition or exposes a cycle. -/
def convPathLoop (dense : Dense) (category : TagSort) :
    Nat → List Ref → Ref → Except ConvError ConvPath
  | 0, _, _ => .error .exhausted
  | fuel + 1, members, current =>
      if current ∈ members then
        .ok { root := cycleRoot current members, classifier := none, members }
      else
        let members := members ++ [current]
        match dense.conv.get? current with
        | none => .ok { root := current, classifier := none, members }
        | some parent =>
            match dense.tagSort? parent with
            | none => .error (.missing parent)
            | some parentCategory =>
                if parentCategory = category then
                  convPathLoop dense category fuel members parent
                else
                  match expectedClassifier category with
                  | none => .error (.wrongCategory parent category parentCategory)
                  | some expected =>
                      if parentCategory = expected then
                        .ok { root := current, classifier := some parent, members }
                      else .error (.wrongCategory parent expected parentCategory)

/-- Read-only path traversal. The initial source is checked for residency
before any column read, matching `Kernel::category_as`. -/
def convPath (dense : Dense) (reference : Ref) : Except ConvError ConvPath :=
  match dense.tagSort? reference with
  | none => .error (.missing reference)
  | some category => convPathLoop dense category (dense.defs.length + 1) [] reference

theorem convPath_ok_source_resident (dense : Dense) (reference : Ref)
    (path : ConvPath) (found : dense.convPath reference = .ok path) :
    dense.expr? reference ≠ none := by
  intro missing
  have noCategory : dense.tagSort? reference = none := by
    change (Nucleus.Hol.Ethane.OneBased.Dense.expr? dense reference).map
      (·.tag.sort) = none
    have missing' : Nucleus.Hol.Ethane.OneBased.Dense.expr? dense reference = none :=
      missing
    rw [missing']
    rfl
  simp [convPath, noCategory] at found

/-- `classifier?` is guarded by source residency exactly like Rust's public
kernel query. Raw dangling or absent sources never acquire a classifier. -/
def checkedClassifier? (dense : Dense) (reference : Ref) : Option Ref :=
  if dense.expr? reference = none then none else dense.classifier? reference

@[simp] theorem checkedClassifier?_missing (dense : Dense) (reference : Ref)
    (missing : dense.expr? reference = none) :
    dense.checkedClassifier? reference = none := by
  simp [checkedClassifier?, missing]

@[simp] theorem checkedClassifier?_resident (dense : Dense) (reference : Ref)
    (resident : dense.expr? reference ≠ none) :
    dense.checkedClassifier? reference = dense.classifier? reference := by
  simp [checkedClassifier?, resident]

/-- Exact trailing-null-eliding update used by `Dense::set_column`. -/
def setColumnNormalized (column : Column α) (position : Nat) (value : Option α) : Column α :=
  let extended := column ++ List.replicate (position + 1 - column.length) none
  Column.normalize (extended.set position value)

@[simp] theorem getElem?_setColumnNormalized_self
    (column : Column α) (position : Nat) (value : Option α) :
    (setColumnNormalized column position value)[position]?.bind id = value := by
  rw [setColumnNormalized, Column.getElem?_normalize_bind, List.getElem?_set]
  have inside : position <
      (column ++ List.replicate (position + 1 - column.length) none).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [if_pos inside]
  simp

theorem getElem?_setColumnNormalized_of_ne
    (column : Column α) (position other : Nat) (value : Option α)
    (different : position ≠ other) :
    (setColumnNormalized column position value)[other]?.bind id =
      column[other]?.bind id := by
  rw [setColumnNormalized, Column.getElem?_normalize_bind, List.getElem?_set]
  simp only [if_neg different]
  by_cases inside : other < column.length
  · rw [List.getElem?_append_left inside]
  · have beyond : column[other]? = none := List.getElem?_eq_none (Nat.le_of_not_gt inside)
    rw [beyond]
    simp only [Option.bind_none]
    rw [List.getElem?_append_right (Nat.le_of_not_gt inside)]
    simp [List.getElem?_replicate]

/-- Mutate a conversion cell only when its source is a resident definition. -/
def setConv? (dense : Dense) (reference : Ref) (value : Option Ref) : Option Dense :=
  let position := reference.value.toNat - 1
  if position < dense.defs.length then
    some { dense with conv := setColumnNormalized dense.conv position value }
  else none

structure ConvCellUpdate (before after : Dense) (reference : Ref)
    (value : Option Ref) : Prop where
  defs : after.defs = before.defs
  eq : after.eq = before.eq
  synEq : after.synEq = before.synEq
  updated : after.conv.get? reference = value
  unchanged : ∀ other, other ≠ reference →
    after.conv.get? other = before.conv.get? other

theorem setConv?_spec (before after : Dense) (reference : Ref)
    (value : Option Ref) (result : before.setConv? reference value = some after) :
    ConvCellUpdate before after reference value := by
  simp only [setConv?] at result
  split at result
  · simp only [Option.some.injEq] at result
    subst after
    constructor
    · rfl
    · rfl
    · rfl
    · exact getElem?_setColumnNormalized_self before.conv
        (reference.value.toNat - 1) value
    · intro other different
      exact getElem?_setColumnNormalized_of_ne before.conv
        (reference.value.toNat - 1) (other.value.toNat - 1) value
        (fun equal => different (refPosition_injective equal).symm)
  · simp at result

theorem ConvCellUpdate.expr?_eq (update : ConvCellUpdate before after reference value)
    (other : Ref) : after.expr? other = before.expr? other := by
  simp [Nucleus.Hol.Ethane.OneBased.Dense.expr?, update.defs]

theorem ConvCellUpdate.tagSort?_eq
    (update : ConvCellUpdate before after reference value) (other : Ref) :
    after.tagSort? other = before.tagSort? other := by
  simp [Nucleus.Hol.Ethane.OneBased.Dense.tagSort?, update.expr?_eq]

theorem ConvCellUpdate.semantic_edge_iff
    (update : ConvCellUpdate before after reference value) :
    Edge after .semantic left right ↔ Edge before .semantic left right := by
  simp [Edge, update.eq]

theorem ConvCellUpdate.semantic_class_iff
    (update : ConvCellUpdate before after reference value) :
    Class after .semantic left right ↔ Class before .semantic left right := by
  constructor <;> intro related
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (update.semantic_edge_iff.mp edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ leftMiddle middleRight =>
      exact Relation.EqvGen.trans _ _ _ leftMiddle middleRight
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (update.semantic_edge_iff.mpr edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Relation.EqvGen.trans _ _ _ leftMiddle middleRight

theorem ConvCellUpdate.syn_edge_iff
    (update : ConvCellUpdate before after reference value) :
    Edge after .syn left right ↔ Edge before .syn left right := by
  simp [Edge, update.synEq]

theorem ConvCellUpdate.syn_class_iff
    (update : ConvCellUpdate before after reference value) :
    Class after .syn left right ↔ Class before .syn left right := by
  constructor <;> intro related
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (update.syn_edge_iff.mp edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Relation.EqvGen.trans _ _ _ leftMiddle middleRight
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (update.syn_edge_iff.mpr edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Relation.EqvGen.trans _ _ _ leftMiddle middleRight
theorem ConvCellUpdate.convEdge_of_ne
    (update : ConvCellUpdate before after reference value)
    (different : left ≠ reference) (edge : ConvEdge before left right) :
    ConvEdge after left right := by
  refine ⟨update.unchanged left different ▸ edge.1, ?_⟩
  obtain ⟨category, leftCategory, rightCategory⟩ := edge.2
  exact ⟨category, update.tagSort?_eq left ▸ leftCategory,
    update.tagSort?_eq right ▸ rightCategory⟩

theorem ConvCellUpdate.convEdge_before_of_ne
    (update : ConvCellUpdate before after reference value)
    (different : left ≠ reference) (edge : ConvEdge after left right) :
    ConvEdge before left right := by
  refine ⟨update.unchanged left different ▸ edge.1, ?_⟩
  obtain ⟨category, leftCategory, rightCategory⟩ := edge.2
  exact ⟨category, update.tagSort?_eq left ▸ leftCategory,
    update.tagSort?_eq right ▸ rightCategory⟩

theorem ConvCellUpdate.classifierEdge_of_ne
    (update : ConvCellUpdate before after reference value)
    (different : root ≠ reference)
    (edge : ClassifierEdge before root classifier) :
    ClassifierEdge after root classifier := by
  refine ⟨update.unchanged root different ▸ edge.1, ?_⟩
  intro same
  apply edge.2
  obtain ⟨category, rootCategory, classifierCategory⟩ := same
  exact ⟨category, update.tagSort?_eq root ▸ rootCategory,
    update.tagSort?_eq classifier ▸ classifierCategory⟩

theorem ConvCellUpdate.classifierEdge_before_of_ne
    (update : ConvCellUpdate before after reference value)
    (different : root ≠ reference)
    (edge : ClassifierEdge after root classifier) :
    ClassifierEdge before root classifier := by
  refine ⟨update.unchanged root different ▸ edge.1, ?_⟩
  intro same
  apply edge.2
  obtain ⟨category, rootCategory, classifierCategory⟩ := same
  exact ⟨category, update.tagSort?_eq root ▸ rootCategory,
    update.tagSort?_eq classifier ▸ classifierCategory⟩

/-- A concrete one-cell update preserves every old conversion class once the
single overwritten outgoing edge is known to remain connected. -/
theorem ConvCellUpdate.convClass_mono
    (update : ConvCellUpdate before after reference value)
    (overwritten : ∀ {right}, ConvEdge before reference right →
      ConvClass after reference right)
    (connected : ConvClass before left right) : ConvClass after left right := by
  apply connected.mono
  intro edgeLeft edgeRight edge
  by_cases same : edgeLeft = reference
  · subst edgeLeft
    exact overwritten edge
  · exact Relation.EqvGen.rel _ _ (update.convEdge_of_ne same edge)

def compressMembers (path : ConvPath) (dense : Dense) : Option Dense :=
  path.members.foldlM (m := Option) (fun state member =>
    state.setConv? member (if member = path.root then path.classifier else some path.root)) dense

/-- Functional counterpart of `find_conv_mut`: traverse, then point every
visited non-root at the representative while restoring the root classifier.
The latter is the crucial difference from ordinary union-find compression. -/
def findConvMut (dense : Dense) (reference : Ref) : Except ConvError (Dense × Ref) := do
  let path ← dense.convPath reference
  match compressMembers path dense with
  | none => .error (.missing reference)
  | some compressed => .ok (compressed, path.root)

/-- Parameters kept abstract by the column model but supplied by the HOL
kernel: semantic equality of classifier references. -/
abbrev Equivalent := Ref → Ref → Bool

def require (error : ConvError) : Option α → Except ConvError α
  | none => .error error
  | some value => .ok value

/-- Functional counterpart of `union_conv`. Conversion classes are joined by
least root. For non-kinds, classifiers must be present and semantically equal.
The child's classifier edge is intentionally overwritten by the parent edge. -/
def unionConv (equivalent : Equivalent) (dense : Dense) (left right : Ref) :
    Except ConvError Dense := do
  let leftCategory ← require (.missing left) (dense.tagSort? left)
  let rightCategory ← require (.missing right) (dense.tagSort? right)
  if rightCategory != leftCategory then
    throw (.wrongCategory right leftCategory rightCategory)
  if leftCategory != .kind then
    let leftClassifier ← require (.noClassifier left) (dense.checkedClassifier? left)
    let rightClassifier ← require (.noClassifier right) (dense.checkedClassifier? right)
    if !equivalent leftClassifier rightClassifier then
      throw (.classifierMismatch leftClassifier rightClassifier)
  -- Rust validates both read-only paths before mutating either, so every
  -- preflight error leaves the conversion column unchanged. The pure model
  -- below discards state on `Except.error`; Rust can expose left compression
  -- if the defensive recomputation after it fails on malformed private
  -- state. `FusedChecked` preservation proves that branch unreachable for
  -- kernel states, which is the correspondence boundary used by the TCB.
  let leftPath ← dense.convPath left
  let _ ← dense.convPath right
  let leftRoot := leftPath.root
  let dense ← require (.missing left) (dense.compressMembers leftPath)
  -- Recompute against the compressed state.  Rust treats failure here as an
  -- invariant violation because the same path was successfully preflighted.
  let rightPath ← dense.convPath right
  let rightRoot := rightPath.root
  let dense ← require (.missing right) (dense.compressMembers rightPath)
  if leftRoot = rightRoot then return dense
  let child := max leftRoot rightRoot
  let parent := min leftRoot rightRoot
  match dense.setConv? child (some parent) with
  | none => throw (.missing child)
  | some joined => return joined

end Dense

/-! ## Preservation surface

An actual union does *not* preserve every classifier edge: the classifier on
the child root is replaced by its same-category parent.  What is preserved is
the classifier modulo semantic equality.  This is precisely what Rust checks
before mutation and what HOL typing consumes.
-/

/-- Classification modulo the semantic equality forest. -/
def HasSemanticClassifier (dense : Dense) (value classifier : Ref) : Prop :=
  ∃ actual, HasClassifier dense value actual ∧ Class dense .semantic actual classifier

theorem HasSemanticClassifier.of_exact
    (classified : HasClassifier dense value classifier) :
    HasSemanticClassifier dense value classifier :=
  ⟨classifier, classified, Class.refl classifier⟩

/-- General compression/union preservation theorem with the correct
classifier-replacement premise.  `classifiers` permits an old root classifier
to move to another root and to be replaced by a semantically equal classifier.
-/
theorem mutation_preserves_semantic_classifier
    (classes : ∀ {left right}, ConvEdge before left right →
      ConvClass after left right)
    (classifiers : ∀ {root classifier}, ClassifierEdge before root classifier →
      ∃ newRoot newClassifier,
        ConvClass after root newRoot ∧
        ClassifierEdge after newRoot newClassifier ∧
        Class after .semantic newClassifier classifier)
    (semantic : ∀ {left right}, Class before .semantic left right →
      Class after .semantic left right)
    (classified : HasSemanticClassifier before value classifier) :
    HasSemanticClassifier after value classifier := by
  obtain ⟨actual, ⟨root, valueRoot, edge⟩, actualClassifier⟩ := classified
  obtain ⟨newRoot, newClassifier, rootNewRoot, newEdge, replacement⟩ := classifiers edge
  refine ⟨newClassifier, ⟨newRoot, ?_, newEdge⟩, ?_⟩
  · exact Relation.EqvGen.trans _ _ _ (valueRoot.mono classes) rootNewRoot
  · exact Class.trans replacement (semantic actualClassifier)

/-- Exact classifier-preservation surface for one concrete cell update. Only
a classifier rooted at the overwritten source needs a replacement witness. -/
theorem Dense.ConvCellUpdate.semanticClassifier_mono
    (update : Dense.ConvCellUpdate before after reference value)
    (overwrittenConv : ∀ {right}, ConvEdge before reference right →
      ConvClass after reference right)
    (overwrittenClassifier : ∀ {classifier},
      ClassifierEdge before reference classifier →
      ∃ newRoot newClassifier,
        ConvClass after reference newRoot ∧
        ClassifierEdge after newRoot newClassifier ∧
        Class after .semantic newClassifier classifier)
    (classified : HasSemanticClassifier before subject classifier) :
    HasSemanticClassifier after subject classifier := by
  apply mutation_preserves_semantic_classifier
    (fun edge => update.convClass_mono overwrittenConv
      (Relation.EqvGen.rel _ _ edge)) _ _ classified
  · intro root oldClassifier edge
    by_cases same : root = reference
    · subst root
      exact overwrittenClassifier edge
    · exact ⟨root, oldClassifier, Relation.EqvGen.refl root,
        update.classifierEdge_of_ne same edge, Class.refl oldClassifier⟩
  · intro left right semantic
    exact update.semantic_class_iff.mpr semantic

/-- A concrete conversion-cell mutation preserves the cache refinement chain
when its overwritten old edge remains connected and its one new edge is
semantically sound. These are exactly the two local obligations discharged by
compression and checked union. -/
theorem Refines.afterConvCellUpdate
    (beforeRefines : Refines before)
    (update : Dense.ConvCellUpdate before after reference value)
    (overwritten : ∀ {right}, ConvEdge before reference right →
      ConvClass after reference right)
    (newSound : ∀ {right}, ConvEdge after reference right →
      Class after .semantic reference right) :
    Refines after := by
  constructor
  · intro left right related
    have beforeSyn : Class before .syn left right :=
      update.syn_class_iff.mp related
    exact update.convClass_mono overwritten (beforeRefines.syn_conv beforeSyn)
  · intro left right related
    induction related with
    | rel left right edge =>
        by_cases same : left = reference
        · subst left
          exact newSound edge
        · have oldEdge := update.convEdge_before_of_ne same edge
          exact update.semantic_class_iff.mpr
            (beforeRefines.conv_semantic (Relation.EqvGen.rel _ _ oldEdge))
    | refl reference => exact Class.refl reference
    | symm left right _ ih => exact Class.symm ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Class.trans leftMiddle middleRight

/-- Pure path compression is the special case where classifier edges are
retained literally. -/
theorem compression_preserves_semantic_classifier
    (classes : ∀ {left right}, ConvEdge before left right →
      ConvClass after left right)
    (classifiers : ∀ {root classifier}, ClassifierEdge before root classifier →
      ClassifierEdge after root classifier)
    (semantic : ∀ {left right}, Class before .semantic left right →
      Class after .semantic left right)
    (classified : HasSemanticClassifier before value classifier) :
    HasSemanticClassifier after value classifier := by
  apply mutation_preserves_semantic_classifier classes _ semantic classified
  intro root classifier edge
  exact ⟨root, classifier, Relation.EqvGen.refl root, classifiers edge,
    Class.refl classifier⟩

/-- If a mutation preserves/extends each cache edge at its corresponding
semantic level, the checked refinement chain remains valid. -/
theorem Refines.of_edge_sound
    (synConv : ∀ {left right}, Edge after .syn left right →
      Class after .conv left right)
    (convSemantic : ∀ {left right}, Edge after .conv left right →
      Class after .semantic left right) :
    Refines after := by
  constructor
  · intro left right related
    induction related with
    | rel left right edge => exact synConv edge
    | refl reference => exact Class.refl reference
    | symm left right _ ih => exact Class.symm ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Class.trans leftMiddle middleRight
  · intro left right related
    induction related with
    | rel left right edge => exact convSemantic edge
    | refl reference => exact Class.refl reference
    | symm left right _ ih => exact Class.symm ih
    | trans left middle right _ _ leftMiddle middleRight =>
        exact Class.trans leftMiddle middleRight

end Nucleus.Hol.Ethane.OneBased.Columns
