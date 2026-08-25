import Nucleus.Hol.Ethane.Arena.OneBased.FusedTransitions

/-!
# Correctness of executable fused-column traversal

This file connects the executable conversion traversal and compression in
`FusedTransitions` to the relational conversion classes used by the soundness
model.  In particular, successful traversal is not treated as an unchecked
oracle: it has an inductive certificate whose constructors expose every branch
of the executable loop.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

namespace Dense

/-- A proof-relevant trace of a successful `convPathLoop`.  This deliberately
retains the accumulated prefix: it makes the cycle branch, including its
least-root convention, explicit rather than hiding malformed input behind
fuel. -/
inductive ConvPathTrace (dense : Dense) (category : TagSort) :
    Nat → List Ref → Ref → ConvPath → Prop
  | cycle {fuel members current}
      (seen : current ∈ members) :
      ConvPathTrace dense category (fuel + 1) members current {
        root := cycleRoot current members
        classifier := none
        members := members
      }
  | root {fuel members current}
      (fresh : current ∉ members)
      (empty : dense.conv.get? current = none) :
      ConvPathTrace dense category (fuel + 1) members current {
        root := current
        classifier := none
        members := members ++ [current]
      }
  | classifier {fuel members current target parentCategory expected}
      (fresh : current ∉ members)
      (raw : dense.conv.get? current = some target)
      (targetCategory : dense.tagSort? target = some parentCategory)
      (different : parentCategory ≠ category)
      (expectedCategory : expectedClassifier category = some expected)
      (correct : parentCategory = expected) :
      ConvPathTrace dense category (fuel + 1) members current {
        root := current
        classifier := some target
        members := members ++ [current]
      }
  | step {fuel members current target path}
      (fresh : current ∉ members)
      (raw : dense.conv.get? current = some target)
      (same : dense.tagSort? target = some category)
      (tail : ConvPathTrace dense category fuel (members ++ [current]) target path) :
      ConvPathTrace dense category (fuel + 1) members current path

theorem convPathLoop_ok_trace (dense : Dense) (category : TagSort)
    (fuel : Nat) (members : List Ref) (current : Ref) (path : ConvPath)
    (found : dense.convPathLoop category fuel members current = .ok path) :
    ConvPathTrace dense category fuel members current path := by
  fun_induction convPathLoop generalizing path <;>
    simp_all only [Except.ok.injEq, reduceCtorEq]
  case case2 =>
    subst path
    exact .cycle ‹_›
  case case3 =>
    subst path
    exact .root ‹_› ‹_›
  case case5 =>
    exact .step ‹_› ‹_› ‹_› (by apply ‹∀ _, _›; rfl)
  case case7 =>
    subst path
    exact .classifier ‹_› ‹_› ‹_› ‹_› ‹_› rfl

private theorem ConvPathTrace.no_convEdge_member_eq_root
    (trace : ConvPathTrace dense category fuel members current path)
    (currentCategory : dense.tagSort? current = some category)
    (priorCategory : ∀ member ∈ members,
      dense.tagSort? member = some category)
    (priorEdge : ∀ member ∈ members, ∃ target, ConvEdge dense member target)
    (selected : Ref) (selectedIn : selected ∈ path.members)
    (selectedRoot : ∀ {target}, ¬ConvEdge dense selected target) :
    selected = path.root := by
  cases trace with
  | cycle seen =>
      obtain ⟨target, edge⟩ := priorEdge selected selectedIn
      exact (selectedRoot edge).elim
  | root fresh empty =>
      rcases List.mem_append.mp selectedIn with prior | last
      · obtain ⟨target, edge⟩ := priorEdge selected prior
        exact (selectedRoot edge).elim
      · simpa only [List.mem_singleton] using last
  | classifier fresh raw targetCategory different expected correct =>
      rcases List.mem_append.mp selectedIn with prior | last
      · obtain ⟨target, edge⟩ := priorEdge selected prior
        exact (selectedRoot edge).elim
      · simpa only [List.mem_singleton] using last
  | step fresh raw same tail =>
      apply tail.no_convEdge_member_eq_root
        (currentCategory := same)
        (priorCategory := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | last
          · exact priorCategory member prior
          · simp only [List.mem_singleton] at last
            subst member
            exact currentCategory)
        (priorEdge := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | last
          · exact priorEdge member prior
          · simp only [List.mem_singleton] at last
            subst member
            exact ⟨_, ⟨raw, ⟨category, currentCategory, same⟩⟩⟩)
        selected selectedIn selectedRoot
termination_by fuel

private theorem cycleRoot_mem {current : Ref} {members : List Ref}
    (seen : current ∈ members) : cycleRoot current members ∈ members := by
  have suffixNonempty : members.dropWhile (· != current) ≠ [] := by
    induction members with
    | nil => simp at seen
    | cons head tail ih =>
        by_cases equal : head = current
        · subst head
          simp
        · simp only [List.mem_cons] at seen
          have tailSeen : current ∈ tail := seen.resolve_left (Ne.symm equal)
          have test : (head != current) = true := bne_iff_ne.mpr equal
          rw [List.dropWhile, test]
          exact ih tailSeen
  obtain ⟨least, leastEq⟩ : ∃ least, (members.dropWhile (· != current)).min? = some least := by
    cases found : (members.dropWhile (· != current)).min? with
    | none =>
        have : members.dropWhile (· != current) = [] :=
          List.min?_eq_none_iff.mp found
        contradiction
    | some least => exact ⟨least, rfl⟩
  rw [cycleRoot, leastEq]
  simp only [Option.getD_some]
  exact (List.dropWhile_sublist (· != current)).mem (List.min?_mem leastEq)

/-- Accumulator invariant used by the executable loop.  Every prior member is
already in the conversion class of the current node, and every node has the
category fixed at traversal entry. -/
structure ConvAccumulator (dense : Dense) (category : TagSort)
    (members : List Ref) (current : Ref) : Prop where
  currentCategory : dense.tagSort? current = some category
  memberCategory : ∀ member ∈ members, dense.tagSort? member = some category
  memberConnected : ∀ member ∈ members, ConvClass dense member current
  successorClosed : ∀ member ∈ members, ∀ {target},
    ConvEdge dense member target → target ∈ members ∨ target = current
  noClassifier : ∀ member ∈ members, ∀ {classifier},
    ¬ ClassifierEdge dense member classifier

/-- The declarative content needed by compression. -/
structure ConvPathWitness (dense : Dense) (category : TagSort)
    (path : ConvPath) : Prop where
  rootMember : path.root ∈ path.members
  rootCategory : dense.tagSort? path.root = some category
  memberResident : ∀ member ∈ path.members, dense.expr? member ≠ none
  memberConnected : ∀ member ∈ path.members, ConvClass dense member path.root
  successorClosed : ∀ member ∈ path.members, ∀ {target},
    ConvEdge dense member target → target ∈ path.members
  classifierClosed : ∀ member ∈ path.members, ∀ {classifier},
    ClassifierEdge dense member classifier →
      member = path.root ∧ path.classifier = some classifier
  classifier : ∀ classifier, path.classifier = some classifier →
    ClassifierEdge dense path.root classifier ∧
      ClassifierShape dense path.root classifier

/-- Allocation-order information carried by a successfully traversed path.
It is deliberately separate from the graph-theoretic witness above: raw
arenas may contain cycles, while checked kernels require every fused link to
point strictly backward. -/
structure ConvPathOrder (path : ConvPath) : Prop where
  root_le : ∀ member ∈ path.members, path.root ≤ member
  classifier_lt : ∀ classifier, path.classifier = some classifier →
    classifier < path.root

private structure ConvOrderAccumulator (members : List Ref) (current : Ref) : Prop where
  current_lt : ∀ member ∈ members, current < member

private structure ConvMembershipAccumulator (members : List Ref)
    (current origin : Ref) : Prop where
  seen : origin = current ∨ origin ∈ members

private theorem ConvPathTrace.origin_mem
    (trace : ConvPathTrace dense category fuel members current path)
    (accumulator : ConvMembershipAccumulator members current origin) :
    origin ∈ path.members := by
  cases trace with
  | cycle currentSeen =>
      rcases accumulator.seen with rfl | seen
      · exact currentSeen
      · exact seen
  | root _ _ =>
      rcases accumulator.seen with rfl | seen
      · simp
      · exact List.mem_append_left _ seen
  | classifier _ _ _ _ _ _ =>
      rcases accumulator.seen with rfl | seen
      · simp
      · exact List.mem_append_left _ seen
  | step _ _ _ tail =>
      apply tail.origin_mem
      rcases accumulator.seen with rfl | seen
      · exact ⟨Or.inr (by simp)⟩
      · exact ⟨Or.inr (List.mem_append_left _ seen)⟩
termination_by fuel

theorem convPath_ok_source_mem (dense : Dense) (reference : Ref)
    (path : ConvPath) (found : dense.convPath reference = .ok path) :
    reference ∈ path.members := by
  unfold Dense.convPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      rw [categoryEq] at found
      have trace := dense.convPathLoop_ok_trace category
        (dense.defs.length + 1) [] reference path found
      exact trace.origin_mem ⟨Or.inl rfl⟩

private theorem ConvPathTrace.order
    (trace : ConvPathTrace dense category fuel members current path)
    (decreases : dense.conv.Decreases)
    (accumulator : ConvOrderAccumulator members current) :
    ConvPathOrder path := by
  cases trace with
  | cycle seen =>
      exact (lt_irrefl current (accumulator.current_lt current seen)).elim
  | root fresh empty =>
      refine {
        root_le := ?_
        classifier_lt := by simp
      }
      intro member memberIn
      rcases List.mem_append.mp memberIn with prior | last
      · exact (accumulator.current_lt member prior).le
      · simp only [List.mem_singleton] at last
        subst member
        exact le_rfl
  | classifier fresh raw targetCategory different expectedCategory correct =>
      refine {
        root_le := ?_
        classifier_lt := ?_
      }
      · intro member memberIn
        rcases List.mem_append.mp memberIn with prior | last
        · exact (accumulator.current_lt member prior).le
        · simp only [List.mem_singleton] at last
          subst member
          exact le_rfl
      · intro classifier classifierEq
        simp only [Option.some.injEq] at classifierEq
        subst classifier
        exact decreases raw
  | step fresh raw same tail =>
      apply tail.order decreases
      refine { current_lt := ?_ }
      intro member memberIn
      rcases List.mem_append.mp memberIn with prior | last
      · exact (decreases raw).trans (accumulator.current_lt member prior)
      · simp only [List.mem_singleton] at last
        subst member
        exact decreases raw
termination_by fuel

theorem convPath_ok_order (dense : Dense) (reference : Ref) (path : ConvPath)
    (decreases : dense.conv.Decreases)
    (found : dense.convPath reference = .ok path) : ConvPathOrder path := by
  cases categoryEq : dense.tagSort? reference with
  | none => simp [Dense.convPath, categoryEq] at found
  | some category =>
      have loopFound : dense.convPathLoop category (dense.defs.length + 1)
          [] reference = .ok path := by
        simpa [Dense.convPath, categoryEq] using found
      have trace := convPathLoop_ok_trace dense category _ [] reference path loopFound
      exact trace.order decreases ⟨by simp⟩

private theorem tagSort_some_expr_resident (dense : Dense) (reference : Ref)
    (found : dense.tagSort? reference = some category) :
    dense.expr? reference ≠ none := by
  intro missing
  have missing' : Nucleus.Hol.Ethane.OneBased.Dense.expr? dense reference = none :=
    missing
  change (Nucleus.Hol.Ethane.OneBased.Dense.expr? dense reference).map
    (·.tag.sort) = some category at found
  rw [missing'] at found
  contradiction

theorem ConvPathTrace.witness
    (trace : ConvPathTrace dense category fuel members current path)
    (accumulator : ConvAccumulator dense category members current) :
    ConvPathWitness dense category path := by
  induction trace with
  | cycle seen =>
      have rootMember := cycleRoot_mem seen
      have rootCurrent := accumulator.memberConnected _ rootMember
      refine {
        rootMember := rootMember
        rootCategory := accumulator.memberCategory _ rootMember
        memberResident := ?_
        memberConnected := ?_
        successorClosed := ?_
        classifierClosed := ?_
        classifier := ?_
      }
      · intro member memberIn
        exact tagSort_some_expr_resident dense member
          (accumulator.memberCategory member memberIn)
      · intro member memberIn
        exact Relation.EqvGen.trans _ _ _ (accumulator.memberConnected member memberIn)
          (Relation.EqvGen.symm _ _ rootCurrent)
      · intro member memberIn target edge
        rcases accumulator.successorClosed member memberIn edge with inside | currentEq
        · exact inside
        · exact currentEq ▸ seen
      · intro member memberIn classifier edge
        exact (accumulator.noClassifier member memberIn edge).elim
      · intro classifier impossible
        simp at impossible
  | root fresh empty =>
      refine {
        rootMember := by simp
        rootCategory := accumulator.currentCategory
        memberResident := ?_
        memberConnected := ?_
        successorClosed := ?_
        classifierClosed := ?_
        classifier := ?_
      }
      · intro member memberIn
        rcases List.mem_append.mp memberIn with prior | current
        · exact tagSort_some_expr_resident dense member
            (accumulator.memberCategory member prior)
        · simp only [List.mem_singleton] at current
          subst member
          exact tagSort_some_expr_resident dense _ accumulator.currentCategory
      · intro member memberIn
        rcases List.mem_append.mp memberIn with prior | current
        · exact accumulator.memberConnected member prior
        · simp only [List.mem_singleton] at current
          subst member
          exact Relation.EqvGen.refl _
      · intro member memberIn target edge
        rcases List.mem_append.mp memberIn with prior | current
        · rcases accumulator.successorClosed member prior edge with inside | targetEq
          · exact List.mem_append_left _ inside
          · subst target
            simp
        · simp only [List.mem_singleton] at current
          subst member
          cases empty.symm.trans edge.1
      · intro member memberIn classifier edge
        rcases List.mem_append.mp memberIn with prior | current
        · exact (accumulator.noClassifier member prior edge).elim
        · simp only [List.mem_singleton] at current
          subst member
          cases empty.symm.trans edge.1
      · intro classifier impossible
        simp at impossible
  | classifier fresh raw targetCategory different expectedCategory correct =>
      rename_i fuelStep priorMembers source classifierTarget parentCategory expected
      refine {
        rootMember := by simp
        rootCategory := accumulator.currentCategory
        memberResident := ?_
        memberConnected := ?_
        successorClosed := ?_
        classifierClosed := ?_
        classifier := ?_
      }
      · intro member memberIn
        rcases List.mem_append.mp memberIn with prior | current
        · exact tagSort_some_expr_resident dense member
            (accumulator.memberCategory member prior)
        · simp only [List.mem_singleton] at current
          subst member
          exact tagSort_some_expr_resident dense _ accumulator.currentCategory
      · intro member memberIn
        rcases List.mem_append.mp memberIn with prior | current
        · exact accumulator.memberConnected member prior
        · simp only [List.mem_singleton] at current
          subst member
          exact Relation.EqvGen.refl _
      · intro member memberIn next edge
        rcases List.mem_append.mp memberIn with prior | current
        · rcases accumulator.successorClosed member prior edge with inside | targetEq
          · exact List.mem_append_left _ inside
          · subst next
            simp
        · simp only [List.mem_singleton] at current
          subst member
          have targetEq : next = classifierTarget :=
            Option.some.inj (edge.1.symm.trans raw)
          subst next
          obtain ⟨sameCategory, sourceCategory, targetSameCategory⟩ := edge.2
          rw [accumulator.currentCategory] at sourceCategory
          cases sourceCategory
          rw [targetCategory] at targetSameCategory
          exact (different (Option.some.inj targetSameCategory)).elim
      · intro member memberIn classifier edge
        rcases List.mem_append.mp memberIn with prior | current
        · exact (accumulator.noClassifier member prior edge).elim
        · simp only [List.mem_singleton] at current
          subst member
          have classifierEq : classifier = classifierTarget :=
            Option.some.inj (edge.1.symm.trans raw)
          subst classifier
          exact ⟨rfl, rfl⟩
      · intro classifier classifierEq
        simp only [Option.some.injEq] at classifierEq
        subst classifier
        constructor
        · refine ⟨raw, ?_⟩
          rintro ⟨sameCategory, currentCategory, classifierCategory⟩
          rw [accumulator.currentCategory] at currentCategory
          cases currentCategory
          rw [targetCategory] at classifierCategory
          cases classifierCategory
          exact different rfl
        · have sourceCategory := accumulator.currentCategory
          cases category <;> simp_all [expectedClassifier, ClassifierShape]
  | step fresh raw same tail ih =>
      rename_i fuelStep priorMembers source next result
      have edge : ConvEdge dense source next :=
        ⟨raw, ⟨category, accumulator.currentCategory, same⟩⟩
      have nextAccumulator :
          ConvAccumulator dense category (priorMembers ++ [source]) next := {
        currentCategory := same
        memberCategory := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | last
          · exact accumulator.memberCategory member prior
          · simp only [List.mem_singleton] at last
            subst member
            exact accumulator.currentCategory
        memberConnected := by
          intro member memberIn
          rcases List.mem_append.mp memberIn with prior | last
          · exact Relation.EqvGen.trans _ _ _ (accumulator.memberConnected member prior)
              (Relation.EqvGen.rel _ _ edge)
          · simp only [List.mem_singleton] at last
            subst member
            exact Relation.EqvGen.rel _ _ edge
        successorClosed := by
          intro member memberIn successor successorEdge
          rcases List.mem_append.mp memberIn with prior | last
          · rcases accumulator.successorClosed member prior successorEdge with
              inside | isSource
            · exact Or.inl (List.mem_append_left _ inside)
            · exact Or.inl (isSource ▸ by simp)
          · simp only [List.mem_singleton] at last
            subst member
            have successorEq : successor = next :=
              Option.some.inj (successorEdge.1.symm.trans raw)
            exact Or.inr successorEq
        noClassifier := by
          intro member memberIn classifier classifierEdge
          rcases List.mem_append.mp memberIn with prior | last
          · exact accumulator.noClassifier member prior classifierEdge
          · simp only [List.mem_singleton] at last
            subst member
            have classifierEq : classifier = next :=
              Option.some.inj (classifierEdge.1.symm.trans raw)
            subst classifier
            exact convEdge_classifierEdge_disjoint ⟨edge, classifierEdge⟩
      }
      exact ih nextAccumulator

/-- Every successful public traversal returns a concrete resident conversion
class and, when present, a correctly-shaped classifier edge. -/
theorem convPath_ok_witness (dense : Dense) (reference : Ref) (path : ConvPath)
    (found : dense.convPath reference = .ok path) :
    ∃ category, dense.tagSort? reference = some category ∧
      ConvPathWitness dense category path := by
  cases categoryEq : dense.tagSort? reference with
  | none => simp [convPath, categoryEq] at found
  | some category =>
      refine ⟨category, rfl, ?_⟩
      have loopFound : dense.convPathLoop category (dense.defs.length + 1)
          [] reference = .ok path := by simpa [convPath, categoryEq] using found
      have trace := convPathLoop_ok_trace dense category _ [] reference path loopFound
      exact trace.witness {
        currentCategory := categoryEq
        memberCategory := by simp
        memberConnected := by simp
        successorClosed := by simp
        noClassifier := by simp
      }

theorem convPath_ok_no_convEdge_member_eq_root (dense : Dense)
    (reference selected : Ref) (path : ConvPath)
    (found : dense.convPath reference = .ok path)
    (selectedIn : selected ∈ path.members)
    (selectedRoot : ∀ {target}, ¬ConvEdge dense selected target) :
    selected = path.root := by
  unfold convPath at found
  cases categoryEq : dense.tagSort? reference with
  | none => simp [categoryEq] at found
  | some category =>
      rw [categoryEq] at found
      have trace := dense.convPathLoop_ok_trace category
        (dense.defs.length + 1) [] reference path found
      exact trace.no_convEdge_member_eq_root categoryEq (by simp) (by simp)
        selected selectedIn selectedRoot

/-- A successful mutable lookup exposes both halves of its implementation:
the checked traversal witness and the successful compression fold.  In
particular the returned representative is definitionally the witnessed root;
it cannot be invented by the mutation phase. -/
theorem findConvMut_ok_witness (dense compressed : Dense)
    (reference root : Ref)
    (found : dense.findConvMut reference = .ok (compressed, root)) :
    ∃ path category,
      dense.convPath reference = .ok path ∧
      dense.compressMembers path = some compressed ∧
      root = path.root ∧
      dense.tagSort? reference = some category ∧
      ConvPathWitness dense category path := by
  simp only [findConvMut] at found
  cases pathResult : dense.convPath reference with
  | error error =>
      rw [pathResult] at found
      contradiction
  | ok path =>
      rw [pathResult] at found
      change (match dense.compressMembers path with
        | none => Except.error (ConvError.missing reference)
        | some result => Except.ok (result, path.root)) =
          Except.ok (compressed, root) at found
      cases compressedResult : dense.compressMembers path with
      | none =>
          rw [compressedResult] at found
          contradiction
      | some result =>
          rw [compressedResult] at found
          simp only [Except.ok.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          obtain ⟨category, sourceCategory, witness⟩ :=
            convPath_ok_witness dense reference path pathResult
          exact ⟨path, category, rfl, compressedResult, rfl,
            sourceCategory, witness⟩

/-- Extensional effect of compressing an arbitrary suffix of the path. -/
structure CompressionUpdate (before after : Dense) (path : ConvPath)
    (members : List Ref) : Prop where
  defs : after.defs = before.defs
  eq : after.eq = before.eq
  synEq : after.synEq = before.synEq
  updated : ∀ member ∈ members,
    after.conv.get? member =
      if member = path.root then path.classifier else some path.root
  unchanged : ∀ other, other ∉ members →
    after.conv.get? other = before.conv.get? other

private theorem compressFold_spec (path : ConvPath) (members : List Ref)
    (before after : Dense)
    (result : members.foldlM (m := Option) (fun state member =>
      state.setConv? member
        (if member = path.root then path.classifier else some path.root)) before =
      some after) :
    CompressionUpdate before after path members := by
  induction members generalizing before after with
  | nil =>
      simp only [List.foldlM_nil, pure, Pure.pure] at result
      cases result
      exact {
        defs := rfl
        eq := rfl
        synEq := rfl
        updated := by simp
        unchanged := by simp
      }
  | cons member tail ih =>
      simp only [List.foldlM_cons] at result
      cases updateResult : before.setConv? member
          (if member = path.root then path.classifier else some path.root) with
      | none => simp [updateResult] at result
      | some middle =>
          rw [updateResult] at result
          have first := setConv?_spec before middle member
            (if member = path.root then path.classifier else some path.root) updateResult
          have rest := ih middle after result
          refine {
            defs := rest.defs.trans first.defs
            eq := rest.eq.trans first.eq
            synEq := rest.synEq.trans first.synEq
            updated := ?_
            unchanged := ?_
          }
          · intro selected selectedIn
            simp only [List.mem_cons] at selectedIn
            rcases selectedIn with rfl | inTail
            · by_cases again : selected ∈ tail
              · exact rest.updated selected again
              · rw [rest.unchanged selected again]
                exact first.updated
            · exact rest.updated selected inTail
          · intro other outside
            simp only [List.mem_cons, not_or] at outside
            rw [rest.unchanged other outside.2]
            exact first.unchanged other outside.1

theorem compressMembers_spec (path : ConvPath) (before after : Dense)
    (result : before.compressMembers path = some after) :
    CompressionUpdate before after path path.members := by
  exact compressFold_spec path path.members before after result

theorem CompressionUpdate.expr?_eq
    (update : CompressionUpdate before after path members) (reference : Ref) :
    after.expr? reference = before.expr? reference := by
  change after.defs[(reference.value.toNat - 1)]? =
    before.defs[(reference.value.toNat - 1)]?
  rw [update.defs]

theorem CompressionUpdate.tagSort?_eq
    (update : CompressionUpdate before after path members) (reference : Ref) :
    after.tagSort? reference = before.tagSort? reference := by
    change (after.expr? reference).map (·.tag.sort) =
      (before.expr? reference).map (·.tag.sort)
    rw [update.expr?_eq]

theorem CompressionUpdate.preserve_distinct_root_no_convEdge
    (update : CompressionUpdate before after path path.members)
    (found : before.convPath source = .ok path)
    (different : selected ≠ path.root)
    (selectedRoot : ∀ {target}, ¬ConvEdge before selected target) :
    ∀ {target}, ¬ConvEdge after selected target := by
  intro target edge
  by_cases inside : selected ∈ path.members
  · have equal := before.convPath_ok_no_convEdge_member_eq_root source selected
      path found inside selectedRoot
    exact different equal
  · apply selectedRoot
    refine ⟨update.unchanged selected inside ▸ edge.1, ?_⟩
    obtain ⟨category, selectedCategory, targetCategory⟩ := edge.2
    exact ⟨category, (update.tagSort?_eq selected).symm ▸ selectedCategory,
      (update.tagSort?_eq target).symm ▸ targetCategory⟩

theorem CompressionUpdate.root_no_convEdge
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path) :
    ∀ {target}, ¬ConvEdge after path.root target := by
  intro target edge
  have raw := edge.1
  rw [update.updated path.root witness.rootMember, if_pos rfl] at raw
  cases classifierEq : path.classifier with
  | none => simp [classifierEq] at raw
  | some classifier =>
      rw [classifierEq] at raw
      have targetEq : target = classifier := (Option.some.inj raw).symm
      subst target
      exact (witness.classifier classifier classifierEq).1.2 <| by
        obtain ⟨edgeCategory, rootCategory, classifierCategory⟩ := edge.2
        exact ⟨edgeCategory,
          (update.tagSort?_eq path.root).symm ▸ rootCategory,
          (update.tagSort?_eq classifier).symm ▸ classifierCategory⟩

theorem CompressionUpdate.conv_decreases
    (update : CompressionUpdate before after path path.members)
    (order : ConvPathOrder path) (beforeDecreases : before.conv.Decreases) :
    after.conv.Decreases := by
  intro source target found
  by_cases inside : source ∈ path.members
  · rw [update.updated source inside] at found
    by_cases root : source = path.root
    · subst source
      simp only [if_pos] at found
      cases classifier : path.classifier with
      | none => simp [classifier] at found
      | some value =>
          rw [classifier] at found
          have targetEq := Option.some.inj found
          subst target
          exact order.classifier_lt value classifier
    · rw [if_neg root] at found
      have targetEq := Option.some.inj found
      subst target
      exact lt_of_le_of_ne (order.root_le source inside) (Ne.symm root)
  · exact beforeDecreases (update.unchanged source inside ▸ found)

theorem CompressionUpdate.semantic_class_iff
    (update : CompressionUpdate before after path members) :
    Class after .semantic left right ↔ Class before .semantic left right := by
  constructor <;> intro related
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (by simpa [Edge, update.eq] using edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (by simpa [Edge, update.eq] using edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr

theorem CompressionUpdate.syn_class_iff
    (update : CompressionUpdate before after path members) :
    Class after .syn left right ↔ Class before .syn left right := by
  constructor <;> intro related
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (by simpa [Edge, update.synEq] using edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr
  · induction related with
    | rel left right edge =>
        exact Relation.EqvGen.rel _ _ (by simpa [Edge, update.synEq] using edge)
    | refl reference => exact Relation.EqvGen.refl reference
    | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans left middle right _ _ lm mr => exact Relation.EqvGen.trans _ _ _ lm mr

theorem CompressionUpdate.member_class_root
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (memberIn : member ∈ path.members) :
    ConvClass after member path.root := by
  by_cases root : member = path.root
  · subst member
    exact Relation.EqvGen.refl _
  · apply Relation.EqvGen.rel
    constructor
    · simp [update.updated member memberIn, root]
    · exact ⟨category,
        update.tagSort?_eq member ▸
          (witness.memberConnected member memberIn).category_eq.trans
            witness.rootCategory,
        update.tagSort?_eq path.root ▸ witness.rootCategory⟩

theorem CompressionUpdate.convEdge_mono
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (edge : ConvEdge before left right) :
    ConvClass after left right := by
  by_cases inside : left ∈ path.members
  · have rightInside := witness.successorClosed left inside edge
    exact Relation.EqvGen.trans _ _ _
      (update.member_class_root witness inside)
      (Relation.EqvGen.symm _ _ (update.member_class_root witness rightInside))
  · apply Relation.EqvGen.rel
    refine ⟨update.unchanged left inside ▸ edge.1, ?_⟩
    obtain ⟨category, leftCategory, rightCategory⟩ := edge.2
    exact ⟨category, update.tagSort?_eq left ▸ leftCategory,
      update.tagSort?_eq right ▸ rightCategory⟩

theorem CompressionUpdate.convClass_mono
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (related : ConvClass before left right) : ConvClass after left right := by
  exact related.mono fun edge => update.convEdge_mono witness edge

theorem CompressionUpdate.convEdge_reflect
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (edge : ConvEdge after left right) :
    ConvClass before left right := by
  by_cases inside : left ∈ path.members
  · by_cases root : left = path.root
    · subst left
      have rawAfter := edge.1
      rw [update.updated path.root witness.rootMember, if_pos rfl] at rawAfter
      cases classifierEq : path.classifier with
      | none => simp [classifierEq] at rawAfter
      | some classifier =>
          have shaped := (witness.classifier classifier classifierEq).1
          rw [classifierEq] at rawAfter
          have rawEq : classifier = right := Option.some.inj rawAfter
          subst right
          exfalso
          apply shaped.2
          obtain ⟨edgeCategory, rootCategory, classifierCategory⟩ := edge.2
          exact ⟨edgeCategory, (update.tagSort?_eq path.root).symm ▸ rootCategory,
            (update.tagSort?_eq classifier).symm ▸ classifierCategory⟩
    · have raw : after.conv.get? left = some path.root := by
        simp [update.updated left inside, root]
      have rightEq : right = path.root := Option.some.inj (edge.1.symm.trans raw)
      subst right
      exact witness.memberConnected left inside
  · apply Relation.EqvGen.rel
    refine ⟨update.unchanged left inside ▸ edge.1, ?_⟩
    obtain ⟨category, leftCategory, rightCategory⟩ := edge.2
    exact ⟨category, (update.tagSort?_eq left).symm ▸ leftCategory,
      (update.tagSort?_eq right).symm ▸ rightCategory⟩

theorem CompressionUpdate.conv_class_iff
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path) :
    ConvClass after left right ↔ ConvClass before left right := by
  constructor
  · intro related
    exact related.mono fun edge => update.convEdge_reflect witness edge
  · exact update.convClass_mono witness

theorem CompressionUpdate.classifier_edge_iff
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path) :
    ClassifierEdge after value classifier ↔
      ClassifierEdge before value classifier := by
  constructor
  · intro edge
    by_cases inside : value ∈ path.members
    · by_cases root : value = path.root
      · subst value
        have raw := edge.1
        rw [update.updated path.root witness.rootMember, if_pos rfl] at raw
        have classifierValue : path.classifier = some classifier := raw
        exact (witness.classifier classifier classifierValue).1
      · have raw := edge.1
        rw [update.updated value inside, if_neg root] at raw
        have classifierRoot : classifier = path.root := (Option.some.inj raw).symm
        subst classifier
        apply (edge.2 ?_).elim
        exact ⟨category,
          update.tagSort?_eq value ▸
            (witness.memberConnected value inside).category_eq.trans
              witness.rootCategory,
          update.tagSort?_eq path.root ▸ witness.rootCategory⟩
    · refine ⟨update.unchanged value inside ▸ edge.1, ?_⟩
      intro same
      apply edge.2
      obtain ⟨edgeCategory, valueCategory, classifierCategory⟩ := same
      exact ⟨edgeCategory, update.tagSort?_eq value ▸ valueCategory,
        update.tagSort?_eq classifier ▸ classifierCategory⟩
  · intro edge
    by_cases inside : value ∈ path.members
    · obtain ⟨root, classifierValue⟩ :=
        witness.classifierClosed value inside edge
      subst value
      refine ⟨?_, ?_⟩
      · rw [update.updated path.root witness.rootMember, if_pos rfl,
          classifierValue]
      · intro same
        apply edge.2
        obtain ⟨edgeCategory, valueCategory, classifierCategory⟩ := same
        exact ⟨edgeCategory, (update.tagSort?_eq path.root).symm ▸ valueCategory,
          (update.tagSort?_eq classifier).symm ▸ classifierCategory⟩
    · refine ⟨update.unchanged value inside ▸ edge.1, ?_⟩
      intro same
      apply edge.2
      obtain ⟨edgeCategory, valueCategory, classifierCategory⟩ := same
      exact ⟨edgeCategory, (update.tagSort?_eq value).symm ▸ valueCategory,
        (update.tagSort?_eq classifier).symm ▸ classifierCategory⟩

theorem CompressionUpdate.has_classifier_iff
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path) :
    HasClassifier after value classifier ↔ HasClassifier before value classifier := by
  constructor
  · rintro ⟨root, connected, edge⟩
    exact ⟨root, (update.conv_class_iff witness).mp connected,
      (update.classifier_edge_iff witness).mp edge⟩
  · rintro ⟨root, connected, edge⟩
    exact ⟨root, (update.conv_class_iff witness).mpr connected,
      (update.classifier_edge_iff witness).mpr edge⟩


theorem CompressionUpdate.refines
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (refines : Refines before) : Refines after := by
  constructor
  · intro left right related
    exact update.conv_class_iff witness |>.mpr <|
      refines.syn_conv (update.syn_class_iff.mp related)
  · intro left right related
    exact update.semantic_class_iff |>.mpr <|
      refines.conv_semantic (update.conv_class_iff witness |>.mp related)

theorem findConvMut_refines (before after : Dense) (reference root : Ref)
    (found : before.findConvMut reference = .ok (after, root))
    (refines : Refines before) : Refines after := by
  obtain ⟨path, category, pathFound, compressed, rootEq, sourceCategory, witness⟩ :=
    findConvMut_ok_witness before after reference root found
  exact (compressMembers_spec path before after compressed).refines witness refines

theorem findConvMut_conv_class_iff (before after : Dense)
    (reference root left right : Ref)
    (found : before.findConvMut reference = .ok (after, root)) :
    ConvClass after left right ↔ ConvClass before left right := by
  obtain ⟨path, category, pathFound, compressed, rootEq, sourceCategory, witness⟩ :=
    findConvMut_ok_witness before after reference root found
  exact (compressMembers_spec path before after compressed).conv_class_iff witness

theorem findConvMut_has_classifier_iff (before after : Dense)
    (reference root value classifier : Ref)
    (found : before.findConvMut reference = .ok (after, root)) :
    HasClassifier after value classifier ↔ HasClassifier before value classifier := by
  obtain ⟨path, category, pathFound, compressed, rootEq, sourceCategory, witness⟩ :=
    findConvMut_ok_witness before after reference root found
  exact (compressMembers_spec path before after compressed).has_classifier_iff witness

/-- A directed, proof-relevant route to a classifier. Its length counts all
raw cells read, including the final cross-category classifier cell. -/
inductive ClassifierRoute (dense : Dense) (classifier : Ref) :
    Ref → Nat → Prop
  | terminal {value} (edge : ClassifierEdge dense value classifier) :
      ClassifierRoute dense classifier value 1
  | step {value next length} (edge : ConvEdge dense value next)
      (tail : ClassifierRoute dense classifier next length) :
      ClassifierRoute dense classifier value (length + 1)

/-- A classifier route retaining the source of its terminal classifier edge.
The executable traversal does not return this root, but carrying it in proofs
makes the functional-forest argument behind root linking explicit. -/
inductive RootedClassifierRoute (dense : Dense) (classifier root : Ref) :
    Ref → Nat → Prop
  | terminal (edge : ClassifierEdge dense root classifier) :
      RootedClassifierRoute dense classifier root root 1
  | step {value next length} (edge : ConvEdge dense value next)
      (tail : RootedClassifierRoute dense classifier root next length) :
      RootedClassifierRoute dense classifier root value (length + 1)

theorem RootedClassifierRoute.length_unique
    (left : RootedClassifierRoute dense leftClassifier leftRoot value leftLength)
    (right : RootedClassifierRoute dense rightClassifier rightRoot value rightLength) :
    leftLength = rightLength := by
  induction left generalizing rightLength with
  | terminal leftEdge =>
      cases right with
      | terminal => rfl
      | step rightEdge _ =>
          have target : _ = leftClassifier :=
            Option.some.inj (rightEdge.1.symm.trans leftEdge.1)
          subst leftClassifier
          exact (leftEdge.2 rightEdge.2).elim
  | @step source next tailLength leftEdge leftTail ih =>
      cases right with
      | terminal rightEdge =>
          have target : next = rightClassifier :=
            Option.some.inj (leftEdge.1.symm.trans rightEdge.1)
          subst next
          exact (rightEdge.2 leftEdge.2).elim
      | @step _ rightNext rightTailLength rightEdge rightTail =>
          have target : next = rightNext :=
            Option.some.inj (leftEdge.1.symm.trans rightEdge.1)
          subst rightNext
          have tailLengthEq := ih rightTail
          omega

/-- Strictly backward conversion/classifier links bound a route by its source
allocation index.  This is the executable traversal's fuel argument without
any global node-list counting. -/
theorem RootedClassifierRoute.length_le_value
    (route : RootedClassifierRoute dense classifier root value length)
    (decreases : dense.conv.Decreases) : length ≤ value.value.toNat := by
  induction route with
  | terminal edge =>
      have positive : 0 < root.value.toNat := by
        apply Nat.pos_of_ne_zero
        intro zero
        change root.1.toNat = 0 at zero
        exact root.property.1 (UInt64.toNat_inj.mp zero)
      omega
  | @step source next tailLength edge tail ih =>
      have backward := decreases edge.1
      change next.value.toNat < source.value.toNat at backward
      omega

theorem RootedClassifierRoute.toClassifierRoute
    (route : RootedClassifierRoute dense classifier root value length) :
    ClassifierRoute dense classifier value length := by
  induction route with
  | terminal edge => exact .terminal edge
  | step edge tail ih => exact .step edge ih

theorem RootedClassifierRoute.nodeList
    (route : RootedClassifierRoute dense classifier root value length) :
    ∃ nodes : List Ref,
      nodes.length = length ∧ nodes.Nodup ∧ value ∈ nodes ∧
      (∀ {reference}, reference ∈ nodes →
        ∃ suffixLength, suffixLength ≤ length ∧
          RootedClassifierRoute dense classifier root reference suffixLength) := by
  induction route with
  | terminal edge =>
      exact ⟨[root], rfl, by simp, by simp, by
        intro reference member
        simp only [List.mem_singleton] at member
        subst reference
        exact ⟨1, le_rfl, .terminal edge⟩⟩
  | @step source next tailLength edge tail ih =>
      obtain ⟨tailNodes, tailLengthEq, tailNodup, nextMember, suffix⟩ := ih
      refine ⟨source :: tailNodes, by simp [tailLengthEq], ?_, by simp, ?_⟩
      · simp only [List.nodup_cons]
        refine ⟨?_, tailNodup⟩
        intro inside
        obtain ⟨suffixLength, bound, suffixRoute⟩ := suffix inside
        have equal := (RootedClassifierRoute.step edge tail).length_unique suffixRoute
        omega
      · intro reference member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨tailLength + 1, le_rfl, .step edge tail⟩
        · obtain ⟨suffixLength, bound, suffixRoute⟩ := suffix member
          exact ⟨suffixLength, by omega, suffixRoute⟩

def HasRootedClassifierRoute (dense : Dense) (classifier root value : Ref) : Prop :=
  ∃ length, RootedClassifierRoute dense classifier root value length

theorem RootedClassifierRoute.connected
    (route : RootedClassifierRoute dense classifier root value length) :
    ConvClass dense value root := by
  induction route with
  | terminal => exact Relation.EqvGen.refl _
  | step edge _ ih =>
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ edge) ih

theorem ClassifierRoute.rooted
    (route : ClassifierRoute dense classifier value length) :
    ∃ root, RootedClassifierRoute dense classifier root value length := by
  induction route with
  | terminal edge => exact ⟨_, .terminal edge⟩
  | step edge _ ih =>
      obtain ⟨root, tail⟩ := ih
      exact ⟨root, .step edge tail⟩

theorem RootedClassifierRoute.forward
    (edge : ConvEdge dense value next)
    (route : RootedClassifierRoute dense classifier root value length) :
    HasRootedClassifierRoute dense classifier root next := by
  cases route with
  | terminal classifierEdge =>
      have target : next = classifier :=
        Option.some.inj (edge.1.symm.trans classifierEdge.1)
      subst next
      exact (classifierEdge.2 edge.2).elim
  | @step _ routeNext routeLength routeEdge tail =>
      have same : routeNext = next :=
        Option.some.inj (routeEdge.1.symm.trans edge.1)
      subst routeNext
      exact ⟨routeLength, tail⟩

theorem RootedClassifierRoute.backward
    (edge : ConvEdge dense value next)
    (route : HasRootedClassifierRoute dense classifier root next) :
    HasRootedClassifierRoute dense classifier root value := by
  obtain ⟨length, tail⟩ := route
  exact ⟨length + 1, .step edge tail⟩

theorem ConvEdge.hasRootedClassifierRoute_iff
    (edge : ConvEdge dense value next) :
    HasRootedClassifierRoute dense classifier root value ↔
      HasRootedClassifierRoute dense classifier root next := by
  constructor
  · rintro ⟨length, route⟩
    exact route.forward edge
  · exact RootedClassifierRoute.backward edge

theorem ConvClass.hasRootedClassifierRoute_iff
    (connected : ConvClass dense left right) :
    HasRootedClassifierRoute dense classifier root left ↔
      HasRootedClassifierRoute dense classifier root right := by
  induction connected with
  | rel _ _ edge => exact ConvEdge.hasRootedClassifierRoute_iff edge
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ leftMiddle middleRight =>
      exact leftMiddle.trans middleRight

theorem RootedClassifierRoute.terminal_unique
    (route : HasRootedClassifierRoute dense classifier root value)
    (edge : ClassifierEdge dense value expected) :
    root = value ∧ classifier = expected := by
  obtain ⟨length, route⟩ := route
  cases route with
  | terminal terminalEdge =>
      exact ⟨rfl, Option.some.inj (terminalEdge.1.symm.trans edge.1)⟩
  | step conversionEdge _ =>
      have target : _ = expected :=
        Option.some.inj (conversionEdge.1.symm.trans edge.1)
      subst expected
      exact (edge.2 conversionEdge.2).elim

/-- In a functional conversion component, any directed classifier route ends
at the unique node of that component carrying a classifier edge. -/
theorem ClassifierRoute.terminal_eq_of_connected
    (route : ClassifierRoute dense classifier value length)
    (connected : ConvClass dense value root)
    (edge : ClassifierEdge dense root expected) : classifier = expected := by
  obtain ⟨terminal, rooted⟩ := route.rooted
  have atRoot : HasRootedClassifierRoute dense classifier terminal root :=
    (ConvClass.hasRootedClassifierRoute_iff connected).mp ⟨length, rooted⟩
  exact (RootedClassifierRoute.terminal_unique atRoot edge).2

theorem ClassifierRoute.rooted_at_of_connected
    (route : ClassifierRoute dense classifier value length)
    (connected : ConvClass dense value root)
    (edge : ClassifierEdge dense root expected) :
    RootedClassifierRoute dense expected root value length := by
  obtain ⟨terminal, rooted⟩ := route.rooted
  have atRoot : HasRootedClassifierRoute dense classifier terminal root :=
    (ConvClass.hasRootedClassifierRoute_iff connected).mp ⟨length, rooted⟩
  obtain ⟨terminalEq, classifierEq⟩ :=
    RootedClassifierRoute.terminal_unique atRoot edge
  subst terminal
  subst classifier
  exact rooted

/-- Replace the terminal classifier edge of the child component by the new
same-category `child → parent` edge and then follow the parent's classifier
route. This is the directed core of conversion-class union. -/
theorem RootedClassifierRoute.splice_child
    (update : ConvCellUpdate before after child (some parent))
    (same : SameCategory before child parent)
    (childEdge : ClassifierEdge before child childClassifier)
    (parentRoute : RootedClassifierRoute after parentClassifier parent parent parentLength)
    (route : RootedClassifierRoute before childClassifier child value length) :
    ∃ newLength, newLength ≤ length + parentLength ∧
      RootedClassifierRoute after parentClassifier parent value newLength := by
  have linked : ConvEdge after child parent := by
    refine ⟨update.updated, ?_⟩
    obtain ⟨category, childCategory, parentCategory⟩ := same
    exact ⟨category, update.tagSort?_eq child ▸ childCategory,
      update.tagSort?_eq parent ▸ parentCategory⟩
  induction route with
  | terminal _ =>
      exact ⟨parentLength + 1, by omega, .step linked parentRoute⟩
  | @step source next tailLength routeEdge tail ih =>
      have sourceNe : source ≠ child := by
        intro sourceEq
        subst source
        have targetEq : next = childClassifier :=
          Option.some.inj (routeEdge.1.symm.trans childEdge.1)
        subst next
        exact childEdge.2 routeEdge.2
      obtain ⟨newLength, bound, transformed⟩ := ih
      exact ⟨newLength + 1, by omega,
        .step (update.convEdge_of_ne sourceNe routeEdge) transformed⟩

/-- A rooted route in a component disjoint from the linked child is retained
cell-for-cell by the one-cell update. -/
theorem RootedClassifierRoute.preserve_of_not_connected
    (update : ConvCellUpdate before after child (some parent))
    (route : RootedClassifierRoute before classifier root value length)
    (outside : ¬ ConvClass before value child) :
    RootedClassifierRoute after classifier root value length := by
  induction route with
  | terminal edge =>
      have rootNe : root ≠ child := by
        intro rootEq
        subst root
        exact outside (Relation.EqvGen.refl _)
      exact .terminal (update.classifierEdge_of_ne rootNe edge)
  | @step source next tailLength edge tail ih =>
      have sourceNe : source ≠ child := by
        intro sourceEq
        subst source
        exact outside (Relation.EqvGen.refl _)
      have tailOutside : ¬ ConvClass before next child := by
        intro connected
        exact outside (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ edge) connected)
      exact .step (update.convEdge_of_ne sourceNe edge) (ih tailOutside)

theorem classifierAt?_route (dense : Dense) (fuel : Nat)
    (value classifier : Ref)
    (checked : dense.Checked) (resident : dense.expr? value ≠ none)
    (found : dense.classifierAt? fuel value = some classifier) :
    ∃ length, length ≤ fuel ∧ ClassifierRoute dense classifier value length := by
  change Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? dense fuel value =
    some classifier at found
  fun_induction Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? dense fuel value
      generalizing classifier <;>
    simp_all only [Option.some.injEq, reduceCtorEq]
  · rename_i remaining source target raw same ih
    obtain ⟨sourceResident, targetResident⟩ := checked.convTargets _ _ raw
    obtain ⟨sourceExpr, sourceExprEq⟩ := Option.ne_none_iff_exists'.mp sourceResident
    have sourceCategory : dense.tagSort? source = some sourceExpr.tag.sort := by
      change (Nucleus.Hol.Ethane.OneBased.Dense.expr? dense source).map
        (·.tag.sort) = some sourceExpr.tag.sort
      have sourceExprEq' :
          Nucleus.Hol.Ethane.OneBased.Dense.expr? dense source = some sourceExpr :=
        sourceExprEq
      rw [sourceExprEq']
      rfl
    have targetCategory : dense.tagSort? target = some sourceExpr.tag.sort :=
      same.symm.trans sourceCategory
    obtain ⟨length, bound, route⟩ := ih classifier targetResident rfl
    exact ⟨length + 1, Nat.succ_le_succ bound,
      .step ⟨raw, ⟨_, sourceCategory, targetCategory⟩⟩ route⟩
  · rename_i remaining source returned raw different expected
    subst returned
    obtain ⟨sourceResident, targetResident⟩ := checked.convTargets _ _ raw
    exact ⟨1, Nat.succ_le_succ (Nat.zero_le _),
      .terminal ⟨raw, fun same => by
        apply different
        obtain ⟨category, sourceCategory, targetCategory⟩ := same
        have sourceCategory' :
            Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense source =
              some category := sourceCategory
        have targetCategory' :
            Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense classifier =
              some category := targetCategory
        exact sourceCategory'.trans targetCategory'.symm⟩⟩

/-- The equivalence relation obtained by merging exactly the old classes of
`child` and `parent`. -/
def JoinedClass (dense : Dense) (child parent left right : Ref) : Prop :=
  ConvClass dense left right ∨
    ((ConvClass dense left child ∨ ConvClass dense left parent) ∧
      (ConvClass dense right child ∨ ConvClass dense right parent))

theorem ConvCellUpdate.convClass_decompose
    (update : ConvCellUpdate before after child (some parent))
    (related : ConvClass after left right) :
    JoinedClass before child parent left right := by
  induction related with
  | rel edgeLeft edgeRight edge =>
      by_cases source : edgeLeft = child
      · subst edgeLeft
        have target : edgeRight = parent := by
          exact Option.some.inj (edge.1.symm.trans update.updated)
        subst edgeRight
        right
        exact ⟨Or.inl (Relation.EqvGen.refl _),
          Or.inr (Relation.EqvGen.refl _)⟩
      · left
        exact Relation.EqvGen.rel _ _ (update.convEdge_before_of_ne source edge)
  | refl reference => exact Or.inl (Relation.EqvGen.refl reference)
  | symm left right _ ih =>
      rcases ih with old | ⟨leftMerged, rightMerged⟩
      · exact Or.inl (Relation.EqvGen.symm _ _ old)
      · exact Or.inr ⟨rightMerged, leftMerged⟩
  | trans left middle right _ _ leftMiddle middleRight =>
      rcases leftMiddle with oldLeft | ⟨leftMerged, middleMerged⟩
      · rcases middleRight with oldRight | ⟨middleMerged', rightMerged⟩
        · exact Or.inl (Relation.EqvGen.trans _ _ _ oldLeft oldRight)
        · right
          refine ⟨?_, rightMerged⟩
          rcases middleMerged' with middleChild | middleParent
          · exact Or.inl (Relation.EqvGen.trans _ _ _ oldLeft middleChild)
          · exact Or.inr (Relation.EqvGen.trans _ _ _ oldLeft middleParent)
      · rcases middleRight with oldRight | ⟨middleMerged', rightMerged⟩
        · right
          refine ⟨leftMerged, ?_⟩
          rcases middleMerged with middleChild | middleParent
          · exact Or.inl (Relation.EqvGen.trans _ _ _
              (Relation.EqvGen.symm _ _ oldRight) middleChild)
          · exact Or.inr (Relation.EqvGen.trans _ _ _
              (Relation.EqvGen.symm _ _ oldRight) middleParent)
        · exact Or.inr ⟨leftMerged, rightMerged⟩

theorem ClassifierRoute.positive
    (route : ClassifierRoute dense classifier value length) : 0 < length := by
  cases route <;> omega

theorem ClassifierRoute.eval
    (route : ClassifierRoute dense classifier value length)
    (shape : ∀ {root target}, ClassifierEdge dense root target →
      ClassifierShape dense root target)
    (bound : length ≤ fuel) :
    dense.classifierAt? fuel value = some classifier := by
  induction route generalizing fuel with
  | terminal edge =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?]
          rw [edge.1]
          obtain shape | shape := shape edge
          · simp [shape.1, shape.2,
              Nucleus.Hol.Ethane.OneBased.Dense.classifierSort?]
          · simp [shape.1, shape.2,
              Nucleus.Hol.Ethane.OneBased.Dense.classifierSort?]
  | @step value next length edge tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Nucleus.Hol.Ethane.OneBased.Dense.classifierAt?]
          rw [edge.1]
          obtain ⟨category, valueCategory, nextCategory⟩ := edge.2
          have valueCategory' :
              Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense value =
                some category := valueCategory
          have nextCategory' :
              Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense next =
                some category := nextCategory
          rw [valueCategory']
          change (if some category =
              Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense next then
            Nucleus.Hol.Ethane.OneBased.Dense.classifierAt? dense fuel next
          else if (some category).bind
              Nucleus.Hol.Ethane.OneBased.Dense.classifierSort? =
                Nucleus.Hol.Ethane.OneBased.Dense.tagSort? dense next then
            some next else none) = some classifier
          rw [nextCategory', if_pos rfl]
          exact ih (by omega)

/-- Completeness of executable classifier lookup follows from the strictly
decreasing checked forest; it is not an independent mutable invariant. -/
theorem _root_.Nucleus.Hol.Ethane.OneBased.Columns.FusedChecked.classifierComplete
    (checked : FusedChecked dense)
    (resident : dense.expr? value ≠ none)
    (classified : HasClassifier dense value classifier) :
    dense.classifier? value = some classifier := by
  obtain ⟨root, connected, edge⟩ := classified
  have atRoot : HasRootedClassifierRoute dense classifier root root :=
    ⟨1, .terminal edge⟩
  obtain ⟨length, rooted⟩ :
      HasRootedClassifierRoute dense classifier root value :=
    (ConvClass.hasRootedClassifierRoute_iff connected).mpr atRoot
  have route := rooted.toClassifierRoute
  unfold Dense.classifier?
  apply route.eval checked.classifierShape
  have position : value.value.toNat - 1 < dense.defs.length := by
    change dense.defs[(value.value.toNat - 1)]? ≠ none at resident
    simpa [List.getElem?_eq_none_iff] using resident
  have positive : 0 < value.value.toNat := by
    apply Nat.pos_of_ne_zero
    intro zero
    change value.1.toNat = 0 at zero
    exact value.property.1 (UInt64.toNat_inj.mp zero)
  have lengthBound := rooted.length_le_value checked.convDecreases
  omega

theorem _root_.Nucleus.Hol.Ethane.OneBased.Columns.FusedChecked.classifierLookup
    (checked : FusedChecked dense)
    (resident : dense.expr? value ≠ none) :
    dense.classifier? value = some classifier ↔ HasClassifier dense value classifier := by
  constructor
  · exact dense.classifier?_sound value classifier checked.toChecked resident
  · exact checked.classifierComplete resident

theorem HasClassifier.unique (checked : FusedChecked dense)
    (resident : dense.expr? value ≠ none)
    (left : HasClassifier dense value leftClassifier)
    (right : HasClassifier dense value rightClassifier) :
    leftClassifier = rightClassifier := by
  have leftFound := checked.classifierComplete resident left
  have rightFound := checked.classifierComplete resident right
  exact Option.some.inj (leftFound.symm.trans rightFound)

theorem HasClassifier.route (checked : FusedChecked dense)
    (resident : dense.expr? value ≠ none)
    (classified : HasClassifier dense value classifier) :
    ∃ length, length ≤ dense.defs.length + 1 ∧
      ClassifierRoute dense classifier value length := by
  exact classifierAt?_route dense _ value classifier checked.toChecked resident
    (checked.classifierComplete resident classified)

theorem ClassifierRoute.inside_classifier
    (route : ClassifierRoute before classifier member length)
    (witness : ConvPathWitness before category path)
    (inside : member ∈ path.members) :
    path.classifier = some classifier := by
  induction route with
  | terminal edge => exact (witness.classifierClosed _ inside edge).2
  | step edge tail ih =>
      exact ih (witness.successorClosed _ inside edge)

theorem ClassifierRoute.compress
    (route : ClassifierRoute before classifier value length)
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path) :
    ∃ compressedLength, compressedLength ≤ length ∧
      ClassifierRoute after classifier value compressedLength := by
  induction route with
  | terminal edge =>
      exact ⟨1, le_rfl, .terminal ((update.classifier_edge_iff witness).mpr edge)⟩
  | @step value next length edge tail ih =>
      by_cases inside : value ∈ path.members
      · have classifierValue :=
          (ClassifierRoute.step edge tail).inside_classifier witness inside
        by_cases root : value = path.root
        · subst value
          exact ⟨1, by omega,
            .terminal ((update.classifier_edge_iff witness).mpr
              (witness.classifier _ classifierValue).1)⟩
        · have memberEdge : ConvEdge after value path.root := by
            refine ⟨?_, ⟨category, ?_, ?_⟩⟩
            · simp [update.updated value inside, root]
            · exact update.tagSort?_eq value ▸
                (witness.memberConnected value inside).category_eq.trans
                  witness.rootCategory
            · exact update.tagSort?_eq path.root ▸ witness.rootCategory
          have rootClassifier : ClassifierEdge after path.root classifier :=
            (update.classifier_edge_iff witness).mpr
              (witness.classifier _ classifierValue).1
          have positive := tail.positive
          exact ⟨2, by omega, .step memberEdge (.terminal rootClassifier)⟩
      · obtain ⟨compressedLength, bound, compressedTail⟩ := ih
        have retained : ConvEdge after value next := by
          refine ⟨update.unchanged value inside ▸ edge.1, ?_⟩
          obtain ⟨edgeCategory, valueCategory, nextCategory⟩ := edge.2
          exact ⟨edgeCategory, update.tagSort?_eq value ▸ valueCategory,
            update.tagSort?_eq next ▸ nextCategory⟩
        exact ⟨compressedLength + 1, Nat.add_le_add_right bound 1,
          .step retained compressedTail⟩

theorem CompressionUpdate.classifier_shape
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (beforeShape : ∀ {value classifier}, ClassifierEdge before value classifier →
      ClassifierShape before value classifier)
    (edge : ClassifierEdge after value classifier) :
    ClassifierShape after value classifier := by
  have oldShape := beforeShape ((update.classifier_edge_iff witness).mp edge)
  rcases oldShape with shape | shape
  · left
    exact ⟨update.tagSort?_eq value ▸ shape.1,
      update.tagSort?_eq classifier ▸ shape.2⟩
  · right
    exact ⟨update.tagSort?_eq value ▸ shape.1,
      update.tagSort?_eq classifier ▸ shape.2⟩

theorem CompressionUpdate.classifier_complete
    (update : CompressionUpdate before after path path.members)
    (witness : ConvPathWitness before category path)
    (beforeChecked : FusedChecked before)
    {value classifier : Ref} (resident : after.expr? value ≠ none)
    (classified : HasClassifier after value classifier) :
    after.classifier? value = some classifier := by
  have beforeResident : before.expr? value ≠ none := by
    simpa [update.expr?_eq value] using resident
  have beforeClassified : HasClassifier before value classifier :=
    (update.has_classifier_iff witness).mp classified
  have lookup := beforeChecked.classifierComplete beforeResident beforeClassified
  obtain ⟨length, bound, route⟩ := classifierAt?_route before _ value classifier
    beforeChecked.toChecked beforeResident lookup
  obtain ⟨compressedLength, compressedBound, compressedRoute⟩ :=
    route.compress update witness
  apply compressedRoute.eval
  · exact fun edge => update.classifier_shape witness beforeChecked.classifierShape edge
  · rw [update.defs]
    exact compressedBound.trans bound

theorem setConv?_checked (before after : Dense) (reference : Ref)
    (value : Option Ref) (beforeChecked : before.Checked)
    (targetResident : ∀ target, value = some target → before.expr? target ≠ none)
    (result : before.setConv? reference value = some after) :
    after.Checked := by
  have update := setConv?_spec before after reference value result
  have sourceResident : before.expr? reference ≠ none := by
    simp only [setConv?] at result
    split at result
    · rename_i inside
      intro missing
      have outside : ¬(reference.value.toNat - 1 < before.defs.length) := by
        change before.defs[(reference.value.toNat - 1)]? = none at missing
        simpa [List.getElem?_eq_none_iff] using missing
      contradiction
    · simp at result
  refine {
    toWellFormed := {
      eq := by
        intro position target cell
        rw [update.eq] at cell
        rw [update.defs]
        exact beforeChecked.toWellFormed.eq position target cell
      synEq := by
        intro position target cell
        rw [update.synEq] at cell
        rw [update.defs]
        exact beforeChecked.toWellFormed.synEq position target cell
      conv := ?_
    }
    eqTargets := ?_
    synEqTargets := ?_
    convTargets := ?_
  }
  · intro position target cell
    simp only [setConv?] at result
    split at result
    next sourceInside =>
      simp only [Option.some.injEq] at result
      subst after
      have flat :
          (setColumnNormalized before.conv (reference.value.toNat - 1) value)[position]?.bind id =
            some target := by rw [cell]; rfl
      rw [setColumnNormalized, Column.getElem?_normalize_bind] at flat
      by_cases same : position = reference.value.toNat - 1
      · subst position
        exact sourceInside
      · rw [List.getElem?_set, if_neg (Ne.symm same)] at flat
        by_cases inside : position < before.conv.length
        · rw [List.getElem?_append_left inside] at flat
          have original : before.conv[position]? = some (some target) := by
            cases found : before.conv[position]? <;> simp_all
          exact beforeChecked.toWellFormed.conv position target original
        · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at flat
          simp only [List.getElem?_replicate] at flat
          split at flat <;> simp_all
    next sourceOutside => simp at result
  · intro left right edge
    rw [update.eq] at edge
    obtain ⟨leftResident, rightResident⟩ := beforeChecked.eqTargets left right edge
    exact ⟨update.expr?_eq left ▸ leftResident, update.expr?_eq right ▸ rightResident⟩
  · intro left right edge
    rw [update.synEq] at edge
    obtain ⟨leftResident, rightResident⟩ := beforeChecked.synEqTargets left right edge
    exact ⟨update.expr?_eq left ▸ leftResident, update.expr?_eq right ▸ rightResident⟩
  · intro left right edge
    by_cases same : left = reference
    · subst left
      have updated := update.updated
      change Column.get? after.conv reference = value at updated
      rw [updated] at edge
      obtain rfl : value = some right := edge
      exact ⟨update.expr?_eq reference ▸ sourceResident,
        update.expr?_eq right ▸ targetResident right rfl⟩
    · have unchanged := update.unchanged left same
      change Column.get? after.conv left = Column.get? before.conv left at unchanged
      rw [unchanged] at edge
      obtain ⟨leftResident, rightResident⟩ := beforeChecked.convTargets left right edge
      exact ⟨update.expr?_eq left ▸ leftResident,
        update.expr?_eq right ▸ rightResident⟩

theorem setConv?_decreases (before after : Dense) (reference : Ref)
    (value : Option Ref) (beforeDecreases : before.conv.Decreases)
    (valueDecreases : ∀ target, value = some target → target < reference)
    (result : before.setConv? reference value = some after) :
    after.conv.Decreases := by
  have update := setConv?_spec before after reference value result
  intro source target edge
  by_cases same : source = reference
  · subst source
    rw [update.updated] at edge
    exact valueDecreases target edge
  · exact beforeDecreases (update.unchanged source same ▸ edge)

theorem setConv?_fusedChecked_sameCategory (before after : Dense)
    (reference target : Ref) (beforeChecked : FusedChecked before)
    (same : SameCategory before reference target) (backward : target < reference)
    (result : before.setConv? reference (some target) = some after) :
    FusedChecked after := by
  have update := setConv?_spec before after reference (some target) result
  have targetResident : before.expr? target ≠ none := by
    obtain ⟨category, _, targetCategory⟩ := same
    exact tagSort_some_expr_resident before target targetCategory
  refine {
    toChecked := setConv?_checked before after reference (some target)
      beforeChecked.toChecked (by
        intro selected equality
        cases Option.some.inj equality
        exact targetResident) result
    eqDecreases := by
      intro source selected edge
      apply beforeChecked.eqDecreases
      simpa [update.eq] using edge
    synEqDecreases := by
      intro source selected edge
      apply beforeChecked.synEqDecreases
      simpa [update.synEq] using edge
    convDecreases := setConv?_decreases before after reference (some target)
      beforeChecked.convDecreases (by
        intro selected equality
        cases Option.some.inj equality
        exact backward) result
    classifierShape := ?_
  }
  intro root classifier edge
  by_cases rootEq : root = reference
  · subst root
    have targetEq : classifier = target :=
      Option.some.inj (edge.1.symm.trans update.updated)
    subst classifier
    apply False.elim
    apply edge.2
    obtain ⟨category, sourceCategory, targetCategory⟩ := same
    exact ⟨category, update.tagSort?_eq reference ▸ sourceCategory,
      update.tagSort?_eq target ▸ targetCategory⟩
  · have oldEdge := update.classifierEdge_before_of_ne rootEq edge
    have shape := beforeChecked.classifierShape oldEdge
    rcases shape with shape | shape
    · exact Or.inl ⟨update.tagSort?_eq root ▸ shape.1,
        update.tagSort?_eq classifier ▸ shape.2⟩
    · exact Or.inr ⟨update.tagSort?_eq root ▸ shape.1,
        update.tagSort?_eq classifier ▸ shape.2⟩

private theorem compressFold_checked (path : ConvPath)
    (original current resultDense : Dense) (category : TagSort)
    (witness : ConvPathWitness original category path)
    (originalChecked : original.Checked)
    (currentChecked : current.Checked) (sameDefs : current.defs = original.defs)
    (members : List Ref) (membersIn : ∀ member ∈ members, member ∈ path.members)
    (result : members.foldlM (m := Option) (fun state member =>
      state.setConv? member
        (if member = path.root then path.classifier else some path.root)) current =
      some resultDense) : resultDense.Checked := by
  induction members generalizing current resultDense with
  | nil =>
      simp only [List.foldlM_nil, pure, Pure.pure, Option.some.injEq] at result
      subst resultDense
      exact currentChecked
  | cons member tail ih =>
      simp only [List.foldlM_cons] at result
      let value := if member = path.root then path.classifier else some path.root
      change (current.setConv? member value).bind (fun initial =>
        tail.foldlM (m := Option) (fun state selected =>
          state.setConv? selected
            (if selected = path.root then path.classifier else some path.root)) initial) =
        some resultDense at result
      cases updateResult : current.setConv? member value with
      | none => simp [updateResult] at result
      | some middle =>
          rw [updateResult] at result
          have valueResident : ∀ target, value = some target → current.expr? target ≠ none := by
            intro target valueEq
            have originalResident : original.expr? target ≠ none := by
              by_cases root : member = path.root
              · simp only [value, root, ↓reduceIte] at valueEq
                have edge := (witness.classifier target valueEq).1
                exact (originalChecked.convTargets _ _ edge.1).2
              · simp only [value, root, ↓reduceIte, Option.some.injEq] at valueEq
                subst target
                exact witness.memberResident path.root witness.rootMember
            change current.defs[(target.value.toNat - 1)]? ≠ none
            change original.defs[(target.value.toNat - 1)]? ≠ none at originalResident
            simpa [sameDefs] using originalResident
          have middleChecked :=
            setConv?_checked current middle member value currentChecked valueResident updateResult
          have middleUpdate := setConv?_spec current middle member value updateResult
          apply ih middle resultDense middleChecked (middleUpdate.defs.trans sameDefs)
          · intro selected selectedIn
            exact membersIn selected (by simp [selectedIn])
          · exact result

/-- A preflighted path may be compressed after an earlier mutation that kept
the definition table fixed.  This is the exact shape used by `unionConv`,
which validates both paths before compressing either one. -/
theorem compressMembers_checked_from (path : ConvPath)
    (original current after : Dense) (category : TagSort)
    (witness : ConvPathWitness original category path)
    (originalChecked : original.Checked) (currentChecked : current.Checked)
    (sameDefs : current.defs = original.defs)
    (result : current.compressMembers path = some after) : after.Checked := by
  apply compressFold_checked path original current after category witness
    originalChecked currentChecked sameDefs path.members
  · simp
  · exact result

theorem compressMembers_checked (path : ConvPath) (before after : Dense)
    (category : TagSort) (witness : ConvPathWitness before category path)
    (beforeChecked : before.Checked)
    (result : before.compressMembers path = some after) : after.Checked := by
  apply compressFold_checked path before before after category witness beforeChecked
    beforeChecked rfl path.members
  · simp
  · exact result

theorem compressMembers_fusedChecked (path : ConvPath) (before after : Dense)
    (category : TagSort) (witness : ConvPathWitness before category path)
    (order : ConvPathOrder path)
    (beforeChecked : FusedChecked before)
    (result : before.compressMembers path = some after) : FusedChecked after := by
  have update := compressMembers_spec path before after result
  have afterChecked := compressMembers_checked path before after category witness
    beforeChecked.toChecked result
  exact {
    toChecked := afterChecked
    eqDecreases := by
      intro source target found
      apply beforeChecked.eqDecreases
      simpa [update.eq] using found
    synEqDecreases := by
      intro source target found
      apply beforeChecked.synEqDecreases
      simpa [update.synEq] using found
    convDecreases := update.conv_decreases order beforeChecked.convDecreases
    classifierShape := fun edge =>
      update.classifier_shape witness beforeChecked.classifierShape edge
  }

theorem findConvMut_fusedChecked (before after : Dense)
    (reference root : Ref) (beforeChecked : FusedChecked before)
    (found : before.findConvMut reference = .ok (after, root)) :
    FusedChecked after := by
  obtain ⟨path, category, pathFound, compressed, rootEq, sourceCategory, witness⟩ :=
    findConvMut_ok_witness before after reference root found
  have order := convPath_ok_order before reference path
    beforeChecked.convDecreases pathFound
  exact compressMembers_fusedChecked path before after category witness order
    beforeChecked compressed

end Dense
end Nucleus.Hol.Ethane.OneBased.Columns
