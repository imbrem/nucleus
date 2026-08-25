import Nucleus.Hol.Ethane.Arena.OneBased.FusedPathProofs

/-!
# Correctness of executable fused conversion union

This module connects `Dense.unionConv` itself—not an abstract transition
certificate—to the checked/refinement surface.  Rust and Lean both validate
the two read-only paths before either compression, then compress both paths
and finally link the greater root to the lesser root.
-/

namespace Nucleus.Hol.Ethane.OneBased.Columns

open Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

namespace Dense

theorem RootedClassifierRoute.hasClassifier
    (route : RootedClassifierRoute dense classifier root value length) :
    HasClassifier dense value classifier := by
  refine ⟨root, route.connected, ?_⟩
  induction route with
  | terminal edge => exact edge
  | step _ _ ih => exact ih

/-- Linking two conversion roots either leaves a value outside the child
component (and hence preserves its classifier exactly), or replaces the
child component's classifier by the parent's classifier. -/
theorem ConvCellUpdate.classifier_dichotomy
    (update : ConvCellUpdate before after child (some parent))
    (sameCategory : SameCategory before child parent)
    (beforeChecked : FusedChecked before) (afterChecked : FusedChecked after)
    (valueResident : before.expr? value ≠ none)
    (childResident : before.expr? child ≠ none)
    (parentResident : after.expr? parent ≠ none)
    (oldClassified : HasClassifier before value oldClassifier)
    (newClassified : HasClassifier after value newClassifier)
    (childEdge : ClassifierEdge before child childClassifier)
    (parentClassified : HasClassifier after parent parentClassifier) :
    oldClassifier = newClassifier ∨
      (oldClassifier = childClassifier ∧ newClassifier = parentClassifier) := by
  by_cases inside : ConvClass before value child
  · right
    have childOld : HasClassifier before child oldClassifier :=
      HasClassifier.of_conv inside.symm oldClassified
    have oldEq := HasClassifier.unique beforeChecked childResident
      childOld (HasClassifier.of_edge childEdge)
    have linked : ConvEdge after child parent := by
      refine ⟨update.updated, ?_⟩
      obtain ⟨category, childCategory, parentCategory⟩ := sameCategory
      exact ⟨category, update.tagSort?_eq child ▸ childCategory,
        update.tagSort?_eq parent ▸ parentCategory⟩
    have overwritten : ∀ {right}, ConvEdge before child right →
        ConvClass after child right := by
      intro right edge
      have targetEq : right = childClassifier :=
        Option.some.inj (edge.1.symm.trans childEdge.1)
      subst right
      exact (childEdge.2 edge.2).elim
    have valueChild := update.convClass_mono overwritten inside
    have valueParent : ConvClass after value parent :=
      Relation.EqvGen.trans _ _ _ valueChild (Relation.EqvGen.rel _ _ linked)
    have parentNew : HasClassifier after parent newClassifier :=
      HasClassifier.of_conv valueParent.symm newClassified
    have newEq := HasClassifier.unique afterChecked parentResident
      parentNew parentClassified
    exact ⟨oldEq, newEq⟩
  · left
    obtain ⟨length, _bound, route⟩ :=
      HasClassifier.route beforeChecked valueResident oldClassified
    obtain ⟨root, rooted⟩ := route.rooted
    have retained := rooted.preserve_of_not_connected update inside
    have retainedClassified := retained.hasClassifier
    have afterResident : after.expr? value ≠ none := by
      simpa [update.expr?_eq value] using valueResident
    exact HasClassifier.unique afterChecked afterResident
      retainedClassified newClassified

def ClassifierAgreement (equivalent : Equivalent) (dense : Dense)
    (category : TagSort) (left right : Ref) : Prop :=
  category = .kind ∨
    ∃ leftClassifier rightClassifier,
      dense.checkedClassifier? left = some leftClassifier ∧
      dense.checkedClassifier? right = some rightClassifier ∧
      equivalent leftClassifier rightClassifier = true

/-- Exact successful execution trace after all fallible read-only preflight.
The final constructor distinguishes an already-shared root from the single
least-root cell update. -/
inductive UnionConvTrace (equivalent : Equivalent) (before : Dense)
    (left right : Ref) : Dense → Prop
  | sameRoot {category leftPath rightPreflight rightPath leftCompressed after}
      (leftCategory : before.tagSort? left = some category)
      (rightCategory : before.tagSort? right = some category)
      (agreement : ClassifierAgreement equivalent before category left right)
      (leftFound : before.convPath left = .ok leftPath)
      (rightPreflightFound : before.convPath right = .ok rightPreflight)
      (leftCompression : before.compressMembers leftPath = some leftCompressed)
      (rightFound : leftCompressed.convPath right = .ok rightPath)
      (rightCompression : leftCompressed.compressMembers rightPath = some after)
      (same : leftPath.root = rightPath.root) :
      UnionConvTrace equivalent before left right after
  | joined {category leftPath rightPreflight rightPath leftCompressed compressed child parent after}
      (leftCategory : before.tagSort? left = some category)
      (rightCategory : before.tagSort? right = some category)
      (agreement : ClassifierAgreement equivalent before category left right)
      (leftFound : before.convPath left = .ok leftPath)
      (rightPreflightFound : before.convPath right = .ok rightPreflight)
      (leftCompression : before.compressMembers leftPath = some leftCompressed)
      (rightFound : leftCompressed.convPath right = .ok rightPath)
      (rightCompression : leftCompressed.compressMembers rightPath = some compressed)
      (different : leftPath.root ≠ rightPath.root)
      (childEq : child = max leftPath.root rightPath.root)
      (parentEq : parent = min leftPath.root rightPath.root)
      (joined : compressed.setConv? child (some parent) = some after) :
      UnionConvTrace equivalent before left right after

theorem unionConv_ok_trace (equivalent : Equivalent) (before after : Dense)
    (left right : Ref) (found : before.unionConv equivalent left right = .ok after) :
    UnionConvTrace equivalent before left right after := by
  simp only [unionConv] at found
  cases leftCategoryEq : before.tagSort? left with
  | none =>
      rw [leftCategoryEq] at found
      simp only [require, bind, Except.bind] at found
      cases found
  | some leftCategory =>
      rw [leftCategoryEq] at found
      simp only [require] at found
      cases rightCategoryEq : before.tagSort? right with
      | none =>
          rw [rightCategoryEq] at found
          simp only [bind, Except.bind] at found
          cases found
      | some rightCategory =>
          rw [rightCategoryEq] at found
          simp only at found
          simp only [bind, Except.bind] at found
          by_cases categories : rightCategory = leftCategory
          · subst rightCategory
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne,
              ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, ite_not] at found
            by_cases kind : leftCategory = .kind
            · have agreement : ClassifierAgreement equivalent before leftCategory left right :=
                Or.inl kind
              simp only [kind, ↓reduceIte] at found
              exact finishTrace leftCategory leftCategoryEq rightCategoryEq agreement found
            · simp only [kind, ↓reduceIte] at found
              cases leftClassifierEq : before.checkedClassifier? left with
              | none => simp [leftClassifierEq] at found
              | some leftClassifier =>
                  rw [leftClassifierEq] at found
                  simp only at found
                  cases rightClassifierEq : before.checkedClassifier? right with
                  | none => simp [rightClassifierEq] at found
                  | some rightClassifier =>
                      rw [rightClassifierEq] at found
                      simp only at found
                      by_cases equal : equivalent leftClassifier rightClassifier = false
                      · simp only [equal, ↓reduceIte, reduceCtorEq] at found
                      · simp only [equal, Bool.true_eq_false, ↓reduceIte] at found
                        have agreement :
                            ClassifierAgreement equivalent before leftCategory left right := by
                          right
                          exact ⟨leftClassifier, rightClassifier, leftClassifierEq,
                            rightClassifierEq, Bool.eq_true_of_not_eq_false equal⟩
                        exact finishTrace leftCategory leftCategoryEq rightCategoryEq
                          agreement found
          · have categoriesBool : (rightCategory != leftCategory) = true := by
              simpa [bne_iff_ne] using categories
            rw [if_pos categoriesBool] at found
            simp at found
where
  finishTrace (category : TagSort)
      (leftCategory : before.tagSort? left = some category)
      (rightCategory : before.tagSort? right = some category)
      (agreement : ClassifierAgreement equivalent before category left right)
      (found : (do
        let leftPath ← before.convPath left
        let _ ← before.convPath right
        let leftRoot := leftPath.root
        let dense ← require (ConvError.missing left) (before.compressMembers leftPath)
        let rightPath ← dense.convPath right
        let rightRoot := rightPath.root
        let dense ← require (ConvError.missing right) (dense.compressMembers rightPath)
        if leftRoot = rightRoot then return dense
        let child := max leftRoot rightRoot
        let parent := min leftRoot rightRoot
        match dense.setConv? child (some parent) with
        | none => throw (ConvError.missing child)
        | some joined => return joined) = .ok after) :
      UnionConvTrace equivalent before left right after := by
    cases leftPathEq : before.convPath left with
    | error error =>
        rw [leftPathEq] at found
        simp only [bind, Except.bind] at found
        cases found
    | ok leftPath =>
        rw [leftPathEq] at found
        cases rightPreflightEq : before.convPath right with
        | error error =>
            rw [rightPreflightEq] at found
            simp only [bind, Except.bind] at found
            cases found
        | ok rightPreflight =>
            rw [rightPreflightEq] at found
            simp only [bind, Except.bind] at found
            cases leftCompressionEq : before.compressMembers leftPath with
            | none =>
                rw [leftCompressionEq] at found
                simp only [require] at found
                cases found
            | some leftCompressed =>
                rw [leftCompressionEq] at found
                simp only [require] at found
                cases rightPathEq : leftCompressed.convPath right with
                | error error =>
                    rw [rightPathEq] at found
                    simp only at found
                    cases found
                | ok rightPath =>
                    rw [rightPathEq] at found
                    simp only at found
                    cases rightCompressionEq : leftCompressed.compressMembers rightPath with
                    | none => simp [rightCompressionEq] at found
                    | some compressed =>
                        rw [rightCompressionEq] at found
                        simp only at found
                        by_cases same : leftPath.root = rightPath.root
                        · rw [if_pos same] at found
                          cases found
                          exact .sameRoot leftCategory rightCategory agreement
                            leftPathEq rightPreflightEq leftCompressionEq rightPathEq
                            rightCompressionEq same
                        · rw [if_neg same] at found
                          cases joinedEq : compressed.setConv?
                              (max leftPath.root rightPath.root)
                              (some (min leftPath.root rightPath.root)) with
                          | none => simp [joinedEq] at found
                          | some joined =>
                              rw [joinedEq] at found
                              cases found
                              exact .joined leftCategory rightCategory agreement
                                leftPathEq rightPreflightEq leftCompressionEq rightPathEq
                                rightCompressionEq same rfl rfl joinedEq

theorem UnionConvTrace.defs
    (trace : UnionConvTrace equivalent before left right after) :
    after.defs = before.defs := by
  cases trace with
  | sameRoot _ _ _ _ _ leftCompression _ rightCompression _ =>
      exact (compressMembers_spec _ _ _ rightCompression).defs.trans
        (compressMembers_spec _ _ _ leftCompression).defs
  | joined _ _ _ _ _ leftCompression _ rightCompression _ _ _ joined =>
      exact (setConv?_spec _ _ _ _ joined).defs.trans <|
        (compressMembers_spec _ _ _ rightCompression).defs.trans
          (compressMembers_spec _ _ _ leftCompression).defs

theorem UnionConvTrace.semantic_class_iff
    (trace : UnionConvTrace equivalent before left right after) :
    Class after .semantic a b ↔ Class before .semantic a b := by
  cases trace with
  | sameRoot _ _ _ _ _ leftCompression _ rightCompression _ =>
      exact (compressMembers_spec _ _ _ rightCompression).semantic_class_iff.trans
        (compressMembers_spec _ _ _ leftCompression).semantic_class_iff
  | joined _ _ _ _ _ leftCompression _ rightCompression _ _ _ joined =>
      exact (setConv?_spec _ _ _ _ joined).semantic_class_iff.trans <|
        (compressMembers_spec _ _ _ rightCompression).semantic_class_iff.trans
          (compressMembers_spec _ _ _ leftCompression).semantic_class_iff

theorem UnionConvTrace.syn_class_iff
    (trace : UnionConvTrace equivalent before left right after) :
    Class after .syn a b ↔ Class before .syn a b := by
  cases trace with
  | sameRoot _ _ _ _ _ leftCompression _ rightCompression _ =>
      exact (compressMembers_spec _ _ _ rightCompression).syn_class_iff.trans
        (compressMembers_spec _ _ _ leftCompression).syn_class_iff
  | joined _ _ _ _ _ leftCompression _ rightCompression _ _ _ joined =>
      exact (setConv?_spec _ _ _ _ joined).syn_class_iff.trans <|
        (compressMembers_spec _ _ _ rightCompression).syn_class_iff.trans
          (compressMembers_spec _ _ _ leftCompression).syn_class_iff

theorem UnionConvTrace.checked
    (trace : UnionConvTrace equivalent before left right after)
    (checked : before.Checked) : after.Checked := by
  cases trace with
  | @sameRoot category leftPath rightPreflight rightPath leftCompressed after
      _ _ _ leftFound _ leftCompression rightFound rightCompression _ =>
      obtain ⟨leftCategory, _, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      obtain ⟨rightCategory, _, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have leftChecked := compressMembers_checked leftPath before leftCompressed
        leftCategory leftWitness checked leftCompression
      exact compressMembers_checked rightPath leftCompressed after rightCategory
        rightWitness leftChecked rightCompression
  | @joined category leftPath rightPreflight rightPath leftCompressed compressed child parent after
      _ _ _ leftFound _ leftCompression rightFound rightCompression _ childEq parentEq joined =>
      obtain ⟨leftCategory, _, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      obtain ⟨rightCategory, _, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have leftChecked := compressMembers_checked leftPath before leftCompressed
        leftCategory leftWitness checked leftCompression
      have compressedChecked := compressMembers_checked rightPath leftCompressed compressed
        rightCategory rightWitness leftChecked rightCompression
      have parentResident : compressed.expr? parent ≠ none := by
        subst parent
        have rootResident : before.expr? (min leftPath.root rightPath.root) ≠ none := by
          rcases min_choice leftPath.root rightPath.root with minimum | minimum
          · rw [minimum]
            exact leftWitness.memberResident leftPath.root leftWitness.rootMember
          · rw [minimum]
            have resident := rightWitness.memberResident rightPath.root rightWitness.rootMember
            have leftUpdate := compressMembers_spec _ _ _ leftCompression
            change leftCompressed.defs[(rightPath.root.value.toNat - 1)]? ≠ none at resident
            change before.defs[(rightPath.root.value.toNat - 1)]? ≠ none
            simpa [leftUpdate.defs] using resident
        have leftUpdate := compressMembers_spec _ _ _ leftCompression
        have rightUpdate := compressMembers_spec _ _ _ rightCompression
        change before.defs[((min leftPath.root rightPath.root).value.toNat - 1)]? ≠
          none at rootResident
        change compressed.defs[((min leftPath.root rightPath.root).value.toNat - 1)]? ≠
          none
        simpa [rightUpdate.defs, leftUpdate.defs] using rootResident
      apply setConv?_checked compressed after child (some parent) compressedChecked
      · intro target targetEq
        cases Option.some.inj targetEq
        exact parentResident
      · exact joined

theorem UnionConvTrace.fusedChecked
    (trace : UnionConvTrace equivalent before left right after)
    (checked : FusedChecked before) : FusedChecked after := by
  cases trace with
  | @sameRoot category leftPath rightPreflight rightPath leftCompressed after
      _ _ _ leftFound _ leftCompression rightFound rightCompression _ =>
      obtain ⟨leftCategory, _, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      have leftOrder := convPath_ok_order before left leftPath
        checked.convDecreases leftFound
      have leftChecked := compressMembers_fusedChecked leftPath before
        leftCompressed leftCategory leftWitness leftOrder checked leftCompression
      obtain ⟨rightCategory, _, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have rightOrder := convPath_ok_order leftCompressed right rightPath
        leftChecked.convDecreases rightFound
      exact compressMembers_fusedChecked rightPath leftCompressed after
        rightCategory rightWitness rightOrder leftChecked rightCompression
  | @joined category leftPath rightPreflight rightPath leftCompressed compressed
      child parent after leftCategoryFound rightCategoryFound _ leftFound _
      leftCompression rightFound
      rightCompression different childEq parentEq joined =>
      obtain ⟨leftCategory, leftSourceCategory, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      have leftCategoryEq : leftCategory = category := by
        exact Option.some.inj (leftSourceCategory.symm.trans leftCategoryFound)
      subst leftCategory
      have leftOrder := convPath_ok_order before left leftPath
        checked.convDecreases leftFound
      have leftChecked := compressMembers_fusedChecked leftPath before
        leftCompressed category leftWitness leftOrder checked leftCompression
      obtain ⟨rightCategory, rightSourceCategory, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have leftUpdate := compressMembers_spec leftPath before leftCompressed
        leftCompression
      have rightCategoryEq : rightCategory = category := by
        have original : before.tagSort? right = some rightCategory := by
          simpa [leftUpdate.tagSort?_eq] using rightSourceCategory
        exact Option.some.inj (original.symm.trans rightCategoryFound)
      subst rightCategory
      have rightOrder := convPath_ok_order leftCompressed right rightPath
        leftChecked.convDecreases rightFound
      have compressedChecked := compressMembers_fusedChecked rightPath
        leftCompressed compressed category rightWitness rightOrder
        leftChecked rightCompression
      have sameCategory : SameCategory compressed child parent := by
        have leftRootCategory : compressed.tagSort? leftPath.root = some category := by
          have rightUpdate := compressMembers_spec rightPath leftCompressed compressed
            rightCompression
          simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
            leftWitness.rootCategory
        have rightRootCategory : compressed.tagSort? rightPath.root = some category := by
          have rightUpdate := compressMembers_spec rightPath leftCompressed compressed
            rightCompression
          simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory
        subst child
        subst parent
        rcases max_choice leftPath.root rightPath.root with maximum | maximum
        · rw [maximum]
          have minimum : min leftPath.root rightPath.root = rightPath.root :=
            min_eq_right (max_eq_left_iff.mp maximum)
          rw [minimum]
          exact ⟨category, leftRootCategory, rightRootCategory⟩
        · rw [maximum]
          have minimum : min leftPath.root rightPath.root = leftPath.root :=
            min_eq_left (max_eq_right_iff.mp maximum)
          rw [minimum]
          exact ⟨category, rightRootCategory, leftRootCategory⟩
      have backward : parent < child := by
        subst child
        subst parent
        exact min_lt_max.mpr different
      exact setConv?_fusedChecked_sameCategory compressed after child parent
        compressedChecked sameCategory backward joined

/-- A successful conversion union preserves every classifier up to the
semantic equality checked during preflight. -/
theorem UnionConvTrace.classifier_supported
    (trace : UnionConvTrace equivalent before left right after)
    (classifierSound : ∀ {leftClassifier rightClassifier},
      before.checkedClassifier? left = some leftClassifier →
      before.checkedClassifier? right = some rightClassifier →
      equivalent leftClassifier rightClassifier = true →
      Class before .semantic leftClassifier rightClassifier)
    (checked : FusedChecked before) (resident : before.expr? value ≠ none)
    (oldFound : before.classifier? value = some oldClassifier)
    (newFound : after.classifier? value = some newClassifier) :
    Class before .semantic oldClassifier newClassifier := by
  have oldClassified := (checked.classifierLookup resident).mp oldFound
  have finalChecked := trace.fusedChecked checked
  cases trace with
  | @sameRoot category leftPath rightPreflight rightPath leftCompressed after
      _ _ _ leftFound _ leftCompression rightFound rightCompression _ =>
      obtain ⟨leftCategory, _, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      have leftUpdate := compressMembers_spec leftPath before leftCompressed
        leftCompression
      have leftChecked := (compressMembers_fusedChecked leftPath before
        leftCompressed leftCategory leftWitness
        (convPath_ok_order before left leftPath checked.convDecreases leftFound)
        checked leftCompression)
      obtain ⟨rightCategory, _, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have rightUpdate := compressMembers_spec rightPath leftCompressed after
        rightCompression
      have afterChecked := compressMembers_fusedChecked rightPath leftCompressed
        after rightCategory rightWitness
        (convPath_ok_order leftCompressed right rightPath
          leftChecked.convDecreases rightFound) leftChecked rightCompression
      have oldAfter : HasClassifier after value oldClassifier :=
        (rightUpdate.has_classifier_iff rightWitness).mpr <|
          (leftUpdate.has_classifier_iff leftWitness).mpr oldClassified
      have afterResident : after.expr? value ≠ none := by
        simpa [rightUpdate.expr?_eq, leftUpdate.expr?_eq] using resident
      have newClassified := (afterChecked.classifierLookup afterResident).mp newFound
      have same := HasClassifier.unique afterChecked afterResident oldAfter newClassified
      subst newClassifier
      exact Class.refl _
  | @joined category leftPath rightPreflight rightPath leftCompressed compressed
      child parent after leftCategoryFound rightCategoryFound agreement leftFound
      rightPreflightFound leftCompression rightFound rightCompression different
      childEq parentEq joined =>
      obtain ⟨leftCategory, leftSourceCategory, leftWitness⟩ :=
        convPath_ok_witness before left leftPath leftFound
      have leftCategoryEq : leftCategory = category :=
        Option.some.inj (leftSourceCategory.symm.trans leftCategoryFound)
      subst leftCategory
      have leftUpdate := compressMembers_spec leftPath before leftCompressed
        leftCompression
      have leftOrder := convPath_ok_order before left leftPath
        checked.convDecreases leftFound
      have leftChecked := compressMembers_fusedChecked leftPath before leftCompressed
        category leftWitness leftOrder checked leftCompression
      obtain ⟨rightCategory, rightSourceCategory, rightWitness⟩ :=
        convPath_ok_witness leftCompressed right rightPath rightFound
      have rightCategoryEq : rightCategory = category := by
        have original : before.tagSort? right = some rightCategory := by
          simpa [leftUpdate.tagSort?_eq] using rightSourceCategory
        exact Option.some.inj (original.symm.trans rightCategoryFound)
      subst rightCategory
      have rightUpdate := compressMembers_spec rightPath leftCompressed compressed
        rightCompression
      have rightOrder := convPath_ok_order leftCompressed right rightPath
        leftChecked.convDecreases rightFound
      have compressedChecked := compressMembers_fusedChecked rightPath leftCompressed
        compressed category rightWitness rightOrder leftChecked rightCompression
      have cell := setConv?_spec compressed after child (some parent) joined
      have afterChecked := finalChecked
      have compressedResident : compressed.expr? value ≠ none := by
        simpa [rightUpdate.expr?_eq, leftUpdate.expr?_eq] using resident
      have afterResident : after.expr? value ≠ none := by
        simpa [cell.expr?_eq] using compressedResident
      have oldCompressed : HasClassifier compressed value oldClassifier :=
        (rightUpdate.has_classifier_iff rightWitness).mpr <|
          (leftUpdate.has_classifier_iff leftWitness).mpr oldClassified
      have newClassified := (afterChecked.classifierLookup afterResident).mp newFound
      rcases agreement with kindCategory | classifierAgreement
      · have categoryEq : category = .kind := kindCategory
        subst category
        have childKind : compressed.tagSort? child = some .kind := by
          rw [childEq]
          rcases max_choice leftPath.root rightPath.root with maximum | maximum
          · rw [maximum]
            simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
              leftWitness.rootCategory
          · rw [maximum]
            simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory
        have outside : ¬ ConvClass compressed value child := by
          intro connected
          have childOld := HasClassifier.of_conv connected.symm oldCompressed
          exact compressedChecked.kind_has_no_classifier childKind childOld
        obtain ⟨length, _bound, route⟩ :=
          HasClassifier.route compressedChecked compressedResident oldCompressed
        obtain ⟨root, rooted⟩ := route.rooted
        have retained := rooted.preserve_of_not_connected cell outside
        have same := HasClassifier.unique afterChecked afterResident
          retained.hasClassifier newClassified
        subst newClassifier
        exact Class.refl _
      · obtain ⟨leftClassifier, rightClassifier, leftClassifierFound,
            rightClassifierFound, equivalentFound⟩ := classifierAgreement
        have leftResident := convPath_ok_source_resident before left leftPath leftFound
        have rightResident := convPath_ok_source_resident before right rightPreflight
          rightPreflightFound
        have leftLookup : before.classifier? left = some leftClassifier := by
          simpa [checkedClassifier?, leftResident] using leftClassifierFound
        have rightLookup : before.classifier? right = some rightClassifier := by
          simpa [checkedClassifier?, rightResident] using rightClassifierFound
        have leftClassified := (checked.classifierLookup leftResident).mp leftLookup
        have rightClassified := (checked.classifierLookup rightResident).mp rightLookup
        obtain ⟨leftLength, _, leftRoute⟩ :=
          HasClassifier.route checked leftResident leftClassified
        have leftPathClassifier := leftRoute.inside_classifier leftWitness
          (convPath_ok_source_mem before left leftPath leftFound)
        have rightClassifiedLeft : HasClassifier leftCompressed right rightClassifier :=
          (leftUpdate.has_classifier_iff leftWitness).mpr rightClassified
        have rightResidentLeft : leftCompressed.expr? right ≠ none := by
          simpa [leftUpdate.expr?_eq] using rightResident
        obtain ⟨rightLength, _, rightRoute⟩ :=
          HasClassifier.route leftChecked rightResidentLeft rightClassifiedLeft
        have rightPathClassifier := rightRoute.inside_classifier rightWitness
          (convPath_ok_source_mem leftCompressed right rightPath rightFound)
        have leftEdgeBefore := (leftWitness.classifier leftClassifier
          leftPathClassifier).1
        have rightEdgeLeft := (rightWitness.classifier rightClassifier
          rightPathClassifier).1
        have leftEdgeCompressed : ClassifierEdge compressed leftPath.root leftClassifier :=
          (rightUpdate.classifier_edge_iff rightWitness).mpr <|
            (leftUpdate.classifier_edge_iff leftWitness).mpr leftEdgeBefore
        have rightEdgeCompressed :
            ClassifierEdge compressed rightPath.root rightClassifier :=
          (rightUpdate.classifier_edge_iff rightWitness).mpr rightEdgeLeft
        rcases lt_or_gt_of_ne different with leftLt | rightLt
        · have childIs : child = rightPath.root :=
            childEq.trans (max_eq_right leftLt.le)
          have parentIs : parent = leftPath.root :=
            parentEq.trans (min_eq_left leftLt.le)
          have cell' : ConvCellUpdate compressed after rightPath.root
              (some leftPath.root) := by simpa [childIs, parentIs] using cell
          have parentAfter : HasClassifier after leftPath.root leftClassifier :=
            HasClassifier.of_edge
              (cell'.classifierEdge_of_ne different leftEdgeCompressed)
          have childResident : compressed.expr? rightPath.root ≠ none := by
            simpa [rightUpdate.expr?_eq] using
              rightWitness.memberResident _ rightWitness.rootMember
          have parentResident : after.expr? leftPath.root ≠ none := by
            have beforeResident :=
              leftWitness.memberResident _ leftWitness.rootMember
            have compressedParent : compressed.expr? leftPath.root ≠ none := by
              simpa [rightUpdate.expr?_eq, leftUpdate.expr?_eq] using beforeResident
            simpa [cell'.expr?_eq] using compressedParent
          have result := cell'.classifier_dichotomy
            (⟨category,
              by simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory,
              by simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
                leftWitness.rootCategory⟩)
            compressedChecked afterChecked compressedResident
            childResident parentResident oldCompressed newClassified
            rightEdgeCompressed parentAfter
          rcases result with same | ⟨oldEq, newEq⟩
          · subst newClassifier; exact Class.refl _
          · subst oldClassifier; subst newClassifier
            exact (classifierSound leftClassifierFound rightClassifierFound
              equivalentFound).symm
        · have childIs : child = leftPath.root :=
            childEq.trans (max_eq_left rightLt.le)
          have parentIs : parent = rightPath.root :=
            parentEq.trans (min_eq_right rightLt.le)
          have cell' : ConvCellUpdate compressed after leftPath.root
              (some rightPath.root) := by simpa [childIs, parentIs] using cell
          have parentAfter : HasClassifier after rightPath.root rightClassifier :=
            HasClassifier.of_edge
              (cell'.classifierEdge_of_ne (Ne.symm different) rightEdgeCompressed)
          have childResident : compressed.expr? leftPath.root ≠ none := by
            simpa [rightUpdate.expr?_eq, leftUpdate.expr?_eq] using
              leftWitness.memberResident _ leftWitness.rootMember
          have parentResident : after.expr? rightPath.root ≠ none := by
            have compressedParent : compressed.expr? rightPath.root ≠ none := by
              simpa [rightUpdate.expr?_eq] using
                rightWitness.memberResident _ rightWitness.rootMember
            simpa [cell'.expr?_eq] using compressedParent
          have result := cell'.classifier_dichotomy
            (⟨category,
              by simpa [rightUpdate.tagSort?_eq, leftUpdate.tagSort?_eq] using
                leftWitness.rootCategory,
              by simpa [rightUpdate.tagSort?_eq] using rightWitness.rootCategory⟩)
            compressedChecked afterChecked compressedResident
            childResident parentResident oldCompressed newClassified
            leftEdgeCompressed parentAfter
          rcases result with same | ⟨oldEq, newEq⟩
          · subst newClassifier; exact Class.refl _
          · subst oldClassifier; subst newClassifier
            exact classifierSound leftClassifierFound rightClassifierFound
              equivalentFound

theorem unionConv_semantic_class_iff (equivalent : Equivalent) (before after : Dense)
    (left right : Ref) (found : before.unionConv equivalent left right = .ok after) :
    Class after .semantic a b ↔ Class before .semantic a b :=
  (unionConv_ok_trace equivalent before after left right found).semantic_class_iff

theorem unionConv_syn_class_iff (equivalent : Equivalent) (before after : Dense)
    (left right : Ref) (found : before.unionConv equivalent left right = .ok after) :
    Class after .syn a b ↔ Class before .syn a b :=
  (unionConv_ok_trace equivalent before after left right found).syn_class_iff

end Dense
end Nucleus.Hol.Ethane.OneBased.Columns
