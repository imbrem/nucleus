import Nucleus.HolE.ClassicalKernelSoundness
import Nucleus.HolE.ClassicalFamilySoundness

/-! # Classical semantic laws for type existentials and guarded models -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

private theorem CChecks.erase : CChecks Γ expression classification →
    Checks Γ expression classification
  | .boolTy => .boolTy
  | .arr hA hB => .arr hA.erase hB.erase
  | .tyApp hF hA => .tyApp hF.erase hA.erase
  | .tyLam body => .tyLam body.erase
  | .tyBv v => .tyBv v
  | .sub hA hp => .sub hA.erase hp.erase
  | .model hp => .model hp.erase
  | .primFam symbol => nomatch symbol
  | .primTm rule => nomatch rule
  | .bv hA lookup => .bv hA.erase lookup
  | .fv name hA => .fv name hA.erase
  | .app _ _ hf hx => .app hf.erase hx.erase
  | .lam body hA _ hb => .lam body hA.erase hb.erase
  | .bool literal => .bool literal
  | .eq hA hx hy => .eq hA.erase hx.erase hy.erase
  | .eps hA hp => .eps hA.erase hp.erase
  | .abs hA hp hx => .abs hA.erase hp.erase hx.erase
  | .rep hA hp hx => .rep hA.erase hp.erase hx.erase
  | .tyExists hp => .tyExists hp.erase

  | .tyForall hp => .tyForall hp.erase

private theorem cSem_openType
    {types : List Kind} {predicate : Tm ClassicalSig (.star :: types) 0}
    {A : Ty ClassicalSig types}
    (hp : CChecks (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)
      predicate (.tm .boolTy)) (hA : Kinded A) (cA : CKinded A)
    (opened : CChecks (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate A) (.tm .boolTy)) (env : CTypeEnv types) :
    cSem opened env emptyCBoundEnv cBool =
      cSem hp (extendCTypeEnv (cSem cA env) env) emptyCBoundEnv cBool := by
  rw [cA.unique hA.certificate]
  let wf : WellFormedTySub (headTySub A) :=
    wellFormed_headTySub (kind := .star) hA
  have instantiated := hp.instantiateTypes wf
  rw [instantiateBoundCtx_empty] at instantiated
  change CChecks emptyBound (openType predicate A) (.tm .boolTy) at instantiated
  rw [opened.unique instantiated]
  have semantic := cSem_instantiateTypes hp wf env
  simp only [CInstantiateEq] at semantic
  have normalize := cSem_instantiate_tm_normalize wf
    (hp.instantiateTypes wf) emptyBound
    (instantiateBoundCtx_empty (headTySub A)) instantiated env
  rw [normalize] at semantic
  rw [CTypeEnv.ofSub_head hA env] at semantic
  exact congrFun (congrFun semantic emptyCBoundEnv) cBool

theorem tyExistsIntro_sound
    {types : List Kind} {H : List (Tm ClassicalSig types 0)}
    {A : Ty ClassicalSig types} {predicate : Tm ClassicalSig (.star :: types) 0}
    (conclusionTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig types 0) (.tyExists predicate) .boolTy)
    (hA : Kinded A)
    (_predicateTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig (.star :: types) 0) predicate .boolTy)
    (_instanceTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig types 0) (openType predicate A) .boolTy)
    (premise : CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (openType predicate A)) :
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (.tyExists predicate) := by
  classical
  intro env bound typed valid truths
  have boundEq : bound = emptyCBoundEnv := by
    funext i
    exact Fin.elim0 i
  subst bound
  obtain ⟨instanceCheck, instanceTrue⟩ :=
    premise env emptyCBoundEnv typed valid truths
  let conclusionCheck := conclusionTyping.certificate
  refine ⟨conclusionCheck, ?_⟩
  rw [conclusionCheck.rawView_semantics]
  cases hv : conclusionCheck.rawView with
  | mk result raw =>
    cases raw with
    | tyExists hp =>
      simp only [CDefRawView.sem, cSem]
      apply congrArg ULift.up
      rw [alignCValue_bool]
      apply decide_eq_true
      refine ⟨(cSem hA.certificate env : CPointed), ?_⟩
      rw [instanceCheck.rawView_semantics] at instanceTrue
      cases hi : instanceCheck.rawView with
      | mk instanceType instanceRaw =>
        rw [hi] at instanceTrue
        simp only [CDefRawView.sem] at instanceTrue
        let wf : WellFormedTySub (headTySub A) :=
          wellFormed_headTySub (kind := .star) hA
        have instantiated := hp.instantiateTypes wf
        rw [instantiateBoundCtx_empty] at instantiated
        change CChecks emptyBound (openType predicate A) (.tm .boolTy) at instantiated
        have typeEq := instanceRaw.type_unique instantiated
        subst instanceType
        rw [← cSem_openType hp hA hA.certificate instanceRaw env]
        exact instanceTrue


theorem modelSpec_sound
    {types : List Kind} {H : List (Tm ClassicalSig types 0)}
    {predicate : Tm ClassicalSig (.star :: types) 0}
    (conclusionTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate (.model predicate)) .boolTy)
    (_predicateTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig (.star :: types) 0) predicate .boolTy)
    (_modelInstanceTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate (.model predicate)) .boolTy)
    (premise : CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (.tyExists predicate)) :
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (openType predicate (.model predicate)) := by
  classical
  intro env bound typed valid truths
  have boundEq : bound = emptyCBoundEnv := by
    funext i
    exact Fin.elim0 i
  subst bound
  obtain ⟨existsCheck, existsTrue⟩ :=
    premise env emptyCBoundEnv typed valid truths
  rw [existsCheck.rawView_semantics] at existsTrue
  cases he : existsCheck.rawView with
  | mk existsType existsRaw =>
    rw [he] at existsTrue
    simp only [CDefRawView.sem] at existsTrue
    cases existsRaw with
    | tyExists hp =>
      simp only [cSem] at existsTrue
      have decided : decide (∃ candidate : CPointed,
          cSem hp (extendCTypeEnv candidate env) emptyCBoundEnv cBool = ⟨true⟩) =
          true := by
        change ULift.up (alignCValue cBool cBool (decide _)) = ULift.up true at existsTrue
        rw [alignCValue_bool] at existsTrue
        exact ULift.up.inj existsTrue
      obtain ⟨witness, witnessHolds⟩ := of_decide_eq_true decided
      let sat := fun candidate : CPointed =>
        cSem hp (extendCTypeEnv candidate env) emptyCBoundEnv cBool = ⟨true⟩
      have chosenHolds : sat (chooseCModel sat) :=
        chooseCModel_spec sat witness witnessHolds
      let modelRaw : CKinded (.model predicate) := .model hp
      have modelKinded : Kinded (.model predicate) := .model hp.erase
      let resultCheck := conclusionTyping.certificate
      refine ⟨resultCheck, ?_⟩
      rw [resultCheck.rawView_semantics]
      cases hr : resultCheck.rawView with
      | mk resultType resultRaw =>
        simp only [CDefRawView.sem]
        have instantiated := hp.instantiateTypes
          (wellFormed_headTySub (kind := .star) modelKinded)
        rw [instantiateBoundCtx_empty] at instantiated
        change CChecks emptyBound (openType predicate (.model predicate))
          (.tm .boolTy) at instantiated
        have typeEq := resultRaw.type_unique instantiated
        subst resultType
        rw [cSem_openType hp modelKinded modelRaw resultRaw env]
        exact chosenHolds


end Nucleus.HolE
