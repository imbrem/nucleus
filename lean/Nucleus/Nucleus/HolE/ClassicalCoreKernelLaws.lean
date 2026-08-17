import Nucleus.HolE.ClassicalEqTmSoundness
import Nucleus.HolE.ClassicalKernelSoundness

/-! # Core classical kernel laws -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem CRealizes.eq_true_elim
    (hA : Kinded A)
    (realizes : CRealizes (Γ := Γ) env bound (.eq A x y) .boolTy cBool true) :
    ∃ (left : CDefChecks Γ x A) (right : CDefChecks Γ y A),
      cDefSem left env bound (denoteChecked hA env) =
        cDefSem right env bound (denoteChecked hA env) := by
  classical
  obtain ⟨checking, truth⟩ := realizes
  rw [checking.rawView_semantics] at truth
  cases viewEq : checking.rawView with
  | mk rawType raw =>
    rw [viewEq] at truth
    simp only [CDefRawView.sem] at truth
    cases raw with
    | eq cA left right =>
        refine ⟨.exact left, .exact right, ?_⟩
        have decision := congrArg ULift.down truth
        change alignCValue cBool cBool (decide
          ((cSem left env bound (cSem cA env)).down =
            (cSem right env bound (cSem cA env)).down)) = true at decision
        have decided : decide
            ((cSem left env bound (cSem cA env)).down =
              (cSem right env bound (cSem cA env)).down) = true :=
          (alignCValue_self cBool _).symm.trans decision
        have carrierEq : cSem cA env = denoteChecked hA env :=
          cSem_certificate_coherent cA hA.certificate env
        rw [← carrierEq]
        exact congrArg ULift.up (of_decide_eq_true decided)

theorem classical_convert (eqLaws : ClassicalEqTmRuleLaws)
    (conclusionTyping : HasTypeDefEq Γ q .boolTy)
    (equality : EqTm Γ p q .boolTy)
    (premise : CEntails (Γ := Γ) H p) : CEntails (Γ := Γ) H q := by
  intro env bound truths
  obtain ⟨premiseChecking, premiseTrue⟩ := premise env bound truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  have equal := equality.sound_of_laws eqLaws equality.typing.1 conclusionTyping
    env bound cBool
  have premiseTrue' : cDefSem equality.typing.1.certificate env bound cBool = ⟨true⟩ :=
    (equality.typing.1.certificate.coherent premiseChecking env bound cBool).trans premiseTrue
  exact equal.symm.trans premiseTrue'

theorem classical_eqOfEqTm (eqLaws : ClassicalEqTmRuleLaws)
    (_hA : Kinded A) (conclusionTyping : HasTypeDefEq Γ (.eq A x y) .boolTy)
    (equality : EqTm Γ x y A) : CEntails (Γ := Γ) H (.eq A x y) := by
  intro env bound truths
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cA leftChecking rightChecking =>
        let leftTyping : HasTypeDefEq Γ x A := .exact leftChecking.toChecks
        let rightTyping : HasTypeDefEq Γ y A := .exact rightChecking.toChecks
        have operandsEqual := equality.sound_of_laws eqLaws leftTyping rightTyping
          env bound (cSem cA env)
        have rawOperandsEqual :
            cSem leftChecking env bound (cSem cA env) =
              cSem rightChecking env bound (cSem cA env) :=
          ((.exact leftChecking : CDefChecks Γ x A).coherent
            leftTyping.certificate env bound (cSem cA env)).trans
            (operandsEqual.trans
              (rightTyping.certificate.coherent (.exact rightChecking)
                env bound (cSem cA env)))
        change ULift.up (alignCValue cBool cBool (decide (_ = _))) = ULift.up true
        rw [rawOperandsEqual]
        simp
        exact congrArg ULift.up (alignCValue_self cBool true)

end Nucleus.HolE
