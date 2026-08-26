import Nucleus.HolE.ClassicalCoreKernelLaws
import Nucleus.HolE.ClassicalRealization

/-! # Semantic decoding of classical HOL equality -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A well-typed equality realizes Boolean truth exactly when the deterministic
realizations of its operands are equal.  Conversion wrappers and alternative
proof-relevant checking certificates cannot affect the result. -/
theorem CRealizes.eq_true_iff
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    {leftTerm rightTerm : Tm ClassicalSig types depth}
    {env : CTypeEnv types} {bound : CBoundEnv depth}
    (hA : CChecks (Nucleus.HolE.emptyBound :
      BoundCtx ClassicalSig types 0) A .kind)
    (equalityTyping : HasTypeDefEq Γ (.eq A leftTerm rightTerm) .boolTy)
    {left right : (cSem hA env).carrier}
    (leftRealizes : CRealizes (Γ := Γ) env bound leftTerm A
      (cSem hA env) left)
    (rightRealizes : CRealizes (Γ := Γ) env bound rightTerm A
      (cSem hA env) right) :
    CRealizes (Γ := Γ) env bound (.eq A leftTerm rightTerm) .boolTy cBool true ↔
      left = right := by
  classical
  constructor
  · intro equalityRealizes
    obtain ⟨leftChecking, rightChecking, operandsEqual⟩ :=
      equalityRealizes.eq_true_elim hA.toChecks
    have carrierEqual : denoteChecked hA.toChecks env = cSem hA env :=
      (cSem_certificate_coherent hA hA.toChecks.certificate env).symm
    rw [carrierEqual] at operandsEqual
    let checkedLeft := (cSem leftChecking env bound (cSem hA env)).down
    let checkedRight := (cSem rightChecking env bound (cSem hA env)).down
    have checkedLeftRealizes : CRealizes (Γ := Γ) env bound leftTerm A
        (cSem hA env) checkedLeft :=
      ⟨.exact leftChecking, rfl⟩
    have checkedRightRealizes : CRealizes (Γ := Γ) env bound rightTerm A
        (cSem hA env) checkedRight :=
      ⟨.exact rightChecking, rfl⟩
    have leftEqual : left = checkedLeft :=
      leftRealizes.value_unique checkedLeftRealizes
    have rightEqual : right = checkedRight :=
      rightRealizes.value_unique checkedRightRealizes
    exact leftEqual.trans <| (congrArg ULift.down operandsEqual).trans rightEqual.symm
  · intro operandsEqual
    let certificate := equalityTyping.certificate
    refine ⟨certificate, ?_⟩
    rw [certificate.rawView_semantics]
    cases viewEq : certificate.rawView with
    | mk rawType raw =>
        simp only [CDefRawView.sem]
        cases raw with
        | eq cA leftChecking rightChecking =>
            have carrierEqual : cSem cA env = cSem hA env :=
              cSem_certificate_coherent cA hA env
            change ULift.up (alignCValue cBool cBool (decide
              ((cSem leftChecking env bound (cSem cA env)).down =
                (cSem rightChecking env bound (cSem cA env)).down))) =
              ULift.up true
            rw [carrierEqual]
            let checkedLeft :=
              (cSem leftChecking env bound (cSem hA env)).down
            let checkedRight :=
              (cSem rightChecking env bound (cSem hA env)).down
            have checkedLeftRealizes : CRealizes (Γ := Γ) env bound leftTerm A
                (cSem hA env) checkedLeft :=
              ⟨.exact leftChecking, rfl⟩
            have checkedRightRealizes : CRealizes (Γ := Γ) env bound rightTerm A
                (cSem hA env) checkedRight :=
              ⟨.exact rightChecking, rfl⟩
            have leftEqual : checkedLeft = left :=
              checkedLeftRealizes.value_unique leftRealizes
            have rightEqual : checkedRight = right :=
              checkedRightRealizes.value_unique rightRealizes
            have checkedEqual : checkedLeft = checkedRight :=
              leftEqual.trans <| operandsEqual.trans rightEqual.symm
            change ULift.up (alignCValue cBool cBool
              (decide (checkedLeft = checkedRight))) = ULift.up true
            rw [checkedEqual, decide_eq_true (rfl : checkedRight = checkedRight),
              alignCValue_bool]
            rfl

end Nucleus.HolE
