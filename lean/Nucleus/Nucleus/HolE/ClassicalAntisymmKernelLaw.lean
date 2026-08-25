import Nucleus.HolE.ClassicalKernelSoundness

/-! # Classical soundness of Boolean antisymmetry

This file isolates the semantic law for the HOL Boolean extensionality rule.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Mutual derivability of Boolean propositions makes their Boolean denotations
equal.  The two non-equal Boolean cases contradict the corresponding directed
entailment. -/
theorem classical_antisymm_law
    (_hp : HasTypeDefEq Γ p .boolTy) (_hq : HasTypeDefEq Γ q .boolTy)
    (conclusionTyping : HasTypeDefEq Γ (.eq .boolTy p q) .boolTy)
    (left : CEntails (Γ := Γ) (p :: H) q)
    (right : CEntails (Γ := Γ) (q :: H) p) :
    CEntails (Γ := Γ) H (.eq .boolTy p q) := by
  intro env bound typed valid truths
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cBoolCheck pCheck qCheck =>
      have boolSem : cSem cBoolCheck env = cBool :=
        cSem_certificate_coherent cBoolCheck .boolTy env
      change ULift.up (alignCValue cBool cBool
        (decide ((cSem pCheck env bound (cSem cBoolCheck env)).down =
          (cSem qCheck env bound (cSem cBoolCheck env)).down))) = ULift.up true
      rw [boolSem]
      let pValue := (cSem pCheck env bound cBool).down
      let qValue := (cSem qCheck env bound cBool).down
      have pEta : cSem pCheck env bound cBool = ULift.up pValue := by
        dsimp [pValue]
      have qEta : cSem qCheck env bound cBool = ULift.up qValue := by
        dsimp [qValue]
      have valuesEqual : pValue = qValue := by
        cases hpv : pValue <;> cases hqv : qValue
        · rfl
        · exfalso
          have pTrue := right env bound typed valid (fun candidate member => by
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨.exact qCheck, ?_⟩
              change cSem qCheck env bound cBool = ⟨true⟩
              rw [qEta, hqv]
            · exact truths candidate member)
          obtain ⟨pWitness, pTrue⟩ := pTrue
          have pCheckTrue := (pCheck |> CDefChecks.exact).coherent
            pWitness env bound cBool
          have : cSem pCheck env bound cBool = ⟨true⟩ :=
            pCheckTrue.trans pTrue
          rw [pEta, hpv] at this
          have impossible := congrArg ULift.down this
          contradiction
        · exfalso
          have qTrue := left env bound typed valid (fun candidate member => by
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨.exact pCheck, ?_⟩
              change cSem pCheck env bound cBool = ⟨true⟩
              rw [pEta, hpv]
            · exact truths candidate member)
          obtain ⟨qWitness, qTrue⟩ := qTrue
          have qCheckTrue := (qCheck |> CDefChecks.exact).coherent
            qWitness env bound cBool
          have : cSem qCheck env bound cBool = ⟨true⟩ :=
            qCheckTrue.trans qTrue
          rw [qEta, hqv] at this
          have impossible := congrArg ULift.down this
          contradiction
        · rfl
      rw [pEta, qEta]
      simp only
      rw [valuesEqual]
      simp
      exact congrArg ULift.up (alignCValue_self cBool true)

end Nucleus.HolE
