import Nucleus.HolE.ClassicalBoundTransport
import Nucleus.HolE.ClassicalEqTmSoundness

/-! # Soundness of term eta conversion -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

private theorem cSem_align_expected
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types}
    (checking : CChecks Γ term (.tm A)) (hOut : CChecks emptyBound A .kind)
    (typed : TypedCtx Γ)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (valid : CBoundValid typed env bound) (expected : CPointed) :
    cSem checking env bound expected = ULift.up
      (alignCValue (cSem hOut env) expected
        (cSem checking env bound (cSem hOut env)).down) := by
  cases checking with
  | primTm rule => exact nomatch rule
  | bv hA lookup =>
      rename_i index
      subst lookup
      rw [hOut.unique hA]
      have semanticEq := cSem_certificate_coherent hA (typed index).certificate env
      have lookupValid := valid index expected
      change bound index expected = alignCValue (cSem (typed index).certificate env)
        expected (bound index (cSem (typed index).certificate env)) at lookupValid
      rw [← semanticEq] at lookupValid
      simpa only [cSem] using congrArg ULift.up lookupValid
  | fv name hA =>
      rw [hOut.unique hA]
      simp only [cSem]
      apply congrArg ULift.up
      let semantic : CPointed := cSem hA env
      change expected.point = alignCValue semantic expected semantic.point
      classical
      by_cases equal : semantic = expected
      · subst expected
        exact (alignCValue_self _ _).symm
      · unfold alignCValue
        simp only [dif_neg equal]
  | app hA hB hf hx =>
      rw [hOut.unique hB]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | lam body hA hB hb =>
      rw [hOut.unique (.arr hA hB)]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | bool literal =>
      rw [hOut.unique .boolTy]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | eq hA hx hy =>
      rw [hOut.unique .boolTy]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | eps hA hp =>
      rw [hOut.unique hA]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | abs hA hp hx =>
      rw [hOut.unique (.sub hA hp)]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | rep hA hp hx =>
      rw [hOut.unique hA]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self
  | tyExists hp =>
      rw [hOut.unique .boolTy]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self

  | tyForall hp =>
      rw [hOut.unique .boolTy]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      symm
      apply alignCValue_self

theorem classical_eqTm_eta
    {Γ : BoundCtx ClassicalSig types depth}
    {A B : Ty ClassicalSig types} {f : Tm ClassicalSig types depth}
    (_name : Nat) (_fresh : Fresh _name f) (_typedContext : TypedCtx Γ)
    (functionTyping : HasTypeDefEq Γ f (.arr A B))
    (etaTyping : HasTypeDefEq Γ
      (.lam A (.app (weaken f) (.bv 0))) (.arr A B)) :
    CSemEq (Γ := Γ) (.lam A (.app (weaken f) (.bv 0))) f (.arr A B) := by
  intro leftTyping rightTyping env bound typed valid expected
  rw [leftTyping.certificate.coherent etaTyping.certificate env bound expected,
    rightTyping.certificate.coherent functionTyping.certificate env bound expected]
  rw [etaTyping.certificate.rawView_semantics,
    functionTyping.certificate.rawView_semantics]
  cases etaView : etaTyping.certificate.rawView with
  | mk etaRawType etaRaw =>
    cases functionView : functionTyping.certificate.rawView with
    | mk functionRawType functionRaw =>
      simp only [CDefRawView.sem]
      cases etaRaw with
      | lam body domain codomain bodyChecking =>
        cases bodyChecking with
        | app appDomain appCodomain weakenedFunction argumentChecking =>
          cases argumentChecking with
          | bv argumentType lookup =>
            cases lookup
            have domainEq := domain.unique appDomain
            have codomainEq := codomain.unique appCodomain
            cases domainEq
            cases codomainEq
            let renamed : CChecks (extendBound A Γ) (weaken f)
                (.tm functionRawType) :=
              ((functionRaw.toChecks.renameTm Fin.succ (fun _ => rfl)).certificate)
            have functionTypeEq := weakenedFunction.type_unique renamed
            cases functionTypeEq
            have sourceAligned := cSem_align_expected functionRaw
              (.arr domain codomain) typed env bound valid expected
            rw [sourceAligned]
            simp only [cSem]
            apply congrArg ULift.up
            apply congrArg (alignCValue _ expected)
            funext value
            have weakenedEq := cSem_rename_raw functionRaw Fin.succ (fun _ => rfl)
              weakenedFunction env
              (extendCBoundEnv (cSem domain env) value bound)
              ⟨(cSem domain env).carrier → (cSem codomain env).carrier,
                fun _ => (cSem codomain env).point⟩
            have envEq := CBoundEnv.rename_succ_extend (cSem domain env) value bound
            rw [envEq] at weakenedEq
            have argumentEq :
                (cSem (CChecks.bv argumentType rfl) env
                  (extendCBoundEnv (cSem domain env) value bound)
                  (cSem domain env)).down = value := by
              rw [argumentType.unique domain]
              change extendCBoundEnv (cSem domain env) value bound 0
                (cSem domain env) = value
              exact (extendCBoundEnv_zero (cSem domain env) value bound
                (cSem domain env)).trans (alignCValue_self _ _)
            have headEq : extendCBoundEnv (cSem domain env) value bound 0
                (cSem domain env) = value :=
              (extendCBoundEnv_zero (cSem domain env) value bound
                (cSem domain env)).trans (alignCValue_self _ _)
            have applicationEq :
                (cSem weakenedFunction env
                    (extendCBoundEnv (cSem domain env) value bound)
                    ⟨(cSem domain env).carrier → (cSem codomain env).carrier,
                      fun _ => (cSem codomain env).point⟩).down
                    (extendCBoundEnv (cSem domain env) value bound 0
                      (cSem domain env)) =
                  (cSem functionRaw env bound
                    ⟨(cSem domain env).carrier → (cSem codomain env).carrier,
                      fun _ => (cSem codomain env).point⟩).down value := by
              rw [headEq]
              exact congrFun (congrArg ULift.down weakenedEq) value
            exact (alignCValue_self _ _).trans applicationEq

end Nucleus.HolE
