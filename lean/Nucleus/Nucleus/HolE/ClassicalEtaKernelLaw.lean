import Nucleus.HolE.ClassicalBoundTransport
import Nucleus.HolE.ClassicalKernelAssembly

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

end Nucleus.HolE
