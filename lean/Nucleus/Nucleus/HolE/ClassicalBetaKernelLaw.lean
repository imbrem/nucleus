import Nucleus.HolE.ClassicalCoreKernelLaws

/-! # Semantic beta conversion -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

@[simp] theorem alignCValue_point (source target : CPointed) :
    alignCValue source target source.point = target.point := by
  by_cases equal : source = target
  · subst target
    simp [alignCValue]
  · simp [alignCValue, equal]

/-- Evaluation of a raw-typed term at an arbitrary target is alignment of its
value at its actual type.  The bound-variable case is precisely where validity
of the context environment is needed. -/
theorem CChecks.cSem_expected_valid
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : CChecks Γ term (.tm A))
    (hA : CKinded A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (typed : TypedCtx Γ)
    (valid : CBoundValid typed env bound) (expected : CPointed) :
    cSem typing env bound expected =
      ⟨alignCValue (cSem hA env) expected
        (cSem typing env bound (cSem hA env)).down⟩ := by
  have typeSemantic : cSem hA env = cSem typing.typeKinded env :=
    cSem_certificate_coherent hA typing.typeKinded env
  rw [typeSemantic]
  cases typing with
  | primTm rule => nomatch rule
  | @bv _ _ _ _ index hA lookup =>
      cases lookup
      have contextType : typed index = hA.toChecks := Subsingleton.elim _ _
      have semantic : denoteChecked (typed index) env = cSem hA env := by
        rw [contextType]
        exact cSem_certificate_coherent _ hA env
      change ULift.up (bound index expected) = ULift.up
        (alignCValue (cSem hA env) expected (bound index (cSem hA env)))
      rw [valid index expected]
      rw [semantic]
  | fv name hA =>
      change ULift.up expected.point = ULift.up
        (alignCValue (cSem hA env) expected (cSem hA env).point)
      exact congrArg ULift.up (alignCValue_point (cSem hA env) expected).symm
  | app hA hB hf hx =>
      change ULift.up (alignCValue (cSem hB env) expected _) = ULift.up
        (alignCValue (cSem hB env) expected
          (alignCValue (cSem hB env) (cSem hB env) _))
      apply congrArg ULift.up
      exact congrArg (alignCValue (cSem hB env) expected)
        (alignCValue_self (cSem hB env) _).symm
  | lam body hDomain hB hb =>
      let functionType : CPointed :=
        ⟨(cSem hDomain env).carrier → (cSem hB env).carrier,
          fun _ => (cSem hB env).point⟩
      rw [← typeSemantic]
      have functionTypeEq : cSem hA env = functionType :=
        (cSem_certificate_coherent hA (.arr hDomain hB) env).trans rfl
      rw [functionTypeEq]
      change ULift.up (alignCValue functionType expected _) = ULift.up
        (alignCValue functionType expected (alignCValue functionType functionType _))
      apply congrArg ULift.up
      exact congrArg (alignCValue functionType expected)
        (alignCValue_self functionType _).symm
  | bool value =>
      change ULift.up (alignCValue cBool expected value) = ULift.up
        (alignCValue cBool expected (alignCValue cBool cBool value))
      apply congrArg ULift.up
      exact congrArg (alignCValue cBool expected)
        (alignCValue_self cBool value).symm
  | eq hA hx hy =>
      change ULift.up (alignCValue cBool expected _) = ULift.up
        (alignCValue cBool expected (alignCValue cBool cBool _))
      apply congrArg ULift.up
      exact congrArg (alignCValue cBool expected)
        (alignCValue_self cBool _).symm
  | eps hA hp =>
      change ULift.up (alignCValue (cSem hA env) expected _) = ULift.up
        (alignCValue (cSem hA env) expected
          (alignCValue (cSem hA env) (cSem hA env) _))
      apply congrArg ULift.up
      exact congrArg (alignCValue (cSem hA env) expected)
        (alignCValue_self (cSem hA env) _).symm
  | abs hCarrier hp hx =>
      let subtype := cGuardedType (cSem hCarrier env) fun value =>
        (cSem hp env (extendCBoundEnv (cSem hCarrier env) value emptyCBoundEnv)
          cBool).down
      rw [← typeSemantic]
      have subtypeEq : cSem hA env = subtype :=
        (cSem_certificate_coherent hA (.sub hCarrier hp) env).trans rfl
      rw [subtypeEq]
      change ULift.up (alignCValue subtype expected _) = ULift.up
        (alignCValue subtype expected (alignCValue subtype subtype _))
      apply congrArg ULift.up
      exact congrArg (alignCValue subtype expected)
        (alignCValue_self subtype _).symm
  | rep hA hp hx =>
      change ULift.up (alignCValue (cSem hA env) expected _) = ULift.up
        (alignCValue (cSem hA env) expected
          (alignCValue (cSem hA env) (cSem hA env) _))
      apply congrArg ULift.up
      exact congrArg (alignCValue (cSem hA env) expected)
        (alignCValue_self (cSem hA env) _).symm
  | tyExists hp =>
      change ULift.up (alignCValue cBool expected _) = ULift.up
        (alignCValue cBool expected (alignCValue cBool cBool _))
      apply congrArg ULift.up
      exact congrArg (alignCValue cBool expected)
        (alignCValue_self cBool _).symm

end Nucleus.HolE
