import Nucleus.HolE.ClassicalSoundness

/-! # Basic laws of proof-relevant HolE realization -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Every term typed modulo family equality has a value at every requested
pointed carrier.  Later coherence theorems show that requesting the denotation
of its advertised type never uses `alignCValue`'s fallback branch. -/
theorem CRealizes.exists_of_type
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    ∃ value, CRealizes (Γ := Γ) env bound term A expected value := by
  let checking := typing.certificate
  let value := (cDefSem checking env bound expected).down
  exact ⟨value, checking, rfl⟩

/-- Realization is independent of the proof-relevant typing or conversion
certificate used to compute it. -/
theorem CRealizes.value_unique
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} {env : CTypeEnv types} {bound : CBoundEnv depth}
    {expected : CPointed} {left right : expected.carrier}
    (leftRealizes : CRealizes (Γ := Γ) env bound term A expected left)
    (rightRealizes : CRealizes (Γ := Γ) env bound term A expected right) :
    left = right := by
  obtain ⟨leftChecking, leftValue⟩ := leftRealizes
  obtain ⟨rightChecking, rightValue⟩ := rightRealizes
  have values : (ULift.up left : ULift expected.carrier) = ULift.up right :=
    leftValue.symm.trans <|
      (leftChecking.coherent rightChecking env bound expected).trans rightValue
  exact congrArg ULift.down values

/-- A Boolean term has one of the two Boolean realizations. -/
theorem CRealizes.bool_cases
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    (typing : HasTypeDefEq Γ term .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    CRealizes (Γ := Γ) env bound term .boolTy cBool true ∨
      CRealizes (Γ := Γ) env bound term .boolTy cBool false := by
  obtain ⟨value, realizes⟩ := CRealizes.exists_of_type typing env bound cBool
  cases value with
  | false => exact Or.inr realizes
  | true => exact Or.inl realizes

theorem cDefSem_bool_literal
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.bool literal) A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    cDefSem checking env bound cBool = ⟨literal⟩ := by
  cases checking with
  | exact raw =>
      cases raw
      change ULift.up (alignCValue cBool cBool literal) = ULift.up literal
      exact congrArg ULift.up (alignCValue_self cBool literal)
  | conv source hB conversion => exact cDefSem_bool_literal source env bound
termination_by sizeOf checking

/-- Realization of a literal is canonical, independently of conversion
wrappers in its typing certificate. -/
theorem CRealizes.bool_literal_iff (literal value : Bool)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    CRealizes (Γ := Γ) env bound (.bool literal) .boolTy cBool value ↔
      value = literal := by
  constructor
  · rintro ⟨checking, evaluates⟩
    rw [cDefSem_bool_literal checking env bound] at evaluates
    exact (congrArg ULift.down evaluates).symm
  · intro equal
    subst value
    exact CRealizes.boolean literal env bound

end Nucleus.HolE
