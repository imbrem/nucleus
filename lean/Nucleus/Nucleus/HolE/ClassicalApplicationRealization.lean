import Nucleus.HolE.ClassicalRealization

/-! # Semantic decoding of classical HOL application -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A checked application realizes exactly the result of applying the
deterministic realizations of its function and argument.  The statement is
entirely about checked HOL syntax and is independent of source languages. -/
theorem CRealizes.app_iff
    {Γ : BoundCtx ClassicalSig types depth}
    {A B : Ty ClassicalSig types}
    {functionTerm argumentTerm : Tm ClassicalSig types depth}
    {env : CTypeEnv types} {bound : CBoundEnv depth}
    (hA : CChecks (Nucleus.HolE.emptyBound :
      BoundCtx ClassicalSig types 0) A .kind)
    (hB : CChecks (Nucleus.HolE.emptyBound :
      BoundCtx ClassicalSig types 0) B .kind)
    (functionChecking : CChecks Γ functionTerm (.tm (.arr A B)))
    (argumentChecking : CChecks Γ argumentTerm (.tm A))
    {function : (cSem hA env).carrier → (cSem hB env).carrier}
    {argument : (cSem hA env).carrier} {result : (cSem hB env).carrier}
    (functionRealizes : CRealizes (Γ := Γ) env bound functionTerm (.arr A B)
      ⟨(cSem hA env).carrier → (cSem hB env).carrier,
        fun _ => (cSem hB env).point⟩ function)
    (argumentRealizes : CRealizes (Γ := Γ) env bound argumentTerm A
      (cSem hA env) argument) :
    CRealizes (Γ := Γ) env bound (.app functionTerm argumentTerm) B
        (cSem hB env) result ↔
      result = function argument := by
  let functionType : CPointed :=
    ⟨(cSem hA env).carrier → (cSem hB env).carrier,
      fun _ => (cSem hB env).point⟩
  let checkedFunction : functionType.carrier :=
    (cSem functionChecking env bound functionType).down
  let checkedArgument : (cSem hA env).carrier :=
    (cSem argumentChecking env bound (cSem hA env)).down
  let checkedResult : (cSem hB env).carrier :=
    checkedFunction checkedArgument
  have checkedFunctionRealizes : CRealizes (Γ := Γ) env bound functionTerm
      (.arr A B) functionType checkedFunction :=
    ⟨.exact functionChecking, rfl⟩
  have checkedArgumentRealizes : CRealizes (Γ := Γ) env bound argumentTerm A
      (cSem hA env) checkedArgument :=
    ⟨.exact argumentChecking, rfl⟩
  have checkedResultRealizes : CRealizes (Γ := Γ) env bound
      (.app functionTerm argumentTerm) B (cSem hB env) checkedResult := by
    refine ⟨.exact (.app hA hB functionChecking argumentChecking), ?_⟩
    change ULift.up (alignCValue (cSem hB env) (cSem hB env)
      checkedResult) = ULift.up checkedResult
    exact congrArg ULift.up (alignCValue_self (cSem hB env) checkedResult)
  have functionEqual : function = checkedFunction :=
    functionRealizes.value_unique checkedFunctionRealizes
  have argumentEqual : argument = checkedArgument :=
    argumentRealizes.value_unique checkedArgumentRealizes
  constructor
  · intro realizes
    have resultEqual : result = checkedResult :=
      realizes.value_unique checkedResultRealizes
    exact resultEqual.trans <| congrArg checkedFunction argumentEqual.symm |>.trans <|
      congrFun functionEqual.symm argument
  · intro resultEqual
    have targetEqual : result = checkedResult := by
      rw [resultEqual, functionEqual, argumentEqual]
    rw [targetEqual]
    exact checkedResultRealizes

end Nucleus.HolE
