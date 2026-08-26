import Nucleus.HolE.ClassicalRealization

/-! # Semantic decoding of classical HOL lambdas -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A checked lambda realizes exactly the function obtained by realizing its
body under an extended bound-variable environment.  This is a law of checked
HOL syntax; no source-language elaborator or naming convention is involved. -/
theorem CRealizes.lambda_iff
    {Γ : BoundCtx ClassicalSig types depth}
    {A B : Ty ClassicalSig types}
    {body : Tm ClassicalSig types (depth + 1)}
    {env : CTypeEnv types} {bound : CBoundEnv depth}
    (hA : CChecks (Nucleus.HolE.emptyBound :
      BoundCtx ClassicalSig types 0) A .kind)
    (hB : CChecks (Nucleus.HolE.emptyBound :
      BoundCtx ClassicalSig types 0) B .kind)
    (bodyChecking : CChecks (extendBound A Γ) body (.tm B))
    {function : (cSem hA env).carrier → (cSem hB env).carrier} :
    CRealizes (Γ := Γ) env bound (.lam A body) (.arr A B)
        ⟨(cSem hA env).carrier → (cSem hB env).carrier,
          fun _ => (cSem hB env).point⟩ function ↔
      ∀ argument,
        CRealizes (Γ := extendBound A Γ) env
          (extendCBoundEnv (cSem hA env) argument bound)
          body B (cSem hB env) (function argument) := by
  let functionType : CPointed :=
    ⟨(cSem hA env).carrier → (cSem hB env).carrier,
      fun _ => (cSem hB env).point⟩
  let lambdaChecking : CChecks Γ (.lam A body) (.tm (.arr A B)) :=
    .lam body hA hB bodyChecking
  let canonical : functionType.carrier := fun argument =>
    (cSem bodyChecking env
      (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env)).down
  have canonicalRealizes : CRealizes (Γ := Γ) env bound (.lam A body) (.arr A B)
      functionType canonical := by
    refine ⟨.exact lambdaChecking, ?_⟩
    change ULift.up (alignCValue functionType functionType canonical) =
      ULift.up canonical
    exact congrArg ULift.up (alignCValue_self functionType canonical)
  constructor
  · intro realizes argument
    have functionEqual : function = canonical :=
      realizes.value_unique canonicalRealizes
    subst function
    exact ⟨.exact bodyChecking, rfl⟩
  · intro bodyRealizes
    have functionEqual : function = canonical := by
      funext argument
      exact (bodyRealizes argument).value_unique
        ⟨.exact bodyChecking, rfl⟩
    subst function
    exact canonicalRealizes

end Nucleus.HolE
