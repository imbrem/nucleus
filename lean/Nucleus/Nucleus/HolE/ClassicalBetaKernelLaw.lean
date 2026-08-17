import Nucleus.HolE.ClassicalCoreKernelLaws
import Nucleus.HolE.ClassicalInstantiateOneLaw

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

/-- The substitution environment for opening agrees extensionally with the
environment obtained by evaluating the argument and pushing its value. -/
private theorem openSub_bound_eq
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    {x : Tm ClassicalSig types depth}
    (hA : CKinded A) (cx : CChecks Γ x (.tm A))
    (typed : TypedCtx Γ) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (valid : CBoundValid typed env bound) :
    let σ : Fin (depth + 1) → Tm ClassicalSig types depth := Fin.cases x .bv
    let checked : CWellTypedSub (extendBound A Γ) Γ σ := fun i =>
      Fin.cases cx (fun j => .bv (typed j).certificate rfl) i
    checked.bound env bound = extendCBoundEnv (cSem hA env)
      (cSem cx env bound (cSem hA env)).down bound := by
  dsimp only
  funext i expected
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold CWellTypedSub.bound
    have argumentAtExpected := cx.cSem_expected_valid hA env bound typed valid expected
    change (cSem cx env bound expected).down =
      extendCBoundEnv (cSem hA env)
        (cSem cx env bound (cSem hA env)).down bound 0 expected
    exact (congrArg ULift.down argumentAtExpected).trans
      (extendCBoundEnv_zero (cSem hA env)
        (cSem cx env bound (cSem hA env)).down bound expected).symm
  · unfold CWellTypedSub.bound
    change bound j expected = extendCBoundEnv (cSem hA env)
      (cSem cx env bound (cSem hA env)).down bound j.succ expected
    exact (extendCBoundEnv_succ (cSem hA env)
      (cSem cx env bound (cSem hA env)).down bound j expected).symm

private theorem extendCBoundEnv_valid_of_eq
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (hA : Kinded A) (typed : TypedCtx Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (valid : CBoundValid typed env bound)
    (semantic : CPointed) (equal : denoteChecked hA env = semantic) :
    ∀ value : semantic.carrier,
      CBoundValid (typed.extend hA) env
        (extendCBoundEnv semantic value bound) := by
  subst semantic
  exact fun value => extendCBoundEnv_valid hA typed env bound valid value

private theorem extendCBoundEnv_valid_raw
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (hA : CKinded A) (typed : TypedCtx Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (valid : CBoundValid typed env bound)
    (value : (cSem hA env).carrier) :
    CBoundValid (typed.extend hA.toChecks) env
      (extendCBoundEnv (cSem hA env) value bound) :=
  extendCBoundEnv_valid_of_eq hA.toChecks typed env bound valid (cSem hA env)
    (cSem_certificate_coherent _ hA env) value

/-- Concrete semantic soundness of kernel beta conversion. -/
theorem classical_eqTm_beta
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {A B : Ty ClassicalSig types} {body : Tm ClassicalSig types (depth + 1)}
    {x : Tm ClassicalSig types depth}
    (_hA : Kinded A) (typedContext : TypedCtx Γ)
    (applicationRaw : HasType Γ (.app (.lam A body) x) B)
    (_bodyTyping : HasTypeDefEq (extendBound A Γ) body B)
    (_argumentTyping : HasTypeDefEq Γ x A)
    (_resultTyping : HasTypeDefEq Γ (openBound body x) B) :
    CSemEq (Γ := Γ) (.app (.lam A body) x) (openBound body x) B := by
  intro leftTyping rightTyping env bound typed valid expected
  cases applicationRaw.certificate with
  | app cA cB function argument =>
    cases function with
    | lam _ cA' cB' bodyRaw =>
      have domainCertEq := cA.unique cA'
      have codomainCertEq := cB.unique cB'
      cases domainCertEq
      cases codomainCertEq
      let openRaw : CChecks Γ (openBound body x) (.tm B) :=
        (HasType.openBound typedContext bodyRaw.toChecks argument.toChecks).certificate
      let σ : Fin (depth + 1) → Tm ClassicalSig types depth := Fin.cases x .bv
      let checked : CWellTypedSub (extendBound A Γ) Γ σ := fun i =>
        Fin.cases argument (fun j => .bv (typedContext j).certificate rfl) i
      rw [leftTyping.certificate.coherent
          (.exact (.app cA' cB (.lam body cA' cB bodyRaw) argument))
          env bound expected,
        rightTyping.certificate.coherent (.exact openRaw) env bound expected]
      have contextProofEq : typedContext = typed := Subsingleton.elim _ _
      subst typedContext
      have substitutionBound : checked.bound env bound =
          extendCBoundEnv (cSem cA' env)
            (cSem argument env bound (cSem cA' env)).down bound :=
        openSub_bound_eq cA' argument typed env bound valid
      have opened := cSem_instantiate_raw bodyRaw σ checked openRaw
        env bound expected
      rw [substitutionBound] at opened
      let argumentValue := (cSem argument env bound (cSem cA' env)).down
      have extendedValid := extendCBoundEnv_valid_raw cA' typed env bound valid
        argumentValue
      have bodyExpected := bodyRaw.cSem_expected_valid cB env
        (extendCBoundEnv (cSem cA' env) argumentValue bound)
        (typed.extend cA'.toChecks) extendedValid expected
      simp only [cDefSem, cSem]
      rw [alignCValue_self]
      exact bodyExpected.symm.trans opened.symm

end Nucleus.HolE
