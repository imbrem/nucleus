import Nucleus.HolE.ClassicalApplicationRealization
import Nucleus.HolE.ClassicalEqualityRealization
import Nucleus.HolE.ClassicalIntrinsicRealization
import Nucleus.HolE.ClassicalLambdaRealization
import Nucleus.HolE.EmptySemantics

/-! # Deterministic semantics of equality-encoded universal quantification -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace Infinity

/-- The standard HOL encoding `(λx. p x) = (λx. true)` realizes truth
exactly when its checked body realizes truth at every argument. -/
theorem IEval.forallTm_true_iff
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (hA : Kinded A) (body : InfinityTm ClassicalSig (extendBound A Γ) .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    IEval (InfinityTm.forallTm hA body) env bound cBool true ↔
      ∀ argument : (cSem hA.certificate env).carrier,
        IEval body env
          (extendCBoundEnv (cSem hA.certificate env) argument bound)
          cBool true := by
  let domain := cSem hA.certificate env
  let functionType : CPointed :=
    ⟨domain.carrier → Bool, fun _ => false⟩
  let predicate : functionType.carrier := fun argument =>
    iValue body env (extendCBoundEnv domain argument bound) cBool
  let alwaysTrue : functionType.carrier := fun _ => true
  have predicateRealizes : CRealizes (Γ := Γ) env bound
      (.lam A body.tm) (.arr A .boolTy) functionType predicate := by
    apply (CRealizes.lambda_iff hA.certificate CChecks.boolTy
      body.typing.certificate).mpr
    intro argument
    exact IEval.iff_cRealizes.mp <|
      IEval.canonical body env (extendCBoundEnv domain argument bound) cBool
  have truthRealizes : CRealizes (Γ := Γ) env bound
      (.lam A (.bool true)) (.arr A .boolTy) functionType alwaysTrue := by
    apply (CRealizes.lambda_iff hA.certificate CChecks.boolTy
      (CChecks.bool true)).mpr
    intro argument
    exact CRealizes.boolean true env
      (extendCBoundEnv domain argument bound)
  have equalityTyping : HasTypeDefEq Γ
      (.eq (.arr A .boolTy) (.lam A body.tm) (.lam A (.bool true)))
      .boolTy :=
    .exact (InfinityTm.forallTm hA body).typing
  have equalityIff := CRealizes.eq_true_iff
    (CChecks.arr hA.certificate CChecks.boolTy) equalityTyping
    predicateRealizes truthRealizes
  constructor
  · intro universal argument
    have equalityRealizes : CRealizes (Γ := Γ) env bound
        (.eq (.arr A .boolTy) (.lam A body.tm) (.lam A (.bool true)))
        .boolTy cBool true := by
      exact IEval.iff_cRealizes.mp universal
    have functionsEqual : predicate = alwaysTrue := equalityIff.mp equalityRealizes
    have valueEqual : iValue body env
        (extendCBoundEnv domain argument bound) cBool = true :=
      congrFun functionsEqual argument
    rw [← valueEqual]
    exact IEval.canonical body env
      (extendCBoundEnv domain argument bound) cBool
  · intro every
    apply IEval.iff_cRealizes.mpr
    apply equalityIff.mpr
    funext argument
    have canonical := IEval.canonical body env
      (extendCBoundEnv domain argument bound) cBool
    exact canonical.value_unique (every argument)

end Infinity

end Nucleus.HolE

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Checked-API form of `Infinity.IEval.forallTm_true_iff`. -/
theorem Eval.forallTm_true_iff
    {types : List Kind} {depth : Nat} {Γ : Empty.Ctx types depth}
    (A : Empty.Ty types) (body : Empty.BoolTm (Γ.extend A))
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    Eval (Empty.forallTm A body) env bound cBool true ↔
      ∀ argument : (A.denote env).carrier,
        Eval body env
          (extendCBoundEnv (A.denote env) argument bound) cBool true := by
  unfold Eval
  rw [Term.toIntrinsic_forallTm]
  exact Infinity.IEval.forallTm_true_iff A.kinded body.toIntrinsic env bound

end Nucleus.HolE.Empty
