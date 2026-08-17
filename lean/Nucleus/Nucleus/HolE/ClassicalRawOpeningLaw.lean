import Nucleus.HolE.ClassicalBetaKernelLaw
import Nucleus.HolE.ClassicalRawOpeningInterface

/-! # Raw-typed semantic opening

This module isolates the syntax-directed version of the predicate-opening law.
Unlike `CInstantiateOneTrueLaw`, it does not need to reconcile replacement
terms whose advertised type is connected to the predicate carrier only by
`FamEq`.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

private theorem CRealizes.raw_bool_iff
    {Γ : BoundCtx ClassicalSig types depth}
    {term : Tm ClassicalSig types depth}
    (raw : CChecks Γ term (.tm .boolTy))
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    CRealizes (Γ := Γ) env bound term .boolTy cBool true ↔
      cSem raw env bound cBool = ⟨true⟩ := by
  constructor
  · rintro ⟨checking, value⟩
    rw [checking.coherent (.exact raw) env bound cBool] at value
    exact value
  · intro value
    exact ⟨.exact raw, value⟩

private theorem instantiateOne_bound_eq
    {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {x : Tm ClassicalSig types depth}
    (hA : CKinded A) (hx : CChecks Γ x (.tm A))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (typed : TypedCtx Γ) (valid : CBoundValid typed env bound) :
    let checked : CWellTypedSub (extendBound A emptyBound) Γ
        (fun _ => x) := fun i => Fin.cases hx (fun j => Fin.elim0 j) i
    checked.bound env bound = extendCBoundEnv (cSem hA env)
      (cSem hx env bound (cSem hA env)).down emptyCBoundEnv := by
  dsimp only
  funext i expected
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  unfold CWellTypedSub.bound
  have atExpected := hx.cSem_expected_valid hA env bound typed valid expected
  change (cSem hx env bound expected).down =
    extendCBoundEnv (cSem hA env)
      (cSem hx env bound (cSem hA env)).down emptyCBoundEnv 0 expected
  exact (congrArg ULift.down atExpected).trans
    (extendCBoundEnv_zero (cSem hA env)
      (cSem hx env bound (cSem hA env)).down emptyCBoundEnv expected).symm

private theorem raw_opening_true_iff
    {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth}
    (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm A))
    (instanceTyping : CChecks Γ (instantiateOne p x) (.tm .boolTy))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (typed : TypedCtx Γ) (valid : CBoundValid typed env bound) :
    CRealizes (Γ := Γ) env bound (instantiateOne p x) .boolTy cBool true ↔
      (cSem hp env
        (extendCBoundEnv (cSem hA env)
          (cSem hx env bound (cSem hA env)).down emptyCBoundEnv)
        cBool).down = true := by
  let checked : CWellTypedSub (extendBound A emptyBound) Γ (fun _ => x) :=
    fun i => Fin.cases hx (fun j => Fin.elim0 j) i
  have semantic := cSem_instantiate_raw hp (fun _ => x) checked
    instanceTyping env bound cBool
  have boundEq := instantiateOne_bound_eq hA hx env bound typed valid
  rw [boundEq] at semantic
  rw [CRealizes.raw_bool_iff instanceTyping]
  constructor
  · intro instanceTrue
    have predicateTrue := semantic.symm.trans instanceTrue
    exact congrArg ULift.down predicateTrue
  · intro predicateTrue
    exact semantic.trans (congrArg ULift.up predicateTrue)

/-- The concrete syntax-directed opening law. -/
theorem classicalRawInstantiateOneTrueLaw : CRawInstantiateOneTrueLaw where
  true_iff := raw_opening_true_iff
  rep_true_iff := by
    intro types depth Γ A p x hA hp hx instanceTyping env bound typed valid
    exact raw_opening_true_iff hA hp (.rep hA hp hx) instanceTyping env bound
      typed valid

end Nucleus.HolE
