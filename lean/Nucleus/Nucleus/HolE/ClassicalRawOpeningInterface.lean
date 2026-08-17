import Nucleus.HolE.ClassicalDefEqCoherence

/-! # Interface for raw-typed semantic opening

The predicate-sensitive kernel rules expose syntax-directed typings for the
values substituted into predicates.  These witnesses already imply the
corresponding `HasTypeDefEq` facts, so the kernel does not duplicate them as
premises.  This is the minimal sound interface needed by the concrete
semantics.  Recovering variants whose premises accept arbitrary
`HasTypeDefEq` derivations is a later admissibility result: it requires a
component-decomposition capability for `FamEq`, so that a converted composite
typing can be inverted at the carrier types expected by substitution.  Such a
capability cannot be assumed for arbitrary signature-provided equalities.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- The raw-typed opening facts needed by predicate-sensitive subtype rules. -/
structure CRawInstantiateOneTrueLaw where
  true_iff : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x : Tm ClassicalSig types depth},
    (hA : CKinded A) →
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) →
    (hx : CChecks Γ x (.tm A)) →
    (instanceTyping : CChecks Γ (instantiateOne p x) (.tm .boolTy)) →
    ∀ (env : CTypeEnv types) (bound : CBoundEnv depth)
      (typed : TypedCtx Γ), CBoundValid typed env bound → (
      CRealizes (Γ := Γ) env bound (instantiateOne p x) .boolTy cBool true ↔
        (cSem hp env
          (extendCBoundEnv (cSem hA env)
            (cSem hx env bound (cSem hA env)).down emptyCBoundEnv)
          cBool).down = true)
  rep_true_iff : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x : Tm ClassicalSig types depth},
    (hA : CKinded A) →
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) →
    (hx : CChecks Γ x (.tm (.sub A p))) →
    (instanceTyping :
      CChecks Γ (instantiateOne p (.rep A p x)) (.tm .boolTy)) →
    ∀ (env : CTypeEnv types) (bound : CBoundEnv depth)
      (typed : TypedCtx Γ), CBoundValid typed env bound → (
      CRealizes (Γ := Γ) env bound (instantiateOne p (.rep A p x))
          .boolTy cBool true ↔
        (cSem hp env
          (extendCBoundEnv (cSem hA env)
            (cSem (.rep hA hp hx) env bound (cSem hA env)).down
            emptyCBoundEnv)
          cBool).down = true)

end Nucleus.HolE
