import Nucleus.HolE.ClassicalDefEqCoherence
import Nucleus.HolE.ClassicalEquations

/-! # Classical semantic laws for guarded HOL subtypes -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

@[simp] theorem cSem_sub_eq
    {types} {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (env : CTypeEnv types) :
    cSem (CChecks.sub hA hp) env =
      cGuardedType (cSem hA env) fun value =>
        (cEval env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) hp
          cBool).down := by
  rfl

@[simp] theorem cEval_abs_at_subtype
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm A)) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    (cEval env bound (.abs hA hp hx)
      (cGuardedType (cSem hA env) fun value =>
        (cEval env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) hp
          cBool).down)).down =
      cGuardedAbs (cSem hA env)
        (fun value => (cEval env
          (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) hp cBool).down)
        (cEval env bound hx (cSem hA env)).down := by
  change alignCValue _ _ _ = _
  exact alignCValue_self _ _

@[simp] theorem cEval_rep_at_carrier
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm (.sub A p))) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    (cEval env bound (.rep hA hp hx) (cSem hA env)).down =
      (cEval env bound hx
        (cGuardedType (cSem hA env) fun value =>
          (cEval env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) hp
            cBool).down)).down.1 := by
  change alignCValue _ _ _ = _
  exact alignCValue_self _ _

theorem cSem_abs_at_subtype
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm A)) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    (cSem (.abs hA hp hx) env bound
      (cGuardedType (cSem hA env) fun value =>
        (cSem hp env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv)
          cBool).down)).down =
      cGuardedAbs (cSem hA env)
        (fun value => (cSem hp env
          (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) cBool).down)
        (cSem hx env bound (cSem hA env)).down :=
  cEval_abs_at_subtype hA hp hx env bound

theorem cSem_rep_at_carrier
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm (.sub A p))) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    (cSem (.rep hA hp hx) env bound (cSem hA env)).down =
      (cSem hx env bound
        (cGuardedType (cSem hA env) fun value =>
          (cSem hp env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv)
            cBool).down)).down.1 :=
  cEval_rep_at_carrier hA hp hx env bound

theorem cSem_absRep_eq_true
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm (.sub A p)))
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    cSem (CChecks.eq (.sub hA hp) (.abs hA hp (.rep hA hp hx)) hx)
      env bound cBool = ⟨true⟩ := by
  classical
  have subtypeEq := cSem_sub_eq hA hp env
  cases subtypeEq
  apply congrArg ULift.up
  simp only [cSem]
  simp only [alignCValue_self]
  let carrier : CPointed := cSem hA env
  let predicate : carrier.carrier → Bool := fun value =>
    (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
  let subtype := cGuardedType carrier predicate
  let value := (cSem hx env bound subtype).down
  have identity : cGuardedAbs carrier predicate
      (alignCValue carrier carrier value.1) = value := by
    rw [alignCValue_self]
    exact cGuardedAbs_rep carrier predicate value
  have decision : @decide
      (cGuardedAbs carrier predicate
        (alignCValue carrier carrier value.1) = value)
      (Classical.propDecidable _) = true := decide_eq_true identity
  rw [decision]
  exact alignCValue_self cBool true

theorem cSem_repAbs_eq_true
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
    {x : Tm ClassicalSig types depth} (hA : CKinded A)
    (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
    (hx : CChecks Γ x (.tm A)) (env : CTypeEnv types)
    (bound : CBoundEnv depth)
    (predicateTrue : (cSem hp env
      (extendCBoundEnv (cSem hA env) (cSem hx env bound (cSem hA env)).down
        emptyCBoundEnv) cBool).down = true) :
    cSem (CChecks.eq hA (.rep hA hp (.abs hA hp hx)) hx)
      env bound cBool = ⟨true⟩ := by
  classical
  have subtypeEq := cSem_sub_eq hA hp env
  cases subtypeEq
  apply congrArg ULift.up
  simp only [cSem]
  simp only [alignCValue_self]
  let carrier : CPointed := cSem hA env
  let predicate : carrier.carrier → Bool := fun value =>
    (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
  let value := (cSem hx env bound carrier).down
  have identity : alignCValue carrier carrier
      (cGuardedAbs carrier predicate value).1 = value := by
    rw [alignCValue_self]
    exact cGuarded_rep_abs_of_true carrier predicate value predicateTrue
  have decision : @decide
      (alignCValue carrier carrier
        (cGuardedAbs carrier predicate value).1 = value)
      (Classical.propDecidable _) = true := decide_eq_true identity
  rw [decision]
  exact alignCValue_self cBool true

/-- The precise bound-opening fact needed by the two predicate-sensitive
subtype rules.  It is intentionally stated as an iff: `repAbs` consumes an
instantiated proof, whereas `repPredOfWitness` produces one. -/
structure CInstantiateOneTrueLaw where
  true_iff : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x : Tm ClassicalSig types depth},
    (hA : Kinded A) →
    (hp : HasType (extendBound A emptyBound) p .boolTy) →
    (hx : CDefChecks Γ x A) →
    (instanceTyping : HasTypeDefEq Γ (instantiateOne p x) .boolTy) →
    ∀ (env : CTypeEnv types) (bound : CBoundEnv depth),
      CRealizes (Γ := Γ) env bound (instantiateOne p x) .boolTy cBool true ↔
        (cEval env
          (extendCBoundEnv (cSem hA.certificate env)
            (cDefSem hx env bound (cSem hA.certificate env)).down
            emptyCBoundEnv)
          hp.certificate cBool).down = true
  rep_true_iff : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x : Tm ClassicalSig types depth},
    (hA : Kinded A) →
    (hp : HasType (extendBound A emptyBound) p .boolTy) →
    (hx : HasTypeDefEq Γ x (.sub A p)) →
    (instanceTyping :
      HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy) →
    ∀ (env : CTypeEnv types) (bound : CBoundEnv depth),
      CRealizes (Γ := Γ) env bound (instantiateOne p (.rep A p x))
          .boolTy cBool true ↔
        (cEval env
          (extendCBoundEnv (cSem hA.certificate env)
            (cDefSem hx.certificate env bound
              (cSem (.sub hA.certificate hp.certificate) env)).down.1
            emptyCBoundEnv)
          hp.certificate cBool).down = true

namespace CEntails

/-- Abstraction after representation is the identity on a guarded subtype. -/
theorem absRepLaw {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth}
    (_hA : Kinded A)
    (conclusionTyping : HasTypeDefEq Γ
      (.eq (.sub A p) (.abs A p (.rep A p x)) x) .boolTy)
    (_hp : HasType (extendBound A emptyBound) p .boolTy)
    (_hx : HasTypeDefEq Γ x (.sub A p)) :
    CEntails (Γ := Γ) H (.eq (.sub A p) (.abs A p (.rep A p x)) x) := by
  intro env bound typed valid truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  classical
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cSub left right =>
      cases left with
      | abs cA cp representation =>
        cases representation with
        | rep cA' cp' represented =>
          have carrierEq := cA.unique cA'
          cases carrierEq
          have predicateEq := cp.unique cp'
          cases predicateEq
          have valueEq := represented.unique right
          cases valueEq
          have subtypeKindEq := cSub.unique (.sub cA cp)
          cases subtypeKindEq
          exact cSem_absRep_eq_true cA cp right env bound

/-- Representation after abstraction is the identity when the represented
value satisfies the subtype predicate. -/
theorem repAbsLaw (opening : CInstantiateOneTrueLaw)
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth}
    (hA : Kinded A)
    (conclusionTyping : HasTypeDefEq Γ
      (.eq A (.rep A p (.abs A p x)) x) .boolTy)
    (hp : HasType (extendBound A emptyBound) p .boolTy)
    (hx : HasTypeDefEq Γ x A)
    (instanceTyping : HasTypeDefEq Γ (instantiateOne p x) .boolTy)
    (premise : CEntails (Γ := Γ) H (instantiateOne p x)) :
    CEntails (Γ := Γ) H (.eq A (.rep A p (.abs A p x)) x) := by
  intro env bound typed valid truths
  have predicateTrue :=
    (opening.true_iff hA hp hx.certificate instanceTyping env bound).mp
      (premise env bound typed valid truths)
  refine ⟨conclusionTyping.certificate, ?_⟩
  classical
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cA left right =>
      cases left with
      | rep cA' cp abstraction =>
        cases abstraction with
        | abs cA'' cp' value =>
          have carrierEq := cA.unique cA'
          cases carrierEq
          have carrierEq' := cA.unique cA''
          cases carrierEq'
          have predicateEq := cp.unique cp'
          cases predicateEq
          have valueEq := value.unique right
          cases valueEq
          have cAEq := cA.unique hA.certificate
          cases cAEq
          have cpEq := cp.unique hp.certificate
          cases cpEq
          have valueSem := hx.certificate.coherent (.exact right) env bound
            (cSem hA.certificate env)
          have valueSemDown := congrArg ULift.down valueSem
          have rawPredicateTrue :
              (cEval env (extendCBoundEnv (cSem hA.certificate env)
                (cSem right env bound (cSem hA.certificate env)).down
                emptyCBoundEnv) hp.certificate cBool).down = true := by
            change (cEval env (extendCBoundEnv (cSem hA.certificate env)
              (cDefSem (.exact right) env bound
                (cSem hA.certificate env)).down emptyCBoundEnv)
              hp.certificate cBool).down = true
            rw [← valueSemDown]
            exact predicateTrue
          exact cSem_repAbs_eq_true hA.certificate hp.certificate right
            env bound rawPredicateTrue

/-- If the guarded predicate has a witness, every representation of a subtype
value satisfies it.  The nonempty fallback branch of `CGuarded` is thereby
excluded. -/
theorem repPredOfWitnessLaw (opening : CInstantiateOneTrueLaw)
    {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {p : Tm ClassicalSig types 1} {witness x : Tm ClassicalSig types depth}
    (hA : Kinded A)
    (_conclusionTyping :
      HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy)
    (hp : HasType (extendBound A emptyBound) p .boolTy)
    (witnessTyping : HasTypeDefEq Γ witness A)
    (witnessPredicateTyping :
      HasTypeDefEq Γ (instantiateOne p witness) .boolTy)
    (subtypeTyping : HasTypeDefEq Γ x (.sub A p))
    (representationPredicateTyping :
      HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy)
    (premise : CEntails (Γ := Γ) H (instantiateOne p witness)) :
    CEntails (Γ := Γ) H (instantiateOne p (.rep A p x)) := by
  intro env bound typed valid truths
  let cw := witnessTyping.certificate
  have witnessTrue :=
    (opening.true_iff hA hp cw witnessPredicateTyping env bound).mp
      (premise env bound typed valid truths)
  apply (opening.rep_true_iff hA hp subtypeTyping
    representationPredicateTyping env bound).mpr
  have subtypeEq := cSem_sub_eq hA.certificate hp.certificate env
  cases subtypeEq
  exact cGuarded_rep_pred_of_witness (cSem hA.certificate env)
    (fun value =>
      (cEval env (extendCBoundEnv (cSem hA.certificate env) value
        emptyCBoundEnv) hp.certificate cBool).down)
    (cDefSem cw env bound (cSem hA.certificate env)).down witnessTrue
    (cDefSem subtypeTyping.certificate env bound
      (cGuardedType (cSem hA.certificate env) fun value =>
        (cEval env (extendCBoundEnv (cSem hA.certificate env) value
          emptyCBoundEnv) hp.certificate cBool).down)).down


end CEntails

end Nucleus.HolE
