import Nucleus.HolE.ClassicalEqTmSoundness
import Nucleus.HolE.ClassicalKernelSoundness

/-! # Core classical kernel laws -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem CRealizes.eq_true_elim
    {types : List Kind} {depth : Nat} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {x y : Tm ClassicalSig types depth}
    {env : CTypeEnv types} {bound : CBoundEnv depth}
    (hA : Kinded A)
    (realizes : CRealizes (Γ := Γ) env bound (.eq A x y) .boolTy cBool true) :
    ∃ (left : CChecks Γ x (.tm A)) (right : CChecks Γ y (.tm A)),
      cSem left env bound (denoteChecked hA env) =
        cSem right env bound (denoteChecked hA env) := by
  classical
  obtain ⟨checking, truth⟩ := realizes
  rw [checking.rawView_semantics] at truth
  cases viewEq : checking.rawView with
  | mk rawType raw =>
    rw [viewEq] at truth
    simp only [CDefRawView.sem] at truth
    cases raw with
    | eq cA left right =>
        refine ⟨left, right, ?_⟩
        have decision := congrArg ULift.down truth
        change alignCValue cBool cBool (decide
          ((cSem left env bound (cSem cA env)).down =
            (cSem right env bound (cSem cA env)).down)) = true at decision
        have decided : decide
            ((cSem left env bound (cSem cA env)).down =
              (cSem right env bound (cSem cA env)).down) = true :=
          (alignCValue_self cBool _).symm.trans decision
        have carrierEq : cSem cA env = denoteChecked hA env :=
          cSem_certificate_coherent cA hA.certificate env
        rw [← carrierEq]
        exact congrArg ULift.up (of_decide_eq_true decided)

theorem classical_convert (eqLaws : ClassicalEqTmRuleLaws)
    (conclusionTyping : HasTypeDefEq Γ q .boolTy)
    (equality : EqTm Γ p q .boolTy)
    (premise : CEntails (Γ := Γ) H p) : CEntails (Γ := Γ) H q := by
  intro env bound truths
  obtain ⟨premiseChecking, premiseTrue⟩ := premise env bound truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  have equal := equality.sound_of_laws eqLaws equality.typing.1 conclusionTyping
    env bound cBool
  have premiseTrue' : cDefSem equality.typing.1.certificate env bound cBool = ⟨true⟩ :=
    (equality.typing.1.certificate.coherent premiseChecking env bound cBool).trans premiseTrue
  exact equal.symm.trans premiseTrue'

theorem classical_eqOfEqTm (eqLaws : ClassicalEqTmRuleLaws)
    (_hA : Kinded A) (conclusionTyping : HasTypeDefEq Γ (.eq A x y) .boolTy)
    (equality : EqTm Γ x y A) : CEntails (Γ := Γ) H (.eq A x y) := by
  intro env bound truths
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cA leftChecking rightChecking =>
        let leftTyping : HasTypeDefEq Γ x A := .exact leftChecking.toChecks
        let rightTyping : HasTypeDefEq Γ y A := .exact rightChecking.toChecks
        have operandsEqual := equality.sound_of_laws eqLaws leftTyping rightTyping
          env bound (cSem cA env)
        have rawOperandsEqual :
            cSem leftChecking env bound (cSem cA env) =
              cSem rightChecking env bound (cSem cA env) :=
          ((.exact leftChecking : CDefChecks Γ x A).coherent
            leftTyping.certificate env bound (cSem cA env)).trans
            (operandsEqual.trans
              (rightTyping.certificate.coherent (.exact rightChecking)
                env bound (cSem cA env)))
        change ULift.up (alignCValue cBool cBool (decide (_ = _))) = ULift.up true
        rw [rawOperandsEqual]
        simp
        exact congrArg ULift.up (alignCValue_self cBool true)

private theorem entails_at_certificate
    {types : List Kind} {depth : Nat} {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)}
    {proposition : Tm ClassicalSig types depth}
    (typing : HasTypeDefEq Γ proposition .boolTy)
    (entails : CEntails (Γ := Γ) H proposition)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (truths : CHypsTrue (Γ := Γ) env bound H) :
    cDefSem typing.certificate env bound cBool = ⟨true⟩ := by
  obtain ⟨checking, truth⟩ := entails env bound truths
  exact (typing.certificate.coherent checking env bound cBool).trans truth

theorem classical_eqTm_app
    (leftRaw : HasType Γ (.app f x) B) (_rightRaw : HasType Γ (.app g y) B)
    (leftFunctionRaw : HasType Γ f (.arr A B)) (leftArgumentRaw : HasType Γ x A)
    (rightFunctionRaw : HasType Γ g (.arr A B)) (rightArgumentRaw : HasType Γ y A)
    (functionEqual : CSemEq (Γ := Γ) f g (.arr A B))
    (argumentEqual : CSemEq (Γ := Γ) x y A) :
    CSemEq (Γ := Γ) (.app f x) (.app g y) B := by
  intro leftTyping rightTyping env bound expected
  let hA := leftArgumentRaw.certificate.typeKinded
  let hB := leftRaw.certificate.typeKinded
  let leftApp : CDefChecks Γ (.app f x) B :=
    .exact (.app hA hB leftFunctionRaw.certificate leftArgumentRaw.certificate)
  let rightApp : CDefChecks Γ (.app g y) B :=
    .exact (.app hA hB rightFunctionRaw.certificate rightArgumentRaw.certificate)
  rw [leftTyping.certificate.coherent leftApp env bound expected,
    rightTyping.certificate.coherent rightApp env bound expected]
  let domain := cSem hA env
  let codomain := cSem hB env
  let leftFunctionTyping : HasTypeDefEq Γ f (.arr A B) := .exact leftFunctionRaw
  let rightFunctionTyping : HasTypeDefEq Γ g (.arr A B) := .exact rightFunctionRaw
  let leftArgumentTyping : HasTypeDefEq Γ x A := .exact leftArgumentRaw
  let rightArgumentTyping : HasTypeDefEq Γ y A := .exact rightArgumentRaw
  have functions₀ := functionEqual leftFunctionTyping rightFunctionTyping
    env bound ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
  have functions : cSem leftFunctionRaw.certificate env bound
      ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ =
      cSem rightFunctionRaw.certificate env bound
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ :=
    ((.exact leftFunctionRaw.certificate : CDefChecks Γ f (.arr A B)).coherent
      leftFunctionTyping.certificate env bound _).trans
      (functions₀.trans (rightFunctionTyping.certificate.coherent
        (.exact rightFunctionRaw.certificate) env bound _))
  have arguments₀ := argumentEqual leftArgumentTyping rightArgumentTyping env bound domain
  have arguments : cSem leftArgumentRaw.certificate env bound domain =
      cSem rightArgumentRaw.certificate env bound domain :=
    ((.exact leftArgumentRaw.certificate : CDefChecks Γ x A).coherent
      leftArgumentTyping.certificate env bound domain).trans
      (arguments₀.trans (rightArgumentTyping.certificate.coherent
        (.exact rightArgumentRaw.certificate) env bound domain))
  dsimp [leftApp, rightApp, cDefSem, cSem]
  rw [functions, arguments]

theorem classical_eqTm_lam
    (leftRaw : HasType Γ (.lam A body₁) (.arr A B))
    (rightRaw : HasType Γ (.lam A body₂) (.arr A B)) (_hA : Kinded A)
    (bodiesEqual : CSemEq (Γ := extendBound A Γ) body₁ body₂ B) :
    CSemEq (Γ := Γ) (.lam A body₁) (.lam A body₂) (.arr A B) := by
  intro leftTyping rightTyping env bound expected
  let leftCheck := leftRaw.certificate
  let rightCheck := rightRaw.certificate
  rw [leftTyping.certificate.coherent (.exact leftCheck) env bound expected,
    rightTyping.certificate.coherent (.exact rightCheck) env bound expected]
  cases leftCheck with
  | lam body hA hB leftBody =>
    cases rightCheck with
    | lam _ hA' hB' rightBody =>
      have domainCertEq := hA.unique hA'
      have codomainCertEq := hB.unique hB'
      cases domainCertEq
      cases codomainCertEq
      change ULift.up (alignCValue
        ⟨(cSem hA env).carrier → (cSem hB env).carrier,
          fun _ => (cSem hB env).point⟩ expected
        (fun argument =>
          (cSem leftBody env
            (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env)).down)) =
        ULift.up (alignCValue
          ⟨(cSem hA env).carrier → (cSem hB env).carrier,
            fun _ => (cSem hB env).point⟩ expected
          (fun argument =>
            (cSem rightBody env
              (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env)).down))
      congr 2
      funext argument
      let leftBodyTyping : HasTypeDefEq (extendBound A Γ) body₁ B :=
        .exact leftBody.toChecks
      let rightBodyTyping : HasTypeDefEq (extendBound A Γ) body₂ B :=
        .exact rightBody.toChecks
      have bodyEq := bodiesEqual leftBodyTyping rightBodyTyping env
        (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env)
      have rawBodyEq : cSem leftBody env
          (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env) =
          cSem rightBody env
            (extendCBoundEnv (cSem hA env) argument bound) (cSem hB env) :=
        ((.exact leftBody : CDefChecks (extendBound A Γ) body₁ B).coherent
          leftBodyTyping.certificate env _ _).trans
          (bodyEq.trans (rightBodyTyping.certificate.coherent
            (.exact rightBody) env _ _))
      exact congrArg ULift.down rawBodyEq

theorem classical_eqMp
    (hA : Kinded A) (conclusionTyping : HasTypeDefEq Γ (.app p y) .boolTy)
    (_hp : HasTypeDefEq Γ p (.arr A .boolTy))
    (_hx : HasTypeDefEq Γ x A) (_hy : HasTypeDefEq Γ y A)
    (_equalityTyping : HasTypeDefEq Γ (.eq A x y) .boolTy)
    (premiseTyping : HasTypeDefEq Γ (.app p x) .boolTy)
    (equality : CEntails (Γ := Γ) H (.eq A x y))
    (premise : CEntails (Γ := Γ) H (.app p x)) :
    CEntails (Γ := Γ) H (.app p y) := by
  intro env bound truths
  classical
  have eqRealizes : CRealizes (Γ := Γ) env bound (.eq A x y) .boolTy cBool true :=
    equality env bound truths
  obtain ⟨xChecking, yChecking, xy⟩ := eqRealizes.eq_true_elim hA
  have premiseTrue := entails_at_certificate premiseTyping premise env bound truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [premiseTyping.certificate.rawView_semantics] at premiseTrue
  rw [conclusionTyping.certificate.rawView_semantics]
  cases premiseView : premiseTyping.certificate.rawView with
  | mk premiseType premiseRaw =>
    rw [premiseView] at premiseTrue
    simp only [CDefRawView.sem] at premiseTrue
    cases premiseRaw with
    | app premiseDomain premiseCodomain premiseFunction premiseArgument =>
      cases conclusionView : conclusionTyping.certificate.rawView with
      | mk conclusionType conclusionRaw =>
        simp only [CDefRawView.sem]
        cases conclusionRaw with
        | app conclusionDomain conclusionCodomain conclusionFunction conclusionArgument =>
          have domainEq := premiseArgument.type_unique xChecking
          cases domainEq
          have conclusionDomainEq := conclusionArgument.type_unique yChecking
          cases conclusionDomainEq
          have functionTypeEq := premiseFunction.type_unique conclusionFunction
          injection functionTypeEq with domainAgain codomainEq
          subst conclusionType
          have functionEq := premiseFunction.unique conclusionFunction
          cases functionEq
          have xCertEq := premiseArgument.unique xChecking
          have yCertEq := conclusionArgument.unique yChecking
          cases xCertEq
          cases yCertEq
          have domainCertEq := premiseDomain.unique conclusionDomain
          have codomainCertEq := premiseCodomain.unique conclusionCodomain
          cases domainCertEq
          cases codomainCertEq
          have carrierEq : cSem premiseDomain env = denoteChecked hA env :=
            cSem_certificate_coherent premiseDomain hA.certificate env
          change ULift.up (alignCValue (cSem premiseCodomain env) cBool
            ((cSem premiseFunction env bound
              ⟨(cSem premiseDomain env).carrier → (cSem premiseCodomain env).carrier,
                fun _ => (cSem premiseCodomain env).point⟩).down
              (cSem xChecking env bound (cSem premiseDomain env)).down)) =
                ULift.up true at premiseTrue
          change ULift.up (alignCValue (cSem premiseCodomain env) cBool
            ((cSem premiseFunction env bound
              ⟨(cSem premiseDomain env).carrier → (cSem premiseCodomain env).carrier,
                fun _ => (cSem premiseCodomain env).point⟩).down
              (cSem yChecking env bound (cSem premiseDomain env)).down)) =
                ULift.up true
          rw [carrierEq] at premiseTrue ⊢
          have valueEq := congrArg ULift.down xy
          rw [← valueEq]
          exact premiseTrue

theorem classical_antisymm
    (_hp : HasTypeDefEq Γ p .boolTy) (_hq : HasTypeDefEq Γ q .boolTy)
    (conclusionTyping : HasTypeDefEq Γ (.eq .boolTy p q) .boolTy)
    (left : CEntails (Γ := Γ) (p :: H) q)
    (right : CEntails (Γ := Γ) (q :: H) p) :
    CEntails (Γ := Γ) H (.eq .boolTy p q) := by
  intro env bound truths
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cBoolCheck pCheck qCheck =>
      have boolSem : cSem cBoolCheck env = cBool :=
        cSem_certificate_coherent cBoolCheck .boolTy env
      change ULift.up (alignCValue cBool cBool
        (decide ((cSem pCheck env bound (cSem cBoolCheck env)).down =
          (cSem qCheck env bound (cSem cBoolCheck env)).down))) = ULift.up true
      rw [boolSem]
      let pValue := (cSem pCheck env bound cBool).down
      let qValue := (cSem qCheck env bound cBool).down
      have pEta : cSem pCheck env bound cBool = ULift.up pValue := by
        dsimp [pValue]
      have qEta : cSem qCheck env bound cBool = ULift.up qValue := by
        dsimp [qValue]
      have valuesEqual : pValue = qValue := by
        cases hpv : pValue <;> cases hqv : qValue
        · rfl
        · exfalso
          have qTrue := right env bound (fun candidate member => by
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨.exact qCheck, ?_⟩
              change cSem qCheck env bound cBool = ⟨true⟩
              rw [qEta, hqv]
            · exact truths candidate member)
          obtain ⟨pWitness, pTrue⟩ := qTrue
          have pCheckTrue := (pCheck |> CDefChecks.exact).coherent
            pWitness env bound cBool
          have : cSem pCheck env bound cBool = ⟨true⟩ := pCheckTrue.trans pTrue
          rw [pEta, hpv] at this
          have impossible := congrArg ULift.down this
          contradiction
        · exfalso
          have qTrue := left env bound (fun candidate member => by
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨.exact pCheck, ?_⟩
              change cSem pCheck env bound cBool = ⟨true⟩
              rw [pEta, hpv]
            · exact truths candidate member)
          obtain ⟨qWitness, qTrue⟩ := qTrue
          have qCheckTrue := (qCheck |> CDefChecks.exact).coherent
            qWitness env bound cBool
          have : cSem qCheck env bound cBool = ⟨true⟩ := qCheckTrue.trans qTrue
          rw [qEta, hqv] at this
          have impossible := congrArg ULift.down this
          contradiction
        · rfl
      rw [pEta, qEta]
      simp only
      rw [valuesEqual]
      simp
      exact congrArg ULift.up (alignCValue_self cBool true)

theorem classical_choice
    (_hA : Kinded A)
    (conclusionTyping : HasTypeDefEq Γ (.app p (.eps A p)) .boolTy)
    (_hp : HasTypeDefEq Γ p (.arr A .boolTy)) (_hx : HasTypeDefEq Γ x A)
    (premiseTyping : HasTypeDefEq Γ (.app p x) .boolTy)
    (premise : CEntails (Γ := Γ) H (.app p x)) :
    CEntails (Γ := Γ) H (.app p (.eps A p)) := by
  intro env bound truths
  classical
  have premiseTrue := entails_at_certificate premiseTyping premise env bound truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [premiseTyping.certificate.rawView_semantics] at premiseTrue
  rw [conclusionTyping.certificate.rawView_semantics]
  cases premiseView : premiseTyping.certificate.rawView with
  | mk premiseType premiseRaw =>
    rw [premiseView] at premiseTrue
    simp only [CDefRawView.sem] at premiseTrue
    cases premiseRaw with
    | app premiseDomain premiseCodomain premiseFunction premiseArgument =>
      cases conclusionView : conclusionTyping.certificate.rawView with
      | mk conclusionType conclusionRaw =>
        simp only [CDefRawView.sem]
        cases conclusionRaw with
        | app conclusionDomain conclusionCodomain conclusionFunction conclusionArgument =>
          cases conclusionArgument with
          | eps epsCarrier predicateChecking =>
            have functionTypeEq := conclusionFunction.type_unique predicateChecking
            injection functionTypeEq with _ codomainEq
            subst conclusionType
            have conclusionFunctionEq := conclusionFunction.unique predicateChecking
            cases conclusionFunctionEq
            have conclusionDomainEq := conclusionDomain.unique epsCarrier
            cases conclusionDomainEq
            have conclusionCodomainEq := conclusionCodomain.unique CChecks.boolTy
            cases conclusionCodomainEq
            have premiseFunctionTypeEq := premiseFunction.type_unique predicateChecking
            cases premiseFunctionTypeEq
            have premiseFunctionEq := premiseFunction.unique predicateChecking
            cases premiseFunctionEq
            have premiseDomainEq := premiseDomain.unique epsCarrier
            cases premiseDomainEq
            have premiseCodomainEq := premiseCodomain.unique CChecks.boolTy
            cases premiseCodomainEq
            simp only [cSem]
            change ULift.up (alignCValue cBool cBool
              ((cSem predicateChecking env bound
                ⟨(cSem epsCarrier env).carrier → Bool, fun _ => false⟩).down
                (alignCValue (cSem epsCarrier env) (cSem epsCarrier env)
                  (if witness : ∃ value,
                    (cSem predicateChecking env bound
                      ⟨(cSem epsCarrier env).carrier → Bool, fun _ => false⟩).down value = true
                  then Classical.choose witness else (cSem epsCarrier env).point)))) =
                    ULift.up true
            change ULift.up (alignCValue cBool cBool
              ((cSem predicateChecking env bound
                ⟨(cSem epsCarrier env).carrier → Bool, fun _ => false⟩).down
                (cSem premiseArgument env bound (cSem epsCarrier env)).down)) =
                    ULift.up true at premiseTrue
            have witness : ∃ value,
                (cSem predicateChecking env bound
                  ⟨(cSem epsCarrier env).carrier → Bool, fun _ => false⟩).down value = true := by
              refine ⟨(cSem premiseArgument env bound (cSem epsCarrier env)).down, ?_⟩
              have downTrue := congrArg ULift.down premiseTrue
              exact (alignCValue_self cBool _).symm.trans downTrue
            rw [dif_pos witness]
            have chosen := Classical.choose_spec witness
            rw [alignCValue_self (cSem epsCarrier env) (Classical.choose witness)]
            rw [chosen]
            exact congrArg ULift.up (alignCValue_self cBool true)

end Nucleus.HolE
