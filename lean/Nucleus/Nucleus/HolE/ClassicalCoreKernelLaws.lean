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
  intro env bound typed valid truths
  obtain ⟨premiseChecking, premiseTrue⟩ := premise env bound typed valid truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  have equal := equality.sound_of_laws eqLaws equality.typing.1 conclusionTyping
    env bound typed valid cBool
  have premiseTrue' : cDefSem equality.typing.1.certificate env bound cBool = ⟨true⟩ :=
    (equality.typing.1.certificate.coherent premiseChecking env bound cBool).trans premiseTrue
  exact equal.symm.trans premiseTrue'

theorem classical_eqOfEqTm (eqLaws : ClassicalEqTmRuleLaws)
    (_hA : Kinded A) (conclusionTyping : HasTypeDefEq Γ (.eq A x y) .boolTy)
    (equality : EqTm Γ x y A) : CEntails (Γ := Γ) H (.eq A x y) := by
  intro env bound typed valid truths
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
          env bound typed valid (cSem cA env)
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
    (typed : TypedCtx Γ) (valid : CBoundValid typed env bound)
    (truths : CHypsTrue (Γ := Γ) env bound H) :
    cDefSem typing.certificate env bound cBool = ⟨true⟩ := by
  obtain ⟨checking, truth⟩ := entails env bound typed valid truths
  exact (typing.certificate.coherent checking env bound cBool).trans truth

private theorem raw_semantics_of_eqTm
    {types : List Kind} {depth : Nat} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} {left right : Tm ClassicalSig types depth}
    (leftRaw : HasType Γ left A) (rightRaw : HasType Γ right A)
    (equality : CSemEq (Γ := Γ) left right A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (typed : TypedCtx Γ)
    (valid : CBoundValid typed env bound) (expected : CPointed) :
    cSem leftRaw.certificate env bound expected =
      cSem rightRaw.certificate env bound expected := by
  let leftTyping : HasTypeDefEq Γ left A := .exact leftRaw
  let rightTyping : HasTypeDefEq Γ right A := .exact rightRaw
  exact (leftTyping.certificate.coherent (.exact leftRaw.certificate)
      env bound expected).symm.trans
    ((equality leftTyping rightTyping env bound typed valid expected).trans
      (rightTyping.certificate.coherent (.exact rightRaw.certificate)
        env bound expected))

theorem classical_eqTm_app
    (leftRaw : HasType Γ (.app f x) B) (_rightRaw : HasType Γ (.app g y) B)
    (leftFunctionRaw : HasType Γ f (.arr A B)) (leftArgumentRaw : HasType Γ x A)
    (rightFunctionRaw : HasType Γ g (.arr A B)) (rightArgumentRaw : HasType Γ y A)
    (functionEqual : CSemEq (Γ := Γ) f g (.arr A B))
    (argumentEqual : CSemEq (Γ := Γ) x y A) :
    CSemEq (Γ := Γ) (.app f x) (.app g y) B := by
  intro leftTyping rightTyping env bound typed valid expected
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
    env bound typed valid ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
  have functions : cSem leftFunctionRaw.certificate env bound
      ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ =
      cSem rightFunctionRaw.certificate env bound
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ :=
    ((.exact leftFunctionRaw.certificate : CDefChecks Γ f (.arr A B)).coherent
      leftFunctionTyping.certificate env bound _).trans
      (functions₀.trans (rightFunctionTyping.certificate.coherent
        (.exact rightFunctionRaw.certificate) env bound _))
  have arguments₀ := argumentEqual leftArgumentTyping rightArgumentTyping env bound
    typed valid domain
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
    (rightRaw : HasType Γ (.lam A body₂) (.arr A B)) (kindedA : Kinded A)
    (bodiesEqual : CSemEq (Γ := extendBound A Γ) body₁ body₂ B) :
    CSemEq (Γ := Γ) (.lam A body₁) (.lam A body₂) (.arr A B) := by
  intro leftTyping rightTyping env bound typed valid expected
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
      have declaredDomainEq := hA.unique kindedA.certificate
      cases declaredDomainEq
      change ULift.up (alignCValue
        ⟨(denoteChecked kindedA env).carrier → (cSem hB env).carrier,
          fun _ => (cSem hB env).point⟩ expected
        (fun argument =>
          (cSem leftBody env
            (extendCBoundEnv (denoteChecked kindedA env) argument bound) (cSem hB env)).down)) =
        ULift.up (alignCValue
          ⟨(denoteChecked kindedA env).carrier → (cSem hB env).carrier,
            fun _ => (cSem hB env).point⟩ expected
          (fun argument =>
            (cSem rightBody env
              (extendCBoundEnv (denoteChecked kindedA env) argument bound) (cSem hB env)).down))
      congr 2
      funext argument
      let leftBodyTyping : HasTypeDefEq (extendBound A Γ) body₁ B :=
        .exact leftBody.toChecks
      let rightBodyTyping : HasTypeDefEq (extendBound A Γ) body₂ B :=
        .exact rightBody.toChecks
      have extendedValid := extendCBoundEnv_valid kindedA typed env bound valid argument
      have bodyEq := bodiesEqual leftBodyTyping rightBodyTyping env
        (extendCBoundEnv (denoteChecked kindedA env) argument bound) (typed.extend kindedA)
        extendedValid (cSem hB env)
      have rawBodyEq : cSem leftBody env
          (extendCBoundEnv (denoteChecked kindedA env) argument bound) (cSem hB env) =
          cSem rightBody env
            (extendCBoundEnv (denoteChecked kindedA env) argument bound) (cSem hB env) :=
        ((.exact leftBody : CDefChecks (extendBound A Γ) body₁ B).coherent
          leftBodyTyping.certificate env _ _).trans
          (bodyEq.trans (rightBodyTyping.certificate.coherent
            (.exact rightBody) env _ _))
      exact congrArg ULift.down rawBodyEq

theorem classical_eqTm_eq
    (leftRaw : HasType Γ (.eq A x₁ y₁) .boolTy)
    (rightRaw : HasType Γ (.eq A x₂ y₂) .boolTy) (hA : Kinded A)
    (leftEqual : CSemEq (Γ := Γ) x₁ x₂ A)
    (rightEqual : CSemEq (Γ := Γ) y₁ y₂ A) :
    CSemEq (Γ := Γ) (.eq A x₁ y₁) (.eq A x₂ y₂) .boolTy := by
  intro leftTyping rightTyping env bound typed valid expected
  cases leftRaw with
  | eq _ left₁ right₁ =>
    cases rightRaw with
    | eq _ left₂ right₂ =>
      let leftCheck : CDefChecks Γ (.eq A x₁ y₁) .boolTy :=
        .exact (.eq hA.certificate left₁.certificate right₁.certificate)
      let rightCheck : CDefChecks Γ (.eq A x₂ y₂) .boolTy :=
        .exact (.eq hA.certificate left₂.certificate right₂.certificate)
      rw [leftTyping.certificate.coherent leftCheck env bound expected,
        rightTyping.certificate.coherent rightCheck env bound expected]
      have leftOperands := raw_semantics_of_eqTm left₁ left₂ leftEqual
        env bound typed valid (denoteChecked hA env)
      have rightOperands := raw_semantics_of_eqTm right₁ right₂ rightEqual
        env bound typed valid (denoteChecked hA env)
      have leftOperandValues :
          (cSem left₁.certificate env bound (cSem hA.certificate env)).down =
            (cSem left₂.certificate env bound (cSem hA.certificate env)).down := by
        simpa [denoteChecked] using congrArg ULift.down leftOperands
      have rightOperandValues :
          (cSem right₁.certificate env bound (cSem hA.certificate env)).down =
            (cSem right₂.certificate env bound (cSem hA.certificate env)).down := by
        simpa [denoteChecked] using congrArg ULift.down rightOperands
      dsimp [leftCheck, rightCheck, cDefSem, cSem]
      rw [leftOperandValues, rightOperandValues]

theorem classical_eqTm_eps
    (leftRaw : HasType Γ (.eps A p) A) (rightRaw : HasType Γ (.eps A q) A)
    (hA : Kinded A) (predicatesEqual : CSemEq (Γ := Γ) p q (.arr A .boolTy)) :
    CSemEq (Γ := Γ) (.eps A p) (.eps A q) A := by
  intro leftTyping rightTyping env bound typed valid expected
  cases leftRaw with
  | eps _ leftPredicate =>
    cases rightRaw with
    | eps _ rightPredicate =>
      let leftCheck : CDefChecks Γ (.eps A p) A :=
        .exact (.eps hA.certificate leftPredicate.certificate)
      let rightCheck : CDefChecks Γ (.eps A q) A :=
        .exact (.eps hA.certificate rightPredicate.certificate)
      rw [leftTyping.certificate.coherent leftCheck env bound expected,
        rightTyping.certificate.coherent rightCheck env bound expected]
      let carrier := denoteChecked hA env
      let predicateType : CPointed :=
        ⟨carrier.carrier → Bool, fun _ => false⟩
      have predicates := raw_semantics_of_eqTm leftPredicate rightPredicate
        predicatesEqual env bound typed valid predicateType
      have predicateValues := congrArg ULift.down predicates
      have predicateValues' :
          (cSem leftPredicate.certificate env bound
            ⟨(cSem hA.certificate env).carrier → Bool, fun _ => false⟩).down =
          (cSem rightPredicate.certificate env bound
            ⟨(cSem hA.certificate env).carrier → Bool, fun _ => false⟩).down := by
        simpa [predicateType, carrier, denoteChecked] using predicateValues
      dsimp [leftCheck, rightCheck, cDefSem, cSem]
      rw [predicateValues']

theorem classical_eqTm_abs
    (leftRaw : HasType Γ (.abs A p x) (.sub A p))
    (rightRaw : HasType Γ (.abs A p y) (.sub A p)) (hA : Kinded A)
    (hp : HasType (extendBound A emptyBound) p .boolTy)
    (valuesEqual : CSemEq (Γ := Γ) x y A) :
    CSemEq (Γ := Γ) (.abs A p x) (.abs A p y) (.sub A p) := by
  intro leftTyping rightTyping env bound typed valid expected
  cases leftRaw with
  | abs _ _ leftValue =>
    cases rightRaw with
    | abs _ _ rightValue =>
      let leftCheck : CDefChecks Γ (.abs A p x) (.sub A p) :=
        .exact (.abs hA.certificate hp.certificate leftValue.certificate)
      let rightCheck : CDefChecks Γ (.abs A p y) (.sub A p) :=
        .exact (.abs hA.certificate hp.certificate rightValue.certificate)
      rw [leftTyping.certificate.coherent leftCheck env bound expected,
        rightTyping.certificate.coherent rightCheck env bound expected]
      have values := raw_semantics_of_eqTm leftValue rightValue valuesEqual
        env bound typed valid (denoteChecked hA env)
      have valueContents := congrArg ULift.down values
      have valueContents' :
          (cSem leftValue.certificate env bound (cSem hA.certificate env)).down =
            (cSem rightValue.certificate env bound (cSem hA.certificate env)).down := by
        simpa [denoteChecked] using valueContents
      dsimp [leftCheck, rightCheck, cDefSem, cSem]
      rw [valueContents']

theorem classical_eqTm_rep
    (leftRaw : HasType Γ (.rep A p x) A) (rightRaw : HasType Γ (.rep A p y) A)
    (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy)
    (valuesEqual : CSemEq (Γ := Γ) x y (.sub A p)) :
    CSemEq (Γ := Γ) (.rep A p x) (.rep A p y) A := by
  intro leftTyping rightTyping env bound typed valid expected
  cases leftRaw with
  | rep _ _ leftValue =>
    cases rightRaw with
    | rep _ _ rightValue =>
      let leftCheck : CDefChecks Γ (.rep A p x) A :=
        .exact (.rep hA.certificate hp.certificate leftValue.certificate)
      let rightCheck : CDefChecks Γ (.rep A p y) A :=
        .exact (.rep hA.certificate hp.certificate rightValue.certificate)
      rw [leftTyping.certificate.coherent leftCheck env bound expected,
        rightTyping.certificate.coherent rightCheck env bound expected]
      let carrier := denoteChecked hA env
      let predicate := fun value =>
        (cSem hp.certificate env
          (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      have values := raw_semantics_of_eqTm leftValue rightValue valuesEqual
        env bound typed valid (cGuardedType carrier predicate)
      have valueContents := congrArg ULift.down values
      have valueContents' :
          (cSem leftValue.certificate env bound
            (cGuardedType (cSem hA.certificate env) (fun value =>
              (cSem hp.certificate env
                (extendCBoundEnv (cSem hA.certificate env) value emptyCBoundEnv)
                cBool).down))).down =
          (cSem rightValue.certificate env bound
            (cGuardedType (cSem hA.certificate env) (fun value =>
              (cSem hp.certificate env
                (extendCBoundEnv (cSem hA.certificate env) value emptyCBoundEnv)
                cBool).down))).down := by
        simpa [carrier, predicate, denoteChecked] using valueContents
      dsimp [leftCheck, rightCheck, cDefSem, cSem]
      rw [valueContents']

theorem classical_eqTm_tyExists
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {p q : Tm ClassicalSig (.star :: types) 0}
    (leftRaw : HasType Γ (.tyExists p) .boolTy)
    (rightRaw : HasType Γ (.tyExists q) .boolTy)
    (predicatesEqual : CSemEq
      (Γ := (emptyBound : BoundCtx ClassicalSig (.star :: types) 0))
      p q .boolTy) :
    CSemEq (Γ := Γ) (.tyExists p) (.tyExists q) .boolTy := by
  intro leftTyping rightTyping env bound typed valid expected
  cases leftRaw with
  | tyExists leftPredicate =>
    cases rightRaw with
    | tyExists rightPredicate =>
      let leftCheck : CDefChecks Γ (.tyExists p) .boolTy :=
        .exact (.tyExists leftPredicate.certificate)
      let rightCheck : CDefChecks Γ (.tyExists q) .boolTy :=
        .exact (.tyExists rightPredicate.certificate)
      rw [leftTyping.certificate.coherent leftCheck env bound expected,
        rightTyping.certificate.coherent rightCheck env bound expected]
      have predicateValues : ∀ candidate : CPointed,
          cSem leftPredicate.certificate
              (extendCTypeEnv (kind := .star) candidate env) emptyCBoundEnv cBool =
            cSem rightPredicate.certificate
              (extendCTypeEnv (kind := .star) candidate env) emptyCBoundEnv cBool := by
        intro candidate
        exact raw_semantics_of_eqTm leftPredicate rightPredicate predicatesEqual
          (extendCTypeEnv (kind := .star) candidate env) emptyCBoundEnv
          (fun index => Fin.elim0 index)
          (emptyCBoundEnv_valid (extendCTypeEnv (kind := .star) candidate env)) cBool
      have witnessesEqual :
          (∃ candidate : CPointed,
            cSem leftPredicate.certificate
                (extendCTypeEnv (kind := .star) candidate env) emptyCBoundEnv cBool =
              ⟨true⟩) =
          (∃ candidate : CPointed,
            cSem rightPredicate.certificate
                (extendCTypeEnv (kind := .star) candidate env) emptyCBoundEnv cBool =
              ⟨true⟩) := by
        apply propext
        constructor
        · rintro ⟨candidate, witness⟩
          exact ⟨candidate, (predicateValues candidate).symm.trans witness⟩
        · rintro ⟨candidate, witness⟩
          exact ⟨candidate, (predicateValues candidate).trans witness⟩
      dsimp [leftCheck, rightCheck, cDefSem, cSem]
      rw [witnessesEqual]

theorem classical_eqMp
    (hA : Kinded A) (conclusionTyping : HasTypeDefEq Γ (.app p y) .boolTy)
    (_hp : HasTypeDefEq Γ p (.arr A .boolTy))
    (_hx : HasTypeDefEq Γ x A) (_hy : HasTypeDefEq Γ y A)
    (_equalityTyping : HasTypeDefEq Γ (.eq A x y) .boolTy)
    (premiseTyping : HasTypeDefEq Γ (.app p x) .boolTy)
    (equality : CEntails (Γ := Γ) H (.eq A x y))
    (premise : CEntails (Γ := Γ) H (.app p x)) :
    CEntails (Γ := Γ) H (.app p y) := by
  intro env bound typed valid truths
  classical
  have eqRealizes : CRealizes (Γ := Γ) env bound (.eq A x y) .boolTy cBool true :=
    equality env bound typed valid truths
  obtain ⟨xChecking, yChecking, xy⟩ := eqRealizes.eq_true_elim hA
  have premiseTrue := entails_at_certificate premiseTyping premise env bound typed valid truths
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
  intro env bound typed valid truths
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
          have qTrue := right env bound typed valid (fun candidate member => by
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
          have qTrue := left env bound typed valid (fun candidate member => by
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
  intro env bound typed valid truths
  classical
  have premiseTrue := entails_at_certificate premiseTyping premise env bound typed valid truths
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
