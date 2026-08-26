import Nucleus.HolE.ClassicalBoundTransport
import Nucleus.HolE.ClassicalCoreKernelLaws

/-! # Classical kernel laws for bound-variable transport -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem classical_weakenBound
    {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {K : List (Tm ClassicalSig types (depth + 1))}
    {p : Tm ClassicalSig types depth}
    (typedH : TypedHyps Γ H) (_hA : Kinded A)
    (conclusionTyping : HasTypeDefEq (extendBound A Γ) (weaken p) .boolTy)
    (embedding : ∀ q, q ∈ H → weaken q ∈ K)
    (premise : CEntails (Γ := Γ) H p) :
    CEntails (Γ := extendBound A Γ) K (weaken p) := by
  intro env bound typedK validK truthsK
  let typedContext : TypedCtx Γ := fun i => typedK i.succ
  have validTail : CBoundValid typedContext env (bound.rename Fin.succ) := by
    intro i expected
    have valid := validK i.succ expected
    have proofEq : typedK i.succ = typedContext i := Subsingleton.elim _ _
    rw [proofEq] at valid
    exact valid
  have truthsH : CHypsTrue (Γ := Γ) env (bound.rename Fin.succ) H := by
    intro q member
    exact (truthsK (weaken q) (embedding q member)).of_weakenAt (typedH q member)
  obtain ⟨source, sourceTrue⟩ := premise env (bound.rename Fin.succ)
    typedContext validTail truthsH
  let target := conclusionTyping.certificate
  refine ⟨target, ?_⟩
  exact (cDefSem_weaken source target env bound cBool).trans sourceTrue

theorem classical_abs
    {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A B : Ty ClassicalSig types}
    {left right : Tm ClassicalSig types (depth + 1)}
    (typed : TypedHyps Γ H) (hA : Kinded A) (hB : Kinded B)
    (conclusionTyping : HasTypeDefEq Γ
      (.eq (.arr A B) (.lam A left) (.lam A right)) .boolTy)
    (_leftTyping : HasTypeDefEq (extendBound A Γ) left B)
    (_rightTyping : HasTypeDefEq (extendBound A Γ) right B)
    (premise : CEntails (Γ := extendBound A Γ) (H.map weaken)
      (.eq B left right)) :
    CEntails (Γ := Γ) H (.eq (.arr A B) (.lam A left) (.lam A right)) := by
  intro env bound typedContext valid truthsH
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cArr leftChecking rightChecking =>
      cases leftChecking with
      | lam leftBody cA cCodomain leftBodyChecking =>
        cases rightChecking with
        | lam rightBody rightA rightCodomain rightBodyChecking =>
          rw [cA.unique hA.certificate, cCodomain.unique hB.certificate,
            rightA.unique hA.certificate, rightCodomain.unique hB.certificate,
            cArr.unique (.arr hA.certificate hB.certificate)]
          have functionsEqual :
              (cSem (CChecks.lam left hA.certificate hB.certificate leftBodyChecking)
                env bound (cSem (.arr hA.certificate hB.certificate) env)).down =
              (cSem (CChecks.lam right hA.certificate hB.certificate rightBodyChecking)
                env bound (cSem (.arr hA.certificate hB.certificate) env)).down := by
            simp only [cSem]
            rw [alignCValue_self, alignCValue_self]
            funext argument
            have mappedTrue : CHypsTrue (Γ := extendBound A Γ) env
                (extendCBoundEnv (denoteChecked hA env) argument bound)
                (H.map weaken) := by
              intro q member
              obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
              exact (truthsH source sourceMember).weaken
                (denoteChecked hA env) argument (typed source sourceMember)
            obtain ⟨pointwiseChecking, pointwiseTrue⟩ := premise env
              (extendCBoundEnv (denoteChecked hA env) argument bound)
              (typedContext.extend hA)
              (extendCBoundEnv_valid hA typedContext env bound valid argument) mappedTrue
            let realizes : CRealizes (Γ := extendBound A Γ) env
                (extendCBoundEnv (denoteChecked hA env) argument bound)
                (.eq B left right) .boolTy cBool true :=
              ⟨pointwiseChecking, pointwiseTrue⟩
            obtain ⟨leftPoint, rightPoint, pointwiseEqual⟩ :=
              realizes.eq_true_elim hB
            have leftCoherent := (CDefChecks.exact leftBodyChecking).coherent
              (CDefChecks.exact leftPoint) env
              (extendCBoundEnv (denoteChecked hA env) argument bound)
              (denoteChecked hB env)
            have rightCoherent := (CDefChecks.exact rightBodyChecking).coherent
              (CDefChecks.exact rightPoint) env
              (extendCBoundEnv (denoteChecked hA env) argument bound)
              (denoteChecked hB env)
            exact congrArg ULift.down
              (leftCoherent.trans (pointwiseEqual.trans rightCoherent.symm))
          change ULift.up (alignCValue cBool cBool (decide (_ = _))) = ULift.up true
          rw [functionsEqual]
          simp only [decide_true]
          exact congrArg ULift.up (alignCValue_self cBool true)

theorem classical_generalize
    {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {body : Tm ClassicalSig types (depth + 1)}
    (typed : TypedHyps Γ H) (hA : Kinded A)
    (conclusionTyping : HasTypeDefEq Γ
      (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true))) .boolTy)
    (_bodyTyping : HasTypeDefEq (extendBound A Γ) body .boolTy)
    (premise : CEntails (Γ := extendBound A Γ) (H.map weaken) body) :
    CEntails (Γ := Γ) H
      (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true))) := by
  intro env bound typedContext valid truthsH
  classical
  refine ⟨conclusionTyping.certificate, ?_⟩
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cArr left right =>
      cases left with
      | lam leftBody cA cCodomain leftBodyCheck =>
        cases right with
        | lam rightBody rightA rightBool rightBodyCheck =>
          rw [cA.unique hA.certificate, cCodomain.unique .boolTy,
            rightA.unique hA.certificate, rightBool.unique .boolTy,
            cArr.unique (.arr hA.certificate .boolTy),
            rightBodyCheck.unique (.bool true)]
          have functionsEqual :
              (cSem (CChecks.lam body hA.certificate .boolTy leftBodyCheck)
                env bound (cSem (.arr hA.certificate .boolTy) env)).down =
              (cSem (CChecks.lam (Γ := Γ) (.bool true) hA.certificate .boolTy
                (CChecks.bool (Γ := extendBound A Γ) true))
                env bound (cSem (.arr hA.certificate .boolTy) env)).down := by
            simp only [cSem]
            rw [alignCValue_self, alignCValue_self]
            funext argument
            have mappedTrue : CHypsTrue (Γ := extendBound A Γ) env
                (extendCBoundEnv (denoteChecked hA env) argument bound)
                (H.map weaken) := by
              intro q member
              obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
              exact (truthsH source sourceMember).weaken
                (denoteChecked hA env) argument (typed source sourceMember)
            obtain ⟨bodyChecking, bodyTrue⟩ := premise env
              (extendCBoundEnv (denoteChecked hA env) argument bound)
              (typedContext.extend hA)
              (extendCBoundEnv_valid hA typedContext env bound valid argument) mappedTrue
            have bodyTrue' :=
              ((CDefChecks.exact leftBodyCheck).coherent bodyChecking env
                (extendCBoundEnv (denoteChecked hA env) argument bound) cBool).trans
                bodyTrue
            have down := congrArg ULift.down bodyTrue'
            change (cSem leftBodyCheck env
              (extendCBoundEnv (cSem hA.certificate env) argument bound) cBool).down = true
              at down
            exact down.trans (alignCValue_self cBool true).symm
          change ULift.up (alignCValue cBool cBool (decide (_ = _))) = ULift.up true
          rw [functionsEqual]
          simp only [decide_true]
          exact congrArg ULift.up (alignCValue_self cBool true)

end Nucleus.HolE
