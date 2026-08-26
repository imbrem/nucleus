import Nucleus.HolE.ClassicalEmptyConnectiveRealization
import Nucleus.HolE.ClassicalUniversalRealization

/-! # Checked HOL statements of the Peano laws -/

namespace Nucleus.HolE.Empty.NaturalLaw

open Nucleus.HolE
open Nucleus.HolE.Empty

set_option relaxedAutoImplicit true

/-- Canonical checked statement that successor is injective. -/
def successorInjective (A : Empty.Ty types)
    (successor : Empty.Term Empty.Ctx.empty (A.arr A)) :
    Empty.BoolTm (types := types) Empty.Ctx.empty := by
  let xContext := Empty.Ctx.empty.extend A
  let x : Empty.Term xContext A := Empty.Term.bv xContext 0
  let xyContext := xContext.extend A
  let y : Empty.Term xyContext A := Empty.Term.bv xyContext 0
  let premise := Empty.Term.eq A
    (Empty.Term.app ((successor.weaken A).weaken A) (x.weaken A))
    (Empty.Term.app ((successor.weaken A).weaken A) y)
  let conclusion := Empty.Term.eq A (x.weaken A) y
  exact Empty.forallTm A (Empty.forallTm A (Empty.imp premise conclusion))

/-- Canonical checked statement that zero is outside successor's image. -/
def zeroNeSuccessor (A : Empty.Ty types)
    (zero : Empty.Term Empty.Ctx.empty A)
    (successor : Empty.Term Empty.Ctx.empty (A.arr A)) :
    Empty.BoolTm (types := types) Empty.Ctx.empty := by
  let context := Empty.Ctx.empty.extend A
  let x : Empty.Term context A := Empty.Term.bv context 0
  let successorX := Empty.Term.app (successor.weaken A) x
  exact Empty.forallTm A (Empty.not (Empty.Term.eq A (zero.weaken A) successorX))

/-- Canonical checked Boolean induction principle. -/
def induction (A : Empty.Ty types)
    (zero : Empty.Term Empty.Ctx.empty A)
    (successor : Empty.Term Empty.Ctx.empty (A.arr A)) :
    Empty.BoolTm (types := types) Empty.Ctx.empty := by
  let predicateType := A.arr Empty.FamK.boolTy
  let predicateContext := Empty.Ctx.empty.extend predicateType
  let predicate : Empty.Term predicateContext predicateType :=
    Empty.Term.bv predicateContext 0
  let base := Empty.Term.app predicate (zero.weaken predicateType)
  let stepContext := predicateContext.extend A
  let stepPredicate := predicate.weaken A
  let x : Empty.Term stepContext A := Empty.Term.bv stepContext 0
  let successorX := Empty.Term.app
    ((successor.weaken predicateType).weaken A) x
  let step := Empty.forallTm A (Empty.imp
    (Empty.Term.app stepPredicate x)
    (Empty.Term.app stepPredicate successorX))
  let premise := Empty.and base step
  let conclusion := Empty.forallTm A
    (Empty.Term.app (predicate.weaken A)
      (Empty.Term.bv (predicateContext.extend A) 0))
  exact Empty.forallTm predicateType (Empty.imp premise conclusion)

/-- Successor injectivity has exactly its expected semantic meaning. -/
theorem successorInjective_true_iff
    (A : Empty.Ty types) (successor : Empty.Term Empty.Ctx.empty (A.arr A))
    (env : CTypeEnv types)
    (successorValue : (A.denote env).carrier → (A.denote env).carrier)
    (successorEval : Empty.Eval successor env emptyCBoundEnv
      (Empty.cArrow (A.denote env) (A.denote env)) successorValue) :
    Empty.Eval (successorInjective A successor) env emptyCBoundEnv cBool true ↔
      Function.Injective successorValue := by
  rw [successorInjective]
  rw [Empty.Eval.forallTm_true_iff]
  constructor
  · intro every x y equal
    have body := (Empty.Eval.forallTm_true_iff A _ env
      (extendCBoundEnv (A.denote env) x emptyCBoundEnv)).mp (every x) y
    let xBound := extendCBoundEnv (A.denote env) x emptyCBoundEnv
    let xyBound := extendCBoundEnv (A.denote env) y xBound
    have xEval : Empty.Eval
        ((Empty.Term.bv (Empty.Ctx.empty.extend A) 0).weaken A)
        env xyBound (A.denote env) x := by
      apply Empty.Eval.weaken
      apply Empty.Eval.bv
      dsimp [xBound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have yEval : Empty.Eval
        (Empty.Term.bv ((Empty.Ctx.empty.extend A).extend A) 0)
        env xyBound (A.denote env) y := by
      apply Empty.Eval.bv
      dsimp [xyBound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have successorXY : Empty.Eval ((successor.weaken A).weaken A) env xyBound
        (Empty.cArrow (A.denote env) (A.denote env)) successorValue :=
      Empty.Eval.weaken _ A env xBound y _ _
        (Empty.Eval.weaken successor A env emptyCBoundEnv x _ _ successorEval)
    have sxEval := Empty.Eval.app ((successor.weaken A).weaken A)
      ((Empty.Term.bv (Empty.Ctx.empty.extend A) 0).weaken A)
      env xyBound successorValue x successorXY xEval
    have syEval := Empty.Eval.app ((successor.weaken A).weaken A)
      (Empty.Term.bv ((Empty.Ctx.empty.extend A).extend A) 0)
      env xyBound successorValue y successorXY yEval
    have premiseEval := Empty.Eval.eq A _ _ env xyBound
      (successorValue x) (successorValue y) sxEval syEval
    have conclusionEval := Empty.Eval.eq A _ _ env xyBound x y xEval yEval
    have decoded := (Empty.imp_value_iff _ _ env xyBound
      (Infinity.classicalEqBool (successorValue x) (successorValue y))
      (Infinity.classicalEqBool x y) true premiseEval conclusionEval).mp body
    simpa [Infinity.classicalEqBool, equal] using decoded
  · intro injective x
    rw [Empty.Eval.forallTm_true_iff]
    intro y
    let xBound := extendCBoundEnv (A.denote env) x emptyCBoundEnv
    let xyBound := extendCBoundEnv (A.denote env) y xBound
    have xEval : Empty.Eval
        ((Empty.Term.bv (Empty.Ctx.empty.extend A) 0).weaken A)
        env xyBound (A.denote env) x := by
      apply Empty.Eval.weaken
      apply Empty.Eval.bv
      dsimp [xBound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have yEval : Empty.Eval
        (Empty.Term.bv ((Empty.Ctx.empty.extend A).extend A) 0)
        env xyBound (A.denote env) y := by
      apply Empty.Eval.bv
      dsimp [xyBound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have successorXY : Empty.Eval ((successor.weaken A).weaken A) env xyBound
        (Empty.cArrow (A.denote env) (A.denote env)) successorValue :=
      Empty.Eval.weaken _ A env xBound y _ _
        (Empty.Eval.weaken successor A env emptyCBoundEnv x _ _ successorEval)
    have sxEval := Empty.Eval.app ((successor.weaken A).weaken A)
      ((Empty.Term.bv (Empty.Ctx.empty.extend A) 0).weaken A)
      env xyBound successorValue x successorXY xEval
    have syEval := Empty.Eval.app ((successor.weaken A).weaken A)
      (Empty.Term.bv ((Empty.Ctx.empty.extend A).extend A) 0)
      env xyBound successorValue y successorXY yEval
    have premiseEval := Empty.Eval.eq A _ _ env xyBound
      (successorValue x) (successorValue y) sxEval syEval
    have conclusionEval := Empty.Eval.eq A _ _ env xyBound x y xEval yEval
    apply (Empty.imp_value_iff _ _ env xyBound
      (Infinity.classicalEqBool (successorValue x) (successorValue y))
      (Infinity.classicalEqBool x y) true premiseEval conclusionEval).mpr
    simp only [Infinity.classicalEqBool]
    by_cases equal : successorValue x = successorValue y
    · simp [injective equal]
    · simp [equal]

/-- Zero/successor separation has exactly its expected semantic meaning. -/
theorem zeroNeSuccessor_true_iff
    (A : Empty.Ty types) (zero : Empty.Term Empty.Ctx.empty A)
    (successor : Empty.Term Empty.Ctx.empty (A.arr A))
    (env : CTypeEnv types) (zeroValue : (A.denote env).carrier)
    (successorValue : (A.denote env).carrier → (A.denote env).carrier)
    (zeroEval : Empty.Eval zero env emptyCBoundEnv (A.denote env) zeroValue)
    (successorEval : Empty.Eval successor env emptyCBoundEnv
      (Empty.cArrow (A.denote env) (A.denote env)) successorValue) :
    Empty.Eval (zeroNeSuccessor A zero successor) env emptyCBoundEnv cBool true ↔
      ∀ x, zeroValue ≠ successorValue x := by
  rw [zeroNeSuccessor, Empty.Eval.forallTm_true_iff]
  constructor
  · intro every x equal
    let bound := extendCBoundEnv (A.denote env) x emptyCBoundEnv
    have zeroBound : Empty.Eval (zero.weaken A) env bound
        (A.denote env) zeroValue :=
      Empty.Eval.weaken zero A env emptyCBoundEnv x _ _ zeroEval
    have successorBound : Empty.Eval (successor.weaken A) env bound
        (Empty.cArrow (A.denote env) (A.denote env)) successorValue :=
      Empty.Eval.weaken successor A env emptyCBoundEnv x _ _ successorEval
    have xEval : Empty.Eval (Empty.Term.bv (Empty.Ctx.empty.extend A) 0)
        env bound (A.denote env) x := by
      apply Empty.Eval.bv
      dsimp [bound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have sxEval := Empty.Eval.app (successor.weaken A)
      (Empty.Term.bv (Empty.Ctx.empty.extend A) 0) env bound
      successorValue x successorBound xEval
    have equalityEval := Empty.Eval.eq A _ _ env bound zeroValue
      (successorValue x) zeroBound sxEval
    have decoded := (Empty.not_value_iff _ env bound
      (Infinity.classicalEqBool zeroValue (successorValue x)) true
      equalityEval).mp (every x)
    simp [Infinity.classicalEqBool, equal] at decoded
  · intro separated x
    let bound := extendCBoundEnv (A.denote env) x emptyCBoundEnv
    have zeroBound : Empty.Eval (zero.weaken A) env bound
        (A.denote env) zeroValue :=
      Empty.Eval.weaken zero A env emptyCBoundEnv x _ _ zeroEval
    have successorBound : Empty.Eval (successor.weaken A) env bound
        (Empty.cArrow (A.denote env) (A.denote env)) successorValue :=
      Empty.Eval.weaken successor A env emptyCBoundEnv x _ _ successorEval
    have xEval : Empty.Eval (Empty.Term.bv (Empty.Ctx.empty.extend A) 0)
        env bound (A.denote env) x := by
      apply Empty.Eval.bv
      dsimp [bound]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have sxEval := Empty.Eval.app (successor.weaken A)
      (Empty.Term.bv (Empty.Ctx.empty.extend A) 0) env bound
      successorValue x successorBound xEval
    have equalityEval := Empty.Eval.eq A _ _ env bound zeroValue
      (successorValue x) zeroBound sxEval
    apply (Empty.not_value_iff _ env bound
      (Infinity.classicalEqBool zeroValue (successorValue x)) true
      equalityEval).mpr
    simp [Infinity.classicalEqBool, separated x]

/-- Boolean induction has exactly the semantic law consumed by `CNatDecl`. -/
theorem induction_true_iff
    (A : Empty.Ty types) (zero : Empty.Term Empty.Ctx.empty A)
    (successor : Empty.Term Empty.Ctx.empty (A.arr A))
    (env : CTypeEnv types) (zeroValue : (A.denote env).carrier)
    (successorValue : (A.denote env).carrier → (A.denote env).carrier)
    (zeroEval : Empty.Eval zero env emptyCBoundEnv (A.denote env) zeroValue)
    (successorEval : Empty.Eval successor env emptyCBoundEnv
      (Empty.cArrow (A.denote env) (A.denote env)) successorValue) :
    Empty.Eval (induction A zero successor) env emptyCBoundEnv cBool true ↔
      ∀ P : (A.denote env).carrier → Bool,
        P zeroValue = true →
        (∀ x, P x = true → P (successorValue x) = true) →
      ∀ x, P x = true := by
  have boolDenote : Empty.FamK.boolTy.denote env = cBool := by
    unfold Empty.FamK.denote
    rw [cSem_certificate_coherent Empty.FamK.boolTy.kinded.certificate
      CChecks.boolTy env]
    rfl
  rw [induction, Empty.Eval.forallTm_true_iff, Empty.FamK.denote_arr]
  rw [boolDenote]
  change (∀ P : (A.denote env).carrier → Bool, _) ↔ _
  constructor
  · intro every P base step x
    change (Empty.cArrow (A.denote env) cBool).carrier at P
    let predicateType := A.arr Empty.FamK.boolTy
    let predicateContext := Empty.Ctx.empty.extend predicateType
    let boundP := extendCBoundEnv
      (Empty.cArrow (A.denote env) cBool) P emptyCBoundEnv
    have predicateEval : Empty.Eval (Empty.Term.bv predicateContext 0)
        env boundP (Empty.cArrow (A.denote env) cBool) P := by
      apply Empty.Eval.bv
      dsimp [boundP]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have zeroBound : Empty.Eval (zero.weaken predicateType) env boundP
        (A.denote env) zeroValue := by
      exact Empty.Eval.weakenAt zero predicateType env emptyCBoundEnv
        (Empty.cArrow (A.denote env) cBool) P (A.denote env) zeroValue zeroEval
    have baseEval : Empty.Eval
        (Empty.Term.app (Empty.Term.bv predicateContext 0)
          (zero.weaken predicateType)) env boundP cBool (P zeroValue) :=
      Empty.Eval.appBool _ _ env boundP P zeroValue predicateEval zeroBound
    have stepEval : Empty.Eval
        (Empty.forallTm A (Empty.imp
          (Empty.Term.app ((Empty.Term.bv predicateContext 0).weaken A)
            (Empty.Term.bv (predicateContext.extend A) 0))
          (Empty.Term.app ((Empty.Term.bv predicateContext 0).weaken A)
            (Empty.Term.app ((successor.weaken predicateType).weaken A)
              (Empty.Term.bv (predicateContext.extend A) 0)))))
        env boundP cBool true := by
      apply (Empty.Eval.forallTm_true_iff A _ env boundP).mpr
      intro n
      apply (Empty.imp_true_iff _ _ env _).mpr
      intro pnTrue
      let boundPN := extendCBoundEnv (A.denote env) n boundP
      have predicateN : Empty.Eval
          ((Empty.Term.bv predicateContext 0).weaken A) env boundPN
          (Empty.cArrow (A.denote env) cBool) P :=
        Empty.Eval.weaken _ A env boundP n _ _ predicateEval
      have nEval : Empty.Eval (Empty.Term.bv (predicateContext.extend A) 0)
          env boundPN (A.denote env) n := by
        apply Empty.Eval.bv
        dsimp [boundPN]
        rw [extendCBoundEnv_zero, alignCValue_self]
      have successorP : Empty.Eval (successor.weaken predicateType) env boundP
          (Empty.cArrow (A.denote env) (A.denote env)) successorValue := by
        exact Empty.Eval.weakenAt successor predicateType env emptyCBoundEnv
          (Empty.cArrow (A.denote env) cBool) P _ _ successorEval
      have successorPN : Empty.Eval ((successor.weaken predicateType).weaken A)
          env boundPN (Empty.cArrow (A.denote env) (A.denote env))
          successorValue :=
        Empty.Eval.weaken _ A env boundP n _ _ successorP
      have successorNEval := Empty.Eval.app
        ((successor.weaken predicateType).weaken A)
        (Empty.Term.bv (predicateContext.extend A) 0) env boundPN
        successorValue n successorPN nEval
      have pnEval := Empty.Eval.appBool
        ((Empty.Term.bv predicateContext 0).weaken A)
        (Empty.Term.bv (predicateContext.extend A) 0) env boundPN
        P n predicateN nEval
      have psnEval := Empty.Eval.appBool
        ((Empty.Term.bv predicateContext 0).weaken A)
        (Empty.Term.app ((successor.weaken predicateType).weaken A)
          (Empty.Term.bv (predicateContext.extend A) 0)) env boundPN
        P (successorValue n) predicateN successorNEval
      have pn : P n = true := pnEval.value_unique pnTrue
      have psn : P (successorValue n) = true := step n pn
      exact psn ▸ psnEval
    have baseEvalTrue : Empty.Eval
        (Empty.Term.app (Empty.Term.bv predicateContext 0)
          (zero.weaken predicateType)) env boundP cBool true :=
      base ▸ baseEval
    have premiseEval := Empty.Eval.and_of_true _ _ env boundP baseEvalTrue stepEval
    have body := every P
    rw [Empty.imp_true_iff] at body
    have conclusion := body premiseEval
    have all := (Empty.Eval.forallTm_true_iff A _ env boundP).mp conclusion
    have px := all x
    let boundPX := extendCBoundEnv (A.denote env) x boundP
    have predicateX : Empty.Eval
        ((Empty.Term.bv predicateContext 0).weaken A) env boundPX
        (Empty.cArrow (A.denote env) cBool) P :=
      Empty.Eval.weaken _ A env boundP x _ _ predicateEval
    have xEval : Empty.Eval (Empty.Term.bv (predicateContext.extend A) 0)
        env boundPX (A.denote env) x := by
      apply Empty.Eval.bv
      dsimp [boundPX]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have pxEval := Empty.Eval.appBool
      ((Empty.Term.bv predicateContext 0).weaken A)
      (Empty.Term.bv (predicateContext.extend A) 0) env boundPX
      P x predicateX xEval
    exact pxEval.value_unique px
  · intro principle P
    change (Empty.cArrow (A.denote env) cBool).carrier at P
    let predicateType := A.arr Empty.FamK.boolTy
    let predicateContext := Empty.Ctx.empty.extend predicateType
    let boundP := extendCBoundEnv
      (Empty.cArrow (A.denote env) cBool) P emptyCBoundEnv
    have predicateEval : Empty.Eval (Empty.Term.bv predicateContext 0)
        env boundP (Empty.cArrow (A.denote env) cBool) P := by
      apply Empty.Eval.bv
      dsimp [boundP]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have zeroBound : Empty.Eval (zero.weaken predicateType) env boundP
        (A.denote env) zeroValue :=
      Empty.Eval.weakenAt zero predicateType env emptyCBoundEnv
        (Empty.cArrow (A.denote env) cBool) P (A.denote env) zeroValue zeroEval
    have baseEval : Empty.Eval
        (Empty.Term.app (Empty.Term.bv predicateContext 0)
          (zero.weaken predicateType)) env boundP cBool (P zeroValue) :=
      Empty.Eval.appBool _ _ env boundP P zeroValue predicateEval zeroBound
    apply (Empty.imp_true_iff _ _ env boundP).mpr
    intro premise
    have components := (Empty.and_true_iff _ _ env boundP).mp premise
    have base : P zeroValue = true := baseEval.value_unique components.1
    have step : ∀ n, P n = true → P (successorValue n) = true := by
      have everyStep := (Empty.Eval.forallTm_true_iff A _ env boundP).mp components.2
      intro n pn
      let boundPN := extendCBoundEnv (A.denote env) n boundP
      have predicateN : Empty.Eval
          ((Empty.Term.bv predicateContext 0).weaken A) env boundPN
          (Empty.cArrow (A.denote env) cBool) P :=
        Empty.Eval.weaken _ A env boundP n _ _ predicateEval
      have nEval : Empty.Eval (Empty.Term.bv (predicateContext.extend A) 0)
          env boundPN (A.denote env) n := by
        apply Empty.Eval.bv
        dsimp [boundPN]
        rw [extendCBoundEnv_zero, alignCValue_self]
      have successorP : Empty.Eval (successor.weaken predicateType) env boundP
          (Empty.cArrow (A.denote env) (A.denote env)) successorValue :=
        Empty.Eval.weakenAt successor predicateType env emptyCBoundEnv
          (Empty.cArrow (A.denote env) cBool) P _ _ successorEval
      have successorPN : Empty.Eval ((successor.weaken predicateType).weaken A)
          env boundPN (Empty.cArrow (A.denote env) (A.denote env))
          successorValue :=
        Empty.Eval.weaken _ A env boundP n _ _ successorP
      have successorNEval := Empty.Eval.app
        ((successor.weaken predicateType).weaken A)
        (Empty.Term.bv (predicateContext.extend A) 0) env boundPN
        successorValue n successorPN nEval
      have pnEval := Empty.Eval.appBool
        ((Empty.Term.bv predicateContext 0).weaken A)
        (Empty.Term.bv (predicateContext.extend A) 0) env boundPN
        P n predicateN nEval
      have psnEval := Empty.Eval.appBool
        ((Empty.Term.bv predicateContext 0).weaken A)
        (Empty.Term.app ((successor.weaken predicateType).weaken A)
          (Empty.Term.bv (predicateContext.extend A) 0)) env boundPN
        P (successorValue n) predicateN successorNEval
      have implication := (Empty.imp_true_iff _ _ env boundPN).mp (everyStep n)
      have pnTrue : Empty.Eval
          (Empty.Term.app ((Empty.Term.bv predicateContext 0).weaken A)
            (Empty.Term.bv (predicateContext.extend A) 0))
          env boundPN cBool true := pn ▸ pnEval
      exact psnEval.value_unique (implication pnTrue)
    have all := principle P base step
    apply (Empty.Eval.forallTm_true_iff A _ env boundP).mpr
    intro x
    let boundPX := extendCBoundEnv (A.denote env) x boundP
    have predicateX : Empty.Eval
        ((Empty.Term.bv predicateContext 0).weaken A) env boundPX
        (Empty.cArrow (A.denote env) cBool) P :=
      Empty.Eval.weaken _ A env boundP x _ _ predicateEval
    have xEval : Empty.Eval (Empty.Term.bv (predicateContext.extend A) 0)
        env boundPX (A.denote env) x := by
      apply Empty.Eval.bv
      dsimp [boundPX]
      rw [extendCBoundEnv_zero, alignCValue_self]
    have pxEval := Empty.Eval.appBool
      ((Empty.Term.bv predicateContext 0).weaken A)
      (Empty.Term.bv (predicateContext.extend A) 0) env boundPX
      P x predicateX xEval
    exact (all x) ▸ pxEval

end Nucleus.HolE.Empty.NaturalLaw
