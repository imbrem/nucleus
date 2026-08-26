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

end Nucleus.HolE.Empty.NaturalLaw
