import Nucleus.HolE.ClassicalIntrinsicRealization
import Nucleus.HolE.EmptySemantics

/-! # Deterministic semantics of the equality-defined Boolean connectives -/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

variable {types : List Kind} {depth : Nat} {Γ : Ctx types depth}

theorem not_value_iff (proposition : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (value result : Bool)
    (evaluation : Eval proposition env bound cBool value) :
    Eval (Empty.not proposition) env bound cBool result ↔ result = !value := by
  let computed := Nucleus.HolE.Empty.Eval.not_value proposition env bound value evaluation
  constructor
  · intro actual
    exact actual.value_unique computed
  · intro equal
    rw [equal]
    exact computed

theorem and_value_iff (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue result : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.and left right) env bound cBool result ↔
      result = (leftValue && rightValue) := by
  let computed := Nucleus.HolE.Empty.Eval.and_value left right env bound leftValue rightValue
    leftEval rightEval
  constructor
  · intro actual
    exact actual.value_unique computed
  · intro equal
    rw [equal]
    exact computed

theorem or_value_iff (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue result : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.or left right) env bound cBool result ↔
      result = (leftValue || rightValue) := by
  let computed := Nucleus.HolE.Empty.Eval.or_value left right env bound leftValue rightValue
    leftEval rightEval
  constructor
  · intro actual
    exact actual.value_unique computed
  · intro equal
    rw [equal]
    exact computed

theorem imp_value_iff (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue result : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.imp left right) env bound cBool result ↔
      result = ((!leftValue) || rightValue) := by
  let computed := Nucleus.HolE.Empty.Eval.imp_value left right env bound leftValue rightValue
    leftEval rightEval
  constructor
  · intro actual
    exact actual.value_unique computed
  · intro equal
    rw [equal]
    exact computed

/-- Truth of conjunction is conjunction of truth, independently of the
particular proof-relevant checking certificates used by its operands. -/
theorem and_true_iff (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    Eval (Empty.and left right) env bound cBool true ↔
      Eval left env bound cBool true ∧ Eval right env bound cBool true := by
  let leftValue := Infinity.iValue left.toIntrinsic env bound cBool
  let rightValue := Infinity.iValue right.toIntrinsic env bound cBool
  change Bool at leftValue rightValue
  have leftEval : Eval left env bound cBool leftValue := Eval.canonical left env bound cBool
  have rightEval : Eval right env bound cBool rightValue := Eval.canonical right env bound cBool
  rw [and_value_iff left right env bound leftValue rightValue true leftEval rightEval]
  constructor
  · intro computed
    have computed' := computed.symm
    rw [Bool.and_eq_true] at computed'
    have leftTrue : leftValue = true := computed'.1
    have rightTrue : rightValue = true := computed'.2
    exact ⟨leftTrue ▸ leftEval, rightTrue ▸ rightEval⟩
  · rintro ⟨leftTrue, rightTrue⟩
    have leftEqual : leftValue = true := leftEval.value_unique leftTrue
    have rightEqual : rightValue = true := rightEval.value_unique rightTrue
    symm
    rw [Bool.and_eq_true]
    exact ⟨leftEqual, rightEqual⟩

/-- Material implication is true exactly when truth of its antecedent implies
truth of its consequent. -/
theorem imp_true_iff (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    Eval (Empty.imp left right) env bound cBool true ↔
      (Eval left env bound cBool true → Eval right env bound cBool true) := by
  let leftValue := Infinity.iValue left.toIntrinsic env bound cBool
  let rightValue := Infinity.iValue right.toIntrinsic env bound cBool
  change Bool at leftValue rightValue
  have leftEval : Eval left env bound cBool leftValue := Eval.canonical left env bound cBool
  have rightEval : Eval right env bound cBool rightValue := Eval.canonical right env bound cBool
  rw [imp_value_iff left right env bound leftValue rightValue true leftEval rightEval]
  constructor
  · intro computed leftTrue
    have leftEqual : leftValue = true := leftEval.value_unique leftTrue
    have rightEqual : rightValue = true := by
      have computed' := computed.symm
      rw [leftEqual] at computed'
      simpa using computed'
    exact rightEqual ▸ rightEval
  · intro implication
    cases leftCase : leftValue
    · symm
      rfl
    · have leftTrue : Eval left env bound cBool true := leftCase ▸ leftEval
      have rightTrue := implication leftTrue
      have rightEqual : rightValue = true := rightEval.value_unique rightTrue
      symm
      rw [rightEqual]
      rfl

end Nucleus.HolE.Empty
