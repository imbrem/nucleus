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

end Nucleus.HolE.Empty
