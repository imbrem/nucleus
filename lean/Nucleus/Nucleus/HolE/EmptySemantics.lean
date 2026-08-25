import Nucleus.HolE.ClassicalInfinitySoundness
import Nucleus.HolE.EmptyLogic

/-!
# Classical semantics for checked empty-signature terms

This is a thin bridge from the reusable checked syntax API to the
proof-relevant evaluator originally developed for the infinity sentence.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

noncomputable section

/-- Forget the checked API wrapper while retaining its intrinsic typing. -/
def Term.toIntrinsic {types : List Kind} {depth : Nat}
    {Γ : Ctx types depth} {A : Ty types} (term : Term Γ A) :
    InfinityTm ClassicalSig Γ.raw A.raw :=
  ⟨term.raw, term.typing⟩

/-- Denotation of a checked ordinary type in the deterministic model. -/
noncomputable abbrev FamK.denote {types : List Kind} (type : Ty types)
    (env : CTypeEnv types) : CPointed :=
  cSem type.kinded.certificate env

/-- Pointed function space used by the checked semantic API. -/
abbrev cArrow (domain codomain : CPointed) : CPointed :=
  ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩

theorem FamK.denote_arr (domain codomain : Ty types) (env : CTypeEnv types) :
    (domain.arr codomain).denote env =
      cArrow (domain.denote env) (codomain.denote env) := by
  unfold FamK.denote
  rw [cSem_certificate_coherent
    (domain.arr codomain).kinded.certificate
    (CChecks.arr domain.kinded.certificate codomain.kinded.certificate) env]
  rfl

/-- Evaluation of a checked term at an explicitly supplied semantic value. -/
def Eval {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    {A : Ty types} (term : Term Γ A) (env : CTypeEnv types)
    (bound : CBoundEnv depth)
    (expected : CPointed) (value : expected.carrier) : Prop :=
  Infinity.IEval term.toIntrinsic env bound expected value

@[simp] theorem Term.toIntrinsic_weaken
    {types : List Kind} {depth : Nat} {Γ : Ctx types depth} {A : Ty types}
    (term : Term Γ A) (C : Ty types) :
    (term.weaken C).toIntrinsic = term.toIntrinsic.weaken := by
  unfold Term.weaken Ctx.extend Term.toIntrinsic InfinityTm.weaken
  congr

@[simp] theorem Term.toIntrinsic_forallTm
    {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) :
    (Empty.forallTm A body).toIntrinsic =
      InfinityTm.forallTm A.kinded body.toIntrinsic := by
  rw [InfinityTm.mk.injEq]
  rfl

@[simp] theorem Term.toIntrinsic_existsTm
    {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) :
    (Empty.existsTm A body).toIntrinsic =
      InfinityTm.existsTm A.kinded body.toIntrinsic := by
  rw [InfinityTm.mk.injEq]
  rfl

@[simp] theorem Term.toIntrinsic_not
    {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (proposition : BoolTm Γ) :
    (Empty.not proposition).toIntrinsic =
      InfinityTm.not proposition.toIntrinsic := by
  rw [InfinityTm.mk.injEq]
  rfl

@[simp] theorem Term.toIntrinsic_and
    {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (left right : BoolTm Γ) :
    (Empty.and left right).toIntrinsic =
      InfinityTm.and left.toIntrinsic right.toIntrinsic := by
  rw [InfinityTm.mk.injEq]
  rfl

namespace Eval

variable {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
  {A B : Ty types}

/-- Classical truth value of existential inhabitation. -/
noncomputable def existsBool {α : Type} (predicate : α → Bool) : Bool := by
  classical
  exact decide (∃ value, predicate value = true)

/-- Evaluation depends on checked syntax, not on the proof fields carried by
its wrapper. -/
theorem congr_raw {left right : Term Γ A} (shape : left.raw = right.raw)
    {env : CTypeEnv types} {bound : CBoundEnv depth} {expected : CPointed}
    {value : expected.carrier} (evaluation : Eval left env bound expected value) :
    Eval right env bound expected value := by
  have termsEqual : left = right := by
    cases left with
    | mk leftRaw leftTyping =>
      cases right with
      | mk rightRaw rightTyping =>
        dsimp only at shape
        subst rightRaw
        congr
  cases termsEqual
  exact evaluation

theorem canonical (term : Term Γ A) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (expected : CPointed) :
    Eval term env bound expected
      (Infinity.iValue term.toIntrinsic env bound expected) :=
  by
    simpa [Eval] using
      (Infinity.IEval.canonical term.toIntrinsic env bound expected)

theorem value_unique {term : Term Γ A} {env : CTypeEnv types}
    {bound : CBoundEnv depth} {expected : CPointed}
    {left right : expected.carrier}
    (leftEval : Eval term env bound expected left)
    (rightEval : Eval term env bound expected right) : left = right :=
  by
    exact Infinity.IEval.value_unique leftEval rightEval

theorem bool (Γ : Ctx types depth) (literal : Bool)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    Eval (Term.bool Γ literal) env bound cBool literal :=
  by
    simpa [Eval, Term.toIntrinsic, Term.bool, InfinityTm.boolean,
      FamK.boolTy] using
      (Infinity.IEval.boolean literal env bound)

theorem bvAs (Γ : Ctx types depth) (index : Fin depth) (A : Ty types)
    (lookup : Γ.raw index = A.raw) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (expected : CPointed)
    (value : expected.carrier) (atIndex : bound index expected = value) :
    Eval (Term.bvAs Γ index A lookup) env bound expected value :=
  by
    simpa [Eval, Term.toIntrinsic, Term.bvAs, InfinityTm.bv] using
      (Infinity.IEval.bv A.kinded index lookup env bound expected value atIndex)

theorem bv (Γ : Ctx types depth) (index : Fin depth)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (expected : CPointed) (value : expected.carrier)
    (atIndex : bound index expected = value) :
    Eval (Term.bv Γ index) env bound expected value := by
  simpa [Eval, Term.toIntrinsic, Term.bv, InfinityTm.bv] using
    (Infinity.IEval.bv (Γ.typed index) index rfl env bound expected value atIndex)

/-- Weakening a term preserves its value under an extended environment. -/
theorem weaken (term : Term Γ A) (C : Ty types) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (head : (C.denote env).carrier)
    (expected : CPointed) (value : expected.carrier)
    (evaluation : Eval term env bound expected value) :
    Eval (term.weaken C) env
      (extendCBoundEnv (C.denote env) head bound) expected value := by
  unfold Eval Infinity.IEval at evaluation ⊢
  intro checking
  simp only [Term.toIntrinsic, Term.weaken, Ctx.extend] at checking ⊢
  let target := (term.typing.weaken (B := C.raw)).certificate
  rw [cSem_certificate_coherent checking target env]
  have environment :
      (extendCBoundEnv (C.denote env) head bound).rename Fin.succ = bound := by
    funext index target
    rfl
  calc
    cSem target env (extendCBoundEnv (C.denote env) head bound) expected =
        cSem term.typing.certificate env
          ((extendCBoundEnv (C.denote env) head bound).rename Fin.succ) expected :=
      cSem_rename_raw term.typing.certificate Fin.succ (fun _ => rfl) target
        env _ expected
    _ = cSem term.typing.certificate env bound expected := by rw [environment]
    _ = ⟨value⟩ := evaluation term.typing.certificate

theorem app (function : Term Γ (A.arr B)) (argument : Term Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (functionValue : (A.denote env).carrier → (B.denote env).carrier)
    (argumentValue : (A.denote env).carrier)
    (functionEval : Eval function env bound
      (cArrow (A.denote env) (B.denote env)) functionValue)
    (argumentEval : Eval argument env bound (A.denote env) argumentValue) :
    Eval (Term.app function argument) env bound (B.denote env)
      (functionValue argumentValue) :=
  by
    simpa [Eval, Term.toIntrinsic, Term.app, InfinityTm.app,
      FamK.denote, FamK.arr, cArrow] using
      (Infinity.IEval.app function.toIntrinsic argument.toIntrinsic
        A.kinded.certificate B.kinded.certificate env bound
        functionValue argumentValue functionEval argumentEval)

/-- Boolean-valued specialization of application, avoiding any dependence on
the proof object stored in the checked Boolean alias. -/
theorem appBool (function : Term Γ (A.arr FamK.boolTy))
    (argument : Term Γ A) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (functionValue : (A.denote env).carrier → Bool)
    (argumentValue : (A.denote env).carrier)
    (functionEval : Eval function env bound
      (cArrow (A.denote env) cBool) functionValue)
    (argumentEval : Eval argument env bound (A.denote env) argumentValue) :
    Eval (Term.app function argument) env bound cBool
      (functionValue argumentValue) := by
  unfold Eval
  simpa [Term.toIntrinsic, Term.app, InfinityTm.app, cArrow] using
    (Infinity.IEval.app function.toIntrinsic argument.toIntrinsic
      A.kinded.certificate .boolTy env bound
      functionValue argumentValue functionEval argumentEval)

theorem lam (A : Ty types) (body : Term (Ctx.extend A Γ) B)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (function : (A.denote env).carrier → (B.denote env).carrier)
    (bodyEval : ∀ argument,
      Eval body env (extendCBoundEnv (A.denote env) argument bound)
        (B.denote env) (function argument)) :
    Eval (Term.lam A body) env bound
      (cArrow (A.denote env) (B.denote env)) function :=
  by
    simpa [Eval, Term.toIntrinsic, Term.lam, InfinityTm.lam,
      FamK.denote, FamK.arr, cArrow] using
      (Infinity.IEval.lam A.kinded body.toIntrinsic A.kinded.certificate
        B.kinded.certificate env bound function bodyEval)

theorem eq (A : Ty types) (left right : Term Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (leftValue rightValue : (A.denote env).carrier)
    (leftEval : Eval left env bound (A.denote env) leftValue)
    (rightEval : Eval right env bound (A.denote env) rightValue) :
    Eval (Term.eq A left right) env bound cBool
      (Infinity.classicalEqBool leftValue rightValue) :=
  by
    simpa [Eval, Term.toIntrinsic, Term.eq, InfinityTm.eq,
      FamK.boolTy, FamK.denote] using
      (Infinity.IEval.eq A.kinded left.toIntrinsic right.toIntrinsic
        A.kinded.certificate env bound leftValue rightValue leftEval rightEval)

theorem eps (A : Ty types) (predicate : Term Γ (A.arr FamK.boolTy))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (predicateEval : Eval predicate env bound
      ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning) :
    Eval (Term.eps A predicate) env bound (A.denote env)
      (Infinity.epsilonValue (A.denote env) meaning) :=
  by
    simpa [Eval, Term.toIntrinsic, Term.eps, InfinityTm.eps,
      FamK.denote, FamK.arr, FamK.boolTy] using
      (Infinity.IEval.eps A.kinded predicate.toIntrinsic A.kinded.certificate
        env bound meaning predicateEval)

theorem truth (Γ : Ctx types depth) (env : CTypeEnv types)
    (bound : CBoundEnv depth) : Eval (Term.truth Γ) env bound cBool true :=
  bool Γ true env bound

theorem falsehood (Γ : Ctx types depth) (env : CTypeEnv types)
    (bound : CBoundEnv depth) : Eval (Term.falsehood Γ) env bound cBool false :=
  bool Γ false env bound

theorem forallTm (A : Ty types) (body : BoolTm (Γ.extend A))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (bodyTrue : ∀ argument : (A.denote env).carrier,
      Eval body env (extendCBoundEnv (A.denote env) argument bound)
        cBool true) :
    Eval (Empty.forallTm A body) env bound cBool true := by
  unfold Eval
  rw [Term.toIntrinsic_forallTm]
  simpa [FamK.denote] using
    (Infinity.IEval.forallTm A.kinded body.toIntrinsic
      A.kinded.certificate env bound bodyTrue)

theorem existsTm (A : Ty types) (body : BoolTm (Γ.extend A))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (bodyEval : ∀ argument,
      Eval body env (extendCBoundEnv (A.denote env) argument bound)
        cBool (meaning argument))
    (witness : (A.denote env).carrier) (holds : meaning witness = true) :
    Eval (Empty.existsTm A body) env bound cBool true := by
  unfold Eval
  rw [Term.toIntrinsic_existsTm]
  simpa [FamK.denote] using
    (Infinity.IEval.existsTm A.kinded body.toIntrinsic
      A.kinded.certificate env bound meaning bodyEval witness holds)

/-- Existential quantification computes whether its body has a true witness. -/
theorem existsTm_value (A : Ty types) (body : BoolTm (Γ.extend A))
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (bodyEval : ∀ argument,
      Eval body env (extendCBoundEnv (A.denote env) argument bound)
        cBool (meaning argument)) :
    Eval (Empty.existsTm A body) env bound cBool
      (existsBool meaning) := by
  classical
  let functionType : CPointed :=
    ⟨(A.denote env).carrier → Bool, fun _ => false⟩
  let predicate := InfinityTm.lam A.kinded body.toIntrinsic
  have predicateEval : Infinity.IEval predicate env bound functionType meaning :=
    Infinity.IEval.lam A.kinded body.toIntrinsic A.kinded.certificate
      .boolTy env bound meaning bodyEval
  have epsilonEval := Infinity.IEval.eps A.kinded predicate A.kinded.certificate
    env bound meaning predicateEval
  have applied := Infinity.IEval.app predicate (InfinityTm.eps A.kinded predicate)
    A.kinded.certificate .boolTy env bound meaning
    (Infinity.epsilonValue (A.denote env) meaning) predicateEval epsilonEval
  have result :
      meaning (Infinity.epsilonValue (A.denote env) meaning) =
        existsBool meaning := by
    by_cases witness : ∃ argument, meaning argument = true
    · obtain ⟨argument, holds⟩ := witness
      rw [Infinity.epsilonValue_spec (A.denote env) meaning argument holds]
      have existsWitness : ∃ value, meaning value = true := ⟨argument, holds⟩
      simp [existsBool, existsWitness]
    · have selectedFalse :
          meaning (Infinity.epsilonValue (A.denote env) meaning) = false := by
        cases selected : meaning (Infinity.epsilonValue (A.denote env) meaning)
        · rfl
        · exact False.elim (witness ⟨_, selected⟩)
      rw [selectedFalse]
      simp [existsBool, witness]
  unfold Eval
  rw [Term.toIntrinsic_existsTm]
  exact result ▸ applied

theorem not_of_false (proposition : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth)
    (evaluation : Eval proposition env bound cBool false) :
    Eval (Empty.not proposition) env bound cBool true := by
  unfold Eval
  rw [Term.toIntrinsic_not]
  simpa using
    (Infinity.IEval.not_of_false proposition.toIntrinsic env bound evaluation)

/-- Negation computes Boolean negation. -/
theorem not_value (proposition : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (value : Bool)
    (evaluation : Eval proposition env bound cBool value) :
    Eval (Empty.not proposition) env bound cBool (!value) := by
  have equality := Infinity.IEval.eq (.boolTy) proposition.toIntrinsic
    (Term.falsehood Γ).toIntrinsic .boolTy env bound value false evaluation
    (Infinity.IEval.boolean false env bound)
  have result : Infinity.classicalEqBool value false = !value := by
    cases value <;> simp [Infinity.classicalEqBool]
  unfold Eval
  rw [Term.toIntrinsic_not]
  exact result ▸ equality

theorem and_value (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.and left right) env bound cBool (leftValue && rightValue) := by
  let functionType : Ty types := FamK.boolTy.arr (FamK.boolTy.arr FamK.boolTy)
  have functionSemanticEq : functionType.denote env = cSem
      (CChecks.arr (types := types) CChecks.boolTy
        (CChecks.arr CChecks.boolTy CChecks.boolTy)) env := by
    exact cSem_certificate_coherent functionType.kinded.certificate
      (CChecks.arr CChecks.boolTy (CChecks.arr CChecks.boolTy CChecks.boolTy)) env
  have leftWeakened : ∀ f : (cSem
      (CChecks.arr (types := types) CChecks.boolTy
        (CChecks.arr CChecks.boolTy CChecks.boolTy)) env).carrier,
      Infinity.IEval (left.toIntrinsic.weaken
        (C := .arr .boolTy (.arr .boolTy .boolTy))) env
        (extendCBoundEnv (cSem
          (CChecks.arr CChecks.boolTy (CChecks.arr CChecks.boolTy CChecks.boolTy)) env)
          f bound) cBool leftValue := by
    rw [← functionSemanticEq]
    intro f
    have result := weaken left functionType env bound f cBool leftValue leftEval
    unfold Eval at result
    rw [Term.toIntrinsic_weaken] at result
    simpa [functionType, FamK.arr, Ctx.extend] using result
  have rightWeakened : ∀ f : (cSem
      (CChecks.arr (types := types) CChecks.boolTy
        (CChecks.arr CChecks.boolTy CChecks.boolTy)) env).carrier,
      Infinity.IEval (right.toIntrinsic.weaken
        (C := .arr .boolTy (.arr .boolTy .boolTy))) env
        (extendCBoundEnv (cSem
          (CChecks.arr CChecks.boolTy (CChecks.arr CChecks.boolTy CChecks.boolTy)) env)
          f bound) cBool rightValue := by
    rw [← functionSemanticEq]
    intro f
    have result := weaken right functionType env bound f cBool rightValue rightEval
    unfold Eval at result
    rw [Term.toIntrinsic_weaken] at result
    simpa [functionType, FamK.arr, Ctx.extend] using result
  unfold Eval
  rw [Term.toIntrinsic_and]
  simpa [Eval, Term.toIntrinsic_weaken, functionType, FamK.denote,
    FamK.arr, FamK.boolTy] using
    (Infinity.IEval.and_value left.toIntrinsic right.toIntrinsic env bound
      leftValue rightValue leftWeakened rightWeakened)

theorem and_of_true (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth)
    (leftEval : Eval left env bound cBool true)
    (rightEval : Eval right env bound cBool true) :
    Eval (Empty.and left right) env bound cBool true := by
  simpa using and_value left right env bound true true leftEval rightEval

/-- Disjunction computes Boolean disjunction. -/
theorem or_value (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.or left right) env bound cBool (leftValue || rightValue) := by
  have leftNot := not_value left env bound leftValue leftEval
  have rightNot := not_value right env bound rightValue rightEval
  have conjunction := and_value (Empty.not left) (Empty.not right) env bound
    (!leftValue) (!rightValue) leftNot rightNot
  have negated := not_value (Empty.and (Empty.not left) (Empty.not right)) env bound
    ((!leftValue) && (!rightValue)) conjunction
  cases leftValue <;> cases rightValue <;> simpa [Empty.or] using negated

/-- Implication computes material implication. -/
theorem imp_value (left right : BoolTm Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (leftValue rightValue : Bool)
    (leftEval : Eval left env bound cBool leftValue)
    (rightEval : Eval right env bound cBool rightValue) :
    Eval (Empty.imp left right) env bound cBool ((!leftValue) || rightValue) := by
  have rightNot := not_value right env bound rightValue rightEval
  have conjunction := and_value left (Empty.not right) env bound
    leftValue (!rightValue) leftEval rightNot
  have negated := not_value (Empty.and left (Empty.not right)) env bound
    (leftValue && (!rightValue)) conjunction
  cases leftValue <;> cases rightValue <;> simpa [Empty.imp] using negated

/-- A checked type-existential is true when its body has one semantic witness.
The predicate is evaluated in the *ambient* bound environment: a type binder
does not touch it, which is what makes the open quantifier cost nothing. -/
theorem tyExists (Γ : Ctx types depth)
    (predicate : Term (types := .star :: types) Γ.weakenTypes FamK.boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (candidate : CPointed)
    (predicateTrue : Eval predicate (extendCTypeEnv candidate env)
      bound cBool true) :
    Eval (Term.tyExists Γ predicate) env bound cBool true := by
  classical
  unfold Eval Infinity.IEval
  intro checking
  let explicit : CHasType Γ.raw (.tyExists predicate.raw) .boolTy :=
    .tyExists predicate.typing.certificate
  rw [cSem_certificate_coherent checking explicit env]
  change ULift.up (alignCValue cBool cBool (decide (∃ witness : CPointed,
    cSem predicate.typing.certificate
      (extendCTypeEnv witness env) bound cBool = ⟨true⟩))) = ⟨true⟩
  rw [alignCValue_bool]
  apply congrArg ULift.up
  apply decide_eq_true
  exact ⟨candidate, predicateTrue predicate.typing.certificate⟩

end Eval

end

end Nucleus.HolE.Empty
