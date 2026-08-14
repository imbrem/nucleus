import Nucleus.SExpr.Basic

/-!
# A small Lisp over binary S-expressions

Programs and quoted data are `SExpr2 String`. Runtime closures are deliberately
kept out of the source data model. The evaluator is fuelled, lexically scoped,
and parameterized by the spellings of its special forms, making it a compact
baseline against which later Lisp dialects can be compared.
-/

namespace Nucleus.SExpr2.Lisp

abbrev Expr := SExpr2 String

/-- Surface spellings which commonly vary between Lisp dialects. -/
structure Dialect where
  quoteName : String := "quote"
  ifName : String := "if"
  lambdaName : String := "lambda"
  trueName : String := "t"
  deriving DecidableEq, Repr

def Dialect.standard : Dialect := {}

/-- The deliberately small collection of built-in operations. -/
inductive Primitive where
  | cons | car | cdr | atom | eq | isNil
  deriving DecidableEq, Repr

/-- The two sorts represented by the indexed runtime family. -/
inductive RuntimeKind where
  | value
  | environment
  deriving DecidableEq, Repr

/-- Values and lexical environments in one regular indexed family. The index
rules out nonsensical cases and supplies one induction principle for proofs
about closures together with their captured environments. -/
inductive Runtime : RuntimeKind → Type where
  | datum (value : Expr) : Runtime .value
  | closure (parameters : List String) (body : Expr)
      (environment : Runtime .environment) : Runtime .value
  | primitive (operation : Primitive) : Runtime .value
  | empty : Runtime .environment
  | bind (name : String) (value : Runtime .value)
      (tail : Runtime .environment) : Runtime .environment
  deriving DecidableEq, Repr

abbrev Value := Runtime .value
abbrev Environment := Runtime .environment

namespace Environment

def lookup (environment : Environment) (name : String) : Option Value :=
  match environment with
  | .empty => none
  | .bind key value tail => if name = key then some value else lookup tail name

def append (front back : Environment) : Environment :=
  match front with
  | .empty => back
  | .bind name value tail => .bind name value (append tail back)

def ofList : List (String × Value) → Environment
  | [] => .empty
  | (name, value) :: tail => .bind name value (ofList tail)

@[simp] theorem lookup_bind_eq (environment : Environment) (name : String)
    (value : Value) : lookup (.bind name value environment) name = some value := by
  simp [lookup]

theorem lookup_bind_ne (environment : Environment) {name key : String}
    (value : Value) (h : name ≠ key) :
    lookup (.bind key value environment) name = lookup environment name := by
  simp [lookup, h]

end Environment

/-- Observable evaluator failures. Invalid programs are distinguished from
fuel exhaustion, which is useful when comparing evaluators. -/
inductive Error where
  | outOfFuel
  | unbound (name : String)
  | malformedSpecialForm (name : String)
  | malformedParameters
  | improperApplication
  | notCallable
  | arity (expected actual : Nat)
  | type
  deriving DecidableEq, Repr

abbrev Result := Except Error Value

def toList? : Expr → Option (List Expr)
  | .nil => some []
  | .cons head tail => (head :: ·) <$> toList? tail
  | .atom _ => none

@[simp] theorem toList?_ofList (values : List Expr) :
    toList? (SExpr2.ofList values) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [toList?, SExpr2.ofList, ih]

namespace Syntax

/-- Construct a proper application form. -/
def apply (function : Expr) (arguments : List Expr) : Expr :=
  SExpr2.ofList (function :: arguments)

def quote (dialect : Dialect) (value : Expr) : Expr :=
  apply (.atom dialect.quoteName) [value]

def ifThenElse (dialect : Dialect) (condition yes no : Expr) : Expr :=
  apply (.atom dialect.ifName) [condition, yes, no]

def lambda (dialect : Dialect) (parameters : List String) (body : Expr) : Expr :=
  apply (.atom dialect.lambdaName) [SExpr2.ofAtoms parameters, body]

end Syntax

def parseParameters : Expr → Option (List String)
  | .nil => some []
  | .cons (.atom name) tail => (name :: ·) <$> parseParameters tail
  | _ => none

@[simp] theorem parseParameters_ofAtoms (names : List String) :
    parseParameters (SExpr2.ofAtoms names) = some names := by
  unfold SExpr2.ofAtoms
  induction names with
  | nil => rfl
  | cons name names ih => simp [SExpr2.ofList, parseParameters, ih]

def Value.isTruthy : Value → Bool
  | .datum .nil => false
  | _ => true

def Value.toExpr? : Value → Option Expr
  | .datum value => some value
  | _ => none

private def expectDatum : Value → Except Error Expr
  | .datum value => .ok value
  | _ => .error .type

private def boolDatum (dialect : Dialect) (value : Bool) : Value :=
  .datum (if value then .atom dialect.trueName else .nil)

def primitiveEnvironment : Environment := Environment.ofList [
  ("cons", .primitive .cons),
  ("car", .primitive .car),
  ("cdr", .primitive .cdr),
  ("atom?", .primitive .atom),
  ("eq?", .primitive .eq),
  ("nil?", .primitive .isNil)
]

private def applyPrimitive (dialect : Dialect) (operation : Primitive)
    (arguments : List Value) : Result := do
  match operation, arguments with
  | .cons, [left, right] =>
      return .datum (.cons (← expectDatum left) (← expectDatum right))
  | .car, [value] => return .datum (← expectDatum value).car
  | .cdr, [value] => return .datum (← expectDatum value).cdr
  | .atom, [value] =>
      let value ← expectDatum value
      return boolDatum dialect (match value with | .cons _ _ => false | _ => true)
  | .eq, [left, right] =>
      return boolDatum dialect ((← expectDatum left) == (← expectDatum right))
  | .isNil, [value] => return boolDatum dialect (← expectDatum value).isNil
  | .cons, _ => .error (.arity 2 arguments.length)
  | .eq, _ => .error (.arity 2 arguments.length)
  | _, _ => .error (.arity 1 arguments.length)

private def bindParameters (parameters : List String) (arguments : List Value)
    (tail : Environment) : Except Error Environment :=
  if _h : parameters.length = arguments.length then
    .ok (Environment.ofList (parameters.zip arguments) |>.append tail)
  else
    .error (.arity parameters.length arguments.length)

/- Fuel bounds recursive evaluation, including argument evaluation and
closure calls. Every recursive evaluator call receives strictly less fuel. -/
mutual
  def eval (dialect : Dialect) : Nat → Environment → Expr → Result
    | 0, _, _ => .error .outOfFuel
    | fuel + 1, environment, expression =>
        match expression with
        | .nil => .ok (.datum .nil)
        | .atom name =>
            if name = dialect.trueName then .ok (.datum (.atom dialect.trueName))
            else match environment.lookup name with
              | some value => .ok value
              | none => .error (.unbound name)
        | .cons head tail =>
            match head, toList? tail with
            | .atom name, some arguments =>
                if name = dialect.quoteName then
                  match arguments with
                  | [quoted] => .ok (.datum quoted)
                  | _ => .error (.malformedSpecialForm name)
                else if name = dialect.ifName then
                  match arguments with
                  | [condition, yes, no] => do
                      let condition ← eval dialect fuel environment condition
                      eval dialect fuel environment (if condition.isTruthy then yes else no)
                  | _ => .error (.malformedSpecialForm name)
                else if name = dialect.lambdaName then
                  match arguments with
                  | [parameters, body] => match parseParameters parameters with
                    | some names => .ok (.closure names body environment)
                    | none => .error .malformedParameters
                  | _ => .error (.malformedSpecialForm name)
                else do
                  let function ← eval dialect fuel environment head
                  let values ← evalArguments dialect fuel environment arguments
                  apply dialect fuel function values
            | _, some arguments => do
                let function ← eval dialect fuel environment head
                let values ← evalArguments dialect fuel environment arguments
                apply dialect fuel function values
            | _, none => .error .improperApplication

  def evalArguments (dialect : Dialect) : Nat → Environment → List Expr →
      Except Error (List Value)
    | 0, _, _ => .error .outOfFuel
    | _ + 1, _, [] => .ok []
    | fuel + 1, environment, expression :: tail => do
        let value ← eval dialect fuel environment expression
        let values ← evalArguments dialect fuel environment tail
        return value :: values

  def apply (dialect : Dialect) : Nat → Value → List Value → Result
    | 0, _, _ => .error .outOfFuel
    | _ + 1, .datum _, _ => .error .notCallable
    | _ + 1, .primitive operation, arguments => applyPrimitive dialect operation arguments
    | fuel + 1, .closure parameters body closureEnvironment, arguments => do
        let environment ← bindParameters parameters arguments closureEnvironment
        eval dialect fuel environment body
end

/-- Evaluate in the standard primitive environment. -/
def run (fuel : Nat) (expression : Expr) : Result :=
  eval .standard fuel primitiveEnvironment expression

/-- The unbounded semantic relation induced by successful finite evaluation. -/
def Evaluates (dialect : Dialect) (environment : Environment)
    (expression : Expr) (value : Value) : Prop :=
  ∃ fuel, eval dialect fuel environment expression = .ok value

theorem eval_deterministic {dialect : Dialect} {environment : Environment}
    {expression : Expr} {fuel : Nat} {left right : Value}
    (hl : eval dialect fuel environment expression = .ok left)
    (hr : eval dialect fuel environment expression = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

@[simp] theorem eval_quote (dialect : Dialect) (environment : Environment)
    (fuel : Nat) (value : Expr) :
    eval dialect (fuel + 1) environment
      (SExpr2.ofList [.atom dialect.quoteName, value]) = .ok (.datum value) := by
  simp [eval, toList?, SExpr2.ofList]

@[simp] theorem run_nil (fuel : Nat) : run (fuel + 1) .nil = .ok (.datum .nil) := rfl

/-- Quotation is data-preserving. -/
theorem run_quote (fuel : Nat) (value : Expr) :
    run (fuel + 1) (Syntax.quote .standard value) = .ok (.datum value) := by
  simp [run, Syntax.quote, Syntax.apply]

@[simp] theorem applyPrimitive_cons (dialect : Dialect) (left right : Expr) :
    applyPrimitive dialect .cons [.datum left, .datum right] =
      .ok (.datum (.cons left right)) := rfl

/-- Constructing a standard lambda captures precisely the current lexical
environment; it does not evaluate its body. -/
theorem eval_standard_lambda (fuel : Nat) (environment : Environment)
    (parameters : List String) (body : Expr) :
    eval .standard (fuel + 1) environment
      (Syntax.lambda .standard parameters body) =
      .ok (.closure parameters body environment) := by
  change eval .standard (fuel + 1) environment
    (.cons (.atom "lambda") (SExpr2.ofList [SExpr2.ofAtoms parameters, body])) = _
  simp [Dialect.standard, eval]

end Nucleus.SExpr2.Lisp
