import Nucleus.SExpr.Basic
import Nucleus.SExpr.Atom

/-!
# A reusable Lisp evaluator over binary S-expressions

The evaluator is generic in atoms, symbols, primitive operations, and the
surface conventions of a Lisp dialect. Runtime values and environments form
one indexed family. A String-only Lisp and a small Scheme atom model are
instances of the same evaluator and inherit its proofs.
-/

namespace Nucleus.SExpr2.Lisp

universe u v w

variable {Atom : Type u} {Name : Type v} {Primitive : Type w} {σ : Type*}

abbrev Expr (Atom : Type u) := SExpr2 Atom

/-- Surface syntax and truth conventions supplied by a Lisp-like language. -/
class Language (Atom : Type u) (Name : Type v) where
  symbol? : Atom → Option Name
  symbol : Name → Atom
  symbol?_symbol : ∀ name, symbol? (symbol name) = some name
  quoteName : Name
  ifName : Name
  lambdaName : Name
  trueValue : Expr Atom
  isTruthyDatum : Expr Atom → Bool
  isTruthy_trueValue : isTruthyDatum trueValue = true

namespace Language

variable {Atom : Type u} {Name : Type v} [Language Atom Name]

def boolValue (value : Bool) : Expr Atom :=
  if value then Language.trueValue (Atom := Atom) (Name := Name) else .nil

def quoteAtom : Atom := Language.symbol (Atom := Atom) (Name := Name)
  (Language.quoteName (Atom := Atom) (Name := Name))
def ifAtom : Atom := Language.symbol (Atom := Atom) (Name := Name)
  (Language.ifName (Atom := Atom) (Name := Name))
def lambdaAtom : Atom := Language.symbol (Atom := Atom) (Name := Name)
  (Language.lambdaName (Atom := Atom) (Name := Name))

@[simp] theorem symbol?_quoteAtom :
    Language.symbol? (Atom := Atom) (Name := Name)
      (quoteAtom (Atom := Atom) (Name := Name)) =
      some (Language.quoteName (Atom := Atom) (Name := Name)) :=
  Language.symbol?_symbol _

end Language

/-- The runtime sorts represented by one indexed family. -/
inductive RuntimeKind where
  | value
  | environment
  deriving DecidableEq, Repr

/-- Runtime values and lexical environments. `Primitive` and the atom/symbol
types are parameters, so alternative languages reuse the same induction
principle and evaluator theory. -/
inductive Runtime (Atom : Type u) (Name : Type v) (Primitive : Type w) :
    RuntimeKind → Type (max u v w) where
  | datum (value : Expr Atom) : Runtime Atom Name Primitive .value
  | closure (parameters : List Name) (body : Expr Atom)
      (environment : Runtime Atom Name Primitive .environment) :
      Runtime Atom Name Primitive .value
  | primitive (operation : Primitive) : Runtime Atom Name Primitive .value
  | empty : Runtime Atom Name Primitive .environment
  | bind (name : Name) (value : Runtime Atom Name Primitive .value)
      (tail : Runtime Atom Name Primitive .environment) :
      Runtime Atom Name Primitive .environment
  deriving DecidableEq, Repr

abbrev Value (Atom : Type u) (Name : Type v) (Primitive : Type w) :=
  Runtime Atom Name Primitive .value
abbrev Environment (Atom : Type u) (Name : Type v) (Primitive : Type w) :=
  Runtime Atom Name Primitive .environment

namespace Environment

variable {Atom : Type u} {Name : Type v} {Primitive : Type w}

def lookup [DecidableEq Name] (environment : Environment Atom Name Primitive)
    (name : Name) : Option (Value Atom Name Primitive) :=
  match environment with
  | .empty => none
  | .bind key value tail => if name = key then some value else lookup tail name

def append (front back : Environment Atom Name Primitive) :
    Environment Atom Name Primitive :=
  match front with
  | .empty => back
  | .bind name value tail => .bind name value (append tail back)

def ofList : List (Name × Value Atom Name Primitive) → Environment Atom Name Primitive
  | [] => .empty
  | (name, value) :: tail => .bind name value (ofList tail)

@[simp] theorem lookup_bind_eq [DecidableEq Name]
    (environment : Environment Atom Name Primitive) (name : Name)
    (value : Value Atom Name Primitive) :
    lookup (.bind name value environment) name = some value := by simp [lookup]

theorem lookup_bind_ne [DecidableEq Name]
    (environment : Environment Atom Name Primitive) {name key : Name}
    (value : Value Atom Name Primitive) (h : name ≠ key) :
    lookup (.bind key value environment) name = lookup environment name := by
  simp [lookup, h]

end Environment

/-- Errors shared by every instance of the evaluator. -/
inductive Error (Name : Type v) where
  | outOfFuel
  | unbound (name : Name)
  | malformedSpecialForm (name : Name)
  | malformedParameters
  | improperApplication
  | notCallable
  | arity (expected actual : Nat)
  | type
  deriving DecidableEq, Repr

/-- Primitive bindings and behavior are independent of surface syntax. -/
class PrimitiveSemantics (Atom : Type u) (Name : Type v) (Primitive : Type w)
    [Language Atom Name] where
  State : Type (max u v w)
  initialState : State
  bindings : List (Name × Primitive)
  apply : Primitive → List (Value Atom Name Primitive) →
    StateT State (Except (Error Name)) (Value Atom Name Primitive)

abbrev State (Atom : Type u) (Name : Type v) (Primitive : Type w)
    [Language Atom Name] [PrimitiveSemantics Atom Name Primitive] :=
  PrimitiveSemantics.State (Atom := Atom) (Name := Name) (Primitive := Primitive)

abbrev Result (Atom : Type u) (Name : Type v) (Primitive : Type w)
    [Language Atom Name] [PrimitiveSemantics Atom Name Primitive] :=
  Except (Error Name) (Value Atom Name Primitive × State Atom Name Primitive)

/-- Evaluation effects: mutable language state over exceptions.  This order
means that a failed computation does not expose its intermediate state. -/
abbrev EvalM (Atom : Type u) (Name : Type v) (Primitive : Type w)
    [Language Atom Name] [PrimitiveSemantics Atom Name Primitive] :=
  StateT (State Atom Name Primitive) (Except (Error Name))

namespace EvalM

def throw [Language Atom Name] [PrimitiveSemantics Atom Name Primitive]
    (error : Error Name) : EvalM Atom Name Primitive α :=
  fun _ => .error error

@[simp] theorem run_throw [Language Atom Name] [PrimitiveSemantics Atom Name Primitive]
    (error : Error Name) (state : State Atom Name Primitive) :
    (throw (Atom := Atom) (Primitive := Primitive) error : EvalM Atom Name Primitive α) state =
      .error error := rfl

end EvalM

def toList? : Expr Atom → Option (List (Expr Atom))
  | .nil => some []
  | .cons head tail => (head :: ·) <$> toList? tail
  | .atom _ => none

@[simp] theorem toList?_ofList (values : List (Expr Atom)) :
    toList? (SExpr2.ofList values) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [toList?, SExpr2.ofList, ih]

namespace Syntax

variable {Atom : Type u} {Name : Type v} [Language Atom Name]

def apply (function : Expr Atom) (arguments : List (Expr Atom)) : Expr Atom :=
  SExpr2.ofList (function :: arguments)

def quote (value : Expr Atom) : Expr Atom :=
  apply (.atom (Language.quoteAtom (Atom := Atom) (Name := Name))) [value]

def ifThenElse (condition yes no : Expr Atom) : Expr Atom :=
  apply (.atom (Language.ifAtom (Atom := Atom) (Name := Name))) [condition, yes, no]

def lambda (parameters : List Name) (body : Expr Atom) : Expr Atom :=
  apply (.atom (Language.lambdaAtom (Atom := Atom) (Name := Name)))
    [SExpr2.ofAtoms (parameters.map Language.symbol), body]

end Syntax

def parseParameters [Language Atom Name] : Expr Atom → Option (List Name)
  | .nil => some []
  | .atom _ => none
  | .cons head tail => match head with
    | .atom value => match Language.symbol? (Atom := Atom) (Name := Name) value with
      | some name => (name :: ·) <$> parseParameters tail
      | none => none
    | _ => none

private theorem parseParameters_list_symbols [Language Atom Name] (names : List Name) :
    parseParameters (SExpr2.ofList (names.map fun name =>
      .atom (Language.symbol (Atom := Atom) (Name := Name) name))) = some names := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp [SExpr2.ofList, parseParameters, Language.symbol?_symbol, ih]

@[simp] theorem parseParameters_symbols [Language Atom Name] (names : List Name) :
    parseParameters (SExpr2.ofAtoms (names.map
      (Language.symbol (Atom := Atom) (Name := Name)))) = some names := by
  simpa [SExpr2.ofAtoms, List.map_map, Function.comp_def] using
    parseParameters_list_symbols (Atom := Atom) names

def Value.isTruthy [Language Atom Name] : Value Atom Name Primitive → Bool
  | .datum value => Language.isTruthyDatum (Atom := Atom) (Name := Name) value
  | _ => true

def Value.toExpr? : Value Atom Name Primitive → Option (Expr Atom)
  | .datum value => some value
  | _ => none

def primitiveEnvironment [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] : Environment Atom Name Primitive :=
  Environment.ofList (PrimitiveSemantics.bindings (Atom := Atom) (Name := Name)
    (Primitive := Primitive) |>.map fun pair => (pair.1, .primitive pair.2))

private def bindParameters (parameters : List Name)
    (arguments : List (Value Atom Name Primitive))
    (tail : Environment Atom Name Primitive) :
    Except (Error Name) (Environment Atom Name Primitive) :=
  if _h : parameters.length = arguments.length then
    .ok (Environment.ofList (parameters.zip arguments) |>.append tail)
  else .error (.arity parameters.length arguments.length)

/- The generic fuelled monadic evaluator. Every recursive call receives less fuel. -/
mutual
  def evalM [DecidableEq Name] [Language Atom Name]
      [PrimitiveSemantics Atom Name Primitive] :
      Nat → Environment Atom Name Primitive → Expr Atom → EvalM Atom Name Primitive
        (Value Atom Name Primitive)
    | 0, _, _ => EvalM.throw .outOfFuel
    | fuel + 1, environment, expression => fun state =>
        match expression with
        | .nil => .ok (.datum .nil, state)
        | .atom value => match Language.symbol? (Atom := Atom) (Name := Name) value with
          | none => .ok (.datum (.atom value), state)
          | some name => match Environment.lookup environment name with
            | some value => .ok (value, state)
            | none => .error (.unbound name)
        | .cons head tail =>
            match head, toList? tail with
            | .atom value, some arguments =>
                match Language.symbol? (Atom := Atom) (Name := Name) value with
              | some name =>
                  if name = Language.quoteName (Atom := Atom) (Name := Name) then
                    match arguments with
                    | [quoted] => .ok (.datum quoted, state)
                    | _ => .error (.malformedSpecialForm name)
                  else if name = Language.ifName (Atom := Atom) (Name := Name) then
                    match arguments with
                    | [condition, yes, no] =>
                        match (evalM fuel environment condition state :
                            Result Atom Name Primitive) with
                        | .error error => .error error
                        | .ok (condition, state) =>
                            evalM fuel environment (if condition.isTruthy then yes else no) state
                    | _ => .error (.malformedSpecialForm name)
                  else if name = Language.lambdaName (Atom := Atom) (Name := Name) then
                    match arguments with
                    | [parameters, body] => match parseParameters parameters with
                      | some names => .ok (.closure names body environment, state)
                      | none => .error .malformedParameters
                    | _ => .error (.malformedSpecialForm name)
                  else evalApplicationM fuel environment head arguments state
              | none => evalApplicationM fuel environment head arguments state
            | _, some arguments => evalApplicationM fuel environment head arguments state
            | _, none => .error .improperApplication

  def evalArgumentsM [DecidableEq Name] [Language Atom Name]
      [PrimitiveSemantics Atom Name Primitive] :
      Nat → Environment Atom Name Primitive → List (Expr Atom) →
      EvalM Atom Name Primitive (List (Value Atom Name Primitive))
    | 0, _, _ => EvalM.throw .outOfFuel
    | _ + 1, _, [] => pure []
    | fuel + 1, environment, expression :: tail => do
        let value ← evalM fuel environment expression
        let values ← evalArgumentsM fuel environment tail
        pure (value :: values)

  def applyM [DecidableEq Name] [Language Atom Name]
      [PrimitiveSemantics Atom Name Primitive] :
      Nat → Value Atom Name Primitive → List (Value Atom Name Primitive) →
      EvalM Atom Name Primitive (Value Atom Name Primitive)
    | 0, _, _ => EvalM.throw .outOfFuel
    | _ + 1, .datum _, _ => EvalM.throw .notCallable
    | _ + 1, .primitive operation, arguments => PrimitiveSemantics.apply operation arguments
    | fuel + 1, .closure parameters body closureEnvironment, arguments =>
        match bindParameters parameters arguments closureEnvironment with
        | .error error => EvalM.throw error
        | .ok environment => evalM fuel environment body

  def evalApplicationM [DecidableEq Name] [Language Atom Name]
      [PrimitiveSemantics Atom Name Primitive]
      (fuel : Nat) (environment : Environment Atom Name Primitive)
      (function : Expr Atom) (arguments : List (Expr Atom)) :
      EvalM Atom Name Primitive (Value Atom Name Primitive) := do
    let function ← evalM fuel environment function
    let values ← evalArgumentsM fuel environment arguments
    applyM fuel function values
end

/-- Run the monadic evaluator from an explicit state.  This compatibility
interface is definitionally the old state-threading semantics. -/
def eval [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (fuel : Nat)
    (environment : Environment Atom Name Primitive) (state : State Atom Name Primitive)
    (expression : Expr Atom) : Result Atom Name Primitive :=
  evalM fuel environment expression state

@[simp] theorem eval_eq_run_evalM [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (fuel : Nat)
    (environment : Environment Atom Name Primitive) (state : State Atom Name Primitive)
    (expression : Expr Atom) :
    eval fuel environment state expression = evalM fuel environment expression state := rfl

def run [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (fuel : Nat) (expression : Expr Atom) :
    Result Atom Name Primitive := eval fuel primitiveEnvironment
      PrimitiveSemantics.initialState expression

def Evaluates [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (environment : Environment Atom Name Primitive)
    (state : State Atom Name Primitive) (expression : Expr Atom)
    (value : Value Atom Name Primitive) : Prop :=
  ∃ fuel finalState, eval fuel environment state expression = .ok (value, finalState)

/-- The relational semantics stated directly in terms of the monadic action. -/
def EvaluatesM [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (environment : Environment Atom Name Primitive)
    (state : State Atom Name Primitive) (expression : Expr Atom)
    (value : Value Atom Name Primitive) : Prop :=
  ∃ fuel finalState, evalM fuel environment expression state = .ok (value, finalState)

@[simp] theorem evaluates_iff_evaluatesM [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive] (environment : Environment Atom Name Primitive)
    (state : State Atom Name Primitive) (expression : Expr Atom)
    (value : Value Atom Name Primitive) :
    Evaluates environment state expression value ↔ EvaluatesM environment state expression value :=
  Iff.rfl

theorem eval_deterministic [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive]
    {environment : Environment Atom Name Primitive} {expression : Expr Atom}
    {fuel : Nat} {left right : Value Atom Name Primitive}
    {state leftState rightState : State Atom Name Primitive}
    (hl : eval fuel environment state expression = .ok (left, leftState))
    (hr : eval fuel environment state expression = .ok (right, rightState)) :
    left = right ∧ leftState = rightState := by
  rw [hl] at hr
  have pair := Except.ok.inj hr
  exact ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩

@[simp] theorem eval_quote [DecidableEq Name] [Language Atom Name]
    [PrimitiveSemantics Atom Name Primitive]
    (environment : Environment Atom Name Primitive) (state : State Atom Name Primitive)
    (fuel : Nat) (value : Expr Atom) :
    eval (fuel + 1) environment state (Syntax.quote (Name := Name) value) =
      .ok (.datum value, state) := by
  change eval (fuel + 1) environment state
    (.cons (.atom (Language.quoteAtom (Atom := Atom) (Name := Name)))
      (SExpr2.ofList [value])) = _
  simp [eval, evalM]

/-! ## Shared structural primitives -/

inductive StructuralPrimitive where
  | cons | car | cdr | atom | eq | isNil
  deriving DecidableEq, Repr

private def expectDatum : Value Atom Name Primitive → Except (Error Name) (Expr Atom)
  | .datum value => .ok value
  | _ => .error .type

def applyStructural [DecidableEq Atom] [Language Atom Name]
    (operation : StructuralPrimitive)
    (arguments : List (Value Atom Name Primitive)) (state : σ) :
    Except (Error Name) (Value Atom Name Primitive × σ) :=
  match operation, arguments with
  | .cons, [left, right] => match expectDatum left, expectDatum right with
    | .ok left, .ok right => .ok (.datum (.cons left right), state)
    | .error error, _ | _, .error error => .error error
  | .car, [value] => match expectDatum value with
    | .ok value => .ok (.datum value.car, state)
    | .error error => .error error
  | .cdr, [value] => match expectDatum value with
    | .ok value => .ok (.datum value.cdr, state)
    | .error error => .error error
  | .atom, [value] => match expectDatum value with
    | .ok value => .ok (.datum (Language.boolValue (Name := Name)
        (match value with | .cons _ _ => false | _ => true)), state)
    | .error error => .error error
  | .eq, [left, right] => match expectDatum left, expectDatum right with
    | .ok left, .ok right =>
        .ok (.datum (Language.boolValue (Name := Name) (left == right)), state)
    | .error error, _ | _, .error error => .error error
  | .isNil, [value] => match expectDatum value with
    | .ok value => .ok (.datum (Language.boolValue (Name := Name) value.isNil), state)
    | .error error => .error error
  | .cons, _ | .eq, _ => .error (.arity 2 arguments.length)
  | _, _ => .error (.arity 1 arguments.length)

/-! ## The original String Lisp -/

namespace StringLisp

instance stringLanguage : Language String String where
  symbol? := some
  symbol := id
  symbol?_symbol _ := rfl
  quoteName := "quote"
  ifName := "if"
  lambdaName := "lambda"
  trueValue := .atom "t"
  isTruthyDatum
    | .nil => false
    | _ => true
  isTruthy_trueValue := rfl

instance stringPrimitives : PrimitiveSemantics String String StructuralPrimitive where
  State := Unit
  initialState := ()
  bindings := [("cons", .cons), ("car", .car), ("cdr", .cdr),
    ("atom?", .atom), ("eq?", .eq), ("nil?", .isNil)]
  apply := applyStructural (Primitive := StructuralPrimitive)

abbrev StringExpr := Expr String
abbrev StringValue := Value String String StructuralPrimitive
abbrev StringEnvironment := Environment String String StructuralPrimitive

def runString (fuel : Nat) (expression : StringExpr) :
    Result String String StructuralPrimitive := run fuel expression

end StringLisp

/-! ## A small Scheme-flavoured instance -/

namespace Scheme

inductive SchemeAtom where
  | symbol (name : String)
  | string (value : String)
  | integer (value : Int)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

instance schemeLanguage : Language SchemeAtom String where
  symbol?
    | .symbol name => some name
    | _ => none
  symbol := .symbol
  symbol?_symbol _ := rfl
  quoteName := "quote"
  ifName := "if"
  lambdaName := "lambda"
  trueValue := .atom (.boolean true)
  isTruthyDatum
    | .atom (.boolean false) => false
    | _ => true
  isTruthy_trueValue := rfl

instance schemePrimitives : PrimitiveSemantics SchemeAtom String StructuralPrimitive where
  State := Unit
  initialState := ()
  bindings := [("cons", .cons), ("car", .car), ("cdr", .cdr),
    ("pair?", .atom), ("eq?", .eq), ("null?", .isNil)]
  apply := applyStructural (Primitive := StructuralPrimitive)

@[simp] theorem symbol?_string (value : String) :
    Language.symbol? (Atom := SchemeAtom) (Name := String) (.string value) = none := rfl

@[simp] theorem symbol?_integer (value : Int) :
    Language.symbol? (Atom := SchemeAtom) (Name := String) (.integer value) = none := rfl

abbrev SchemeExpr := Expr SchemeAtom
abbrev SchemeValue := Value SchemeAtom String StructuralPrimitive

def runScheme (fuel : Nat) (expression : SchemeExpr) :
    Result SchemeAtom String StructuralPrimitive := run fuel expression

@[simp] theorem eval_string_literal
    (environment : Environment SchemeAtom String StructuralPrimitive)
    (fuel : Nat) (value : String) :
    eval (fuel + 1) environment () (.atom (.string value)) =
      .ok (.datum (.atom (.string value)), ()) := by
  simp [eval, evalM]

@[simp] theorem eval_integer_literal
    (environment : Environment SchemeAtom String StructuralPrimitive)
    (fuel : Nat) (value : Int) :
    eval (fuel + 1) environment () (.atom (.integer value)) =
      .ok (.datum (.atom (.integer value)), ()) := by
  simp [eval, evalM]

/- A stateful variant uses exactly the same evaluator. -/
namespace Stateful

inductive StatefulPrimitive where
  | structural (operation : StructuralPrimitive)
  | tick
  deriving DecidableEq, Repr

instance statefulPrimitives : PrimitiveSemantics SchemeAtom String StatefulPrimitive where
  State := Nat
  initialState := 0
  bindings := [("cons", .structural .cons), ("car", .structural .car),
    ("cdr", .structural .cdr), ("pair?", .structural .atom),
    ("eq?", .structural .eq), ("null?", .structural .isNil), ("tick", .tick)]
  apply operation arguments state := match operation with
    | .structural operation => applyStructural operation arguments state
    | .tick => match arguments with
      | [] => .ok (.datum (.atom (.integer state)), state + 1)
      | _ => .error (.arity 0 arguments.length)

abbrev StatefulValue := Value SchemeAtom String StatefulPrimitive

def runStateful (fuel : Nat) (expression : SchemeExpr) :
    Result SchemeAtom String StatefulPrimitive := run fuel expression

@[simp] theorem apply_tick (state : Nat) :
    PrimitiveSemantics.apply (Atom := SchemeAtom) (Name := String)
      (Primitive := StatefulPrimitive) .tick [] state =
      .ok (.datum (.atom (.integer state)), state + 1) := rfl

end Stateful

end Scheme

end Nucleus.SExpr2.Lisp
