import Nucleus.SExpr.Forsp.Literal

/-!
# Tree semantics for Forsp

This is a fuelled, pure model of the reference `compute`/`eval` machine.  The
operand stack, literal table, input, and printed output form the transformer
state; lexical environments are threaded separately because a forced closure
uses its captured environment without replacing its caller's environment.
-/

namespace Nucleus.SExpr2.Forsp.Tree

open Nucleus.SExpr2.Forsp

inductive Primitive where
  | push | pop | eq | cons | car | cdr | cswap | tag | read | print
  deriving DecidableEq, Repr

inductive RuntimeKind where
  | value | environment
  deriving DecidableEq, Repr

inductive Runtime : RuntimeKind → Type where
  | datum (object : Object) : Runtime .value
  | closure (body : Object) (environment : Runtime .environment) : Runtime .value
  | primitive (operation : Primitive) : Runtime .value
  | empty : Runtime .environment
  | bind (name : String) (value : Runtime .value) (tail : Runtime .environment) :
      Runtime .environment
  deriving DecidableEq, Repr

abbrev Value := Runtime .value
abbrev Environment := Runtime .environment

namespace Environment

def lookup (environment : Environment) (name : String) : Option Value :=
  match environment with
  | .empty => none
  | .bind key value tail => if name = key then some value else lookup tail name

def define (environment : Environment) (name : String) (value : Value) : Environment :=
  .bind name value environment

end Environment

structure State where
  stack : List Value := []
  literals : LiteralTable := []
  input : List Object := []
  output : List Object := []
  deriving DecidableEq

inductive Error where
  | outOfFuel | malformedComputation | quoteWithoutDatum | unbound (name : String)
  | stackUnderflow | expectedSymbol | expectedDatum | expectedPair | inputExhausted
  deriving DecidableEq, Repr

abbrev M := StateT State (Except Error)

private def throw (error : Error) : M α := fun _ => .error error

private def pop : M Value
  | state => match state.stack with
    | [] => .error .stackUnderflow
    | value :: stack => .ok (value, { state with stack })

private def push (value : Value) : M Unit
  | state => .ok ((), { state with stack := value :: state.stack })

private def expectDatum : Value → Except Error Object
  | .datum object => .ok object
  | _ => .error .expectedDatum

private def expectSymbol : Value → Except Error String
  | .datum (.atom (.symbol name)) => .ok name
  | _ => .error .expectedSymbol

private def liftExcept : Except Error α → M α
  | .ok value => pure value
  | .error error => throw error

private def allocateLiteral (literal : Literal) : M Object
  | state =>
      let allocated := state.literals.allocate literal
      .ok (allocated.2, { state with literals := allocated.1 })

private def valueTag : Value → Int
  | .datum .nil => 0
  | .datum (.atom _) => 1
  | .datum (.cons _ _) => 3
  | .closure _ _ => 4
  | .primitive _ => 5

private def objectsEqual (left right : Value) : Bool := decide (left = right)

def initialEnvironment : Environment :=
  [ ("push", .push), ("pop", .pop), ("eq", .eq), ("cons", .cons),
    ("car", .car), ("cdr", .cdr), ("cswap", .cswap), ("tag", .tag),
    ("read", .read), ("print", .print) ].foldr
      (fun binding tail => .bind binding.1 (.primitive binding.2) tail) .empty

private def applyPrimitive (operation : Primitive) (environment : Environment) :
    M Environment := do
  match operation with
  | .push =>
      let name ← liftExcept (expectSymbol (← pop))
      match environment.lookup name with
      | some value => push value; pure environment
      | none => throw (.unbound name)
  | .pop =>
      let name ← liftExcept (expectSymbol (← pop))
      let value ← pop
      pure (environment.define name value)
  | .eq =>
      let right ← pop
      let left ← pop
      push (.datum (if objectsEqual left right then .atom (.symbol "t") else .nil))
      pure environment
  | .cons =>
      let car ← liftExcept (expectDatum (← pop))
      let cdr ← liftExcept (expectDatum (← pop))
      push (.datum (.cons car cdr))
      pure environment
  | .car =>
      match ← liftExcept (expectDatum (← pop)) with
      | .cons car _ => push (.datum car); pure environment
      | _ => throw .expectedPair
  | .cdr =>
      match ← liftExcept (expectDatum (← pop)) with
      | .cons _ cdr => push (.datum cdr); pure environment
      | _ => throw .expectedPair
  | .cswap =>
      let condition ← pop
      if condition = .datum (.atom (.symbol "t")) then
        let first ← pop
        let second ← pop
        push first
        push second
      pure environment
  | .tag =>
      let object ← allocateLiteral (.integer (valueTag (← pop)))
      push (.datum object)
      pure environment
  | .read => fun state => match state.input with
      | [] => .error .inputExhausted
      | object :: input => .ok (environment,
          { state with input, stack := .datum object :: state.stack })
  | .print =>
      let object ← liftExcept (expectDatum (← pop))
      fun state => .ok (environment, { state with output := state.output ++ [object] })

mutual
  def compute : Nat → Object → Environment → M Environment
    | 0, _, _ => throw .outOfFuel
    | _ + 1, .nil, environment => pure environment
    | _ + 1, .atom _, _ => throw .malformedComputation
    | fuel + 1, .cons command rest, environment =>
        if command = .atom (.symbol "quote") then
          match rest with
          | .cons datum tail => do
              push (.datum datum)
              compute fuel tail environment
          | _ => throw .quoteWithoutDatum
        else do
          let environment ← eval fuel command environment
          compute fuel rest environment

  def eval : Nat → Object → Environment → M Environment
    | 0, _, _ => throw .outOfFuel
    | fuel + 1, object, environment => fun state =>
        if state.literals.decode? object |>.isSome then
          push (.datum object) state |>.map fun result => (environment, result.2)
        else match object with
        | .atom (.symbol name) => match environment.lookup name with
          | none => .error (.unbound name)
          | some (.closure body captured) =>
              compute fuel body captured state |>.map fun result => (environment, result.2)
          | some (.primitive operation) => applyPrimitive operation environment state
          | some value => push value state |>.map fun result => (environment, result.2)
        | .nil | .cons _ _ =>
            push (.closure object environment) state |>.map fun result => (environment, result.2)
        | .atom _ => push (.datum object) state |>.map fun result => (environment, result.2)
end

def run (fuel : Nat) (program : Object) (state : State := {}) :
    Except Error (Environment × State) :=
  compute fuel program initialEnvironment state

@[simp] theorem compute_nil (fuel : Nat) (environment : Environment) (state : State) :
    compute (fuel + 1) .nil environment state = .ok (environment, state) := rfl

@[simp] theorem compute_quote (fuel : Nat) (environment : Environment) (state : State)
    (datum tail : Object) :
    compute (fuel + 1) (.cons (.atom (.symbol "quote")) (.cons datum tail))
      environment state =
        compute fuel tail environment { state with stack := .datum datum :: state.stack } := by
  rfl

end Nucleus.SExpr2.Forsp.Tree
