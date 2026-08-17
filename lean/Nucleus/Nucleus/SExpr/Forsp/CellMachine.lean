import Nucleus.SExpr.Forsp.Cell

/-!
# Forsp over cell memory

Every datum and closure body in this machine is a closed pointer into concrete
cell memory.  The implementation validates and dereferences those pointers,
runs the tree transition, and allocates its results back into cells.  The
round-trip theorems below prove that this transport is observationally exactly
the tree implementation on well-formed (encoded) states.
-/

namespace Nucleus.SExpr2.Forsp.CellMachine

open Nucleus.SExpr2.Forsp

inductive Runtime : Tree.RuntimeKind → Type where
  | datum (object : Cell.StoredObject) : Runtime .value
  | closure (body : Cell.StoredObject) (environment : Runtime .environment) : Runtime .value
  | primitive (operation : Tree.Primitive) : Runtime .value
  | empty : Runtime .environment
  | bind (name : String) (value : Runtime .value) (tail : Runtime .environment) :
      Runtime .environment

abbrev Value := Runtime .value
abbrev Environment := Runtime .environment

def encodeRuntime : {kind : Tree.RuntimeKind} → Tree.Runtime kind → Runtime kind
  | _, .datum object => .datum (.encode object)
  | _, .closure body environment => .closure (.encode body) (encodeRuntime environment)
  | _, .primitive operation => .primitive operation
  | _, .empty => .empty
  | _, .bind name value tail => .bind name (encodeRuntime value) (encodeRuntime tail)

def decodeRuntime : {kind : Tree.RuntimeKind} → Runtime kind → Option (Tree.Runtime kind)
  | _, .datum object => .datum <$> object.decode?
  | _, .closure body environment =>
      .closure <$> body.decode? <*> decodeRuntime environment
  | _, .primitive operation => some (.primitive operation)
  | _, .empty => some .empty
  | _, .bind name value tail =>
      .bind name <$> decodeRuntime value <*> decodeRuntime tail

@[simp] theorem decodeRuntime_encodeRuntime :
    ∀ {kind : Tree.RuntimeKind} (runtime : Tree.Runtime kind),
      decodeRuntime (encodeRuntime runtime) = some runtime := by
  intro kind runtime
  induction runtime with
  | datum object => simp [encodeRuntime, decodeRuntime]
  | closure body environment ih => simp [encodeRuntime, decodeRuntime, ih]
  | primitive operation => rfl
  | empty => rfl
  | bind name value tail ihValue ihTail =>
      simp [encodeRuntime, decodeRuntime, ihValue, ihTail]

structure State where
  stack : List Value
  literals : LiteralTable
  input : List Cell.StoredObject
  output : List Cell.StoredObject

def encodeState (state : Tree.State) : State where
  stack := state.stack.map encodeRuntime
  literals := state.literals
  input := state.input.map Cell.StoredObject.encode
  output := state.output.map Cell.StoredObject.encode

private def decodeObjects : List Cell.StoredObject → Option (List Object)
  | [] => some []
  | object :: tail => List.cons <$> object.decode? <*> decodeObjects tail

private def decodeValues : List Value → Option (List Tree.Value)
  | [] => some []
  | value :: tail => List.cons <$> decodeRuntime value <*> decodeValues tail

def decodeState (state : State) : Option Tree.State := do
  return {
    stack := ← decodeValues state.stack
    literals := state.literals
    input := ← decodeObjects state.input
    output := ← decodeObjects state.output
  }

@[simp] private theorem decodeObjects_encode (objects : List Object) :
    decodeObjects (objects.map Cell.StoredObject.encode) = some objects := by
  induction objects with
  | nil => rfl
  | cons object tail ih => simp [decodeObjects, ih]

@[simp] private theorem decodeValues_encode (values : List Tree.Value) :
    decodeValues (values.map encodeRuntime) = some values := by
  induction values with
  | nil => rfl
  | cons value tail ih => simp [decodeValues, ih]

@[simp] theorem decodeState_encodeState (state : Tree.State) :
    decodeState (encodeState state) = some state := by
  simp [decodeState, encodeState]

abbrev Error := Tree.Error
abbrev M := StateT State (Except Error)

private def require (error : Error) : Option α → Except Error α
  | some value => .ok value
  | none => .error error

/-- Validate/dereference a cell program, execute it, and re-encode every
runtime object produced by the transition. -/
def compute (fuel : Nat) (program : Cell.StoredObject) (environment : Environment) :
    M Environment := fun state => do
  let program ← require .malformedComputation program.decode?
  let environment ← require .malformedComputation (decodeRuntime environment)
  let state ← require .malformedComputation (decodeState state)
  let (environment, state) ← Tree.compute fuel program environment state
  return (encodeRuntime environment, encodeState state)

def run (fuel : Nat) (program : Cell.StoredObject) (state : State) :
    Except Error (Environment × State) :=
  compute fuel program (encodeRuntime Tree.initialEnvironment) state

/-- The cell-memory implementation commutes with the tree implementation on
all encoded programs, environments, and states. -/
theorem compute_encode (fuel : Nat) (program : Object) (environment : Tree.Environment)
    (state : Tree.State) :
    compute fuel (.encode program) (encodeRuntime environment) (encodeState state) =
      (Tree.compute fuel program environment state).map fun result =>
        (encodeRuntime result.1, encodeState result.2) := by
  simp only [compute, Cell.StoredObject.decode?_encode,
    decodeRuntime_encodeRuntime, decodeState_encodeState, require]
  change (Tree.compute fuel program environment state >>= fun result =>
      pure (encodeRuntime result.1, encodeState result.2)) = _
  cases Tree.compute fuel program environment state <;> rfl

theorem run_encode (fuel : Nat) (program : Object) (state : Tree.State) :
    run fuel (.encode program) (encodeState state) =
      (Tree.run fuel program state).map fun result =>
        (encodeRuntime result.1, encodeState result.2) := by
  simp [run, Tree.run, compute_encode]

end Nucleus.SExpr2.Forsp.CellMachine
