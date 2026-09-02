import Nucleus.Wasm.SpecTec.Wasm3.Selection
import Nucleus.Wasm.Word

/-!
# Deep instruction-list interpreter for the Wasm 3.0 addition fragment

This executable model is intentionally shaped differently from
`Nucleus.Wasm.SpecTec.Wasm3.Shallow`: instructions contain no administrative
constants, and the operand stack is a separate top-first list. It is a Lean
reference interpreter only. It does not decode Wasm bytes, ingest the pinned
SpecTec artifact, or produce a Nucleus HOL theorem.

`Selection.executionRoots` records the exact selectors used during the manual
investigation. They are metadata only: this module neither checks the selectors
against the pinned artifact nor interprets the selected roots.
-/

namespace Nucleus.Wasm.SpecTec.Wasm3.Deep

/-- Source instructions supported by the first reference interpreter. -/
inductive Instr where
  | localGet (index : Nat)
  | i32Add
  | return
  deriving DecidableEq, Repr

/-- An instruction-list machine with a top-first operand stack. -/
structure Machine where
  locals : List I32
  stack : List I32
  code : List Instr
  deriving DecidableEq, Repr

/-- The observable result of one interpreter transition. -/
inductive Transition where
  | next (machine : Machine)
  | done (value : I32)
  deriving DecidableEq, Repr

/-- Execute one instruction, or observe one-result fallthrough at body end. -/
def tick (machine : Machine) : Option Transition :=
  match machine.code with
  | [] =>
      match machine.stack with
      | [value] => some (.done value)
      | _ => none
  | .localGet index :: code =>
      match machine.locals[index]? with
      | some value => some (.next { machine with stack := value :: machine.stack, code })
      | none => none
  | .i32Add :: code =>
      match machine.stack with
      | right :: left :: stack =>
          some (.next { machine with stack := Wasm.i32Add left right :: stack, code })
      | _ => none
  | .return :: _ =>
      match machine.stack with
      | result :: _ => some (.done result)
      | [] => none

/-- Run for at most `fuel` transitions. -/
def run : Nat → Machine → Option I32
  | 0, _ => none
  | fuel + 1, machine =>
      match tick machine with
      | none => none
      | some (.done value) => some value
      | some (.next next) => run fuel next

end Nucleus.Wasm.SpecTec.Wasm3.Deep
