import Nucleus.SExpr.Forsp.Parser
import Nucleus.SExpr.Forsp.CellMachine
import Nucleus.SExpr.Forsp.Closure

/-!
# End-to-end Forsp interface

This module connects source parsing, literal-table allocation, and execution.
-/

namespace Nucleus.SExpr2.Forsp

/-- Parse and execute a source expression in the tree machine. -/
def runSource? (fuel : Nat) (source : String) :
    Option (Except Tree.Error (Tree.Environment × Tree.State)) := do
  let (literals, program) ← Parser.parse? source
  some (Tree.run fuel program { literals })

/-- Parse and execute the same source through concrete pointer-cell objects. -/
def runSourceCells? (fuel : Nat) (source : String) :
    Option (Except Tree.Error (CellMachine.Environment × CellMachine.State)) := do
  let (literals, program) ← Parser.parse? source
  let state : Tree.State := { literals }
  some (CellMachine.run fuel (.encode program) (CellMachine.encodeState state))

/-- End-to-end source execution commutes with cell encoding. -/
theorem runSourceCells?_eq (fuel : Nat) (source : String) :
    runSourceCells? fuel source = (runSource? fuel source).map fun result =>
      result.map fun final =>
        (CellMachine.encodeRuntime final.1, CellMachine.encodeState final.2) := by
  simp only [runSourceCells?, runSource?]
  cases hparse : Parser.parse? source with
  | none => simp
  | some parsed =>
      rcases parsed with ⟨literals, program⟩
      simp [CellMachine.run_encode]

/-- A small observation useful for executable specifications and examples. -/
def runTopLiteral? (fuel : Nat) (source : String) : Option Literal := do
  let result ← runSource? fuel source
  let (_, state) ← result.toOption
  let value ← state.stack.head?
  let object ← match value with
    | .datum object => some object
    | _ => none
  state.literals.decode? object

set_option linter.style.nativeDecide false in
example : runTopLiteral? 32 "(42 $x ^x)" = some (.integer 42) := by
  native_decide

set_option linter.style.nativeDecide false in
example : runTopLiteral? 16 "(\"hello\\nworld\")" = some (.string "hello\nworld") := by
  native_decide

set_option linter.style.nativeDecide false in
example : runTopLiteral? 32 "(#00ff#)" =
    some (.bytes ⟨[0, 255].toByteArray⟩) := by
  native_decide

end Nucleus.SExpr2.Forsp
