import Nucleus.Hol.Propane.LiteralCorrespondence
import Nucleus.Hol.Ethane.LiteralArena

/-! # Checked literal theorems and a nested raw application DAG -/

namespace Nucleus.Hol.Propane

set_option maxRecDepth 4096

private def byteAddArgs : LiteralArgs [.word .i8, .word .i8] :=
  .cons 255 (.cons 1 .nil)

private def byteAdd : Closed (.word .i8) :=
  (Tm.builtin (.word .i8 .add) rfl).applyLiterals byteAddArgs

/-- Actual Propane theorem construction, not merely reference evaluation. -/
def byteWrapProof : Proves (Γ := []) [] (.eq byteAdd (.literal (.word .i8) 0)) :=
  .eqOfEqTm (.builtinReduce (.word .i8 .add) (output := .word .i8)
    rfl byteAddArgs 0 (by decide))

private def bigNatArgs : LiteralArgs [.nat, .nat] :=
  .cons (2 ^ 80) (.cons 17 .nil)

def bigNatProof : Proves (Γ := []) []
    (.eq ((Tm.builtin (.nat .add) rfl).applyLiterals bigNatArgs)
      (.literal .nat (2 ^ 80 + 17))) :=
  .eqOfEqTm (.builtinReduce (.nat .add) (output := .nat)
    rfl bigNatArgs (2 ^ 80 + 17) (by decide))

private def signedArgs : LiteralArgs [.word .i32] := .cons 4294967295 .nil

def signedInterpretationProof : Proves (Γ := []) []
    (.eq ((Tm.builtin (.cast (.wordToIntS .i32)) rfl).applyLiterals signedArgs)
      (.literal .int (-1))) :=
  .eqOfEqTm (.builtinReduce (.cast (.wordToIntS .i32)) rfl signedArgs (-1) (by decide))

private def sliceArgs : LiteralArgs [.bytes, .nat, .nat] :=
  .cons [10, 20, 30, 40] (.cons 1 (.cons 2 .nil))

def bytesSliceProof : Proves (Γ := []) []
    (.eq ((Tm.builtin (.bytes .slice) rfl).applyLiterals sliceArgs)
      (.literal .bytes [20, 30])) :=
  .eqOfEqTm (.builtinReduce (.bytes .slice) rfl sliceArgs [20, 30] (by decide))

private def littleEndianArgs : LiteralArgs [.bytes] := .cons [0x78, 0x56, 0x34, 0x12] .nil

def endianProof : Proves (Γ := []) []
    (.eq ((Tm.builtin (.bytes (.decode .i32 .little)) rfl).applyLiterals littleEndianArgs)
      (.literal (.word .i32) 0x12345678)) :=
  .eqOfEqTm (.builtinReduce (.bytes (.decode .i32 .little)) rfl
    littleEndianArgs 0x12345678 (by decide))

example : Builtin.eval (.word .i64 .divS)
    [.word .i64 (2 ^ 63), .word .i64 (2 ^ 64 - 1)] = none := by decide

example : Builtin.eval (.word .i64 .remS)
    [.word .i64 (2 ^ 63), .word .i64 (2 ^ 64 - 1)] = some (.word .i64 0) := by decide

end Nucleus.Hol.Propane

namespace Nucleus.Hol.Ethane.Literals.Dag

open Nucleus.Hol.Propane

private def exampleArena : Arena where
  rows := [
    ⟨.type .nat, 0⟩, ⟨.type .bool, 0⟩,
    ⟨.arrow 1 1, 0⟩, ⟨.arrow 1 3, 0⟩,
    ⟨.natInline 20, 1⟩, ⟨.natInline 22, 1⟩,
    ⟨.builtin (.nat .add), 4⟩, ⟨.app 7 5, 3⟩, ⟨.app 8 6, 1⟩,
    ⟨.builtin (.nat .succ), 3⟩, ⟨.app 10 9, 1⟩,
    ⟨.eq 1 11 13, 2⟩, ⟨.natInline 43, 1⟩]
  constants := []

private def exampleSchedule : List Nat := [5, 6, 9, 11, 13, 12]

example : check exampleArena exampleSchedule 12 = some (.bool true) := by decide

/-- The exact curried application DAG denotes true in every certified natural model. -/
theorem nested_dag_true (naturals : Nucleus.HolE.Infinity.CNatModel) :
    Denotes naturals exampleArena 12 (quote naturals (.bool true)) :=
  check_sound naturals (by decide : check exampleArena exampleSchedule 12 = some (.bool true))

/-- Scheduling a result before its dependencies cannot establish it. -/
example : check exampleArena [12] 12 = none := by decide

/-- A function-valued partial application has no scalar reduction result. -/
example : check exampleArena [5, 8] 8 = none := by decide

end Nucleus.Hol.Ethane.Literals.Dag
