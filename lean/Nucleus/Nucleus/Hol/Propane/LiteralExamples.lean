import Nucleus.Hol.Propane.LiteralCorrespondence
import Nucleus.Hol.Ethane.LiteralArena

/-! # Checked literal theorems and a nested raw application DAG -/

namespace Nucleus.Hol.Propane

set_option maxRecDepth 4096

/-- Boolean equality has one primitive meaning: equivalence. -/
theorem bool_iff_is_equality (left right : Bool) :
    Builtin.eval (.bool .iff) [.bool left, .bool right] =
      some (.bool (decide (left = right))) := by
  cases left <;> cases right <;> decide

theorem bool_imp_is_material (left right : Bool) :
    Builtin.eval (.bool .imp) [.bool left, .bool right] =
      some (.bool (!left || right)) := by
  cases left <;> cases right <;> decide

def booleanProof : Proves (Γ := []) []
    (.eq ((Tm.builtin (.bool .imp) rfl).applyLiterals
      (.cons false (.cons false .nil))) (.literal .bool true)) :=
  .eqOfEqTm (.builtinReduce (.bool .imp) (output := .bool)
    rfl (.cons false (.cons false .nil)) true (by decide))

/-- One symbolic definition equality is reusable before any operands are known. -/
def booleanUnfoldProof (op : BoolOp) : Proves (Γ := []) [] (.eq op.term op.definition) :=
  .eqOfEqTm (.boolUnfold op)

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
    ⟨.app (-1216) (-1048596), -131181⟩,
    ⟨.app 1 (-1048598), -7⟩,
    ⟨.app (-1221) 2, -7⟩,
    ⟨.eq (-7) 3 (-1048619), -2⟩]
  constants := []

private def exampleSchedule : List Int := [-1048596, -1048598, 2, 3, -1048619, 4]

example : check exampleArena exampleSchedule 4 = some (.bool true) := by decide

/-- The exact curried application DAG denotes true in every certified natural model. -/
theorem nested_dag_true (naturals : Nucleus.HolE.Infinity.CNatModel) :
    Denotes naturals exampleArena 4 (quote naturals (.bool true)) :=
  check_sound naturals (by decide : check exampleArena exampleSchedule 4 = some (.bool true))

/-- Scheduling a result before its dependencies cannot establish it. -/
example : check exampleArena [4] 4 = none := by decide

/-- A function-valued partial application has no scalar reduction result. -/
example : check exampleArena [-1048596, 1] 1 = none := by decide

end Nucleus.Hol.Ethane.Literals.Dag
