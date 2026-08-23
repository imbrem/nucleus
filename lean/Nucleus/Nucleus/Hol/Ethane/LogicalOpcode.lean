import Nucleus.Hol.Ethane.Arena.OneBased.Cbor
import Nucleus.Hol.Ethane.Arena.OneBased.Kernel
import Nucleus.Hol.Ethane.Semantics

/-!
# Compact logical opcodes in the Rust-facing Ethane arena

This file reasons about the actual one-based row enum and CBOR codec used by
Rust. Compact rows elaborate directly to their opcode-free Ethane expansion;
there is no second term, row, or wire datatype in this layer.
-/

namespace Nucleus.Hol.Ethane.LogicalOpcode

open Nucleus Nucleus.Hol.Ethane Nucleus.Hol.Ethane.OneBased
set_option relaxedAutoImplicit true

namespace Raw

def one : OneBased.Ref := ⟨1, by decide⟩
def two : OneBased.Ref := ⟨2, by decide⟩

def op1Row (op : Builtin.Op1) : OneBased.detail.Row :=
  { expr := .op1 op one }

def op2Row (op : Builtin.Op2) : OneBased.detail.Row :=
  { expr := .op2 op one two }

/-- Exact Rust golden bytes for `tm.op1.v1/not`. -/
def notGolden : Bytes := ⟨[
  163, 99, 116, 97, 103, 105, 116, 109, 46, 111, 112, 49, 46, 118, 49, 99,
  105, 120, 115, 129, 1, 99, 118, 97, 108, 0].toByteArray⟩

/-- Exact Rust golden bytes for one binary row discriminant. -/
def op2Golden : Builtin.Op2 → Bytes
  | .and => ⟨[
      163, 99, 116, 97, 103, 105, 116, 109, 46, 111, 112, 50, 46, 118, 49, 99,
      105, 120, 115, 130, 1, 2, 99, 118, 97, 108, 0].toByteArray⟩
  | .or => ⟨[
      163, 99, 116, 97, 103, 105, 116, 109, 46, 111, 112, 50, 46, 118, 49, 99,
      105, 120, 115, 130, 1, 2, 99, 118, 97, 108, 1].toByteArray⟩
  | .imp => ⟨[
      163, 99, 116, 97, 103, 105, 116, 109, 46, 111, 112, 50, 46, 118, 49, 99,
      105, 120, 115, 130, 1, 2, 99, 118, 97, 108, 2].toByteArray⟩

/-- The Rust unary golden parses to exactly the production row encoder's CBOR. -/
example : CborWire.parse? notGolden =
    some (OneBased.Cbor.encodeRow (op1Row .not)) := by native_decide

/-- Every Rust binary golden parses to exactly the production row encoder's CBOR. -/
example (op : Builtin.Op2) : CborWire.parse? (op2Golden op) =
    some (OneBased.Cbor.encodeRow (op2Row op)) := by
  cases op <;> native_decide

/-- Exact bytes therefore decode through the production row decoder. -/
example : (CborWire.parse? notGolden).bind OneBased.Cbor.decodeRow? =
    some (op1Row .not) := by native_decide

example (op : Builtin.Op2) :
    (CborWire.parse? (op2Golden op)).bind OneBased.Cbor.decodeRow? =
      some (op2Row op) := by
  cases op <;> native_decide

/-- Re-encoding a row decoded from a Rust golden preserves its exact CBOR tree. -/
example (op : Builtin.Op2) :
    ((CborWire.parse? (op2Golden op)).bind OneBased.Cbor.decodeRow?).map
      OneBased.Cbor.encodeRow = CborWire.parse? (op2Golden op) := by
  cases op <;> native_decide

/-- Wrong arity and reserved discriminants are rejected by the real decoder. -/
example : OneBased.Cbor.decodeRow? (Builtin.op1Row .not 1) =
    some (op1Row .not) := by native_decide

example : OneBased.Cbor.decodeRow?
    (Nucleus.Cbor.mapOfList [
      (.primitive (.text "tag"), .primitive (.text Builtin.op1RowTag)),
      (.primitive (.text "ixs"), Nucleus.Cbor.arrayOfList [
        .primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2))]),
      (.primitive (.text "val"), .primitive (.integer (.unsigned 0)))]) = none := by
  native_decide

example : OneBased.Cbor.decodeRow?
    (Nucleus.Cbor.mapOfList [
      (.primitive (.text "tag"), .primitive (.text Builtin.op2RowTag)),
      (.primitive (.text "ixs"), Nucleus.Cbor.arrayOfList [
        .primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2))]),
      (.primitive (.text "val"), .primitive (.integer (.unsigned 3)))]) = none := by
  native_decide

end Raw

/-! ## Actual row elaboration and logical meaning -/

theorem elaborate_op1
    (op : Builtin.Op1) (operand sort : OneBased.Ref)
    (operandType advertisedType : OneBased.EmptyTy)
    (operandTerm : OneBased.EmptyTm)
    (lookup : OneBased.Ref → Option OneBased.Value)
    (foreign : OneBased.ImportId → OneBased.Ref → Option OneBased.Value)
    (operandFound : lookup operand = some (.term operandType operandTerm))
    (sortFound : lookup sort = some (.family .star advertisedType)) :
    OneBased.elaborateExpr lookup foreign (some sort) (.op1 op operand) =
      some (.term advertisedType (op.lower operandTerm)) := by
  simp [OneBased.elaborateExpr, operandFound, sortFound]

theorem elaborate_op2
    (op : Builtin.Op2) (left right sort : OneBased.Ref)
    (leftType rightType advertisedType : OneBased.EmptyTy)
    (leftTerm rightTerm : OneBased.EmptyTm)
    (lookup : OneBased.Ref → Option OneBased.Value)
    (foreign : OneBased.ImportId → OneBased.Ref → Option OneBased.Value)
    (leftFound : lookup left = some (.term leftType leftTerm))
    (rightFound : lookup right = some (.term rightType rightTerm))
    (sortFound : lookup sort = some (.family .star advertisedType)) :
    OneBased.elaborateExpr lookup foreign (some sort) (.op2 op left right) =
      some (.term advertisedType
        (op.lower leftTerm rightTerm)) := by
  simp [OneBased.elaborateExpr, leftFound, rightFound, sortFound]

/-- Kernel well-formedness of a resolved opcode is exactly typing of the
canonical opcode-free expansion at its advertised classifier. -/
theorem op1_wellFormed_iff (op : Builtin.Op1)
    (operand : OneBased.EmptyTm) (type : OneBased.EmptyTy) :
    OneBased.Value.WellFormed (.term type (op.lower operand)) ↔
      Nucleus.HolE.Named.HasTypeConv (.nil : TyScope [])
        (.nil : TmScope OneBased.ArenaSig 0) Nucleus.HolE.emptyBound
        (op.lower operand).toHolE type.toHolE := Iff.rfl

theorem op2_wellFormed_iff (op : Builtin.Op2)
    (left right : OneBased.EmptyTm) (type : OneBased.EmptyTy) :
    OneBased.Value.WellFormed
      (.term type (op.lower left right)) ↔
      Nucleus.HolE.Named.HasTypeConv (.nil : TyScope [])
        (.nil : TmScope OneBased.ArenaSig 0) Nucleus.HolE.emptyBound
        (op.lower left right).toHolE type.toHolE := Iff.rfl

/-- Evaluation is inherited from the canonical expansion reconstructed by the
actual arena resolver. -/
theorem op1_eval_iff_lower
    (op : Builtin.Op1) (operand : Tm EmptySig) :
    Nucleus.Hol.Ethane.Eval typeScope termScope typeEnv Γ boundEnv
      (op.lower operand) type semantic value ↔
    Nucleus.Hol.Ethane.Eval typeScope termScope typeEnv Γ boundEnv
      (.app Builtin.Init.not operand) type semantic value := by
  cases op
  rfl

theorem op2_eval_iff_lower
    (op : Builtin.Op2) (left right : Tm EmptySig) :
    Nucleus.Hol.Ethane.Eval typeScope termScope typeEnv Γ boundEnv
      (op.lower left right) type semantic value ↔
    Nucleus.Hol.Ethane.Eval typeScope termScope typeEnv Γ boundEnv
      (match op with
        | .and => .app (.app Builtin.Init.and left) right
        | .or => .app (.app Builtin.Init.or left) right
        | .imp => .app (.app Builtin.Init.imp left) right)
      type semantic value := by
  cases op <;> rfl

/-! ## Executable structural comparison on production expressions -/

def sameOpcodeHead : OneBased.detail.Expr → OneBased.detail.Expr → Bool
  | .op1 left _, .op1 right _ => left == right
  | .op2 left _ _, .op2 right _ _ => left == right
  | _, _ => false

theorem sameOpcodeHead_sound {left right : OneBased.detail.Expr}
    (same : sameOpcodeHead left right = true) :
    (∃ op leftOperand rightOperand,
        left = .op1 op leftOperand ∧ right = .op1 op rightOperand) ∨
      ∃ op leftA leftB rightA rightB,
        left = .op2 op leftA leftB ∧ right = .op2 op rightA rightB := by
  cases left <;> cases right <;>
    simp_all [sameOpcodeHead] <;>
    first | exact Or.inl ⟨_, _, _, rfl, rfl⟩ | exact Or.inr ⟨_, _, _, _, _, rfl, rfl⟩

theorem same_op1_lower {left right : OneBased.EmptyTm}
    (equal : left = right) :
    Builtin.Op1.lower op left = Builtin.Op1.lower op right := by
  cases equal
  rfl

theorem same_op2_lower {left left' right right' : OneBased.EmptyTm}
    (leftEqual : left = left') (rightEqual : right = right') :
    Builtin.Op2.lower op left right = Builtin.Op2.lower op left' right' := by
  cases leftEqual
  cases rightEqual
  rfl

end Nucleus.Hol.Ethane.LogicalOpcode
