import Nucleus.Cbor.Containers

/-!
# Ethane compact builtin wire contract, version 1

This is an executable mirror of `crates/logic/hol/builtins-v1.tsv`. It is not
part of the opcode-free init signature. The version is carried in the row tag,
and the numeric code is the `val` field; `ixs` remains ordered left-to-right.
Natural and byte operations are intentionally not reserved by this version.
-/

namespace Nucleus.Hol.Ethane.Builtin

def version : Nat := 1
def op1RowTag : String := "tm.op1.v1"
def op2RowTag : String := "tm.op2.v1"

inductive Op1 where
  | not
  deriving DecidableEq, Repr

namespace Op1

def code : Op1 → UInt8
  | .not => 0

def ofCode? : UInt8 → Option Op1
  | 0 => some .not
  | _ => none

@[simp] theorem ofCode?_code (op : Op1) : ofCode? op.code = some op := by
  cases op
  rfl

end Op1

inductive Op2 where
  | and
  | or
  | imp
  deriving DecidableEq, Repr

namespace Op2

def code : Op2 → UInt8
  | .and => 0
  | .or => 1
  | .imp => 2

def ofCode? : UInt8 → Option Op2
  | 0 => some .and
  | 1 => some .or
  | 2 => some .imp
  | _ => none

@[simp] theorem ofCode?_code (op : Op2) : ofCode? op.code = some op := by
  cases op <;> rfl

end Op2

private def text (value : String) : Nucleus.Cbor := .primitive (.text value)
private def unsigned (value : UInt8) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned value.toUInt64))
private def reference (value : Nat) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned (UInt64.ofNat value)))
private def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  Nucleus.Cbor.arrayOfList values

/-- The semantic CBOR row agreed with Rust before syntax constructors land. -/
def op1Row (op : Op1) (operand : Nat) : Nucleus.Cbor :=
  Nucleus.Cbor.mapOfList [
    (text "tag", text op1RowTag),
    (text "ixs", array [reference operand]),
    (text "val", unsigned op.code)]

/-- Binary operand order is left, then right. -/
def op2Row (op : Op2) (left right : Nat) : Nucleus.Cbor :=
  Nucleus.Cbor.mapOfList [
    (text "tag", text op2RowTag),
    (text "ixs", array [reference left, reference right]),
    (text "val", unsigned op.code)]

example : Op1.ofCode? 1 = none := rfl
example : Op1.ofCode? 255 = none := rfl
example : Op2.ofCode? 3 = none := rfl
example : Op2.ofCode? 255 = none := rfl

end Nucleus.Hol.Ethane.Builtin
