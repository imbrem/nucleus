import Nucleus.Cbor.Wire

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

/-- The registry source is included at elaboration, so Lean cannot silently
drift from the TSV reviewed by Rust. -/
def registrySource : String :=
  include_str ".."/".."/".."/".."/".."/"crates"/"logic"/"hol"/"builtins-v1.tsv"

/-- One row of the finite v1 registry, matching `builtins-v1.tsv`. -/
structure RegistryEntry where
  family : String
  code : UInt8
  name : String
  operands : List String
  result : String
  deriving DecidableEq, Repr

/-- The complete v1 registry. Unlisted codes are reserved. -/
def registry : List RegistryEntry := [
  ⟨"op1", 0, "not", ["bool"], "bool"⟩,
  ⟨"op2", 0, "and", ["bool", "bool"], "bool"⟩,
  ⟨"op2", 1, "or", ["bool", "bool"], "bool"⟩,
  ⟨"op2", 2, "imp", ["bool", "bool"], "bool"⟩]

example : registrySource =
    "# Ethane compact builtin registry v1. This is syntax, not the init manifest.\n# version\tfamily\tcode\tname\toperands\tresult\n1\top1\t0\tnot\tbool\tbool\n1\top2\t0\tand\tbool,bool\tbool\n1\top2\t1\tor\tbool,bool\tbool\n1\top2\t2\timp\tbool,bool\tbool\n" := rfl

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

/-- A decoded compact row envelope. Core arena rows use their existing decoder. -/
inductive Row where
  | op1 (op : Op1) (operand : Nat)
  | op2 (op : Op2) (left right : Nat)
  deriving DecidableEq, Repr

/-- Decode a versioned tag only when its opcode and operand arity are exact. -/
def decodeRow? (tag : String) (ixs : List Nat) (code : UInt8) : Option Row :=
  if tag = op1RowTag then
    match ixs, Op1.ofCode? code with
    | [operand], some op => some (.op1 op operand)
    | _, _ => none
  else if tag = op2RowTag then
    match ixs, Op2.ofCode? code with
    | [left, right], some op => some (.op2 op left right)
    | _, _ => none
  else none

@[simp] theorem decode_op1 (op : Op1) (operand : Nat) :
    decodeRow? op1RowTag [operand] op.code = some (.op1 op operand) := by
  cases op
  simp [decodeRow?, op1RowTag]

@[simp] theorem decode_op2 (op : Op2) (left right : Nat) :
    decodeRow? op2RowTag [left, right] op.code = some (.op2 op left right) := by
  cases op <;> simp [decodeRow?, op1RowTag, op2RowTag]

example : decodeRow? op1RowTag [1, 2] 0 = none := by
  simp [decodeRow?, op1RowTag]

example : decodeRow? op2RowTag [1] 0 = none := by
  simp [decodeRow?, op1RowTag, op2RowTag]

example : decodeRow? op1RowTag [1] 1 = none := by
  simp [decodeRow?, op1RowTag, Op1.ofCode?]

example : decodeRow? op2RowTag [1, 2] 3 = none := by
  simp [decodeRow?, op1RowTag, op2RowTag, Op2.ofCode?]

example : decodeRow? "tm.op1.v2" [1] 0 = none := by
  simp [decodeRow?, op1RowTag, op2RowTag]

-- Cross-language semantic wire goldens. Rust additionally freezes their exact
-- canonical CBOR bytes; these equalities freeze Lean's map shape and order.
example : op1Row .not 1 =
    Nucleus.Cbor.mapOfList [
      (text "tag", text "tm.op1.v1"),
      (text "ixs", array [reference 1]),
      (text "val", unsigned 0)] := rfl

example : op2Row .imp 1 2 =
    Nucleus.Cbor.mapOfList [
      (text "tag", text "tm.op2.v1"),
      (text "ixs", array [reference 1, reference 2]),
      (text "val", unsigned 2)] := rfl

private def wire (xs : List UInt8) : Nucleus.Bytes := ⟨xs.toByteArray⟩

example : Nucleus.CborWire.deterministic? (op1Row .not 1) = some (wire [
    0xa3, 0x63, 0x74, 0x61, 0x67, 0x69, 0x74, 0x6d, 0x2e, 0x6f, 0x70, 0x31,
    0x2e, 0x76, 0x31, 0x63, 0x69, 0x78, 0x73, 0x81, 0x01, 0x63, 0x76, 0x61,
    0x6c, 0x00]) := by native_decide

example : Nucleus.CborWire.deterministic? (op2Row .imp 1 2) = some (wire [
    0xa3, 0x63, 0x74, 0x61, 0x67, 0x69, 0x74, 0x6d, 0x2e, 0x6f, 0x70, 0x32,
    0x2e, 0x76, 0x31, 0x63, 0x69, 0x78, 0x73, 0x82, 0x01, 0x02, 0x63, 0x76,
    0x61, 0x6c, 0x02]) := by native_decide

example : Op1.ofCode? 1 = none := rfl
example : Op1.ofCode? 255 = none := rfl
example : Op2.ofCode? 3 = none := rfl
example : Op2.ofCode? 255 = none := rfl

end Nucleus.Hol.Ethane.Builtin
