import Nucleus.Cbor.Wire
import Nucleus.Hol.Ethane.Logic

/-!
# Ethane compact builtin wire contract, version 1

This is an executable mirror of `crates/logic/hol/builtins-v1.tsv`. It is not
part of the opcode-free init signature. The version is carried in the row tag,
and the numeric code is the `val` field; `ixs` remains ordered left-to-right.
Version 1 also assigns the numeric families `num1` and `num2`. They are
separate from the Boolean `op1` and `op2` because the kernel can type a
Boolean opcode directly but cannot type a numeric one until the init slice
defines `nat` and `int`. Byte operations are still not reserved.
-/

namespace Nucleus.Hol.Ethane.Builtin

set_option relaxedAutoImplicit true
set_option maxRecDepth 100000
set_option linter.style.nativeDecide false

def version : Nat := 1
def op1RowTag : String := "tm.op1.v1"
def op2RowTag : String := "tm.op2.v1"
def num1RowTag : String := "tm.num1.v1"
def num2RowTag : String := "tm.num2.v1"

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
  /-- The value the operation takes where mathematics gives none. -/
  total : String
  deriving DecidableEq, Repr

/-- The complete v1 registry. Unlisted codes are reserved. -/
def registry : List RegistryEntry := [
  ⟨"op1", 0, "not", ["bool"], "bool", "-"⟩,
  ⟨"op2", 0, "and", ["bool", "bool"], "bool", "-"⟩,
  ⟨"op2", 1, "or", ["bool", "bool"], "bool", "-"⟩,
  ⟨"op2", 2, "imp", ["bool", "bool"], "bool", "-"⟩,
  ⟨"num1", 0, "nat.succ", ["nat"], "nat", "-"⟩,
  ⟨"num1", 1, "nat.pred", ["nat"], "nat", "zero"⟩,
  ⟨"num1", 2, "int.succ", ["int"], "int", "-"⟩,
  ⟨"num1", 3, "int.pred", ["int"], "int", "-"⟩,
  ⟨"num1", 4, "int.abs", ["int"], "nat", "-"⟩,
  ⟨"num1", 5, "int.sign", ["int"], "int", "-"⟩,
  ⟨"num1", 6, "nat.to_int", ["nat"], "int", "-"⟩,
  ⟨"num1", 7, "int.to_nat.zigzag", ["int"], "nat", "-"⟩,
  ⟨"num1", 8, "nat.to_int.zigzag", ["nat"], "int", "-"⟩,
  ⟨"num1", 9, "int.neg", ["int"], "int", "-"⟩,
  ⟨"num2", 0, "nat.add", ["nat", "nat"], "nat", "-"⟩,
  ⟨"num2", 1, "nat.sub", ["nat", "nat"], "nat", "zero"⟩,
  ⟨"num2", 2, "nat.mul", ["nat", "nat"], "nat", "-"⟩,
  ⟨"num2", 3, "nat.div", ["nat", "nat"], "nat", "zero"⟩,
  ⟨"num2", 4, "nat.mod", ["nat", "nat"], "nat", "dividend"⟩,
  ⟨"num2", 5, "nat.le", ["nat", "nat"], "bool", "-"⟩,
  ⟨"num2", 6, "nat.lt", ["nat", "nat"], "bool", "-"⟩,
  ⟨"num2", 7, "int.add", ["int", "int"], "int", "-"⟩,
  ⟨"num2", 8, "int.sub", ["int", "int"], "int", "-"⟩,
  ⟨"num2", 9, "int.mul", ["int", "int"], "int", "-"⟩,
  ⟨"num2", 10, "int.div", ["int", "int"], "int", "zero"⟩,
  ⟨"num2", 11, "int.mod", ["int", "int"], "int", "dividend"⟩,
  ⟨"num2", 12, "int.le", ["int", "int"], "bool", "-"⟩,
  ⟨"num2", 13, "int.lt", ["int", "int"], "bool", "-"⟩]

example : registrySource =
    "# Ethane compact builtin registry v1. This is syntax, not the init manifest.\n" ++
    "# Families are grouped by arity and by whether the kernel can type them:\n" ++
    "# op1/op2 are the Boolean connectives; num1/num2 are numeric and are rejected\n" ++
    "# until the init slice defines nat and int. The total column gives the value a\n" ++
    "# partial operation takes, since Ethane has no partiality.\n" ++
    "# version\tfamily\tcode\tname\toperands\tresult\ttotal\n" ++
    "1\top1\t0\tnot\tbool\tbool\t-\n" ++
    "1\top2\t0\tand\tbool,bool\tbool\t-\n" ++
    "1\top2\t1\tor\tbool,bool\tbool\t-\n" ++
    "1\top2\t2\timp\tbool,bool\tbool\t-\n" ++
    "1\tnum1\t0\tnat.succ\tnat\tnat\t-\n" ++
    "1\tnum1\t1\tnat.pred\tnat\tnat\tzero\n" ++
    "1\tnum1\t2\tint.succ\tint\tint\t-\n" ++
    "1\tnum1\t3\tint.pred\tint\tint\t-\n" ++
    "1\tnum1\t4\tint.abs\tint\tnat\t-\n" ++
    "1\tnum1\t5\tint.sign\tint\tint\t-\n" ++
    "1\tnum1\t6\tnat.to_int\tnat\tint\t-\n" ++
    "1\tnum1\t7\tint.to_nat.zigzag\tint\tnat\t-\n" ++
    "1\tnum1\t8\tnat.to_int.zigzag\tnat\tint\t-\n" ++
    "1\tnum1\t9\tint.neg\tint\tint\t-\n" ++
    "1\tnum2\t0\tnat.add\tnat,nat\tnat\t-\n" ++
    "1\tnum2\t1\tnat.sub\tnat,nat\tnat\tzero\n" ++
    "1\tnum2\t2\tnat.mul\tnat,nat\tnat\t-\n" ++
    "1\tnum2\t3\tnat.div\tnat,nat\tnat\tzero\n" ++
    "1\tnum2\t4\tnat.mod\tnat,nat\tnat\tdividend\n" ++
    "1\tnum2\t5\tnat.le\tnat,nat\tbool\t-\n" ++
    "1\tnum2\t6\tnat.lt\tnat,nat\tbool\t-\n" ++
    "1\tnum2\t7\tint.add\tint,int\tint\t-\n" ++
    "1\tnum2\t8\tint.sub\tint,int\tint\t-\n" ++
    "1\tnum2\t9\tint.mul\tint,int\tint\t-\n" ++
    "1\tnum2\t10\tint.div\tint,int\tint\tzero\n" ++
    "1\tnum2\t11\tint.mod\tint,int\tint\tdividend\n" ++
    "1\tnum2\t12\tint.le\tint,int\tbool\t-\n" ++
    "1\tnum2\t13\tint.lt\tint,int\tbool\t-\n" := by native_decide

/-- The TSV spelling of one entry. -/
def RegistryEntry.line (entry : RegistryEntry) : String :=
  s!"{version}\t{entry.family}\t{entry.code.toNat}\t{entry.name}\t" ++
    String.intercalate "," entry.operands ++ s!"\t{entry.result}\t{entry.total}"

/-- The structured registry agrees with the file line for line, so the two
cannot drift apart while both still parse. -/
example : registry.map RegistryEntry.line =
    (registrySource.splitOn "\n").filter
      (fun line => !line.startsWith "#" && line ≠ "") := by
  native_decide


inductive Op1 where
  | not
  deriving DecidableEq, Repr

namespace Op1

def code : Op1 → UInt8
  | .not => 0

def ofCode? : UInt8 → Option Op1
  | 0 => some .not
  | _ => none

def ofUInt64? (value : UInt64) : Option Op1 :=
  if value.toNat < 256 then ofCode? value.toUInt8 else none

@[simp] theorem ofCode?_code (op : Op1) : ofCode? op.code = some op := by
  cases op
  rfl

@[simp] theorem ofUInt64?_code (op : Op1) : ofUInt64? op.code.toUInt64 = some op := by
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

def ofUInt64? (value : UInt64) : Option Op2 :=
  if value.toNat < 256 then ofCode? value.toUInt8 else none

@[simp] theorem ofCode?_code (op : Op2) : ofCode? op.code = some op := by
  cases op <;> rfl

@[simp] theorem ofUInt64?_code (op : Op2) : ofUInt64? op.code.toUInt64 = some op := by
  cases op <;> rfl

end Op2

inductive Num1 where
  | natSucc
  | natPred
  | intSucc
  | intPred
  | intAbs
  | intSign
  | natToInt
  | intToNatZigzag
  | natToIntZigzag
  | intNeg
  deriving DecidableEq, Repr

namespace Num1

def code : Num1 → UInt8
  | .natSucc => 0
  | .natPred => 1
  | .intSucc => 2
  | .intPred => 3
  | .intAbs => 4
  | .intSign => 5
  | .natToInt => 6
  | .intToNatZigzag => 7
  | .natToIntZigzag => 8
  | .intNeg => 9

def ofCode? : UInt8 → Option Num1
  | 0 => some .natSucc
  | 1 => some .natPred
  | 2 => some .intSucc
  | 3 => some .intPred
  | 4 => some .intAbs
  | 5 => some .intSign
  | 6 => some .natToInt
  | 7 => some .intToNatZigzag
  | 8 => some .natToIntZigzag
  | 9 => some .intNeg
  | _ => none

def ofUInt64? (value : UInt64) : Option Num1 :=
  if value.toNat < 256 then ofCode? value.toUInt8 else none

@[simp] theorem ofCode?_code (op : Num1) : ofCode? op.code = some op := by
  cases op <;> rfl

@[simp] theorem ofUInt64?_code (op : Num1) : ofUInt64? op.code.toUInt64 = some op := by
  cases op <;> rfl

end Num1

inductive Num2 where
  | natAdd
  | natSub
  | natMul
  | natDiv
  | natMod
  | natLe
  | natLt
  | intAdd
  | intSub
  | intMul
  | intDiv
  | intMod
  | intLe
  | intLt
  deriving DecidableEq, Repr

namespace Num2

def code : Num2 → UInt8
  | .natAdd => 0
  | .natSub => 1
  | .natMul => 2
  | .natDiv => 3
  | .natMod => 4
  | .natLe => 5
  | .natLt => 6
  | .intAdd => 7
  | .intSub => 8
  | .intMul => 9
  | .intDiv => 10
  | .intMod => 11
  | .intLe => 12
  | .intLt => 13

def ofCode? : UInt8 → Option Num2
  | 0 => some .natAdd
  | 1 => some .natSub
  | 2 => some .natMul
  | 3 => some .natDiv
  | 4 => some .natMod
  | 5 => some .natLe
  | 6 => some .natLt
  | 7 => some .intAdd
  | 8 => some .intSub
  | 9 => some .intMul
  | 10 => some .intDiv
  | 11 => some .intMod
  | 12 => some .intLe
  | 13 => some .intLt
  | _ => none

def ofUInt64? (value : UInt64) : Option Num2 :=
  if value.toNat < 256 then ofCode? value.toUInt8 else none

@[simp] theorem ofCode?_code (op : Num2) : ofCode? op.code = some op := by
  cases op <;> rfl

@[simp] theorem ofUInt64?_code (op : Num2) : ofUInt64? op.code.toUInt64 = some op := by
  cases op <;> rfl

end Num2

/-! ## Exact opcode-free init definitions

These terms transcribe `theories/init-boolean.checked.json` constructor for
constructor. Lowering retains the two applications made by Rust; beta
contraction is a separate conversion fact, not part of macro expansion.
-/

namespace Init

def boolToBool : Ty Sig Nat := .arr .boolTy .boolTy
def boolToBoolToBool : Ty Sig Nat := .arr .boolTy boolToBool

def truth : Tm Sig Nat :=
  let x : Tm Sig Nat := .tmFv 0 .boolTy
  let identity : Tm Sig Nat := .lam 0 .boolTy x
  .eq boolToBool identity identity

def falsehood : Tm Sig Nat :=
  let x : Tm Sig Nat := .tmFv 1 .boolTy
  let identity : Tm Sig Nat := .lam 1 .boolTy x
  let constantTrue : Tm Sig Nat := .lam 2 .boolTy truth
  .eq boolToBool identity constantTrue

def not : Tm Sig Nat :=
  let x : Tm Sig Nat := .tmFv 3 .boolTy
  .lam 3 .boolTy (.eq .boolTy x falsehood)

def and : Tm Sig Nat :=
  let p : Tm Sig Nat := .tmFv 4 .boolTy
  let q : Tm Sig Nat := .tmFv 5 .boolTy
  let body : Tm Sig Nat := .eq .boolTy (.eq .boolTy p q) q
  .lam 4 .boolTy (.lam 5 .boolTy body)

def or : Tm Sig Nat :=
  let p : Tm Sig Nat := .tmFv 6 .boolTy
  let q : Tm Sig Nat := .tmFv 7 .boolTy
  let body : Tm Sig Nat := .eq .boolTy (.eq .boolTy p q) p
  .lam 6 .boolTy (.lam 7 .boolTy body)

def imp : Tm Sig Nat :=
  let p : Tm Sig Nat := .tmFv 8 .boolTy
  let q : Tm Sig Nat := .tmFv 9 .boolTy
  let body : Tm Sig Nat := .eq .boolTy (.eq .boolTy p truth) q
  .lam 8 .boolTy (.lam 9 .boolTy body)

end Init

def Op1.lower (op : Op1) (operand : Tm Sig Nat) : Tm Sig Nat :=
  match op with
  | .not => .app Init.not operand

def Op2.lower (op : Op2) (left right : Tm Sig Nat) : Tm Sig Nat :=
  let definition := match op with
    | .and => Init.and
    | .or => Init.or
    | .imp => Init.imp
  .app (.app definition left) right

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
    0xa3, 0x63, 0x69, 0x78, 0x73, 0x81, 0x01, 0x63, 0x74, 0x61, 0x67, 0x69,
    0x74, 0x6d, 0x2e, 0x6f, 0x70, 0x31, 0x2e, 0x76, 0x31, 0x63, 0x76, 0x61,
    0x6c, 0x00]) := by native_decide

example : Nucleus.CborWire.deterministic? (op2Row .imp 1 2) = some (wire [
    0xa3, 0x63, 0x69, 0x78, 0x73, 0x82, 0x01, 0x02, 0x63, 0x74, 0x61, 0x67,
    0x69, 0x74, 0x6d, 0x2e, 0x6f, 0x70, 0x32, 0x2e, 0x76, 0x31, 0x63, 0x76,
    0x61, 0x6c, 0x02]) := by native_decide

example : Op1.ofCode? 1 = none := rfl
example : Op1.ofCode? 255 = none := rfl
example : Op2.ofCode? 3 = none := rfl
example : Op2.ofCode? 255 = none := rfl

end Nucleus.Hol.Ethane.Builtin
