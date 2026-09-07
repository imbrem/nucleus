import Nucleus.Hol.Propane.Builtin
import Lean.Data.Json.Parser

/-!
# Shared Rust/Lean builtin validation

The fixture format uses Rust's serialized builtin descriptor and explicit
literal types. Parsing here is untrusted test infrastructure. Every vector
checks the full signature as well as the result or undefined outcome.
-/

namespace Nucleus.Hol.Propane.BuiltinFixtures

open Lean

private def tagged (json : Json) : Except String (String × List Json) := do
  match json with
  | .str name => return (name, [])
  | .obj fields => match fields.toList with
      | [(name, .arr arguments)] => return (name, arguments.toList)
      | [(name, argument)] => return (name, [argument])
      | _ => throw "expected one tagged constructor"
  | _ => throw "expected builtin constructor"

private def width (json : Json) : Except String Width := do
  match ← json.getStr? with
  | "W8" => return .i8 | "W16" => return .i16
  | "W32" => return .i32 | "W64" => return .i64
  | _ => throw "unknown word width"

private def endian (json : Json) : Except String Endian := do
  match ← json.getStr? with
  | "Little" => return .little | "Big" => return .big
  | _ => throw "unknown endian"

private def named {α : Type} (names : List (String × α)) (name : String) : Except String α :=
  match names.lookup name with
  | some value => .ok value
  | none => .error s!"unknown operation {name}"

private def wordOp (json : Json) : Except String WordOp := do
  let (name, args) ← tagged json
  if name = "ExtendSign" then
    match args with
    | [arg] => return .extendSign (← width arg)
    | _ => throw "invalid sign extension"
  else
    unless args.isEmpty do throw "unexpected word operation parameters"
    named [
      ("Add", .add), ("Sub", .sub), ("Mul", .mul), ("DivU", .divU), ("DivS", .divS),
      ("RemU", .remU), ("RemS", .remS), ("And", .and), ("Or", .or), ("Xor", .xor),
      ("Not", .not), ("Shl", .shl), ("ShrU", .shrU), ("ShrS", .shrS),
      ("Rotl", .rotl), ("Rotr", .rotr), ("Clz", .clz), ("Ctz", .ctz), ("Popcnt", .popcnt),
      ("Eqz", .eqz), ("Eq", .eq), ("Ne", .ne), ("LtU", .ltU), ("LeU", .leU),
      ("GtU", .gtU), ("GeU", .geU), ("LtS", .ltS), ("LeS", .leS),
      ("GtS", .gtS), ("GeS", .geS)] name

private def natOp (json : Json) : Except String NatOp := do
  named [
    ("Add", .add), ("Sub", .sub), ("Mul", .mul), ("Div", .div), ("Rem", .rem),
    ("Succ", .succ), ("Pred", .pred), ("Pow", .pow), ("Eq", .eq), ("Ne", .ne),
    ("Lt", .lt), ("Le", .le), ("Gt", .gt), ("Ge", .ge), ("Min", .min), ("Max", .max),
    ("And", .and), ("Or", .or), ("Xor", .xor), ("Shl", .shl), ("Shr", .shr)]
    (← json.getStr?)

private def intOp (json : Json) : Except String IntOp := do
  named [
    ("Add", .add), ("Sub", .sub), ("Mul", .mul), ("Div", .div), ("Rem", .rem),
    ("Succ", .succ), ("Pred", .pred), ("Neg", .neg), ("Abs", .abs), ("Pow", .pow),
    ("Eq", .eq), ("Ne", .ne), ("Lt", .lt), ("Le", .le), ("Gt", .gt), ("Ge", .ge),
    ("Min", .min), ("Max", .max), ("And", .and), ("Or", .or), ("Xor", .xor),
    ("Not", .not), ("Shl", .shl), ("Shr", .shr)] (← json.getStr?)

private def bytesOp (json : Json) : Except String BytesOp := do
  let (name, args) ← tagged json
  match args with
  | [] => named [
      ("Empty", .empty), ("Singleton", .singleton), ("Cons", .cons), ("Snoc", .snoc),
      ("Append", .append), ("Repeat", .repeat), ("Length", .length), ("Eq", .eq),
      ("Ne", .ne), ("Lt", .lt), ("Le", .le), ("Gt", .gt), ("Ge", .ge),
      ("Get", .get), ("Set", .set), ("Slice", .slice), ("Replace", .replace),
      ("Take", .take), ("Drop", .drop)] name
  | [bits, order] =>
      let bits ← width bits
      let order ← endian order
      named [("Encode", .encode bits order), ("Decode", .decode bits order),
        ("Read", .read bits order), ("Write", .write bits order)] name
  | _ => throw "invalid byte operation parameters"

private def castOp (json : Json) : Except String CastOp := do
  let (name, args) ← tagged json
  match args with
  | [] => named [("NatToInt", .natToInt), ("IntToNat", .intToNat)] name
  | [bits] =>
      let bits ← width bits
      named [("WordToNat", .wordToNat bits), ("WordToIntU", .wordToIntU bits),
        ("WordToIntS", .wordToIntS bits), ("NatToWord", .natToWord bits),
        ("IntToWordU", .intToWordU bits), ("IntToWordS", .intToWordS bits),
        ("NatToWordWrap", .natToWordWrap bits), ("IntToWordWrap", .intToWordWrap bits)] name
  | [source, target] =>
      let source ← width source
      let target ← width target
      named [("WordWrap", .wordWrap source target),
        ("WordZeroExtend", .wordZeroExtend source target),
        ("WordSignExtend", .wordSignExtend source target)] name
  | _ => throw "invalid cast parameters"

private def builtin (json : Json) : Except String Builtin := do
  let (name, args) ← tagged json
  match name, args with
  | "Word", [bits, op] => return .word (← width bits) (← wordOp op)
  | "Nat", [op] => return .nat (← natOp op)
  | "Int", [op] => return .int (← intOp op)
  | "Bytes", [op] => return .bytes (← bytesOp op)
  | "Cast", [op] => return .cast (← castOp op)
  | _, _ => throw "invalid builtin descriptor"

private def literalType (name : String) : Except String LiteralTy :=
  named [("bool", .bool), ("i8", .word .i8), ("i16", .word .i16),
    ("i32", .word .i32), ("i64", .word .i64), ("nat", .nat), ("int", .int),
    ("bytes", .bytes)] name

private def natural (json : Json) : Except String Nat := do
  match (← json.getStr?).toNat? with
  | some value => return value
  | none => throw "invalid natural decimal"

private def integer (json : Json) : Except String Int := do
  match (← json.getStr?).toInt? with
  | some value => return value
  | none => throw "invalid integer decimal"

private def literal (json : Json) : Except String LiteralValue := do
  let pair ← json.getArr?
  unless pair.size = 2 do throw "expected a typed value pair"
  let type ← literalType (← pair[0]!.getStr?)
  let value := pair[1]!
  match type with
  | .bool => return .bool (← value.getBool?)
  | .word width =>
      let number ← natural value
      unless number < 2 ^ width.bits do throw "word bit pattern out of range"
      return .word width (BitVec.ofNat width.bits number)
  | .nat => return .nat (← natural value)
  | .int => return .int (← integer value)
  | .bytes =>
      let bytes ← (← value.getArr?).toList.mapM fun byte => do
        let number ← byte.getNat?
        unless number < 256 do throw "invalid octet"
        return UInt8.ofNat number
      return .bytes bytes

def checkFixture (entry : Json) : Except String Unit := do
  let descriptor ← entry.getObjVal? "op"
  let op ← builtin descriptor
  let args ← (← (← entry.getObjVal? "args").getArr?).toList.mapM literal
  let result ← entry.getObjVal? "result"
  let expected ← if result.isNull then pure none else some <$> literal result
  let inputs ← (← (← entry.getObjVal? "inputs").getArr?).toList.mapM fun type => do
    literalType (← type.getStr?)
  let output ← literalType (← (← entry.getObjVal? "output").getStr?)
  unless op.signature = some (inputs, output) do
    throw s!"signature mismatch: {descriptor.compress}"
  let actual := op.eval args
  unless actual = expected do
    throw (s!"evaluation mismatch: {descriptor.compress}; " ++
      s!"expected {repr expected}, got {repr actual}")

def checkFixtures (source : String) : Except String Nat := do
  let entries ← (← Json.parse source).getArr?
  entries.toList.forM checkFixture
  return entries.size

private def fixtures : String :=
  include_str "../../../../../crates/logic/hol/literal-vectors.json"

#eval match checkFixtures fixtures with
  | .ok count => IO.println s!"checked {count} shared builtin vectors"
  | .error message => throw (IO.userError message)

end Nucleus.Hol.Propane.BuiltinFixtures
