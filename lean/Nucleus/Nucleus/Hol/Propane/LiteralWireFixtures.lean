import Nucleus.Hol.Propane.LiteralEncoding
import Lean.Data.Json.Parser

/-! Executable cross-language numeric payload vectors. These are tests, not
a substitute for the representation-independence and carrier theorems. -/

namespace Nucleus.Hol.Propane.LiteralWire

private def fixtures : String :=
  include_str "../../../../../crates/logic/hol/literal-wire.json"

private def checkFixture (entry : Lean.Json) : Except String Bool := do
  let fields ← entry.getArr?
  unless fields.size = 3 do throw "expected three fixture fields"
  let tag ← fields[0]!.getStr?
  let bytes ← (← fields[1]!.getArr?).toList.mapM fun value => do
    let value ← value.getNat?
    if value < 256 then pure (UInt8.ofNat value) else throw "invalid octet"
  let constant ← match tag with
    | "nat" => pure (RawConstant.nat bytes)
    | "int" => pure (RawConstant.int bytes)
    | _ => throw "unknown numeric fixture tag"
  let decoded := decodeConstant constant
  let actual := decoded.bind fun value => match value with
    | .nat value => some (toString value)
    | .int value => some (toString value)
    | _ => none
  let expected ← if fields[2]!.isNull then pure none else
    some <$> fields[2]!.getStr?
  let encodingMatches := match decoded with
    | some (.nat value) => LiteralEncoding.encodeNat value == bytes
    | some (.int value) => LiteralEncoding.encodeInt value == bytes
    | none => true
    | _ => false
  pure (actual == expected && encodingMatches)

private def checkFixtures : Except String Bool := do
  let entries ← (← Lean.Json.parse fixtures).getArr?
  let results ← entries.toList.mapM checkFixture
  pure (results.all id)

set_option linter.hashCommand false in
#eval (match checkFixtures with
  | .ok true => pure ()
  | .ok false => throw (IO.userError "literal payload fixture mismatch")
  | .error message => throw (IO.userError message) : IO Unit)

end Nucleus.Hol.Propane.LiteralWire
