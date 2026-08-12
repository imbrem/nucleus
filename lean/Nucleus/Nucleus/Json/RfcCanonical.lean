import Nucleus.Json.RfcParser
import Nucleus.Json.Equiv

/-!
# Canonical RFC JSON text

`RfcJsonAtom.number` deliberately retains an arbitrary source lexeme, so not
every inhabitant is printable as RFC JSON (for example, `.number "01"`).  The
canonicalizer is consequently checked and partial: it emits the unique compact,
key-sorted spelling exactly when parsing that spelling recovers the input.
-/

namespace Nucleus.RfcJson

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

private def escapeChar (c : Char) : List Char :=
  match c with
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | '\n' => ['\\', 'n']
  | '\r' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | c =>
      if c.toNat < 0x20 then
        ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
      else [c]

/-- Quote decoded string contents using a deterministic minimal JSON escape
policy (with the remaining control characters written as lowercase `\u00xx`). -/
def quote (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap escapeChar) ++ "\""

private def renderScalar : RfcJsonScalar → String
  | none => "null"
  | some (.bool true) => "true"
  | some (.bool false) => "false"
  | some (.string s) => quote s
  | some (.number literal) => literal

mutual
  private def renderRaw : RawJson RfcJsonScalar → String
    | .scalar value => renderScalar value
    | .list values => "[" ++ renderArray values ++ "]"
    | .map entries => "{" ++ renderObject entries ++ "}"

  private def renderArray : RawSyn String RfcJsonScalar .arr → String
    | .nil => ""
    | .cons value .nil => renderRaw value
    | .cons value rest => renderRaw value ++ "," ++ renderArray rest

  private def renderObject : RawSyn String RfcJsonScalar .obj → String
    | .objNil => ""
    | .objCons key value .objNil => quote key ++ ":" ++ renderRaw value
    | .objCons key value rest => quote key ++ ":" ++ renderRaw value ++ "," ++ renderObject rest
end

/-- The deterministic compact, key-sorted candidate spelling of an RFC JSON
value.  It is exposed separately so callers can inspect why an ill-formed
number lexeme was rejected by `canonical?`. -/
def canonicalCandidate (json : RfcJson) : String := renderRaw json.toRaw

/-- Return canonical RFC JSON text exactly when the candidate parses back to
the same extensional value.  Partiality is necessary because the unrefined
number-lexeme type also contains strings outside the RFC number grammar. -/
def canonical? (json : RfcJson) : Option String :=
  let text := canonicalCandidate json
  if parse? text = some json then some text else none

/-- Every admitted canonical spelling round-trips semantically through the RFC
parser. -/
theorem parse_canonical?_eq {json : RfcJson} {text : String}
    (h : canonical? json = some text) : parse? text = some json := by
  simp only [canonical?, canonicalCandidate] at h
  split at h
  next hp => simpa using hp
  next => simp at h

/-- Semantic round-tripping makes canonical text syntactically stable: parsing
an admitted output and canonicalizing again returns exactly the same string. -/
theorem canonical?_roundtrip {json : RfcJson} {text : String}
    (h : canonical? json = some text) : (parse? text).bind canonical? = some text := by
  rw [parse_canonical?_eq h]
  exact h

set_option linter.style.nativeDecide false in
example : canonical? (.scalar (.string "a\n\"b")) = some "\"a\\n\\\"b\"" := by native_decide

set_option linter.style.nativeDecide false in
example : canonical? (.scalar (.number "01")) = none := by native_decide

end Nucleus.RfcJson
