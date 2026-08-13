import Nucleus.SExpr.Parser
import Nucleus.Cbor.Bytes
import Nucleus.Json.RfcParser

/-! Typed atom vocabularies layered over the shared S-expression lexer. -/

namespace Nucleus

/-- The first richer atom vocabulary: unquoted symbols and decoded strings. -/
inductive StringSymbol where
  | symbol (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

/-- A Lisp-oriented vocabulary which additionally distinguishes keywords. -/
inductive KeywordSymbol where
  | symbol (value : String)
  | keyword (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

/-- A data-oriented atom vocabulary. Number spellings remain exact, just as in
`RfcJsonAtom`; byte strings use the compact `Bytes` representation. -/
inductive LiteralAtom where
  | symbol (value : String)
  | string (value : String)
  | number (literal : String)
  | bytes (value : Bytes)
  deriving DecidableEq

namespace SExprParser

/-!
`#hex#` is deliberately the sole byte syntax in this layer. It is unambiguous,
already used by the advanced S-expression format, and keeps vertical bars
available for a future Lisp-compatible quoted-symbol syntax. A `b"..."` syntax
would additionally have to specify whether ordinary characters are UTF-8 and
which of the text escapes denote individual octets.
-/

private def Lexeme.toStringSymbol : Lexeme → StringSymbol
  | .symbol value => .symbol value
  | .string value => .string value

/-- Parse while distinguishing unquoted symbols from decoded string literals. -/
def parseStringSymbol? (text : String) : Option (SExpr2 StringSymbol) :=
  SExpr2.map Lexeme.toStringSymbol <$> parseLexemes? text

private def keyword (value : String) : KeywordSymbol :=
  match value.toList with
  | ':' :: tail => if tail.isEmpty then .symbol value else .keyword (String.ofList tail)
  | _ => .symbol value

private def Lexeme.toKeywordSymbol : Lexeme → KeywordSymbol
  | .symbol value => keyword value
  | .string value => .string value

/-- Parse Common-Lisp-style colon-prefixed keywords separately from symbols. -/
def parseKeywordSymbol? (text : String) : Option (SExpr2 KeywordSymbol) :=
  SExpr2.map Lexeme.toKeywordSymbol <$> parseLexemes? text

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let high ← hexDigit? high
      let low ← hexDigit? low
      let tail ← decodeHexChars rest
      some (UInt8.ofNat (high * 16 + low) :: tail)
  | [_] => none

/-- Decode the RFC advanced-S-expression hexadecimal spelling `#...#`.
The payload must contain an even number of hexadecimal digits. -/
def decodeHexBytes? (literal : String) : Option Bytes := do
  let chars := literal.toList
  let body ← match chars with
    | '#' :: rest => match rest.reverse with
      | '#' :: reversedBody => some reversedBody.reverse
      | _ => none
    | _ => none
  let bytes ← decodeHexChars body
  some ⟨bytes.toByteArray⟩

private def numberLiteral? (value : String) : Option String :=
  match RfcJson.parse? value with
  | some (.scalar (some (.number literal))) => some literal
  | _ => none

private def Lexeme.toLiteralAtom? : Lexeme → Option LiteralAtom
  | .string value => some (.string value)
  | .symbol value =>
      match decodeHexBytes? value with
      | some bytes => some (.bytes bytes)
      | none =>
          if value.startsWith "#" && value.endsWith "#" then none
          else match numberLiteral? value with
            | some literal => some (.number literal)
            | none => some (.symbol value)

private def traverseAtoms (f : α → Option β) : SExpr2 α → Option (SExpr2 β)
  | .nil => some .nil
  | .atom value => .atom <$> f value
  | .cons car cdr => .cons <$> traverseAtoms f car <*> traverseAtoms f cdr

/-- Parse symbols, decoded strings, exact RFC-JSON number literals, and
`#hex#` byte literals. Malformed hash-delimited text remains a symbol unless it
has both delimiters, in which case malformed hex is rejected. -/
def parseLiterals? (text : String) : Option (SExpr2 LiteralAtom) := do
  let value ← parseLexemes? text
  traverseAtoms Lexeme.toLiteralAtom? value

set_option linter.style.nativeDecide false in
example : parseStringSymbol? "(name \"name\")" = some
    (.cons (.atom (.symbol "name")) (.cons (.atom (.string "name")) .nil)) := by
  native_decide

set_option linter.style.nativeDecide false in
example : (parseLiterals? "(42 -1.5e2 #00ff# \"42\")").isSome = true := by
  native_decide

set_option linter.style.nativeDecide false in
example : decodeHexBytes? "#00ff#" = some ⟨[0, 255].toByteArray⟩ := by
  native_decide

set_option linter.style.nativeDecide false in
example : (parseLiterals? "#0#").isNone = true := by native_decide

set_option linter.style.nativeDecide false in
example : parseStringSymbol? "\"line\\nnext\"" =
    some (.atom (.string "line\nnext")) := by native_decide

set_option linter.style.nativeDecide false in
example : (parseKeywordSymbol? "(put :key \"value\")").isSome = true := by
  native_decide

end SExprParser
end Nucleus
