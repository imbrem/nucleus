import Nucleus.SExpr.Parser
import Nucleus.Json.RfcParser

/-!
# Portable S-expressions (POSE)

Implements the grammar published by `s-expressions/pose`: proper lists,
lowercase ASCII symbols, strings with only `\\` and `\"` escapes, and exact
integer/floating-point number lexemes.
-/

namespace Nucleus

inductive PoseNumber where
  | integer (literal : String)
  | float (literal : String)
  deriving DecidableEq, Repr

inductive PoseAtom where
  | symbol (name : String)
  | string (value : String)
  | number (value : PoseNumber)
  deriving DecidableEq, Repr

abbrev Pose := SExpr PoseAtom
abbrev PoseDocument := List Pose

namespace Pose

private def lower (c : Char) : Bool := decide ('a' ≤ c ∧ c ≤ 'z')
private def digit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

private def punctFirst (c : Char) : Bool :=
  c = '!' || c = '$' || c = '&' || c = '*' || c = '+' || c = '-' ||
  c = '/' || c = '<' || c = '=' || c = '>' || c = '_'

private def punctCont (c : Char) : Bool :=
  punctFirst c || c = '.' || c = '?' || c = '@'

private def wordFirst (c : Char) : Bool := lower c || punctFirst c
private def wordCont (c : Char) : Bool := lower c || punctCont c || digit c

private def wordSymbol : List Char → Bool
  | first :: rest => wordFirst first && rest.all wordCont
  | [] => false

private def signSymbol : List Char → Bool
  | [sign] => sign = '+' || sign = '-'
  | sign :: second :: rest =>
      (sign = '+' || sign = '-') && (lower second || punctCont second) &&
        rest.all wordCont
  | _ => false

/-- POSE's exact symbol grammar, including its restricted single-colon prefix. -/
def validSymbol (value : String) : Bool :=
  match value.toList with
  | ':' :: rest => wordSymbol rest
  | chars => wordSymbol chars || signSymbol chars

private def numberRequired : List Char → Bool
  | first :: rest =>
      digit first || ((first = '+' || first = '-') && match rest with
        | second :: _ => digit second
        | [] => false)
  | _ => false

private def parseNumber? (value : String) : Option PoseNumber :=
  match RfcJson.parse? value with
  | some (.scalar (some (.number literal))) =>
      if literal.any fun c => c = '.' || c = 'e' || c = 'E' then
        some (.float literal)
      else some (.integer literal)
  | _ => none

private def classify : SExprParser.Lexeme → Option PoseAtom
  | .string value => some (.string value)
  | .symbol value =>
      if numberRequired value.toList then .number <$> parseNumber? value
      else if validSymbol value then some (.symbol value) else none

private def traverse : Nat → SExpr SExprParser.Lexeme → Option Pose
  | 0, _ => none
  | _ + 1, .atom value => .atom <$> classify value
  | fuel + 1, .list _ children => do
      let children ← (List.ofFn children).mapM (traverse fuel)
      some (SExpr.ofList children)

/-- Parse all expressions in a POSE document. -/
def parseDocument? (text : String) : Option PoseDocument := do
  let values ← SExprParser.parsePoseLexemes? text
  values.mapM (traverse (text.length + 1))

/-- Parse a POSE document containing exactly one expression. -/
def parse? (text : String) : Option Pose := do
  let values ← parseDocument? text
  match values with
  | [value] => some value
  | _ => none

set_option linter.style.nativeDecide false in
example : (parse? "(Foo)").isNone = true := by native_decide

set_option linter.style.nativeDecide false in
example : (parse? "(01)").isNone = true := by native_decide

set_option linter.style.nativeDecide false in
example : (parse? "(a . b)").isNone = true := by native_decide

set_option linter.style.nativeDecide false in
example : (parse? "(foo :bar -12 1.5e2 \"a\\\\b\\\"c\")").isSome = true := by
  native_decide


end Pose
end Nucleus
