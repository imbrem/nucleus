import Nucleus.SExpr.Forsp.Literal

/-!
# Forsp reader

The reader implements the three source directives from the reference
implementation:

* `'x` expands to `quote x`;
* `^x` expands to `quote x push`;
* `$x` expands to `quote x pop`.

Strings are decoded, signed decimal integers are parsed exactly, and byte
strings use the unambiguous `#hex#` spelling shared with the S-expression
library.  Every non-symbol scalar is allocated in the literal side table.
-/

namespace Nucleus.SExpr2.Forsp.Parser

open Nucleus.SExpr2.Forsp

inductive RawAtom where
  | symbol (name : String)
  | literal (value : Literal)
  deriving DecidableEq

abbrev Raw := SExpr2 RawAtom

private structure Input where
  source : String
  pos : String.Pos.Raw

private def Input.current (input : Input) : Option Char := input.pos.get? input.source
private def Input.next (input : Input) : Input := ⟨input.source, input.pos.next input.source⟩

private def space (char : Char) : Bool :=
  char = ' ' || char = '\t' || char = '\n' || char = '\r'

private def skip : Nat → Bool → Input → Input
  | 0, _, input => input
  | fuel + 1, comment, input => match input.current with
    | none => input
    | some char =>
        if comment then skip fuel (char ≠ '\n') input.next
        else if char = ';' then skip fuel true input.next
        else if space char then skip fuel false input.next
        else input

private def ws (input : Input) : Input := skip (input.source.length + 1) false input

private def delimiter (char : Char) : Bool :=
  space char || char = '(' || char = ')' || char = ';' ||
    char = '\'' || char = '^' || char = '$'

private def bare : Nat → Input → List Char × Input
  | 0, input => ([], input)
  | fuel + 1, input => match input.current with
    | none => ([], input)
    | some char =>
        if delimiter char then ([], input)
        else
          let (tail, rest) := bare fuel input.next
          (char :: tail, rest)

private def quoted : Nat → Input → Option (List Char × Input)
  | 0, _ => none
  | fuel + 1, input => match input.current with
    | none => none
    | some '"' => some ([], input.next)
    | some '\\' => match input.next.current with
      | none => none
      | some escaped => do
          let (tail, rest) ← quoted fuel input.next.next
          let char := match escaped with
            | 'n' => '\n' | 'r' => '\r' | 't' => '\t'
            | 'b' => Char.ofNat 8 | 'f' => Char.ofNat 12
            | other => other
          some (char :: tail, rest)
    | some char => do
        let (tail, rest) ← quoted fuel input.next
        some (char :: tail, rest)

private def hexDigit? (char : Char) : Option Nat :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char ∧ char ≤ 'f' then some (10 + char.toNat - 'a'.toNat)
  else if 'A' ≤ char ∧ char ≤ 'F' then some (10 + char.toNat - 'A'.toNat)
  else none

private def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: tail => do
      let high ← hexDigit? high
      let low ← hexDigit? low
      return UInt8.ofNat (high * 16 + low) :: (← hexBytes tail)
  | [_] => none

private def byteLiteral? (token : String) : Option Bytes := do
  let chars := token.toList
  let body ← match chars with
    | '#' :: tail => match tail.reverse with
      | '#' :: reversed => some reversed.reverse
      | _ => none
    | _ => none
  return ⟨(← hexBytes body).toByteArray⟩

private def classify (token : String) : Option RawAtom :=
  if token.startsWith "#" && token.endsWith "#" then
    (fun bytes => .literal (.bytes bytes)) <$> byteLiteral? token
  else match token.toInt? with
    | some value => some (.literal (.integer value))
    | none => some (.symbol token)

private def symbol (name : String) : Raw := .atom (.symbol name)

private def directiveName (input : Input) : Option (Raw × Input) :=
  let input := ws input
  let (token, rest) := bare (input.source.length + 1) input
  if token.isEmpty then none
  else match classify (String.ofList token) with
    | some (.symbol name) => some (symbol name, rest)
    | _ => none

mutual
  private def expression : Nat → Input → Option (Raw × Input)
    | 0, _ => none
    | fuel + 1, input =>
        let input := ws input
        match input.current with
        | none | some ')' | some '\'' | some '^' | some '$' => none
        | some '(' => list fuel [] input.next
        | some '"' => do
            let (value, rest) ← quoted fuel input.next
            some (.atom (.literal (.string (String.ofList value))), rest)
        | some _ =>
            let (token, rest) := bare fuel input
            if token.isEmpty then none
            else do
              let atom ← classify (String.ofList token)
              some (.atom atom, rest)

  private def item : Nat → Input → Option (List Raw × Input)
    | 0, _ => none
    | fuel + 1, input =>
        let input := ws input
        match input.current with
        | some '\'' => do
            let (value, rest) ← expression fuel input.next
            some ([symbol "quote", value], rest)
        | some '^' => do
            let (value, rest) ← directiveName input.next
            some ([symbol "quote", value, symbol "push"], rest)
        | some '$' => do
            let (value, rest) ← directiveName input.next
            some ([symbol "quote", value, symbol "pop"], rest)
        | _ => do
            let (value, rest) ← expression fuel input
            some ([value], rest)

  private def list : Nat → List Raw → Input → Option (Raw × Input)
    | 0, _, _ => none
    | fuel + 1, values, input =>
        let input := ws input
        match input.current with
        | none => none
        | some ')' => some (values.foldr .cons .nil, input.next)
        | some '.' => do
            let (tail, rest) ← expression fuel input.next
            let rest := ws rest
            if rest.current = some ')' then some (values.foldr .cons tail, rest.next) else none
        | some _ => do
            let (next, rest) ← item fuel input
            list fuel (values ++ next) rest
end

mutual
  def compile : LiteralTable → Raw → LiteralTable × Object
    | table, .nil => (table, .nil)
    | table, .atom (.symbol name) => (table, .atom (.symbol name))
    | table, .atom (.literal literal) => table.allocate literal
    | table, .cons car cdr =>
        let (table, car) := compile table car
        let (table, cdr) := compile table cdr
        (table, .cons car cdr)
end

/-- Read one complete Forsp expression and allocate all its literals. -/
def parse? (source : String) : Option (LiteralTable × Object) := do
  let input : Input := ⟨source, 0⟩
  let (items, rest) ← item (source.length + 1) input
  if !(ws rest).current.isNone then none
  else match items with
    | [value] => compile [] value
    | values => compile [] (values.foldr .cons .nil)

set_option linter.style.nativeDecide false in
example : (parse? "('hello ^x $y 42 \"hi\\n\" #00ff#)").isSome = true := by
  native_decide

set_option linter.style.nativeDecide false in
example : (parse? "(#0#)").isNone = true := by native_decide

end Nucleus.SExpr2.Forsp.Parser
