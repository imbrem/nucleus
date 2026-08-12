import Nucleus.Json.Rfc
import Nucleus.Json.Validate

/-! A small, total recursive-descent parser for RFC JSON text. -/

namespace Nucleus.RfcJson

private abbrev Input := List Char

private def ws : Input → Input
  | c :: cs => if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' then ws cs else c :: cs
  | [] => []
termination_by cs => cs.length

private def hex? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def hex4? : Input → Option (Nat × Input)
  | a :: b :: c :: d :: rest => do
      let a ← hex? a; let b ← hex? b; let c ← hex? c; let d ← hex? d
      pure (a * 4096 + b * 256 + c * 16 + d, rest)
  | _ => none

/-- Parse string contents after the opening quote. Surrogate pairs are combined;
lone UTF-16 surrogates are rejected. -/
private def stringChars : Nat → Input → Option (List Char × Input)
  | 0, _ => none
  | _fuel, [] => none
  | _fuel + 1, '"' :: rest => some ([], rest)
  | fuel + 1, '\\' :: 'u' :: rest => do
      let (u, rest) ← hex4? rest
      let (code, rest) ←
        if 0xD800 ≤ u ∧ u ≤ 0xDBFF then do
          let rest ← match rest with | '\\' :: 'u' :: r => some r | _ => none
          let (v, rest) ← hex4? rest
          if 0xDC00 ≤ v ∧ v ≤ 0xDFFF then
            some (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00), rest)
          else none
        else if 0xD800 ≤ u ∧ u ≤ 0xDFFF then none else some (u, rest)
      let (tail, rest) ← stringChars fuel rest
      pure (Char.ofNat code :: tail, rest)
  | fuel + 1, '\\' :: e :: rest => do
      let c ← match e with
        | '"' => some '"' | '\\' => some '\\' | '/' => some '/'
        | 'b' => some (Char.ofNat 8) | 'f' => some (Char.ofNat 12) | 'n' => some '\n'
        | 'r' => some '\r' | 't' => some '\t' | _ => none
      let (tail, rest) ← stringChars fuel rest
      pure (c :: tail, rest)
  | fuel + 1, c :: rest => do
      if c.toNat < 0x20 then none else
        let (tail, rest) ← stringChars fuel rest
        pure (c :: tail, rest)

private def string? (fuel : Nat) : Input → Option (String × Input)
  | '"' :: rest => do let (cs, rest) ← stringChars fuel rest; pure (String.ofList cs, rest)
  | _ => none

private def digit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')
private def nonzero (c : Char) : Bool := decide ('1' ≤ c ∧ c ≤ '9')

private def takeDigits : Input → List Char × Input
  | c :: cs => if digit c then let (a, r) := takeDigits cs; (c :: a, r) else ([], c :: cs)
  | [] => ([], [])

private def exponent? (input : Input) : Option (List Char × Input) :=
  match input with
  | e :: r =>
      if e = 'e' ∨ e = 'E' then
        let (sgn, r) := match r with
          | '+' :: r => (['+'], r)
          | '-' :: r => (['-'], r)
          | _ => ([], r)
        match r with
        | c :: r =>
            if digit c then
              let (ds, r) := takeDigits r
              some (e :: (sgn ++ c :: ds), r)
            else none
        | [] => none
      else some ([], input)
  | [] => some ([], [])

/-- Consume precisely the RFC 8259 number grammar, returning its original lexeme. -/
private def number? : Input → Option (String × Input)
  | input => do
      let (sign, input) := match input with | '-' :: r => (['-'], r) | _ => ([], input)
      let (whole, input) ← match input with
        | '0' :: r => some (['0'], r)
        | c :: r => if nonzero c then let (ds, r) := takeDigits r; some (c :: ds, r) else none
        | [] => none
      let (frac, input) ← match input with
        | '.' :: c :: r =>
            if digit c then
              let (ds, r) := takeDigits r
              some ('.' :: c :: ds, r)
            else none
        | _ => some ([], input)
      let (expo, input) ← exponent? input
      pure (String.ofList (sign ++ whole ++ frac ++ expo), input)

mutual
  private def value? : Nat → Input → Option (RawJson RfcJsonScalar × Input)
    | 0, _ => none
    | fuel + 1, input =>
      let input := ws input
      match input with
      | 'n' :: 'u' :: 'l' :: 'l' :: r => some (.scalar none, r)
      | 't' :: 'r' :: 'u' :: 'e' :: r => some (.scalar (.bool true), r)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => some (.scalar (.bool false), r)
      | '"' :: _ => do let (s, r) ← string? fuel input; pure (.scalar (.string s), r)
      | '[' :: r => do let (xs, r) ← array? fuel r; pure (.list (RawSyn.ofList xs), r)
      | '{' :: r => do let (xs, r) ← object? fuel r; pure (.map (RawSyn.ofEntries xs), r)
      | _ => do let (n, r) ← number? input; pure (.scalar (.number n), r)

  private def array? : Nat → Input → Option (List (RawJson RfcJsonScalar) × Input)
    | 0, _ => none
    | fuel + 1, input => match ws input with
      | ']' :: r => some ([], r)
      | input => do
          let (v, r) ← value? fuel input
          match ws r with
          | ']' :: r => some ([v], r)
          | ',' :: r => match ws r with
            | ']' :: _ => none
            | r => do let (vs, r) ← array? fuel r; pure (v :: vs, r)
          | _ => none

  private def object? : Nat → Input → Option (List (String × RawJson RfcJsonScalar) × Input)
    | 0, _ => none
    | fuel + 1, input => match ws input with
      | '}' :: r => some ([], r)
      | input => do
          let (key, r) ← string? fuel input
          let r ← match ws r with | ':' :: r => some r | _ => none
          let (v, r) ← value? fuel r
          match ws r with
          | '}' :: r => some ([(key, v)], r)
          | ',' :: r => match ws r with
            | '}' :: _ => none
            | r => do let (vs, r) ← object? fuel r; pure ((key, v) :: vs, r)
          | _ => none
end

/-- Parse one complete JSON text. Invalid syntax, trailing input, and duplicate
object names all return `none`. JSON `null` returns `some (.scalar none)`. -/
def parse? (text : String) : Option RfcJson := do
  let chars := text.toList
  let (raw, rest) ← value? (chars.length + 1) chars
  if (ws rest).isEmpty then raw.validate.toOption else none

set_option linter.style.nativeDecide false in
@[simp] theorem parse?_null_scalar : (parse? "null").bind (fun
    | .scalar s => some s | _ => none) = some none := by native_decide
set_option linter.style.nativeDecide false in
@[simp] theorem parse?_escaped_scalar : (parse? "\"a\\n\\u0042\"").bind (fun
    | .scalar s => some s | _ => none) = some (.string "a\nB") := by native_decide
set_option linter.style.nativeDecide false in
example : (parse? "[true, -12.50e+2, null]").isSome = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parse? "{\"x\": 1, \"x\": 2}").isNone = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parse? "true trailing").isNone = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parse? "[1,]").isNone = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parse? "{\"x\": 1,}").isNone = true := by native_decide

end Nucleus.RfcJson
