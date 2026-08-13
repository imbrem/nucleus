import Nucleus.SExpr.Tagged

/-! A total parser for Lisp-style S-expressions and checked sublanguages. -/

namespace Nucleus.SExprParser

private structure Input where
  source : String
  pos : String.Pos.Raw

private def Input.current (input : Input) : Option Char := input.pos.get? input.source

private def Input.next (input : Input) : Input :=
  ⟨input.source, input.pos.next input.source⟩

private def space (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

private def wsFuel : Nat → Bool → Input → Input
  | 0, _, input => input
  | fuel + 1, comment, input =>
      match input.current with
      | none => input
      | some c =>
          if comment then
            wsFuel fuel (c ≠ '\n') input.next
          else if c = ';' then
            wsFuel fuel true input.next
          else if space c then
            wsFuel fuel false input.next
          else input

private def ws (input : Input) : Input := wsFuel (input.source.length + 1) false input

private def quoted : Nat → Input → Option (List Char × Input)
  | 0, _ => none
  | fuel + 1, input =>
      match input.current with
      | none => none
      | some '"' => some ([], input.next)
      | some '\\' =>
          let input := input.next
          match input.current with
          | none => none
          | some c => do
              let (tail, rest) ← quoted fuel input.next
              some (c :: tail, rest)
      | some c => do
          let (tail, rest) ← quoted fuel input.next
          some (c :: tail, rest)

private def delimiter (c : Char) : Bool := space c || c = '(' || c = ')' || c = ';'

private def dottedMarker (input : Input) : Bool :=
  input.current = some '.' && match input.next.current with
    | none => true
    | some c => delimiter c

private def bare : Input → List Char × Input
  | input => go (input.source.length + 1) input
where
  go : Nat → Input → List Char × Input
    | 0, input => ([], input)
    | fuel + 1, input =>
        match input.current with
        | none => ([], input)
        | some c => if delimiter c then ([], input) else
            let (token, rest) := go fuel input.next
            (c :: token, rest)

mutual
  private def expr : Nat → Input → Option (SExpr2 String × Input)
    | 0, _ => none
    | fuel + 1, input =>
        let input := ws input
        match input.current with
        | none | some ')' => none
        | some '(' => list fuel [] input.next
        | some '"' => do
            let (token, rest) ← quoted fuel input.next
            some (.atom (String.ofList token), rest)
        | some _ =>
            let (token, rest) := bare input
            if token.isEmpty then none else some (.atom (String.ofList token), rest)

  private def list : Nat → List (SExpr2 String) → Input →
      Option (SExpr2 String × Input)
    | 0, _, _ => none
    | fuel + 1, acc, input =>
        let input := ws input
        match input.current with
        | none => none
        | some ')' => some (acc.foldr .cons .nil, input.next)
        | some '.' =>
            if !dottedMarker input then do
              let (head, rest) ← expr fuel input
              list fuel (acc ++ [head]) rest
            else if acc.isEmpty then none else do
              let (tail, rest) ← expr fuel input.next
              let rest := ws rest
              if rest.current = some ')' then
                some (acc.foldr .cons tail, rest.next)
              else none
        | some _ => do
            let (head, rest) ← expr fuel input
            list fuel (acc ++ [head]) rest
end

/-- Parse one complete dotted or proper Lisp S-expression. Quoted atoms have
their escapes removed; semicolon comments and standard whitespace are skipped. -/
def parseSExpr2? (text : String) : Option (SExpr2 String) := do
  let (value, rest) ← expr (text.length + 1) ⟨text, 0⟩
  if (ws rest).current.isNone then some value else none

mutual
  private def toProper : Nat → SExpr2 α → Option (SExpr α)
    | 0, _ => none
    | _ + 1, .nil => some SExpr.nil
    | _ + 1, .atom value => some (.atom value)
    | fuel + 1, .cons car cdr => do
        let car ← toProper fuel car
        let cdr ← toProperList fuel cdr
        some (SExpr.ofList (car :: cdr))

  private def toProperList : Nat → SExpr2 α → Option (List (SExpr α))
    | 0, _ => none
    | _ + 1, .nil => some []
    | _ + 1, .atom _ => none
    | fuel + 1, .cons car cdr => do
        let car ← toProper fuel car
        let cdr ← toProperList fuel cdr
        some (car :: cdr)
end

/-- Parse only intrinsically proper S-expressions. -/
def parseSExpr? (text : String) : Option (SExpr String) := do
  let value ← parseSExpr2? text
  toProper (text.length + 2) value

mutual
  private def toTagged : Nat → SExpr2 String → Option (TExpr String String)
    | 0, _ => none
    | _ + 1, .nil => none
    | _ + 1, .atom value => some (.atom value)
    | fuel + 1, .cons (.atom tag) cdr => do
        let children ← toTaggedList fuel cdr
        some (.tag tag children.length children.get)
    | _ + 1, .cons _ _ => none

  private def toTaggedList : Nat → SExpr2 String →
      Option (List (TExpr String String))
    | 0, _ => none
    | _ + 1, .nil => some []
    | _ + 1, .atom _ => none
    | fuel + 1, .cons car cdr => do
        let car ← toTagged fuel car
        let cdr ← toTaggedList fuel cdr
        some (car :: cdr)
end

/-- Parse the tagged convention `(tag child ...)`; ordinary atoms remain atom
nodes, empty lists and dotted tails are rejected. -/
def parseTExpr? (text : String) : Option (TExpr String String) := do
  let value ← parseSExpr2? text
  toTagged (text.length + 2) value

set_option linter.style.nativeDecide false in
example : (parseSExpr2? "(a b . c)").isSome = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parseSExpr? "(a b . c)").isNone = true := by native_decide
set_option linter.style.nativeDecide false in
example : (parseTExpr? "(call x (quote y))").isSome = true := by native_decide

end Nucleus.SExprParser
