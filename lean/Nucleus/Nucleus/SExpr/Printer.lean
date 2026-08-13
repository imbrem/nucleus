import Nucleus.SExpr.Pose
import Nucleus.SExpr.Rivest

/-!
# S-expression printers

Printers for the general Lisp syntax, POSE, and Rivest's canonical binary
syntax.  The checked entry points make the parser/printer contract executable:
returning `some text` entails that parsing `text` recovers the input exactly.
-/

namespace Nucleus

namespace SExprPrinter

private def escapeChar : Char → String
  | '\\' => "\\\\"
  | '"' => "\\\""
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => String.singleton c

/-- Quote an arbitrary string as a Lisp string literal. -/
def quote (value : String) : String :=
  "\"" ++ String.join (value.toList.map escapeChar) ++ "\""

mutual
  /-- Print a binary S-expression using a caller-supplied atom representation. -/
  def printSExpr2With (printAtom : α → String) : SExpr2 α → String
    | .nil => "()"
    | .atom value => printAtom value
    | .cons car cdr => "(" ++ printSExpr2With printAtom car ++
        printTailWith printAtom cdr ++ ")"

  private def printTailWith (printAtom : α → String) : SExpr2 α → String
    | .nil => ""
    | .cons car cdr => " " ++ printSExpr2With printAtom car ++
        printTailWith printAtom cdr
    | tail => " . " ++ printSExpr2With printAtom tail

  /-- Print a possibly improper S-expression.  Atoms are quoted so every
  `String` is representable without imposing a symbol grammar. -/
  def printSExpr2 (value : SExpr2 String) : String := printSExpr2With quote value
end

/-- Print an intrinsically proper S-expression. -/
def printSExpr (value : SExpr String) : String :=
  printSExpr2With quote value.toSExpr2

/-- A checked general printer.  Failure would expose a disagreement between
the printer and parser rather than silently emitting a lossy representation. -/
def printSExpr2? (value : SExpr2 String) : Option String :=
  let text := printSExpr2 value
  if SExprParser.parseSExpr2? text = some value then some text else none

theorem printSExpr2?_sound {value : SExpr2 String} {text : String}
    (h : printSExpr2? value = some text) :
    SExprParser.parseSExpr2? text = some value := by
  simp only [printSExpr2?] at h
  split at h <;> simp_all

/-- Checked printer for intrinsically proper expressions. -/
def printSExpr? (value : SExpr String) : Option String :=
  let text := printSExpr value
  match SExprParser.parseSExpr? text with
  | some parsed => if parsed.toSExpr2 = value.toSExpr2 then some text else none
  | none => none

theorem printSExpr?_sound {value : SExpr String} {text : String}
    (h : printSExpr? value = some text) :
    SExprParser.parseSExpr? text = some value := by
  simp only [printSExpr?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value := SExpr.toSExpr2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end SExprPrinter

namespace Pose

private def quoteChar : Char → String
  | '\\' => "\\\\"
  | '"' => "\\\""
  | c => String.singleton c

private def quote (value : String) : String :=
  "\"" ++ String.join (value.toList.map quoteChar) ++ "\""

private def printAtom : PoseAtom → String
  | .symbol name => name
  | .string value => quote value
  | .number (.integer literal) | .number (.float literal) => literal

private def render : Pose → String
  | value => SExprPrinter.printSExpr2With printAtom value.toSExpr2

/-- Print a POSE value when its public, unrestricted atom fields actually
satisfy the POSE grammar. -/
def print? (value : Pose) : Option String :=
  let text := render value
  match parse? text with
  | some parsed => if parsed.toSExpr2 = value.toSExpr2 then some text else none
  | none => none

theorem print?_sound {value : Pose} {text : String} (h : print? value = some text) :
    parse? text = some value := by
  simp only [print?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value := SExpr.toSExpr2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

/-- Print a complete POSE document, checking all atom invariants. -/
def printDocument? (value : PoseDocument) : Option String :=
  let text := String.intercalate "\n" (value.map render)
  match parseDocument? text with
  | some parsed =>
      if parsed.map SExpr.toSExpr2 = value.map SExpr.toSExpr2 then some text else none
  | none => none

theorem printDocument?_sound {value : PoseDocument} {text : String}
    (h : printDocument? value = some text) : parseDocument? text = some value := by
  simp only [printDocument?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value :=
        (List.map_injective_iff.mpr SExpr.toSExpr2_injective) hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end Pose

namespace RivestSExpr

private def ascii (value : String) : Bytes := ⟨value.toUTF8⟩

mutual
  private def printCanonical2 : SExpr2 Bytes → Bytes
    | .nil => ascii "()"
    | .atom value => (ascii (toString value.length ++ ":")).append value
    | .cons car cdr =>
        (ascii "(").append (printCanonical2 car) |>.append (printCanonicalTail cdr)
          |>.append (ascii ")")

  private def printCanonicalTail : SExpr2 Bytes → Bytes
    | .nil => Bytes.empty
    | .cons car cdr => (printCanonical2 car).append (printCanonicalTail cdr)
    | _ => Bytes.empty -- unreachable for the image of `SExpr.toSExpr2`
end

/-- The mandatory canonical representation from draft-rivest-sexp-04. -/
def printCanonical (value : RivestSExpr) : Bytes := printCanonical2 value.toSExpr2

/-- Checked canonical printer, useful as an executable parser/printer
round-trip contract. -/
def printCanonical? (value : RivestSExpr) : Option Bytes :=
  let bytes := printCanonical value
  match parseCanonical? bytes with
  | some parsed => if parsed.toSExpr2 = value.toSExpr2 then some bytes else none
  | none => none

theorem printCanonical?_sound {value : RivestSExpr} {bytes : Bytes}
    (h : printCanonical? value = some bytes) : parseCanonical? bytes = some value := by
  simp only [printCanonical?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst bytes
      have hp : parsed = value := SExpr.toSExpr2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end RivestSExpr

set_option linter.style.nativeDecide false in
example :
    SExprPrinter.printSExpr2?
      (.cons (.atom "a b") (.cons (.atom "x\n\"y") (.atom "tail"))) =
      some "(\"a b\" \"x\\n\\\"y\" . \"tail\")" := by
  native_decide

set_option linter.style.nativeDecide false in
example :
    Pose.print? (SExpr.ofList [
      .atom (.symbol "foo"), .atom (.number (.integer "-12")),
      .atom (.string "a\\b\"c")]) =
      some "(foo -12 \"a\\\\b\\\"c\")" := by
  native_decide

set_option linter.style.nativeDecide false in
example :
    RivestSExpr.printCanonical?
      (SExpr.ofList [.atom ⟨ByteArray.mk #[0, 255, 40, 41]⟩, SExpr.nil]) =
      some ⟨(ByteArray.mk #[40, 52, 58, 0, 255, 40, 41, 40, 41, 41])⟩ := by
  native_decide

end Nucleus
