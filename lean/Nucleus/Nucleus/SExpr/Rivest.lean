import Nucleus.SExpr.Proper
import Nucleus.Cbor.Bytes

/-!
# Rivest/Eastlake S-expressions

The data model in draft-rivest-sexp-04 is just octet strings and finite lists.
This module begins with the mandatory canonical representation. Its parser
takes `Bytes`, since a verbatim atom is not necessarily UTF-8 text.
-/

namespace Nucleus

/-- The semantic data model of draft-rivest-sexp-04. -/
abbrev RivestSExpr := SExpr Bytes

namespace RivestSExpr

private def digit? (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (byte.toNat - 48) else none

private def decimal : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _ => none
  | fuel + 1, bytes =>
      match bytes with
      | [] => none
      | first :: rest => do
          let first ← digit? first
          if first = 0 then
            match rest with
            | 58 :: rest => some (0, rest)
            | _ => none
          else go fuel first rest
where
  go : Nat → Nat → List UInt8 → Option (Nat × List UInt8)
    | 0, _, _ => none
    | fuel + 1, value, bytes =>
        match bytes with
        | 58 :: rest => some (value, rest)
        | byte :: rest => do
            let digit ← digit? byte
            go fuel (value * 10 + digit) rest
        | [] => none

private def splitExact (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

mutual
  private def canonicalExpr : Nat → List UInt8 → Option (RivestSExpr × List UInt8)
    | 0, _ => none
    | fuel + 1, bytes =>
        match bytes with
        | 40 :: rest => do
            let (children, rest) ← canonicalList fuel [] rest
            some (SExpr.ofList children, rest)
        | _ => do
            let (length, rest) ← decimal fuel bytes
            let (payload, rest) ← splitExact length rest
            some (.atom ⟨payload.toByteArray⟩, rest)

  private def canonicalList : Nat → List RivestSExpr → List UInt8 →
      Option (List RivestSExpr × List UInt8)
    | 0, _, _ => none
    | fuel + 1, acc, bytes =>
        match bytes with
        | 41 :: rest => some (acc, rest)
        | [] => none
        | _ => do
            let (head, rest) ← canonicalExpr fuel bytes
            canonicalList fuel (acc ++ [head]) rest
end

/-- Parse one complete canonical representation from arbitrary octets. Leading
zeros in lengths, whitespace, trailing bytes, and short payloads are rejected. -/
def parseCanonical? (bytes : Bytes) : Option RivestSExpr := do
  let input := bytes.data.toList
  let (value, rest) ← canonicalExpr (input.length + 1) input
  if rest.isEmpty then some value else none

set_option linter.style.nativeDecide false in
example : (parseCanonical? ⟨"(3:abc(0:))".toUTF8⟩).isSome = true := by native_decide

set_option linter.style.nativeDecide false in
example : (parseCanonical? ⟨"01:a".toUTF8⟩).isNone = true := by native_decide

end RivestSExpr
end Nucleus
