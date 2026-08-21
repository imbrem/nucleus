import Nucleus.Cbor.Reasonable
import Nucleus.Cbor.Containers

/-!
# RFC 8949 binary CBOR

The parser accepts definite and indefinite arrays, maps, byte/text strings,
all integer argument widths, tags, simple values, and IEEE float widths. It
returns one item plus unconsumed input; `parse?` requires exactly one item.

The deterministic encoder uses definite lengths, shortest integer/length/tag
arguments, and RFC 8949 length-first ordering of encoded map keys. Its domain
is `CborSyn.Reasonable`, exactly because deterministic CBOR forbids indefinite
lengths while a definite head carries at most a 64-bit argument.
-/

namespace Nucleus
namespace CborWire

private def bytesOfList (xs : List UInt8) : Bytes := ⟨xs.toByteArray⟩
private def listOfBytes (xs : Bytes) : List UInt8 := xs.data.data.toList

private def readNat : Nat → List UInt8 → Option (UInt64 × List UInt8)
  | 0, input => some (0, input)
  | n + 1, b :: rest => do
      let (tail, remaining) ← readNat n rest
      some ((UInt64.ofNat b.toNat <<< UInt64.ofNat (8 * n)) ||| tail, remaining)
  | _, [] => none

private def argument? (info : Nat) (input : List UInt8) :
    Option (Option UInt64 × List UInt8) :=
  if info < 24 then some (some (UInt64.ofNat info), input)
  else match info with
    | 24 => do let (n, rest) ← readNat 1 input; some (some n, rest)
    | 25 => do let (n, rest) ← readNat 2 input; some (some n, rest)
    | 26 => do let (n, rest) ← readNat 4 input; some (some n, rest)
    | 27 => do let (n, rest) ← readNat 8 input; some (some n, rest)
    | 31 => some (none, input)
    | _ => none

private def takeBytes (n : UInt64) (input : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if n.toNat ≤ input.length then some (input.take n.toNat, input.drop n.toNat) else none

mutual
  private def parseItem : Nat → List UInt8 → Option (Cbor × List UInt8)
    | 0, _ => none
    | fuel + 1, head :: input => do
        let major := head.toNat / 32
        let info := head.toNat % 32
        let (arg, rest) ← argument? info input
        match major with
        | 0 => match arg with
          | some n => some (.primitive (.integer (.unsigned n)), rest)
          | none => none
        | 1 => match arg with
          | some n => some (.primitive (.integer (.negative n)), rest)
          | none => none
        | 2 => match arg with
          | some n => do
              let (payload, remaining) ← takeBytes n rest
              some (.primitive (.bytes (bytesOfList payload)), remaining)
          | none => do
              let (chunks, remaining) ← parseByteChunks fuel rest
              some (.primitive (.bytes (bytesOfList chunks)), remaining)
        | 3 => match arg with
          | some n => do
              let (payload, remaining) ← takeBytes n rest
              let text ← String.fromUTF8? payload.toByteArray
              some (.primitive (.text text), remaining)
          | none => do
              let (chunks, remaining) ← parseTextChunks fuel rest
              let text ← String.fromUTF8? chunks.toByteArray
              some (.primitive (.text text), remaining)
        | 4 => match arg with
          | some n => do
              let (items, remaining) ← parseItems fuel n.toNat rest
              some (.array (CborSyn.arrayOfList items), remaining)
          | none => do
              let (items, remaining) ← parseIndefItems fuel rest
              some (.array (CborSyn.arrayOfList items), remaining)
        | 5 => match arg with
          | some n => do
              let (items, remaining) ← parsePairs fuel n.toNat rest
              some (.map (CborSyn.mapOfList items), remaining)
          | none => do
              let (items, remaining) ← parseIndefPairs fuel rest
              some (.map (CborSyn.mapOfList items), remaining)
        | 6 => match arg with
          | some n => do
              let (item, remaining) ← parseItem fuel rest
              some (.tag n item, remaining)
          | none => none
        | 7 =>
          match info with
          | 25 => match arg with
            | some n => some (.primitive (.float16 (UInt16.ofNat n.toNat)), rest)
            | none => none
          | 26 => match arg with
            | some n => some (.primitive (.float32 (UInt32.ofNat n.toNat)), rest)
            | none => none
          | 27 => match arg with
            | some n => some (.primitive (.float64 n), rest)
            | none => none
          | 31 => none
          | _ => match arg with
            | some n => if n.toNat ≤ 255 then
                some (.primitive (.simple (UInt8.ofNat n.toNat)), rest) else none
            | none => none
        | _ => none
    | _, [] => none

  private def parseItems : Nat → Nat → List UInt8 → Option (List Cbor × List UInt8)
    | _, 0, input => some ([], input)
    | 0, _, _ => none
    | fuel + 1, n + 1, input => do
        let (head, rest) ← parseItem fuel input
        let (tail, remaining) ← parseItems fuel n rest
        some (head :: tail, remaining)

  private def parsePairs : Nat → Nat → List UInt8 →
      Option (List (Cbor × Cbor) × List UInt8)
    | _, 0, input => some ([], input)
    | 0, _, _ => none
    | fuel + 1, n + 1, input => do
        let (key, afterKey) ← parseItem fuel input
        let (value, rest) ← parseItem fuel afterKey
        let (tail, remaining) ← parsePairs fuel n rest
        some ((key, value) :: tail, remaining)

  private def parseIndefItems : Nat → List UInt8 → Option (List Cbor × List UInt8)
    | 0, _ => none
    | _, 255 :: rest => some ([], rest)
    | fuel + 1, input => do
        let (head, rest) ← parseItem fuel input
        let (tail, remaining) ← parseIndefItems fuel rest
        some (head :: tail, remaining)

  private def parseIndefPairs : Nat → List UInt8 →
      Option (List (Cbor × Cbor) × List UInt8)
    | 0, _ => none
    | _, 255 :: rest => some ([], rest)
    | fuel + 1, input => do
        let (key, afterKey) ← parseItem fuel input
        let (value, rest) ← parseItem fuel afterKey
        let (tail, remaining) ← parseIndefPairs fuel rest
        some ((key, value) :: tail, remaining)

  private def parseByteChunks : Nat → List UInt8 → Option (List UInt8 × List UInt8)
    | 0, _ => none
    | _, 255 :: rest => some ([], rest)
    | fuel + 1, headByte :: input => do
        if headByte.toNat / 32 != 2 then none else pure ()
        let (arg, afterHead) ← argument? (headByte.toNat % 32) input
        let n ← arg
        let (chunk, rest) ← takeBytes n afterHead
        let (tail, remaining) ← parseByteChunks fuel rest
        some (chunk ++ tail, remaining)
    | _, [] => none

  private def parseTextChunks : Nat → List UInt8 → Option (List UInt8 × List UInt8)
    | 0, _ => none
    | _, 255 :: rest => some ([], rest)
    | fuel + 1, headByte :: input => do
        if headByte.toNat / 32 != 3 then none else pure ()
        let (arg, afterHead) ← argument? (headByte.toNat % 32) input
        let n ← arg
        let (chunk, rest) ← takeBytes n afterHead
        let _ ← String.fromUTF8? chunk.toByteArray
        let (tail, remaining) ← parseTextChunks fuel rest
        some (chunk ++ tail, remaining)
    | _, [] => none
end

/-- Parse exactly one complete CBOR data item. -/
def parse? (bytes : Bytes) : Option Cbor := do
  let input := listOfBytes bytes
  let (value, rest) ← parseItem (input.length + 1) input
  if rest.isEmpty then some value else none

private def beBytes (count : Nat) (n : UInt64) : List UInt8 :=
  (List.range count).map fun i =>
    UInt8.ofNat ((n >>> UInt64.ofNat (8 * (count - 1 - i))).toNat)

private def head (major : Nat) (n : UInt64) : List UInt8 :=
  if n < 24 then [UInt8.ofNat (32 * major + n.toNat)]
  else if n ≤ 0xff then UInt8.ofNat (32 * major + 24) :: beBytes 1 n
  else if n ≤ 0xffff then UInt8.ofNat (32 * major + 25) :: beBytes 2 n
  else if n ≤ 0xffffffff then UInt8.ofNat (32 * major + 26) :: beBytes 4 n
  else UInt8.ofNat (32 * major + 27) :: beBytes 8 n

private def lexLt (a b : List UInt8) : Bool :=
  if a.length != b.length then a.length < b.length else a < b

private def insertEntry (entry : List UInt8 × List UInt8) :
    List (List UInt8 × List UInt8) → List (List UInt8 × List UInt8)
  | [] => [entry]
  | x :: xs => if lexLt entry.1 x.1 then entry :: x :: xs else x :: insertEntry entry xs

private def sortEntries : List (List UInt8 × List UInt8) → List (List UInt8 × List UInt8)
  | [] => []
  | x :: xs => insertEntry x (sortEntries xs)

mutual
  private def encodeSyn : {i : CborIx} → CborSyn i → List UInt8
    | _, .primitive (.integer (.unsigned n)) => head 0 n
    | _, .primitive (.integer (.negative n)) => head 1 n
    | _, .primitive (.bytes b) => head 2 (UInt64.ofNat b.length) ++ listOfBytes b
    | _, .primitive (.text s) => head 3 (UInt64.ofNat s.toUTF8.size) ++ s.toUTF8.data.toList
    | _, .primitive (.simple n) =>
        if n.toNat < 24 then [UInt8.ofNat (224 + n.toNat)] else [248, n]
    | _, .primitive (.float16 n) => 249 :: beBytes 2 (UInt64.ofNat n.toNat)
    | _, .primitive (.float32 n) => 250 :: beBytes 4 (UInt64.ofNat n.toNat)
    | _, .primitive (.float64 n) => 251 :: beBytes 8 n
    | _, .array items => head 4 (UInt64.ofNat items.arrayLength) ++ encodeSyn items
    | _, .map entries =>
        let encoded := sortEntries (encodeEntries entries)
        head 5 (UInt64.ofNat encoded.length) ++ encoded.flatMap fun e => e.1 ++ e.2
    | _, .tag n content => head 6 n ++ encodeSyn content
    | _, .arrayNil => []
    | _, .arrayCons item tail => encodeSyn item ++ encodeSyn tail
    | _, .mapNil => []
    | _, .mapCons key value tail => encodeSyn key ++ encodeSyn value ++ encodeSyn tail

  private def encodeEntries : CborSyn .map → List (List UInt8 × List UInt8)
    | .mapNil => []
    | .mapCons key value tail => (encodeSyn key, encodeSyn value) :: encodeEntries tail
end

/-- RFC deterministic encoding candidate. On `Reasonable` values every length
fits the definite argument field. -/
def deterministic (value : {v : Cbor // v.Reasonable}) : Bytes :=
  bytesOfList (encodeSyn value.1)

/-- Executable checked entry point for callers holding an unrestricted CBOR
value. -/
def deterministic? (value : Cbor) : Option Bytes :=
  if h : value.Reasonable then some (deterministic ⟨value, h⟩) else none

/-- Relational presentation requested by RFC-style specifications. -/
def RfcDeterministicEncoding (value : Cbor) (bytes : Bytes) : Prop :=
  ∃ h : value.Reasonable, bytes = deterministic ⟨value, h⟩

/-- Agreement with the chosen encoder also proves uniqueness of the RFC
deterministic relation on every reasonable value. -/
theorem deterministic_unique {value : Cbor} {a b : Bytes}
    (ha : RfcDeterministicEncoding value a)
    (hb : RfcDeterministicEncoding value b) : a = b := by
  rcases ha with ⟨ha, rfl⟩
  rcases hb with ⟨hb, rfl⟩
  rfl

/-- Unreasonable values are outside the RFC deterministic relation. -/
theorem deterministic_undefined_of_not_reasonable {value : Cbor}
    (h : ¬ value.Reasonable) : ¬ ∃ bytes, RfcDeterministicEncoding value bytes := by
  rintro ⟨_, hv, _⟩
  exact h hv

end CborWire
end Nucleus
