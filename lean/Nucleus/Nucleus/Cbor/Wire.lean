import Nucleus.Cbor.Reasonable
import Nucleus.Cbor.Containers

/-!
# RFC 8949 binary CBOR

The parser accepts definite and indefinite arrays, maps, byte/text strings,
all integer argument widths, tags, simple values, and IEEE float widths. It
returns one item plus unconsumed input; `parse?` requires exactly one item.

The width-preserving deterministic encoder uses definite lengths, shortest
integer/length/tag arguments, and RFC 8949 length-first ordering of encoded map
keys. `CborSyn.Reasonable` is exactly its finite-length domain. The stricter
`Canonical` artifact profile additionally rejects duplicate canonical map keys
and floating-point widths whose preferred serialization is not yet formalized.
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

/-! ## Deterministic parsed normal form

Encoding and parsing is not literally an identity on `Cbor`: map syntax keeps
source order, whereas deterministic CBOR orders entries by their encoded keys.
The following transformation states the exact parsed value targeted by the
byte round-trip theorem. Values and array order are preserved; map keys and
values are transformed recursively before entries are sorted. This is a
one-encode-step operation rather than an idempotent normalizer: the existing
insertion sort reverses equal encoded keys, so duplicate-key maps alternate
their equal-key order on repeated application. -/

private def canonicalEntryLt (left right : Cbor × Cbor) : Bool :=
  lexLt (encodeSyn left.1) (encodeSyn right.1)

private def insertCanonicalEntry (entry : Cbor × Cbor) :
    List (Cbor × Cbor) → List (Cbor × Cbor)
  | [] => [entry]
  | head :: tail =>
      if canonicalEntryLt entry head then
        entry :: head :: tail
      else
        head :: insertCanonicalEntry entry tail

private def sortCanonicalEntries :
    List (Cbor × Cbor) → List (Cbor × Cbor)
  | [] => []
  | head :: tail => insertCanonicalEntry head (sortCanonicalEntries tail)

mutual

/-- Recursively transform a CBOR value to the map ordering produced by the
deterministic encoder and recovered by the parser. Duplicate keys are retained
and equal-key ordering exactly matches `sortEntries`. -/
def canonicalize : Cbor → Cbor
  | .primitive primitive => .primitive primitive
  | .array items => .array (canonicalizeArray items)
  | .map entries =>
      .map (CborSyn.mapOfList
        (sortCanonicalEntries (canonicalizeEntries entries)))
  | .tag number content => .tag number (canonicalize content)

private def canonicalizeArray : CborSyn .array → CborSyn .array
  | .arrayNil => .arrayNil
  | .arrayCons head tail =>
      .arrayCons (canonicalize head) (canonicalizeArray tail)

private def canonicalizeEntries : CborSyn .map → List (Cbor × Cbor)
  | .mapNil => []
  | .mapCons key value tail =>
      (canonicalize key, canonicalize value) :: canonicalizeEntries tail

end

@[simp] theorem canonicalize_primitive (primitive : CborPrimitive) :
    canonicalize (.primitive primitive) = .primitive primitive := by
  rw [canonicalize]

@[simp] theorem canonicalize_tag (number : UInt64) (content : Cbor) :
    canonicalize (.tag number content) = .tag number (canonicalize content) := by
  rw [canonicalize]

@[simp] theorem canonicalize_arrayNil :
    canonicalize (.array .arrayNil) = .array .arrayNil := by
  rw [canonicalize, canonicalizeArray]

@[simp] theorem canonicalize_mapNil :
    canonicalize (.map .mapNil) = .map .mapNil := by
  rw [canonicalize, canonicalizeEntries, sortCanonicalEntries, CborSyn.mapOfList]

/-- The canonical byte identity of a map key. Nested maps are transformed to
their deterministic entry order before encoding, so syntactically reordered
but extensionally identical keys collide here. -/
private def canonicalKeyBytes (key : Cbor) : List UInt8 :=
  encodeSyn (canonicalize key)

private def canonicalMapKeyBytes : CborSyn .map → List (List UInt8)
  | .mapNil => []
  | .mapCons key _ tail => canonicalKeyBytes key :: canonicalMapKeyBytes tail

/-! ## Canonical artifact profile

The total CBOR syntax and parser deliberately preserve invalid or ambiguous
wire inputs. Content-addressed Nucleus objects use a smaller profile: all
container lengths are definite and bounded, children satisfy the same profile,
floating-point widths are excluded until preferred-serialization semantics are
formalized, and map keys have distinct canonical encodings. -/

mutual

/-- Values admitted as canonical content-addressed artifacts. -/
def Canonical : Cbor → Prop
  | .primitive (.integer _) => True
  | .primitive (.bytes value) => value.length ≤ Bytes.maxDefiniteLength
  | .primitive (.text value) => value.toUTF8.size ≤ Bytes.maxDefiniteLength
  | .primitive (.simple _) => True
  | .primitive (.float16 _) => False
  | .primitive (.float32 _) => False
  | .primitive (.float64 _) => False
  | .array items =>
      items.arrayLength ≤ Bytes.maxDefiniteLength ∧ CanonicalArray items
  | .map entries =>
      entries.mapLength ≤ Bytes.maxDefiniteLength ∧ CanonicalMap entries ∧
        (canonicalMapKeyBytes entries).Nodup
  | .tag _ content => Canonical content

private def CanonicalArray : CborSyn .array → Prop
  | .arrayNil => True
  | .arrayCons head tail => Canonical head ∧ CanonicalArray tail

private def CanonicalMap : CborSyn .map → Prop
  | .mapNil => True
  | .mapCons key value tail =>
      Canonical key ∧ Canonical value ∧ CanonicalMap tail

end

mutual

/-- Structural decision procedure for the canonical artifact profile. -/
def canonicalDecidable (value : Cbor) : Decidable (Canonical value) :=
  match value with
  | .primitive (.integer _) =>
      @decidable_of_iff _ True (by simp [Canonical]) inferInstance
  | .primitive (.bytes bytes) =>
      @decidable_of_iff _ (bytes.length ≤ Bytes.maxDefiniteLength)
        (by simp [Canonical]) (Nat.decLe _ _)
  | .primitive (.text text) =>
      @decidable_of_iff _ (text.toUTF8.size ≤ Bytes.maxDefiniteLength)
        (by simp [Canonical]) (Nat.decLe _ _)
  | .primitive (.simple _) =>
      @decidable_of_iff _ True (by simp [Canonical]) inferInstance
  | .primitive (.float16 _) =>
      @decidable_of_iff _ False (by simp [Canonical]) inferInstance
  | .primitive (.float32 _) =>
      @decidable_of_iff _ False (by simp [Canonical]) inferInstance
  | .primitive (.float64 _) =>
      @decidable_of_iff _ False (by simp [Canonical]) inferInstance
  | .array items =>
      @decidable_of_iff _
        (items.arrayLength ≤ Bytes.maxDefiniteLength ∧ CanonicalArray items)
        (by simp [Canonical])
        (@instDecidableAnd _ _ (Nat.decLe _ _) (canonicalArrayDecidable items))
  | .map entries =>
      @decidable_of_iff _
        (entries.mapLength ≤ Bytes.maxDefiniteLength ∧ CanonicalMap entries ∧
          (canonicalMapKeyBytes entries).Nodup)
        (by simp [Canonical])
        (@instDecidableAnd _ _ (Nat.decLe _ _)
          (@instDecidableAnd _ _ (canonicalMapDecidable entries) inferInstance))
  | .tag _ content =>
      @decidable_of_iff _ (Canonical content) (by simp [Canonical])
        (canonicalDecidable content)

private def canonicalArrayDecidable (items : CborSyn .array) :
    Decidable (CanonicalArray items) :=
  match items with
  | .arrayNil =>
      @decidable_of_iff _ True (by simp [CanonicalArray]) inferInstance
  | .arrayCons head tail =>
      @decidable_of_iff _ (Canonical head ∧ CanonicalArray tail)
        (by simp [CanonicalArray])
        (@instDecidableAnd _ _ (canonicalDecidable head)
          (canonicalArrayDecidable tail))

private def canonicalMapDecidable (entries : CborSyn .map) :
    Decidable (CanonicalMap entries) :=
  match entries with
  | .mapNil =>
      @decidable_of_iff _ True (by simp [CanonicalMap]) inferInstance
  | .mapCons key value tail =>
      @decidable_of_iff _ (Canonical key ∧ Canonical value ∧ CanonicalMap tail)
        (by simp [CanonicalMap])
        (@instDecidableAnd _ _ (canonicalDecidable key)
          (@instDecidableAnd _ _ (canonicalDecidable value)
            (canonicalMapDecidable tail)))

end

instance (value : Cbor) : Decidable (Canonical value) :=
  canonicalDecidable value

mutual

/-- Every canonical artifact lies in the existing definite-length encoder
domain. -/
theorem Canonical.reasonable {value : Cbor} (canonical : Canonical value) :
    value.Reasonable := by
  cases value with
  | primitive primitive =>
      cases primitive with
      | integer value => exact .integer value
      | bytes value =>
          rw [Canonical] at canonical
          exact .bytes value canonical
      | text value =>
          rw [Canonical] at canonical
          exact .text value canonical
      | simple value => exact .simple value
      | float16 _ => simp [Canonical] at canonical
      | float32 _ => simp [Canonical] at canonical
      | float64 _ => simp [Canonical] at canonical
  | array items =>
      rw [Canonical] at canonical
      exact .array items canonical.1 (CanonicalArray.reasonable canonical.2)
  | map entries =>
      rw [Canonical] at canonical
      exact .map entries canonical.1 (CanonicalMap.reasonable canonical.2.1)
  | tag number content =>
      rw [Canonical] at canonical
      exact .tag number content (Canonical.reasonable canonical)

private theorem CanonicalArray.reasonable {items : CborSyn .array}
    (canonical : CanonicalArray items) : items.Reasonable := by
  cases items with
  | arrayNil => exact .arrayNil
  | arrayCons head tail =>
      rw [CanonicalArray] at canonical
      exact .arrayCons head tail (Canonical.reasonable canonical.1)
        (CanonicalArray.reasonable canonical.2)

private theorem CanonicalMap.reasonable {entries : CborSyn .map}
    (canonical : CanonicalMap entries) : entries.Reasonable := by
  cases entries with
  | mapNil => exact .mapNil
  | mapCons key value tail =>
      rw [CanonicalMap] at canonical
      exact .mapCons key value tail
        (Canonical.reasonable canonical.1)
        (Canonical.reasonable canonical.2.1)
        (CanonicalMap.reasonable canonical.2.2)

end

/-- Deterministic map order is length-first encoded-key order, not source
order. This concrete regression also keeps the transformation executable. -/
theorem canonicalize_unsorted_integer_map :
    canonicalize (.map (CborSyn.mapOfList [
      (.primitive (.integer (.unsigned 2)), .primitive (.integer (.unsigned 1))),
      (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2)))])) =
      .map (CborSyn.mapOfList [
        (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2))),
        (.primitive (.integer (.unsigned 2)), .primitive (.integer (.unsigned 1)))]) := by
  simp [CborSyn.mapOfList, canonicalize,
    canonicalizeEntries, sortCanonicalEntries, insertCanonicalEntry,
    canonicalEntryLt, lexLt, encodeSyn, head,
    show ¬ (([2] : List UInt8) < ([1] : List UInt8)) by decide]

/-- The encoder's current insertion ordering retains duplicate entries but
reverses an equal-key run. The byte-roundtrip theorem must preserve this exact
behavior rather than silently assuming map-key uniqueness. -/
theorem canonicalize_duplicate_integer_keys :
    canonicalize (.map (CborSyn.mapOfList [
      (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 1))),
      (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2)))])) =
      .map (CborSyn.mapOfList [
        (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2))),
        (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 1)))]) := by
  simp [CborSyn.mapOfList, canonicalize,
    canonicalizeEntries, sortCanonicalEntries, insertCanonicalEntry,
    canonicalEntryLt, lexLt, encodeSyn, head]

/-- Duplicate canonical key encodings are excluded from content-addressed
objects even though the general structural parser retains them. -/
theorem duplicate_integer_keys_not_canonical :
    ¬ Canonical (.map (CborSyn.mapOfList [
      (.primitive (.integer (.unsigned 1)), .primitive .true),
      (.primitive (.integer (.unsigned 1)), .primitive .false)])) := by
  intro canonical
  rw [Canonical] at canonical
  simp [CborSyn.mapOfList, canonicalMapKeyBytes, canonicalKeyBytes,
    encodeSyn, head] at canonical

/-- Width-preserving deterministic encoding. On `Reasonable` values every
length fits the definite argument field. This total representation policy is
not by itself RFC-valid or canonical; see `Canonical`. -/
def deterministic (value : {v : Cbor // v.Reasonable}) : Bytes :=
  bytesOfList (encodeSyn value.1)

/-- Deterministic bytes for the strict canonical artifact profile. -/
def canonicalDeterministic (value : {v : Cbor // Canonical v}) : Bytes :=
  deterministic ⟨value.1, value.2.reasonable⟩

/-- Executable checked entry point for canonical content-addressed artifacts. -/
def canonicalDeterministic? (value : Cbor) : Option Bytes :=
  if canonical : Canonical value then
    some (canonicalDeterministic ⟨value, canonical⟩)
  else
    none

@[simp] theorem canonicalDeterministic?_float16 (bits : UInt16) :
    canonicalDeterministic? (.primitive (.float16 bits)) = none := by
  simp [canonicalDeterministic?, Canonical]

@[simp] theorem canonicalDeterministic?_float32 (bits : UInt32) :
    canonicalDeterministic? (.primitive (.float32 bits)) = none := by
  simp [canonicalDeterministic?, Canonical]

@[simp] theorem canonicalDeterministic?_float64 (bits : UInt64) :
    canonicalDeterministic? (.primitive (.float64 bits)) = none := by
  simp [canonicalDeterministic?, Canonical]

/-- Relational form of the canonical artifact encoding. -/
def CanonicalEncoding (value : Cbor) (bytes : Bytes) : Prop :=
  ∃ canonical : Canonical value, bytes = canonicalDeterministic ⟨value, canonical⟩

/-- Canonical encoding is a partial function even though the general parser
accepts a broader structural language. -/
theorem canonicalEncoding_unique {value : Cbor} {left right : Bytes}
    (leftCanonical : CanonicalEncoding value left)
    (rightCanonical : CanonicalEncoding value right) : left = right := by
  rcases leftCanonical with ⟨_, rfl⟩
  rcases rightCanonical with ⟨_, rfl⟩
  rfl

/-- Executable checked entry point for callers holding an unrestricted CBOR
value. -/
def deterministic? (value : Cbor) : Option Bytes :=
  if h : value.Reasonable then some (deterministic ⟨value, h⟩) else none

/-- Relational presentation of the length-bounded, width-preserving encoder. -/
def LengthBoundedDeterministicEncoding (value : Cbor) (bytes : Bytes) : Prop :=
  ∃ h : value.Reasonable, bytes = deterministic ⟨value, h⟩

/-- Agreement with the chosen encoder proves uniqueness of the length-bounded
deterministic relation on every reasonable value. -/
theorem deterministic_unique {value : Cbor} {a b : Bytes}
    (ha : LengthBoundedDeterministicEncoding value a)
    (hb : LengthBoundedDeterministicEncoding value b) : a = b := by
  rcases ha with ⟨ha, rfl⟩
  rcases hb with ⟨hb, rfl⟩
  rfl

/-- Unreasonable values are outside the RFC deterministic relation. -/
theorem deterministic_undefined_of_not_reasonable {value : Cbor}
    (h : ¬ value.Reasonable) :
    ¬ ∃ bytes, LengthBoundedDeterministicEncoding value bytes := by
  rintro ⟨_, hv, _⟩
  exact h hv

end CborWire
end Nucleus
