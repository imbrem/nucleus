import Nucleus.Cbor.Reasonable
import Nucleus.Cbor.Containers
import Std.Tactic.BVDecide

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

@[simp] private theorem bytesOfList_listOfBytes (value : Bytes) :
    bytesOfList (listOfBytes value) = value := by
  rcases value with ⟨⟨data⟩⟩
  simp only [bytesOfList, listOfBytes]
  apply congrArg Bytes.mk
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact List.toList_data_toByteArray

@[simp] private theorem listOfBytes_bytesOfList (value : List UInt8) :
    listOfBytes (bytesOfList value) = value := by
  simp [listOfBytes, bytesOfList]

private def readNat : Nat → List UInt8 → Option (UInt64 × List UInt8)
  | 0, input => some (0, input)
  | n + 1, b :: rest => do
      let (tail, remaining) ← readNat n rest
      some ((b.toUInt64 <<< UInt64.ofNat (8 * n)) ||| tail, remaining)
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

/-- Decode one initial byte plus its optional fixed-width argument. Keeping
this cursor operation explicit lets every major type share one verified head
roundtrip. -/
private def parseHead? : List UInt8 →
    Option (Nat × Nat × Option UInt64 × List UInt8)
  | [] => none
  | head :: input => do
      let major := head.toNat / 32
      let info := head.toNat % 32
      let (argument, rest) ← argument? info input
      some (major, info, argument, rest)

private def takeBytes (n : UInt64) (input : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if n.toNat ≤ input.length then some (input.take n.toNat, input.drop n.toNat) else none

mutual
  private def parseItem : Nat → List UInt8 → Option (Cbor × List UInt8)
    | 0, _ => none
    | fuel + 1, input => do
        let (major, info, arg, rest) ← parseHead? input
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
  -- Every encoded item contributes a head byte, while definite array/map
  -- cursors spend one additional fuel unit per child/pair. Twice the byte
  -- length is therefore a structural bound even for maximally nested input.
  let (value, rest) ← parseItem (2 * input.length) input
  if rest.isEmpty then some value else none

private def beBytes (count : Nat) (n : UInt64) : List UInt8 :=
  (List.range count).map fun i =>
    (n >>> UInt64.ofNat (8 * (count - 1 - i))).toUInt8

set_option linter.flexible false in
private theorem readNat_beBytes_eight (value : UInt64) (suffix : List UInt8) :
    readNat 8 (beBytes 8 value ++ suffix) = some (value, suffix) := by
  change readNat 8 ([(value >>> 56).toUInt8, (value >>> 48).toUInt8,
    (value >>> 40).toUInt8, (value >>> 32).toUInt8,
    (value >>> 24).toUInt8, (value >>> 16).toUInt8,
    (value >>> 8).toUInt8, value.toUInt8] ++ suffix) = some (value, suffix)
  simp [readNat]
  bv_decide

set_option linter.flexible false in
private theorem readNat_beBytes_four (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xffff_ffff) :
    readNat 4 (beBytes 4 value ++ suffix) = some (value, suffix) := by
  change readNat 4 ([(value >>> 24).toUInt8, (value >>> 16).toUInt8,
    (value >>> 8).toUInt8, value.toUInt8] ++ suffix) = some (value, suffix)
  simp [readNat]
  bv_decide

set_option linter.flexible false in
private theorem readNat_beBytes_two (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xffff) :
    readNat 2 (beBytes 2 value ++ suffix) = some (value, suffix) := by
  change readNat 2 ([(value >>> 8).toUInt8, value.toUInt8] ++ suffix) =
    some (value, suffix)
  simp [readNat]
  bv_decide

set_option linter.flexible false in
private theorem readNat_beBytes_one (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xff) :
    readNat 1 (beBytes 1 value ++ suffix) = some (value, suffix) := by
  change readNat 1 ([value.toUInt8] ++ suffix) = some (value, suffix)
  simp [readNat]
  bv_decide

private theorem argument?_beBytes_one (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xff) :
    argument? 24 (beBytes 1 value ++ suffix) = some (some value, suffix) := by
  simp [argument?, readNat_beBytes_one value suffix fits]

private theorem argument?_beBytes_two (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xffff) :
    argument? 25 (beBytes 2 value ++ suffix) = some (some value, suffix) := by
  simp [argument?, readNat_beBytes_two value suffix fits]

private theorem argument?_beBytes_four (value : UInt64) (suffix : List UInt8)
    (fits : value ≤ 0xffff_ffff) :
    argument? 26 (beBytes 4 value ++ suffix) = some (some value, suffix) := by
  simp [argument?, readNat_beBytes_four value suffix fits]

private theorem argument?_beBytes_eight (value : UInt64) (suffix : List UInt8) :
    argument? 27 (beBytes 8 value ++ suffix) = some (some value, suffix) := by
  simp [argument?, readNat_beBytes_eight]

private def head (major : Nat) (n : UInt64) : List UInt8 :=
  if n < 24 then [UInt8.ofNat (32 * major + n.toNat)]
  else if n ≤ 0xff then UInt8.ofNat (32 * major + 24) :: beBytes 1 n
  else if n ≤ 0xffff then UInt8.ofNat (32 * major + 25) :: beBytes 2 n
  else if n ≤ 0xffffffff then UInt8.ofNat (32 * major + 26) :: beBytes 4 n
  else UInt8.ofNat (32 * major + 27) :: beBytes 8 n

private theorem head_length_pos (major : Nat) (value : UInt64) :
    0 < (head major value).length := by
  unfold head
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

private def headInfo (value : UInt64) : Nat :=
  if value < 24 then value.toNat
  else if value ≤ 0xff then 24
  else if value ≤ 0xffff then 25
  else if value ≤ 0xffff_ffff then 26
  else 27

private theorem splitHeadByte (major info : Nat) (majorFits : major < 8)
    (infoFits : info < 32) :
    (UInt8.ofNat (32 * major + info)).toNat / 32 = major ∧
      (UInt8.ofNat (32 * major + info)).toNat % 32 = info := by
  change ((32 * major + info) % 256) / 32 = major ∧
    ((32 * major + info) % 256) % 32 = info
  omega

set_option linter.flexible false in
private theorem parseHead?_head (major : Nat) (value : UInt64)
    (suffix : List UInt8) (majorFits : major < 8) :
    parseHead? (head major value ++ suffix) =
      some (major, headInfo value, some value, suffix) := by
  unfold head headInfo
  split <;> rename_i small
  · have valueFits : value.toNat < 24 := by
      simpa using UInt64.lt_iff_toNat_lt.mp small
    have split := splitHeadByte major value.toNat majorFits (by omega)
    simp only [List.cons_append, List.nil_append, parseHead?]
    rw [split.1, split.2]
    simp [argument?, valueFits]
  split <;> rename_i oneByte
  · have split := splitHeadByte major 24 majorFits (by decide)
    simp only [List.cons_append, parseHead?]
    rw [split.1, split.2, argument?_beBytes_one value suffix oneByte]
    rfl
  split <;> rename_i twoBytes
  · have split := splitHeadByte major 25 majorFits (by decide)
    simp only [List.cons_append, parseHead?]
    rw [split.1, split.2, argument?_beBytes_two value suffix twoBytes]
    rfl
  split <;> rename_i fourBytes
  · have split := splitHeadByte major 26 majorFits (by decide)
    simp only [List.cons_append, parseHead?]
    rw [split.1, split.2, argument?_beBytes_four value suffix fourBytes]
    rfl
  · have split := splitHeadByte major 27 majorFits (by decide)
    simp only [List.cons_append, parseHead?]
    rw [split.1, split.2, argument?_beBytes_eight value suffix]
    rfl

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

/-! ## Primitive cursor roundtrips -/

private theorem parseItem_encode_unsigned (fuel : Nat) (value : UInt64)
    (suffix : List UInt8) :
    parseItem (fuel + 1)
      (encodeSyn (.primitive (.integer (.unsigned value))) ++ suffix) =
      some (.primitive (.integer (.unsigned value)), suffix) := by
  rw [encodeSyn]
  simp only [parseItem]
  rw [parseHead?_head 0 value suffix (by decide)]
  rfl

private theorem parseItem_encode_negative (fuel : Nat) (value : UInt64)
    (suffix : List UInt8) :
    parseItem (fuel + 1)
      (encodeSyn (.primitive (.integer (.negative value))) ++ suffix) =
      some (.primitive (.integer (.negative value)), suffix) := by
  rw [encodeSyn]
  simp only [parseItem]
  rw [parseHead?_head 1 value suffix (by decide)]
  rfl

private theorem takeBytes_length (payload suffix : List UInt8)
    (fits : payload.length ≤ Bytes.maxDefiniteLength) :
    takeBytes (UInt64.ofNat payload.length) (payload ++ suffix) =
      some (payload, suffix) := by
  have lengthFits : payload.length < 2 ^ 64 := by
    unfold Bytes.maxDefiniteLength at fits
    omega
  have lengthFits' : payload.length < 18446744073709551616 := by
    simpa using lengthFits
  have roundtrip : (UInt64.ofNat payload.length).toNat = payload.length := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt lengthFits']
  simp [takeBytes, roundtrip]

set_option linter.flexible false in
private theorem parseItem_encode_bytes (fuel : Nat) (value : Bytes)
    (suffix : List UInt8)
    (fits : value.length ≤ Bytes.maxDefiniteLength) :
    parseItem (fuel + 1) (encodeSyn (.primitive (.bytes value)) ++ suffix) =
      some (.primitive (.bytes value), suffix) := by
  let payload := listOfBytes value
  have payloadLength : payload.length = value.length := by
    simp [payload, listOfBytes, Bytes.length]
  have payloadFits : payload.length ≤ Bytes.maxDefiniteLength := by
    simpa [payloadLength] using fits
  rw [encodeSyn]
  change parseItem (fuel + 1)
    (head 2 (UInt64.ofNat value.length) ++ payload ++ suffix) = _
  rw [List.append_assoc]
  simp only [parseItem]
  rw [parseHead?_head 2 (UInt64.ofNat value.length) (payload ++ suffix) (by decide)]
  rw [← payloadLength]
  change (do
    let (chunk, rest) ← takeBytes (UInt64.ofNat payload.length) (payload ++ suffix)
    some (CborSyn.primitive (.bytes (bytesOfList chunk)), rest)) = _
  rw [takeBytes_length payload suffix payloadFits]
  change some (CborSyn.primitive (.bytes (bytesOfList payload)), suffix) = _
  have payloadRoundtrip : bytesOfList payload = value := by
    simp [payload]
  rw [payloadRoundtrip]

private theorem fromUTF8?_toUTF8 (value : String) :
    String.fromUTF8? value.toUTF8 = some value := by
  rw [String.fromUTF8?]
  simp only [String.toUTF8_eq_toByteArray]
  split
  next valid =>
    congr 1
  next invalid =>
    exact (invalid value.isValidUTF8).elim

set_option linter.flexible false in
private theorem parseItem_encode_text (fuel : Nat) (value : String)
    (suffix : List UInt8)
    (fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength) :
    parseItem (fuel + 1) (encodeSyn (.primitive (.text value)) ++ suffix) =
      some (.primitive (.text value), suffix) := by
  let payload := value.toUTF8.data.toList
  have payloadLength : payload.length = value.toUTF8.size := by
    simp [payload]
  have payloadFits : payload.length ≤ Bytes.maxDefiniteLength := by
    simpa [payloadLength] using fits
  rw [encodeSyn]
  change parseItem (fuel + 1)
    (head 3 (UInt64.ofNat value.toUTF8.size) ++ payload ++ suffix) = _
  rw [List.append_assoc]
  simp only [parseItem]
  rw [parseHead?_head 3 (UInt64.ofNat value.toUTF8.size)
    (payload ++ suffix) (by decide)]
  rw [← payloadLength]
  change (do
    let (chunk, rest) ← takeBytes (UInt64.ofNat payload.length) (payload ++ suffix)
    let text ← String.fromUTF8? chunk.toByteArray
    some (CborSyn.primitive (.text text), rest)) = _
  rw [takeBytes_length payload suffix payloadFits]
  have payloadRoundtrip : payload.toByteArray = value.toUTF8 := by
    apply ByteArray.ext
    simp [payload]
  have decoded : String.fromUTF8? value.toByteArray = some value := by
    simpa using fromUTF8?_toUTF8 value
  simp [payloadRoundtrip, decoded]

private theorem encodeSyn_simple_eq_head (value : UInt8) :
    encodeSyn (.primitive (.simple value)) = head 7 value.toUInt64 := by
  unfold encodeSyn head
  split <;> rename_i small
  · have small' : value.toUInt64 < 24 := by
      exact UInt64.lt_iff_toNat_lt.mpr (by simpa using small)
    rw [if_pos small']
    congr 2
  · have notSmall : ¬ value.toUInt64 < 24 := by
      intro less
      exact small (by simpa using UInt64.lt_iff_toNat_lt.mp less)
    rw [if_neg notSmall]
    have oneByte : value.toUInt64 ≤ 0xff := by
      bv_decide
    rw [if_pos oneByte]
    simp [beBytes]

private theorem parseItem_encode_simple (fuel : Nat) (value : UInt8)
    (suffix : List UInt8) :
    parseItem (fuel + 1) (encodeSyn (.primitive (.simple value)) ++ suffix) =
      some (.primitive (.simple value), suffix) := by
  rw [encodeSyn_simple_eq_head]
  simp only [parseItem]
  rw [parseHead?_head 7 value.toUInt64 suffix (by decide)]
  have oneByte : value.toUInt64 ≤ 0xff := by
    bv_decide
  have valueFits : value.toNat ≤ 255 := by
    have := value.toNat_lt
    omega
  simp only [headInfo, oneByte, if_pos]
  dsimp
  simp only [valueFits, if_pos]
  generalize infoDef : (if value.toUInt64 < 24 then value.toNat else 24) = info at ⊢
  have infoLe : info ≤ 24 := by
    rw [← infoDef]
    split
    · have : value.toNat < 24 := by
        simpa only [UInt8.toNat_toUInt64, UInt64.toNat_ofNat] using
          UInt64.lt_iff_toNat_lt.mp ‹value.toUInt64 < 24›
      omega
    · omega
  have ne25 : info ≠ 25 := by omega
  have ne26 : info ≠ 26 := by omega
  have ne27 : info ≠ 27 := by omega
  have ne31 : info ≠ 31 := by omega
  simp

private theorem parseItem_encode_tag (fuel : Nat) (number : UInt64)
    (content parsed : Cbor) (suffix : List UInt8)
    (contentRoundtrip :
      parseItem fuel (encodeSyn content ++ suffix) = some (parsed, suffix)) :
    parseItem (fuel + 1) (encodeSyn (.tag number content) ++ suffix) =
      some (.tag number parsed, suffix) := by
  rw [encodeSyn]
  rw [List.append_assoc]
  simp only [parseItem]
  rw [parseHead?_head 6 number (encodeSyn content ++ suffix) (by decide)]
  dsimp
  rw [contentRoundtrip]
  simp

/-! ## Array cursor roundtrips

Array decoding spends one unit of fuel for every cons cell before decoding its
head. The explicit cursor budget accounts for those steps as well as nested
items; ordinary CBOR node count alone is not a sufficient bound.
-/

mutual
  /-- Exact structural fuel sufficient for one deterministic item parse. -/
  private def cursorBudget : Cbor → Nat
    | .primitive _ => 1
    | .array items => arrayCursorBudget items + 1
    | .map entries => mapCursorBudget entries + 1
    | .tag _ content => cursorBudget content + 1

  /-- Array-list fuel includes the cursor step spent by each cons cell. -/
  private def arrayCursorBudget : CborSyn .array → Nat
    | .arrayNil => 0
    | .arrayCons head tail =>
        max (cursorBudget head) (arrayCursorBudget tail) + 1

  /-- Map-list fuel includes one cursor step per key/value pair. -/
  private def mapCursorBudget : CborSyn .map → Nat
    | .mapNil => 0
    | .mapCons key value tail =>
        max (max (cursorBudget key) (cursorBudget value))
          (mapCursorBudget tail) + 1
end

private def CursorRoundtrip (source parsed : Cbor) : Prop :=
  ∀ fuel suffix, cursorBudget source ≤ fuel →
    parseItem fuel (encodeSyn source ++ suffix) = some (parsed, suffix)

private inductive ArrayCursorRoundtrip :
    CborSyn .array → CborSyn .array → Prop where
  | nil : ArrayCursorRoundtrip .arrayNil .arrayNil
  | cons {sourceHead parsedHead : Cbor}
      {sourceTail parsedTail : CborSyn .array}
      (head : CursorRoundtrip sourceHead parsedHead)
      (tail : ArrayCursorRoundtrip sourceTail parsedTail) :
      ArrayCursorRoundtrip (.arrayCons sourceHead sourceTail)
        (.arrayCons parsedHead parsedTail)

@[simp] private theorem arrayOfList_toArrayList_self :
    (items : CborSyn .array) → CborSyn.arrayOfList items.toArrayList = items
  | .arrayNil => by simp [CborSyn.toArrayList, CborSyn.arrayOfList]
  | .arrayCons head tail => by
      simp [CborSyn.toArrayList, CborSyn.arrayOfList,
        arrayOfList_toArrayList_self tail]

private theorem parseItems_encode_array {source parsed : CborSyn .array}
    (roundtrip : ArrayCursorRoundtrip source parsed) (fuel : Nat)
    (suffix : List UInt8) (enough : arrayCursorBudget source ≤ fuel) :
    parseItems fuel source.arrayLength (encodeSyn source ++ suffix) =
      some (parsed.toArrayList, suffix) := by
  induction roundtrip generalizing fuel with
  | nil => simp [CborSyn.arrayLength, encodeSyn, parseItems,
      CborSyn.toArrayList]
  | @cons sourceHead parsedHead sourceTail parsedTail head tail ih =>
      cases fuel with
      | zero => simp [arrayCursorBudget] at enough
      | succ fuel =>
          have combined :
              max (cursorBudget sourceHead) (arrayCursorBudget sourceTail) ≤
                fuel := by
            simpa [arrayCursorBudget] using enough
          have headEnough : cursorBudget sourceHead ≤ fuel :=
            le_trans (Nat.le_max_left _ _) combined
          have tailEnough : arrayCursorBudget sourceTail ≤ fuel :=
            le_trans (Nat.le_max_right _ _) combined
          simp only [CborSyn.arrayLength, encodeSyn,
            List.append_assoc, parseItems]
          rw [head fuel (encodeSyn sourceTail ++ suffix) headEnough]
          dsimp
          rw [ih fuel tailEnough]
          simp [CborSyn.toArrayList]

private theorem parseItem_encode_array {source parsed : CborSyn .array}
    (fits : source.arrayLength ≤ Bytes.maxDefiniteLength)
    (roundtrip : ArrayCursorRoundtrip source parsed) (fuel : Nat)
    (suffix : List UInt8) (enough : cursorBudget (.array source) ≤ fuel) :
    parseItem fuel (encodeSyn (.array source) ++ suffix) =
      some (.array parsed, suffix) := by
  cases fuel with
  | zero => simp [cursorBudget] at enough
  | succ fuel =>
      have itemsEnough : arrayCursorBudget source ≤ fuel := by
        simpa [cursorBudget] using enough
      have lengthFits : source.arrayLength < 2 ^ 64 := by
        unfold Bytes.maxDefiniteLength at fits
        omega
      have lengthFits' : source.arrayLength < 18446744073709551616 := by
        simpa using lengthFits
      have lengthRoundtrip :
          (UInt64.ofNat source.arrayLength).toNat = source.arrayLength := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt lengthFits']
      rw [encodeSyn, List.append_assoc]
      simp only [parseItem]
      rw [parseHead?_head 4 (UInt64.ofNat source.arrayLength)
        (encodeSyn source ++ suffix) (by decide)]
      dsimp
      rw [lengthRoundtrip]
      rw [parseItems_encode_array roundtrip fuel suffix itemsEnough]
      simp

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

private def encodeEntry (entry : Cbor × Cbor) :
    List UInt8 × List UInt8 :=
  (encodeSyn entry.1, encodeSyn entry.2)

@[simp] private theorem canonicalEntryLt_eq
    (left right : Cbor × Cbor) :
    canonicalEntryLt left right = lexLt (encodeEntry left).1 (encodeEntry right).1 :=
  rfl

/-- Encoding commutes with one insertion into deterministic map-key order.
The false branch intentionally inserts after an equal key, retaining the
encoder's duplicate-key reversal behavior. -/
private theorem map_encodeEntry_insertCanonicalEntry
    (entry : Cbor × Cbor) (entries : List (Cbor × Cbor)) :
    (insertCanonicalEntry entry entries).map encodeEntry =
      insertEntry (encodeEntry entry) (entries.map encodeEntry) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [insertCanonicalEntry, insertEntry, List.map_cons]
      rw [canonicalEntryLt_eq]
      split <;> simp_all

/-- The value-level and byte-level insertion sorts are the same algorithm.
In particular this theorem does not quotient maps by keys or discard duplicate
entries. -/
private theorem map_encodeEntry_sortCanonicalEntries
    (entries : List (Cbor × Cbor)) :
    (sortCanonicalEntries entries).map encodeEntry =
      sortEntries (entries.map encodeEntry) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [sortCanonicalEntries, List.map_cons]
      change (insertCanonicalEntry head (sortCanonicalEntries tail)).map encodeEntry =
        insertEntry (encodeEntry head) (sortEntries (tail.map encodeEntry))
      rw [map_encodeEntry_insertCanonicalEntry, ih]

/-- Encoding a map syntax rebuilt from a list preserves that list's encounter
order. This is the bridge used after `parsePairs`, whose result is likewise in
wire order. -/
@[simp] private theorem encodeEntries_mapOfList
    (entries : List (Cbor × Cbor)) :
    encodeEntries (CborSyn.mapOfList entries) = entries.map encodeEntry := by
  induction entries with
  | nil => simp [CborSyn.mapOfList, encodeEntries]
  | cons head tail ih =>
      rcases head with ⟨key, value⟩
      simp [CborSyn.mapOfList, encodeEntries, encodeEntry, ih]

/-- Rebuilding the value-level sorted map and then encoding its entries gives
exactly the encoder's sorted byte pairs. -/
private theorem encodeEntries_mapOfList_sortCanonicalEntries
    (entries : List (Cbor × Cbor)) :
    encodeEntries (CborSyn.mapOfList (sortCanonicalEntries entries)) =
      sortEntries (entries.map encodeEntry) := by
  rw [encodeEntries_mapOfList, map_encodeEntry_sortCanonicalEntries]

private theorem encodeEntries_length : (entries : CborSyn .map) →
    (encodeEntries entries).length = entries.mapLength
  | .mapNil => by simp [encodeEntries, CborSyn.mapLength]
  | .mapCons key value tail => by
      simp [encodeEntries, CborSyn.mapLength, encodeEntries_length tail]

private theorem flatMap_encodeEntries : (entries : CborSyn .map) →
    (encodeEntries entries).flatMap (fun entry => entry.1 ++ entry.2) =
      encodeSyn entries
  | .mapNil => by simp [encodeEntries, encodeSyn]
  | .mapCons key value tail => by
      simp [encodeEntries, encodeSyn, flatMap_encodeEntries tail]

/-! ## Map cursor roundtrips -/

/-- Pairwise cursor roundtrips in parser encounter order. Keeping this relation
on map syntax (rather than a finite-map quotient) preserves duplicate keys and
their values exactly. -/
private inductive MapCursorRoundtrip :
    CborSyn .map → CborSyn .map → Prop where
  | nil : MapCursorRoundtrip .mapNil .mapNil
  | cons {sourceKey sourceValue parsedKey parsedValue : Cbor}
      {sourceTail parsedTail : CborSyn .map}
      (key : CursorRoundtrip sourceKey parsedKey)
      (value : CursorRoundtrip sourceValue parsedValue)
      (tail : MapCursorRoundtrip sourceTail parsedTail) :
      MapCursorRoundtrip (.mapCons sourceKey sourceValue sourceTail)
        (.mapCons parsedKey parsedValue parsedTail)

@[simp] private theorem mapOfList_toMapList_self :
    (entries : CborSyn .map) → CborSyn.mapOfList entries.toMapList = entries
  | .mapNil => by simp [CborSyn.toMapList, CborSyn.mapOfList]
  | .mapCons key value tail => by
      simp [CborSyn.toMapList, CborSyn.mapOfList,
        mapOfList_toMapList_self tail]

/-- `parsePairs` consumes deterministic entry bytes in their encoded encounter
order. Equal keys remain separate entries; no lookup or deduplication occurs. -/
private theorem parsePairs_encode_map {source parsed : CborSyn .map}
    (roundtrip : MapCursorRoundtrip source parsed) (fuel : Nat)
    (suffix : List UInt8) (enough : mapCursorBudget source ≤ fuel) :
    parsePairs fuel source.mapLength (encodeSyn source ++ suffix) =
      some (parsed.toMapList, suffix) := by
  induction roundtrip generalizing fuel suffix with
  | nil => simp [CborSyn.mapLength, encodeSyn, parsePairs,
      CborSyn.toMapList]
  | @cons sourceKey sourceValue parsedKey parsedValue sourceTail parsedTail
      key value tail ih =>
      cases fuel with
      | zero => simp [mapCursorBudget] at enough
      | succ fuel =>
          have combined :
              max (max (cursorBudget sourceKey) (cursorBudget sourceValue))
                (mapCursorBudget sourceTail) ≤ fuel := by
            simpa [mapCursorBudget] using enough
          have keyEnough : cursorBudget sourceKey ≤ fuel :=
            le_trans (Nat.le_max_left _ _)
              (le_trans (Nat.le_max_left _ _) combined)
          have valueEnough : cursorBudget sourceValue ≤ fuel :=
            le_trans (Nat.le_max_right _ _)
              (le_trans (Nat.le_max_left _ _) combined)
          have tailEnough : mapCursorBudget sourceTail ≤ fuel :=
            le_trans (Nat.le_max_right _ _) combined
          simp only [CborSyn.mapLength, encodeSyn,
            List.append_assoc, parsePairs]
          rw [key fuel
            (encodeSyn sourceValue ++ (encodeSyn sourceTail ++ suffix)) keyEnough]
          dsimp
          rw [value fuel (encodeSyn sourceTail ++ suffix) valueEnough]
          dsimp
          rw [ih fuel suffix tailEnough]
          simp [CborSyn.toMapList]

/-- Definite-map decoding recovers the exact map syntax supplied by the
entrywise cursor relation, in wire order. -/
private theorem parseItem_encode_ordered_map {source parsed : CborSyn .map}
    (fits : source.mapLength ≤ Bytes.maxDefiniteLength)
    (ordered : sortEntries (encodeEntries source) = encodeEntries source)
    (roundtrip : MapCursorRoundtrip source parsed) (fuel : Nat)
    (suffix : List UInt8) (enough : cursorBudget (.map source) ≤ fuel) :
    parseItem fuel (encodeSyn (.map source) ++ suffix) =
      some (.map parsed, suffix) := by
  cases fuel with
  | zero => simp [cursorBudget] at enough
  | succ fuel =>
      have pairsEnough : mapCursorBudget source ≤ fuel := by
        simpa [cursorBudget] using enough
      have lengthFits : source.mapLength < 2 ^ 64 := by
        unfold Bytes.maxDefiniteLength at fits
        omega
      have lengthFits' : source.mapLength < 18446744073709551616 := by
        simpa using lengthFits
      have lengthRoundtrip :
          (UInt64.ofNat source.mapLength).toNat = source.mapLength := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt lengthFits']
      rw [encodeSyn, List.append_assoc]
      rw [ordered]
      rw [encodeEntries_length]
      simp only [parseItem]
      rw [parseHead?_head 5 (UInt64.ofNat source.mapLength)
        ((encodeEntries source).flatMap
          (fun entry => entry.1 ++ entry.2) ++ suffix) (by decide)]
      dsimp
      rw [lengthRoundtrip]
      rw [flatMap_encodeEntries]
      change (do
        let (items, remaining) ←
          parsePairs fuel source.mapLength (encodeSyn source ++ suffix)
        some (CborSyn.map (CborSyn.mapOfList items), remaining)) = _
      rw [parsePairs_encode_map roundtrip fuel suffix pairsEnough]
      simp

/-! ## Canonical wire-order evidence

This is the consumer-facing profile needed by content-addressed arena
artifacts.  Unlike unrestricted `CborSyn`, every map is already in the exact
deterministic byte order emitted on the wire.  The evidence is structural and
contains no parser execution trace.
-/

mutual

/-- A length-bounded CBOR value whose maps already occur in deterministic wire
order. Duplicate entries are retained; combine this with `Canonical` when map
key uniqueness is required for content-addressed objects. -/
inductive WireNormal : Cbor → Prop where
  | unsigned (value : UInt64) :
      WireNormal (.primitive (.integer (.unsigned value)))
  | negative (value : UInt64) :
      WireNormal (.primitive (.integer (.negative value)))
  | bytes (value : Bytes) (fits : value.length ≤ Bytes.maxDefiniteLength) :
      WireNormal (.primitive (.bytes value))
  | text (value : String)
      (fits : value.toUTF8.size ≤ Bytes.maxDefiniteLength) :
      WireNormal (.primitive (.text value))
  | simple (value : UInt8) : WireNormal (.primitive (.simple value))
  | array (items : CborSyn .array)
      (fits : items.arrayLength ≤ Bytes.maxDefiniteLength)
      (normal : WireNormalArray items) : WireNormal (.array items)
  | map (entries : CborSyn .map)
      (fits : entries.mapLength ≤ Bytes.maxDefiniteLength)
      (ordered : sortEntries (encodeEntries entries) = encodeEntries entries)
      (normal : WireNormalMap entries) : WireNormal (.map entries)
  | tag (number : UInt64) (content : Cbor) (normal : WireNormal content) :
      WireNormal (.tag number content)

private inductive WireNormalArray : CborSyn .array → Prop where
  | nil : WireNormalArray .arrayNil
  | cons {head : Cbor} {tail : CborSyn .array}
      (headNormal : WireNormal head) (tailNormal : WireNormalArray tail) :
      WireNormalArray (.arrayCons head tail)

private inductive WireNormalMap : CborSyn .map → Prop where
  | nil : WireNormalMap .mapNil
  | cons {key value : Cbor} {tail : CborSyn .map}
      (keyNormal : WireNormal key) (valueNormal : WireNormal value)
      (tailNormal : WireNormalMap tail) :
      WireNormalMap (.mapCons key value tail)

end

namespace WireNormal

/-- Build wire-normal evidence for an array from its list representation.
This keeps the private indexed-tail evidence out of generated certificates. -/
theorem arrayOfList (values : List Cbor)
    (fits : values.length ≤ Bytes.maxDefiniteLength)
    (normal : ∀ value ∈ values, WireNormal value) :
    WireNormal (Cbor.arrayOfList values) := by
  have lengthEq : (CborSyn.arrayOfList values).arrayLength = values.length := by
    clear fits normal
    induction values with
    | nil => simp [CborSyn.arrayOfList, CborSyn.arrayLength]
    | cons head tail ih => simp [CborSyn.arrayOfList, CborSyn.arrayLength, ih]
  have itemsNormal : WireNormalArray (CborSyn.arrayOfList values) := by
    clear fits lengthEq
    induction values with
    | nil => exact .nil
    | cons head tail ih =>
        exact .cons (normal head (by simp))
          (ih fun value member => normal value (by simp [member]))
  apply WireNormal.array (CborSyn.arrayOfList values)
  · simpa [lengthEq] using fits
  · exact itemsNormal

/-- Build wire-normal evidence for a map from its encounter-order list.
The ordering premise is intentionally explicit: generated certificates must
show that their map entries already have deterministic encoded-key order. -/
theorem mapOfList (entries : List (Cbor × Cbor))
    (fits : entries.length ≤ Bytes.maxDefiniteLength)
    (ordered : sortEntries (encodeEntries (CborSyn.mapOfList entries)) =
      encodeEntries (CborSyn.mapOfList entries))
    (normal : ∀ entry ∈ entries,
      WireNormal entry.1 ∧ WireNormal entry.2) :
    WireNormal (.map (CborSyn.mapOfList entries)) := by
  have lengthEq : (CborSyn.mapOfList entries).mapLength = entries.length := by
    clear fits ordered normal
    induction entries with
    | nil => simp [CborSyn.mapOfList, CborSyn.mapLength]
    | cons entry tail ih =>
        rcases entry with ⟨key, value⟩
        simp [CborSyn.mapOfList, CborSyn.mapLength, ih]
  have entriesNormal : WireNormalMap (CborSyn.mapOfList entries) := by
    clear fits ordered lengthEq
    induction entries with
    | nil => exact .nil
    | cons entry tail ih =>
        rcases entry with ⟨key, value⟩
        exact .cons (normal (key, value) (by simp)).1
          (normal (key, value) (by simp)).2
          (ih fun entry member => normal entry (by simp [member]))
  apply WireNormal.map (CborSyn.mapOfList entries)
  · simpa [lengthEq] using fits
  · exact ordered
  · exact entriesNormal

end WireNormal

mutual

/-- Structural decision procedure for deterministic wire-normal evidence.
This remains kernel-reduced evidence; it does not use the native compiler. -/
def wireNormalDecidable (value : Cbor) : Decidable (WireNormal value) :=
  match value with
  | .primitive (.integer (.unsigned value)) => isTrue (.unsigned value)
  | .primitive (.integer (.negative value)) => isTrue (.negative value)
  | .primitive (.bytes value) =>
      match Nat.decLe value.length Bytes.maxDefiniteLength with
      | isTrue fits => isTrue (.bytes value fits)
      | isFalse tooLong => isFalse fun normal => by
          cases normal
          exact tooLong ‹_›
  | .primitive (.text value) =>
      match Nat.decLe value.toUTF8.size Bytes.maxDefiniteLength with
      | isTrue fits => isTrue (.text value fits)
      | isFalse tooLong => isFalse fun normal => by
          cases normal
          exact tooLong ‹_›
  | .primitive (.simple value) => isTrue (.simple value)
  | .primitive (.float16 _) => isFalse fun normal => by cases normal
  | .primitive (.float32 _) => isFalse fun normal => by cases normal
  | .primitive (.float64 _) => isFalse fun normal => by cases normal
  | .array items =>
      match Nat.decLe items.arrayLength Bytes.maxDefiniteLength,
          wireNormalArrayDecidable items with
      | isTrue fits, isTrue normal => isTrue (.array items fits normal)
      | isFalse tooLong, _ => isFalse fun evidence => by
          cases evidence
          exact tooLong ‹_›
      | _, isFalse invalid => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›
  | .map entries =>
      match Nat.decLe entries.mapLength Bytes.maxDefiniteLength,
          decEq (sortEntries (encodeEntries entries)) (encodeEntries entries),
          wireNormalMapDecidable entries with
      | isTrue fits, isTrue ordered, isTrue normal =>
          isTrue (.map entries fits ordered normal)
      | isFalse tooLong, _, _ => isFalse fun evidence => by
          cases evidence
          exact tooLong ‹_›
      | _, isFalse unordered, _ => isFalse fun evidence => by
          cases evidence
          exact unordered ‹_›
      | _, _, isFalse invalid => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›
  | .tag number content =>
      match wireNormalDecidable content with
      | isTrue normal => isTrue (.tag number content normal)
      | isFalse invalid => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›

private def wireNormalArrayDecidable (items : CborSyn .array) :
    Decidable (WireNormalArray items) :=
  match items with
  | .arrayNil => isTrue .nil
  | .arrayCons head tail =>
      match wireNormalDecidable head, wireNormalArrayDecidable tail with
      | isTrue headNormal, isTrue tailNormal =>
          isTrue (.cons headNormal tailNormal)
      | isFalse invalid, _ => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›
      | _, isFalse invalid => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›

private def wireNormalMapDecidable (entries : CborSyn .map) :
    Decidable (WireNormalMap entries) :=
  match entries with
  | .mapNil => isTrue .nil
  | .mapCons key value tail =>
      match wireNormalDecidable key, wireNormalDecidable value,
          wireNormalMapDecidable tail with
      | isTrue keyNormal, isTrue valueNormal, isTrue tailNormal =>
          isTrue (.cons keyNormal valueNormal tailNormal)
      | isFalse invalid, _, _ => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›
      | _, isFalse invalid, _ => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›
      | _, _, isFalse invalid => isFalse fun evidence => by
          cases evidence
          exact invalid ‹_›

end

instance (value : Cbor) : Decidable (WireNormal value) :=
  wireNormalDecidable value

mutual

/-- Wire-normal evidence implies the existing deterministic encoder domain. -/
theorem WireNormal.reasonable {value : Cbor} (normal : WireNormal value) :
    value.Reasonable := by
  cases normal with
  | unsigned value => exact .integer (.unsigned value)
  | negative value => exact .integer (.negative value)
  | bytes value fits => exact .bytes value fits
  | text value fits => exact .text value fits
  | simple value => exact .simple value
  | array items fits itemsNormal =>
      exact .array items fits (WireNormalArray.reasonable itemsNormal)
  | map entries fits _ entriesNormal =>
      exact .map entries fits (WireNormalMap.reasonable entriesNormal)
  | tag number content contentNormal =>
      exact .tag number content (WireNormal.reasonable contentNormal)

private theorem WireNormalArray.reasonable {items : CborSyn .array}
    (normal : WireNormalArray items) : items.Reasonable := by
  cases normal with
  | nil => exact .arrayNil
  | cons headNormal tailNormal =>
      exact .arrayCons _ _ (WireNormal.reasonable headNormal)
        (WireNormalArray.reasonable tailNormal)

private theorem WireNormalMap.reasonable {entries : CborSyn .map}
    (normal : WireNormalMap entries) : entries.Reasonable := by
  cases normal with
  | nil => exact .mapNil
  | cons keyNormal valueNormal tailNormal =>
      exact .mapCons _ _ _ (WireNormal.reasonable keyNormal)
        (WireNormal.reasonable valueNormal)
        (WireNormalMap.reasonable tailNormal)

end

mutual

private theorem WireNormal.cursorRoundtrip {source : Cbor}
    (normal : WireNormal source) : CursorRoundtrip source source := by
  intro fuel suffix enough
  cases normal with
  | unsigned value =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel => simpa [Nat.succ_eq_add_one] using
          parseItem_encode_unsigned fuel value suffix
  | negative value =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel => simpa [Nat.succ_eq_add_one] using
          parseItem_encode_negative fuel value suffix
  | bytes value fits =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel => simpa [Nat.succ_eq_add_one] using
          parseItem_encode_bytes fuel value suffix fits
  | text value fits =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel => simpa [Nat.succ_eq_add_one] using
          parseItem_encode_text fuel value suffix fits
  | simple value =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel => simpa [Nat.succ_eq_add_one] using
          parseItem_encode_simple fuel value suffix
  | array items fits itemsNormal =>
      exact parseItem_encode_array fits
        (WireNormalArray.cursorRoundtrip itemsNormal) fuel suffix enough
  | map entries fits ordered entriesNormal =>
      exact parseItem_encode_ordered_map fits ordered
        (WireNormalMap.cursorRoundtrip entriesNormal) fuel suffix enough
  | tag number content contentNormal =>
      cases fuel with
      | zero => simp [cursorBudget] at enough
      | succ fuel =>
          have childEnough : cursorBudget content ≤ fuel := by
            simpa [cursorBudget] using enough
          exact parseItem_encode_tag fuel number content content suffix
            (WireNormal.cursorRoundtrip contentNormal fuel suffix childEnough)

private theorem WireNormalArray.cursorRoundtrip {source : CborSyn .array}
    (normal : WireNormalArray source) : ArrayCursorRoundtrip source source := by
  cases normal with
  | nil => exact .nil
  | cons headNormal tailNormal =>
      exact .cons (WireNormal.cursorRoundtrip headNormal)
        (WireNormalArray.cursorRoundtrip tailNormal)

private theorem WireNormalMap.cursorRoundtrip {source : CborSyn .map}
    (normal : WireNormalMap source) : MapCursorRoundtrip source source := by
  cases normal with
  | nil => exact .nil
  | cons keyNormal valueNormal tailNormal =>
      exact .cons (WireNormal.cursorRoundtrip keyNormal)
        (WireNormal.cursorRoundtrip valueNormal)
        (WireNormalMap.cursorRoundtrip tailNormal)

end

mutual

private theorem WireNormal.cursorBudget_bound {source : Cbor}
    (normal : WireNormal source) :
    cursorBudget source + 1 ≤ 2 * (encodeSyn source).length := by
  cases normal with
  | unsigned value =>
      have positive := head_length_pos 0 value
      simp only [cursorBudget, encodeSyn]
      omega
  | negative value =>
      have positive := head_length_pos 1 value
      simp only [cursorBudget, encodeSyn]
      omega
  | bytes value _ =>
      have positive := head_length_pos 2 (UInt64.ofNat value.length)
      simp only [cursorBudget, encodeSyn, List.length_append]
      omega
  | text value _ =>
      have positive := head_length_pos 3 (UInt64.ofNat value.toUTF8.size)
      simp only [cursorBudget, encodeSyn, List.length_append]
      omega
  | simple value =>
      simp only [cursorBudget, encodeSyn]
      split <;> simp
  | array items _ itemsNormal =>
      have itemsBound := WireNormalArray.cursorBudget_bound itemsNormal
      have positive := head_length_pos 4 (UInt64.ofNat items.arrayLength)
      simp only [cursorBudget, encodeSyn, List.length_append]
      omega
  | map entries _ ordered entriesNormal =>
      have entriesBound := WireNormalMap.cursorBudget_bound entriesNormal
      have positive := head_length_pos 5 (UInt64.ofNat entries.mapLength)
      simp only [cursorBudget, encodeSyn, List.length_append]
      rw [ordered, encodeEntries_length, flatMap_encodeEntries]
      omega
  | tag number content contentNormal =>
      have contentBound := WireNormal.cursorBudget_bound contentNormal
      have positive := head_length_pos 6 number
      simp only [cursorBudget, encodeSyn, List.length_append]
      omega

private theorem WireNormalArray.cursorBudget_bound {source : CborSyn .array}
    (normal : WireNormalArray source) :
    arrayCursorBudget source ≤ 2 * (encodeSyn source).length := by
  cases normal with
  | nil => simp [arrayCursorBudget, encodeSyn]
  | @cons head tail headNormal tailNormal =>
      have headBound := WireNormal.cursorBudget_bound headNormal
      have tailBound := WireNormalArray.cursorBudget_bound tailNormal
      have headPositive : 0 < (encodeSyn head).length := by
        omega
      simp only [arrayCursorBudget, encodeSyn, List.length_append]
      omega

private theorem WireNormalMap.cursorBudget_bound {source : CborSyn .map}
    (normal : WireNormalMap source) :
    mapCursorBudget source ≤ 2 * (encodeSyn source).length := by
  cases normal with
  | nil => simp [mapCursorBudget, encodeSyn]
  | @cons key value tail keyNormal valueNormal tailNormal =>
      have keyBound := WireNormal.cursorBudget_bound keyNormal
      have valueBound := WireNormal.cursorBudget_bound valueNormal
      have tailBound := WireNormalMap.cursorBudget_bound tailNormal
      have keyPositive : 0 < (encodeSyn key).length := by omega
      have valuePositive : 0 < (encodeSyn value).length := by omega
      simp only [mapCursorBudget, encodeSyn, List.length_append]
      omega

end

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

/-- The structural decision procedure accepts exact deterministic map order
and rejects encounter order without executing the byte parser. -/
theorem wireNormal_sorted_integer_map :
    WireNormal (.map (CborSyn.mapOfList [
      (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2))),
      (.primitive (.integer (.unsigned 2)), .primitive (.integer (.unsigned 1)))])) := by
  exact .map _ (by
    simp [CborSyn.mapOfList, CborSyn.mapLength, Bytes.maxDefiniteLength]) (by
      have keyOrder : ([1] : List UInt8) < [2] := by decide
      simpa [CborSyn.mapOfList, encodeEntries, sortEntries, insertEntry, lexLt,
        encodeSyn, head] using keyOrder) <|
    .cons (.unsigned 1) (.unsigned 2) <|
      .cons (.unsigned 2) (.unsigned 1) .nil

theorem not_wireNormal_unsorted_integer_map :
    ¬WireNormal (.map (CborSyn.mapOfList [
      (.primitive (.integer (.unsigned 2)), .primitive (.integer (.unsigned 1))),
      (.primitive (.integer (.unsigned 1)), .primitive (.integer (.unsigned 2)))])) := by
  intro normal
  cases normal with
  | map _ _ ordered _ =>
      have notOrdered : ¬(([2] : List UInt8) < [1]) := by decide
      apply notOrdered
      simpa [CborSyn.mapOfList, encodeEntries, sortEntries, insertEntry, lexLt,
        encodeSyn, head] using ordered

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

/-- Deterministic bytes decode to the identical syntax when every map is
already in deterministic wire order. This is the reusable byte-level boundary
for canonical arena encoders; parser/compiler correctness is not assumed. -/
theorem parse?_deterministic_wireNormal (value : Cbor)
    (normal : WireNormal value) :
    parse? (deterministic ⟨value, normal.reasonable⟩) = some value := by
  unfold parse? deterministic
  simp only [listOfBytes_bytesOfList]
  have enough : cursorBudget value ≤ 2 * (encodeSyn value).length := by
    have bound := WireNormal.cursorBudget_bound normal
    omega
  have parsed :
      parseItem (2 * (encodeSyn value).length) (encodeSyn value) =
        some (value, []) := by
    simpa only [List.append_nil] using WireNormal.cursorRoundtrip normal
      (2 * (encodeSyn value).length) [] enough
  rw [parsed]
  simp

/-- Regression for the parser-fuel bound: each definite array cursor consumes
fuel in addition to its head byte, so `input.length + 1` was insufficient for
even two nested singleton arrays. -/
theorem parse?_nested_singleton_arrays :
    parse? ⟨([129, 129, 0] : List UInt8).toByteArray⟩ =
      some (.array (.arrayCons (.array (.arrayCons
        (.primitive (.integer (.unsigned 0))) .arrayNil)) .arrayNil)) := by
  rfl

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
