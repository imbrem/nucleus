import Nucleus.Cbor.Drisl
import Nucleus.Classical.Tagged.Runtime.Equality
import Nucleus.Classical.Tagged.Runtime.Encode
import Nucleus.Classical.Tagged.Runtime.MachineWord
import Std.Tactic.BVDecide

/-!
# DRISL tree codec for the tagged classical runtime

This is the version-two snapshot for the selected 32-bit runtime.
Machine words use one polarity bit and a 31-bit payload. Every word is stored
as exactly four big-endian bytes; arena words are concatenated into one byte
string.  Decoding accepts only the stated field order and exact field set.

The raw schema codec does not call `Runtime.Arena.decode?`.  The explicitly
named checked composition near the end additionally calls `Runtime.check?`.
Neither layer can create a theorem fact.
-/

namespace Nucleus.Classical.Tagged.Runtime.Cbor

open Nucleus.Classical.Packed

/-- Stable discriminator for the first tagged-classical arena object. -/
def typeName : String := "io.github.imbrem.nucleus.classicalArenaV2"

/-- The wire object fixes the runtime to 32-bit machine words. -/
abbrev Arena := Runtime.Arena 31

/-- One 32-bit sign-magnitude runtime word. -/
abbrev Word32 := Word 31

/-- One nonzero 32-bit runtime formula reference. -/
abbrev Ref32 := Word.Ref 31

/-- Interpret a fixed-width runtime word as the corresponding `UInt32`. -/
def wordMachine (word : Word32) : UInt32 :=
  UInt32.ofNat (MachineWord.pack word).val

/-- Recover a fixed-width runtime word from every `UInt32`. -/
def machineWord (machine : UInt32) : Word32 :=
  MachineWord.unpack ⟨machine.toNat, UInt32.toNat_lt machine⟩

private theorem uint32_ofNat_toNat (value : Nat) (fits : value < 2 ^ 32) :
    (UInt32.ofNat value).toNat = value := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt fits]

@[simp] theorem machineWord_wordMachine (word : Word32) :
    machineWord (wordMachine word) = word := by
  unfold machineWord wordMachine
  have packed :
      (⟨(UInt32.ofNat (MachineWord.pack word).val).toNat,
        UInt32.toNat_lt _⟩ : Fin (2 ^ (31 + 1))) =
        MachineWord.pack word := by
    apply Fin.ext
    exact uint32_ofNat_toNat (MachineWord.pack word).val
      (MachineWord.pack word).isLt
  rw [packed, MachineWord.unpack_pack]

@[simp] theorem wordMachine_machineWord (machine : UInt32) :
    wordMachine (machineWord machine) = machine := by
  apply UInt32.toNat_inj.mp
  simp only [wordMachine, machineWord, MachineWord.pack_unpack]
  exact uint32_ofNat_toNat machine.toNat (UInt32.toNat_lt machine)

/-- The four-octet, big-endian representation of one machine integer. -/
def uint32Bytes (value : UInt32) : Bytes := Bytes.ofList [
  (value >>> 24).toUInt8,
  (value >>> 16).toUInt8,
  (value >>> 8).toUInt8,
  value.toUInt8]

/-- Decode one big-endian machine integer, rejecting every other byte length. -/
def bytesUInt32? (bytes : Bytes) : Option UInt32 :=
  match bytes.toList with
  | [a, b, c, d] => some (
      (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) |||
      (c.toUInt32 <<< 8) ||| d.toUInt32)
  | _ => none

set_option linter.flexible false in
@[simp] theorem bytesUInt32?_uint32Bytes (value : UInt32) :
    bytesUInt32? (uint32Bytes value) = some value := by
  simp only [bytesUInt32?, uint32Bytes, Bytes.toList_ofList]
  congr 1
  bv_decide

/-- Encode one runtime word as exactly four big-endian octets. -/
def encodeWord (word : Word32) : Bytes := uint32Bytes (wordMachine word)

/-- Decode one runtime word from exactly four big-endian octets. -/
def decodeWord? (bytes : Bytes) : Option Word32 :=
  machineWord <$> bytesUInt32? bytes

@[simp] theorem decodeWord?_encodeWord (word : Word32) :
    decodeWord? (encodeWord word) = some word := by
  simp [decodeWord?, encodeWord]

@[simp] theorem encodeWord_length (word : Word32) :
    (encodeWord word).length = 4 := by
  simp [encodeWord, uint32Bytes]

private def encodeWordList : List Word32 → List UInt8
  | [] => []
  | word :: words => (encodeWord word).toList ++ encodeWordList words

private def decodeWordList? : List UInt8 → Option (List Word32)
  | [] => some []
  | a :: b :: c :: d :: rest => do
      let word ← decodeWord? (Bytes.ofList [a, b, c, d])
      let words ← decodeWordList? rest
      some (word :: words)
  | _ => none

@[simp] private theorem decodeWordList?_encodeWordList
    (words : List Word32) :
    decodeWordList? (encodeWordList words) = some words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp only [encodeWordList, encodeWord, uint32Bytes, Bytes.toList_ofList,
        List.cons_append, List.nil_append, decodeWordList?,
        Option.bind_eq_bind, ih]
      change (decodeWord? (encodeWord word)).bind
        (fun decoded => some (decoded :: words)) = some (word :: words)
      simp

/-- Concatenate an arena's fixed-width words into one CBOR byte-string payload. -/
def encodeWords (words : Array Word32) : Bytes :=
  Bytes.ofList (encodeWordList words.toList)

/-- Split a word payload into exact four-octet chunks. -/
def decodeWords? (bytes : Bytes) : Option (Array Word32) :=
  List.toArray <$> decodeWordList? bytes.toList

@[simp] theorem decodeWords?_encodeWords (words : Array Word32) :
    decodeWords? (encodeWords words) = some words := by
  simp [decodeWords?, encodeWords]

private theorem encodeWordList_length (words : List Word32) :
    (encodeWordList words).length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp only [encodeWordList, List.length_append, Bytes.length_toList,
        encodeWord_length, List.length_cons, ih]
      omega

@[simp] theorem encodeWords_length (words : Array Word32) :
    (encodeWords words).length = 4 * words.size := by
  simp [encodeWords, encodeWordList_length]

/-- A root reference has the same four-octet word representation. -/
def encodeRef (reference : Ref32) : Bytes := encodeWord reference.word

/-- Root decoding additionally checks the nonzero-reference invariant. -/
def decodeRef? (bytes : Bytes) : Option Ref32 := do
  let word ← decodeWord? bytes
  if isRef : word.IsRef then some ⟨word, isRef⟩ else none

@[simp] theorem decodeRef?_encodeRef (reference : Ref32) :
    decodeRef? (encodeRef reference) = some reference := by
  rcases reference with ⟨word, isRef⟩
  simp [decodeRef?, encodeRef, isRef]

private def bytes (value : Bytes) : Nucleus.Cbor :=
  .primitive (.bytes value)

private def text (value : String) : Nucleus.Cbor :=
  .primitive (.text value)

private def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  .array (Nucleus.CborSyn.arrayOfList values)

private def object (fields : List (String × Nucleus.Cbor)) : Nucleus.Cbor :=
  .map (Nucleus.CborSyn.textMapOfList fields)

private def asArray? : Nucleus.Cbor → Option (List Nucleus.Cbor)
  | .array values => some values.toArrayList
  | _ => none

private def asObject? : Nucleus.Cbor →
    Option (List (String × Nucleus.Cbor))
  | .map fields => Nucleus.CborSyn.textMapToList? fields
  | _ => none

@[simp] private theorem asArray?_array (values : List Nucleus.Cbor) :
    asArray? (array values) = some values := by
  simp [asArray?, array]

@[simp] private theorem asObject?_object
    (fields : List (String × Nucleus.Cbor)) :
    asObject? (object fields) = some fields := by
  simp [asObject?, object]

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

private theorem traverse_map (encode : α → Nucleus.Cbor)
    (decode : Nucleus.Cbor → Option α)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (values : List α) :
    traverse decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, roundtrip, ih]

/-- A sequent root is an exact two-field map in deterministic key order. -/
def encodeRoot (root : Ref32 × Ref32) : Nucleus.Cbor := object [
  ("premise", bytes (encodeRef root.1)),
  ("conclusion", bytes (encodeRef root.2))]

set_option linter.style.nativeDecide false

/-- The root schema's two keys have distinct canonical encodings. -/
theorem encodeRoot_keysDistinct (root : Ref32 × Ref32) :
    Nucleus.CborWire.DistinctCanonicalMapKeys
      (Nucleus.CborSyn.textMapOfList [
        ("premise", bytes (encodeRef root.1)),
        ("conclusion", bytes (encodeRef root.2))]) := by
  apply Nucleus.CborWire.DistinctCanonicalMapKeys.textMapOfList
  change Nucleus.CborWire.TextKeysDistinct ["premise", "conclusion"]
  native_decide

/-- The root schema's fields are in deterministic length-first key order. -/
theorem encodeRoot_keysOrdered (root : Ref32 × Ref32) :
    Nucleus.CborWire.MapInDeterministicOrder
      (Nucleus.CborSyn.textMapOfList [
        ("premise", bytes (encodeRef root.1)),
        ("conclusion", bytes (encodeRef root.2))]) := by
  apply Nucleus.CborWire.MapInDeterministicOrder.textMapOfList
  change Nucleus.CborWire.TextKeysInDeterministicOrder
    ["premise", "conclusion"]
  native_decide

/-- Decode only the canonical root-map shape. -/
def decodeRoot? (value : Nucleus.Cbor) : Option (Ref32 × Ref32) := do
  let fields ← asObject? value
  match fields with
  | [("premise", .primitive (.bytes premise)),
      ("conclusion", .primitive (.bytes conclusion))] =>
      return (← decodeRef? premise, ← decodeRef? conclusion)
  | _ => none

@[simp] theorem decodeRoot?_encodeRoot (root : Ref32 × Ref32) :
  decodeRoot? (encodeRoot root) = some root := by
  rcases root with ⟨premise, conclusion⟩
  simp only [encodeRoot, decodeRoot?, asObject?_object]
  simp [bytes]

private def decodeRoots? (value : Nucleus.Cbor) :
    Option (List (Ref32 × Ref32)) := do
  traverse decodeRoot? (← asArray? value)

@[simp] private theorem decodeRoots?_encode (roots : List (Ref32 × Ref32)) :
    decodeRoots? (array (roots.map encodeRoot)) = some roots := by
  simp only [decodeRoots?, asArray?_array]
  exact traverse_map encodeRoot decodeRoot? decodeRoot?_encodeRoot roots

/-- The wire snapshot omits mutable allocator state.

The top-level order is RFC 8949 length-first order for these text keys:
`$type`, `roots`, then `words`. -/
def encode (arena : Arena) : Nucleus.Cbor := object [
  ("$type", text typeName),
  ("roots", array (arena.roots.map encodeRoot)),
  ("words", bytes (encodeWords arena.words))]

/-- The arena schema's keys have distinct canonical encodings. -/
theorem encode_keysDistinct (arena : Arena) :
    Nucleus.CborWire.DistinctCanonicalMapKeys
      (Nucleus.CborSyn.textMapOfList [
        ("$type", text typeName),
        ("roots", array (arena.roots.map encodeRoot)),
        ("words", bytes (encodeWords arena.words))]) := by
  apply Nucleus.CborWire.DistinctCanonicalMapKeys.textMapOfList
  change Nucleus.CborWire.TextKeysDistinct
    ["$type", "roots", "words"]
  native_decide

/-- The arena schema's fields are in deterministic length-first key order. -/
theorem encode_keysOrdered (arena : Arena) :
    Nucleus.CborWire.MapInDeterministicOrder
      (Nucleus.CborSyn.textMapOfList [
        ("$type", text typeName),
        ("roots", array (arena.roots.map encodeRoot)),
        ("words", bytes (encodeWords arena.words))]) := by
  apply Nucleus.CborWire.MapInDeterministicOrder.textMapOfList
  change Nucleus.CborWire.TextKeysInDeterministicOrder
    ["$type", "roots", "words"]
  native_decide

/-- Decode only the exact version-two map: missing, repeated, reordered, or
unknown fields are rejected before any runtime validation. -/
def decode? (value : Nucleus.Cbor) : Option Arena := do
  let fields ← asObject? value
  match fields with
  | [("$type", .primitive (.text discriminator)),
      ("roots", roots),
      ("words", .primitive (.bytes words))] =>
      if discriminator = typeName then
        return {
          words := ← decodeWords? words
          freeRoot := Word.zero 31
          roots := ← decodeRoots? roots }
      else
        none
  | _ => none

/-- Snapshot decoding restores the canonical empty allocator. -/
theorem decode?_encode (arena : Arena)
    (dense : arena.freeRoot = Word.zero 31) :
    decode? (encode arena) = some arena := by
  rcases arena with ⟨words, freeRoot, roots⟩
  simp only at dense
  subst freeRoot
  simp only [encode, decode?, asObject?_object]
  simp [text, bytes, typeName]

/-- The schema's strong normal form is exactly the image of its encoder. -/
def StrongNormal (value : Nucleus.Cbor) : Prop :=
  ∃ arena : Arena, arena.freeRoot = Word.zero 31 ∧ encode arena = value

theorem encode_strongNormal (arena : Arena)
    (dense : arena.freeRoot = Word.zero 31) : StrongNormal (encode arena) :=
  ⟨arena, dense, rfl⟩

private theorem encodeRoots_profile (roots : List (Ref32 × Ref32)) :
    Nucleus.Cbor.Drisl.arrayProfile? (fun _ ↦ false)
      (Nucleus.CborSyn.arrayOfList (roots.map encodeRoot)) = true := by
  induction roots with
  | nil => simp [Nucleus.CborSyn.arrayOfList,
      Nucleus.Cbor.Drisl.arrayProfile?]
  | cons root roots ih =>
      rcases root with ⟨premise, conclusion⟩
      simp [encodeRoot, object, bytes, Nucleus.CborSyn.textMapOfList,
        Nucleus.CborSyn.arrayOfList,
        Nucleus.Cbor.Drisl.profile?, Nucleus.Cbor.Drisl.arrayProfile?,
        Nucleus.Cbor.Drisl.mapProfile?, ih]

/-- Every encoded arena lies in the link-free DRISL data profile.
Byte-level normality additionally requires the generic finite-length bounds. -/
theorem encode_profile (arena : Arena) :
    Nucleus.Cbor.Drisl.Profile (fun _ ↦ false) (encode arena) := by
  rcases arena with ⟨words, freeRoot, roots⟩
  simp [Nucleus.Cbor.Drisl.Profile, encode, object, text, bytes, array,
    Nucleus.CborSyn.textMapOfList, Nucleus.Cbor.Drisl.profile?,
    Nucleus.Cbor.Drisl.mapProfile?, typeName, encodeRoots_profile]

/-- Every root map has full link-free DRISL normality. -/
theorem encodeRoot_normal (root : Ref32 × Ref32) :
    Nucleus.Cbor.Drisl.Normal (fun _ ↦ false) (encodeRoot root) := by
  unfold encodeRoot object
  apply Nucleus.Cbor.Drisl.Normal.textMapOfList
  · simp [Bytes.maxDefiniteLength]
  · intro field present
    have choices :
        field = ("premise", bytes (encodeRef root.1)) ∨
        field = ("conclusion", bytes (encodeRef root.2)) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
    rcases choices with rfl | rfl
    · change "premise".toUTF8.size ≤ Bytes.maxDefiniteLength
      native_decide
    · change "conclusion".toUTF8.size ≤ Bytes.maxDefiniteLength
      native_decide
  · exact encodeRoot_keysDistinct root
  · exact encodeRoot_keysOrdered root
  · intro field present
    have choices :
        field = ("premise", bytes (encodeRef root.1)) ∨
        field = ("conclusion", bytes (encodeRef root.2)) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
    rcases choices with rfl | rfl
    · apply Nucleus.Cbor.Drisl.Normal.bytes
      simp [encodeRef, Bytes.maxDefiniteLength]
    · apply Nucleus.Cbor.Drisl.Normal.bytes
      simp [encodeRef, Bytes.maxDefiniteLength]

/-- The finite-length obligations introduced by the single concatenated word
blob and root array. -/
structure Encodable (arena : Arena) : Prop where
  reserved : 4 ≤ arena.words.size
  roots : arena.roots.length ≤ Bytes.maxDefiniteLength
  words : (encodeWords arena.words).length ≤ Bytes.maxDefiniteLength

/-- Executable decision procedure for the strong schema bounds checked at the
tree and byte decoding boundaries. -/
def encodableDecidable (arena : Arena) : Decidable (Encodable arena) :=
  if reserved : 4 ≤ arena.words.size then
    if rootsFit : arena.roots.length ≤ Bytes.maxDefiniteLength then
      if wordsFit : (encodeWords arena.words).length ≤ Bytes.maxDefiniteLength then
        isTrue ⟨reserved, rootsFit, wordsFit⟩
      else
        isFalse fun encodable => wordsFit encodable.words
    else
      isFalse fun encodable => rootsFit encodable.roots
  else
    isFalse fun encodable => reserved encodable.reserved

instance (arena : Arena) : Decidable (Encodable arena) :=
  encodableDecidable arena

/-- The reserved runtime prefix gives the word blob its 16-byte
minimum. -/
theorem Encodable.words_minLength {arena : Arena}
    (encodable : Encodable arena) : 16 ≤ (encodeWords arena.words).length := by
  rw [encodeWords_length]
  have reserved := encodable.reserved
  omega

/-- The schema encoder produces a fully normal DRISL object from its reserved
prefix and variable-size bounds. Fixed field order and key uniqueness are
discharged by the schema lemmas above. -/
theorem encode_normal (arena : Arena) (encodable : Encodable arena) :
    Nucleus.Cbor.Drisl.Normal (fun _ ↦ false) (encode arena) := by
  have typeNormal : Nucleus.Cbor.Drisl.Normal (fun _ ↦ false)
      (text typeName) := by
    unfold text
    apply Nucleus.Cbor.Drisl.Normal.text
    native_decide
  have rootsNormal : Nucleus.Cbor.Drisl.Normal (fun _ ↦ false)
      (array (arena.roots.map encodeRoot)) := by
    unfold array
    apply Nucleus.Cbor.Drisl.Normal.arrayOfList
    · simpa using encodable.roots
    · intro value present
      obtain ⟨root, _, rfl⟩ := List.mem_map.mp present
      exact encodeRoot_normal root
  have wordsNormal : Nucleus.Cbor.Drisl.Normal (fun _ ↦ false)
      (bytes (encodeWords arena.words)) := by
    unfold bytes
    exact Nucleus.Cbor.Drisl.Normal.bytes _ _ encodable.words
  unfold encode object
  apply Nucleus.Cbor.Drisl.Normal.textMapOfList
  · simp [Bytes.maxDefiniteLength]
  · intro field present
    have choices :
        field = ("$type", text typeName) ∨
        field = ("roots", array (arena.roots.map encodeRoot)) ∨
        field = ("words", bytes (encodeWords arena.words)) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
    rcases choices with rfl | rfl | rfl
    · change "$type".toUTF8.size ≤ Bytes.maxDefiniteLength
      native_decide
    · change "roots".toUTF8.size ≤ Bytes.maxDefiniteLength
      native_decide
    · change "words".toUTF8.size ≤ Bytes.maxDefiniteLength
      native_decide
  · exact encode_keysDistinct arena
  · exact encode_keysOrdered arena
  · intro field present
    have choices :
        field = ("$type", text typeName) ∨
        field = ("roots", array (arena.roots.map encodeRoot)) ∨
        field = ("words", bytes (encodeWords arena.words)) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
    rcases choices with rfl | rfl | rfl
    · exact typeNormal
    · exact rootsNormal
    · exact wordsNormal

/-- Assemble full DRISL normality once the generic CBOR container layer has
discharged finite lengths, duplicate keys, and deterministic map order. -/
theorem encode_normal_of_cbor (arena : Arena)
    (canonical : Nucleus.CborWire.Canonical (encode arena))
    (wireNormal : Nucleus.CborWire.WireNormal (encode arena)) :
    Nucleus.Cbor.Drisl.Normal (fun _ ↦ false) (encode arena) :=
  ⟨encode_profile arena, canonical, wireNormal⟩

/-- Deterministic DRISL bytes for an encodable arena. -/
def encodeBytes (arena : Arena) (encodable : Encodable arena) : Bytes :=
  Nucleus.Cbor.Drisl.deterministic ⟨encode arena, encode_normal arena encodable⟩

/-- Decode the exact tree schema and enforce its strong size bounds. Raw
`decode?` remains the broader structural tree codec.  This does not perform
runtime allocation or syntax validation. -/
def decodeEncodable? (value : Nucleus.Cbor) : Option Arena := do
  let arena ← decode? value
  if _encodable : Encodable arena then some arena else none

@[simp] theorem decodeEncodable?_encode (arena : Arena)
    (encodable : Encodable arena) (dense : arena.freeRoot = Word.zero 31) :
    decodeEncodable? (encode arena) = some arena := by
  simp [decodeEncodable?, encodable, decode?_encode arena dense]

/-- Decode only canonical DRISL bytes of the exact strong arena schema. -/
def decodeBytes? (value : Bytes) : Option Arena := do
  let normal ← Nucleus.Cbor.Drisl.parseNormal? (fun _ ↦ false) value
  decodeEncodable? normal.1

/-- Generic CBOR parsing recovers the exact tree serialized for an arena. -/
@[simp] theorem parse?_encodeBytes (arena : Arena)
    (encodable : Encodable arena) :
    Nucleus.CborWire.parse? (encodeBytes arena encodable) = some (encode arena) :=
  Nucleus.Cbor.Drisl.parse?_deterministic
    ⟨encode arena, encode_normal arena encodable⟩

/-- Canonical byte decoding is a left inverse of deterministic arena
serialization. -/
@[simp] theorem decodeBytes?_encodeBytes (arena : Arena)
    (encodable : Encodable arena) (dense : arena.freeRoot = Word.zero 31) :
    decodeBytes? (encodeBytes arena encodable) = some arena := by
  unfold decodeBytes? encodeBytes
  rw [Nucleus.Cbor.Drisl.parseNormal?_deterministic]
  exact decodeEncodable?_encode arena encodable dense

/-! ## Full runtime-checked composition -/

/-- Serialize a checked canonical snapshot. -/
def encodeCheckedBytes (checked : Runtime.Checked 31)
    (encodable : Encodable checked.arena)
    (_normal : ∃ input, Encode.NormalForm 31 input checked.arena) : Bytes :=
  encodeBytes checked.arena encodable

/-- Parse canonical schema bytes and run the complete allocator, ownership,
and tagged-syntax validator.  This is the Lean counterpart of Rust
`decode_checked`. -/
def decodeRuntimeCheckedBytes? (value : Bytes) : Option (Runtime.Checked 31) := do
  let arena ← decodeBytes? value
  Runtime.check? arena

@[simp] theorem check?_checked (checked : Runtime.Checked 31) :
    Runtime.check? checked.arena = some checked := by
  rcases checked with ⟨arena, decoded, valid⟩
  unfold Runtime.check?
  split
  · rename_i impossible
    rw [valid] at impossible
    contradiction
  · rename_i value recovered
    have equal : value = decoded := Option.some.inj (recovered.symm.trans valid)
    subst value
    rfl

/-- Full checked decoding is a left inverse of checked serialization. -/
@[simp] theorem decodeRuntimeCheckedBytes?_encodeCheckedBytes
    (checked : Runtime.Checked 31) (encodable : Encodable checked.arena)
    (normal : ∃ input, Encode.NormalForm 31 input checked.arena) :
    decodeRuntimeCheckedBytes? (encodeCheckedBytes checked encodable normal) =
      some checked := by
  obtain ⟨input, normal⟩ := normal
  unfold decodeRuntimeCheckedBytes? encodeCheckedBytes
  rw [decodeBytes?_encodeBytes _ _ normal.freeRoot_zero]
  exact check?_checked checked

/-! ## Exact empty checked fixture -/

/-- The smallest runtime arena: four reserved zero words and no allocated
blocks or sequent roots. -/
def reservedEmptyArena : Arena where
  words := #[Word.zero 31, Word.zero 31, Word.zero 31, Word.zero 31]
  freeRoot := Word.zero 31
  roots := []

def reservedEmptyDecoded : Runtime.Decoded where
  sequents := []
  live := []
  free := []

theorem reservedEmptyArena_valid :
    reservedEmptyArena.decodeState? = some reservedEmptyDecoded := by
  rfl

/-- A concrete full `Checked 31` witness for the smallest arena. -/
def reservedEmptyChecked : Runtime.Checked 31 :=
  ⟨reservedEmptyArena, reservedEmptyDecoded, reservedEmptyArena_valid⟩

theorem reservedEmptyEncodable : Encodable reservedEmptyArena := by
  native_decide

theorem reservedEmptyNormal : Encode.NormalForm 31 [] reservedEmptyArena := by
  rfl

/-- Compact statement of the exact hard-coded Rust byte vector. -/
def reservedEmptyExpectedBytes : Bytes := Bytes.ofList (
  ([0xa3, 0x65] : List UInt8) ++ "$type".toUTF8.toList ++
  [0x78, 0x29] ++ typeName.toUTF8.toList ++
  [0x65] ++ "roots".toUTF8.toList ++ [0x80, 0x65] ++
  "words".toUTF8.toList ++ [0x50] ++ List.replicate 16 0)

/-- The formal codec emits exactly the Rust empty-arena test vector. -/
theorem encodeCheckedBytes_reservedEmpty :
    encodeCheckedBytes reservedEmptyChecked reservedEmptyEncodable
      ⟨[], reservedEmptyNormal⟩ =
      reservedEmptyExpectedBytes := by
  native_decide

/-- The exact empty byte vector passes both schema and runtime validation. -/
theorem decodeRuntimeCheckedBytes?_reservedEmpty :
    decodeRuntimeCheckedBytes? reservedEmptyExpectedBytes =
      some reservedEmptyChecked := by
  rw [← encodeCheckedBytes_reservedEmpty]
  exact decodeRuntimeCheckedBytes?_encodeCheckedBytes
    reservedEmptyChecked reservedEmptyEncodable ⟨[], reservedEmptyNormal⟩

theorem StrongNormal.decode {value : Nucleus.Cbor}
    (normal : StrongNormal value) : ∃ arena, decode? value = some arena := by
  obtain ⟨arena, dense, rfl⟩ := normal
  exact ⟨arena, decode?_encode arena dense⟩

/-! ## Executable rejection examples -/

set_option linter.style.nativeDecide false

private def zeroWord : Word32 := Word.zero 31

private def emptyArena : Arena where
  words := #[]
  freeRoot := zeroWord
  roots := []

private theorem emptyArenaNormal :
    Nucleus.Cbor.Drisl.Normal (fun _ ↦ false) (encode emptyArena) := by
  native_decide

private def emptyArenaBytes : Bytes :=
  Nucleus.Cbor.Drisl.deterministic ⟨encode emptyArena, emptyArenaNormal⟩

/-- The fixed field order is the deterministic DRISL order, witnessed on the
minimal object independently of the generic variable-container bridge. -/
example : Nucleus.Cbor.Drisl.Normal (fun _ ↦ false) (encode emptyArena) := by
  native_decide

/-- Normal CBOR syntax is insufficient for the strong arena schema: checked
byte decoding rejects a word blob shorter than the four reserved words. -/
example : decodeBytes? emptyArenaBytes = none := by
  native_decide

/-- A word must occupy exactly four bytes. -/
example : decodeWord? (Bytes.ofList [0, 0, 0]) = none := by
  native_decide

/-- The object discriminator is exact. -/
example : decode? (object [
    ("$type", text "io.github.imbrem.nucleus.classicalArenaV1"),
    ("roots", array []),
    ("words", bytes Bytes.empty)]) = none := by
  native_decide

/-- Unknown fields are not ignored. -/
example : decode? (object [
    ("$type", text typeName),
    ("roots", array []),
    ("words", bytes Bytes.empty),
    ("freeRoot", bytes (encodeWord zeroWord)),
    ("extra", text "rejected")]) = none := by
  native_decide

/-- Canonical field order is part of the accepted tree. -/
example : decode? (object [
    ("roots", array []),
    ("$type", text typeName),
    ("words", bytes Bytes.empty)]) = none := by
  native_decide

/-- A zero word is not a valid formula root. -/
example : decodeRoot? (object [
    ("premise", bytes (encodeWord zeroWord)),
    ("conclusion", bytes (encodeWord zeroWord))]) = none := by
  native_decide

example : decode? (encode emptyArena) = some emptyArena := by
  exact decode?_encode emptyArena rfl

end Nucleus.Classical.Tagged.Runtime.Cbor
