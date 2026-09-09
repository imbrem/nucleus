import Nucleus.Classical.Tagged.Runtime.Allocator
import Nucleus.Classical.Tagged.Runtime.MachineWord

/-!
# Length-delimited word tables

The reusable Rust `data::array::Table` interprets only headers and allocator
metadata. Payload words and tags have no logical meaning here. The old
intrusive ring encoding is retained; the new header replaces the live
size-class/zero-termination encoding. This specification uses lists for
indexes that Rust caches in ordered maps.
-/

namespace Nucleus.Classical.ArrayTable

open Nucleus.Classical.Packed

structure Header where
  length : Nat
  tag : Nat
  shared : Bool
  deriving DecidableEq, Repr

def Header.encode (header : Header) : Nat :=
  header.length * 8 + header.tag * 2 + header.shared.toNat

def Header.decode (word : Nat) : Header :=
  ⟨word / 8, word / 2 % 4, decide (word % 2 = 1)⟩

theorem Header.decode_encode (header : Header) (tagBound : header.tag < 4) :
    Header.decode header.encode = header := by
  rcases header with ⟨length, tag, shared⟩
  change tag < 4 at tagBound
  cases shared <;>
    simp only [Header.encode, Header.decode, Bool.toNat, cond_false, cond_true,
      Nat.add_zero] <;> congr 1
  all_goals first | omega | exact decide_eq_true (by omega) | exact decide_eq_false (by omega)


/-- A caller-supplied interpretation of the initial word. The runtime checks
this round trip on every header write, rather than trusting an implementation
of the generic Rust trait. -/
structure Codec where
  decode : Nat → Option Header
  encode : Header → Option Nat

def Codec.write? (codec : Codec) (header : Header) : Option Nat := do
  let word ← codec.encode header
  if codec.decode word = some header then some word else none

theorem Codec.write?_reads {codec : Codec} {header : Header} {word : Nat}
    (written : codec.write? header = some word) : codec.decode word = some header := by
  unfold write? at written
  cases encoded : codec.encode header with
  | none => simp [encoded] at written
  | some candidate =>
    rw [encoded] at written
    change (if codec.decode candidate = some header then some candidate else none) =
      some word at written
    split at written
    · rename_i reads
      cases Option.some.inj written
      exact reads
    · contradiction

/-- Concrete fixed-64-bit codec selected by the classical arena. -/
def packedCodec : Codec where
  decode word := if word < 2 ^ 64 then some (Header.decode word) else none
  encode header :=
    if header.tag < 4 ∧ header.length < 2 ^ 61 then some header.encode else none

/-- Minimum class holding a header and exactly `length` payload slots.
Unlike the former layout, no terminator slot is required. -/
def sizeClass? (length : Nat) : Option Nat :=
  (List.range 61).find? fun sizeClass ↦ decide (length + 1 ≤ 4 * 2 ^ sizeClass)

/-- Only raw words and an intrusive free root belong to the table. -/
structure Raw where
  words : _root_.Array (Word 63)
  freeRoot : Word 63
  deriving DecidableEq, Repr

def Raw.intrusive (table : Raw) : Packed.Intrusive.Arena 63 :=
  ⟨table.words, table.freeRoot, []⟩

def Raw.header? (table : Raw) (base : Nat) : Option Header := do
  let word ← table.words[base]?
  packedCodec.decode (Tagged.Runtime.MachineWord.pack word).val

/-- Reads a full length-delimited array. Zeros remain ordinary payload words
at this layer. Padding outside the payload is canonical zero. -/
def Raw.read? (table : Raw) (base : Nat) : Option (Block × Header × List (Word 63)) := do
  let header ← table.header? base
  let sizeClass ← sizeClass? header.length
  let block : Block := ⟨base, sizeClass⟩
  if block.Fits table.words.size then pure () else none
  if table.intrusive.zeroRange (base + 1 + header.length)
      (block.capacity - (header.length + 1)) then pure () else none
  some (block, header, (table.words.toList.drop (base + 1)).take header.length)

/-- Scan the physical partition. Free nodes are recognized from the validated
rings, so an empty live AND header may also be zero. -/
def Raw.scan (table : Raw) (free : List Block) :
    Nat → Nat → Option (List (Block × Header) × List Block)
  | 0, _ => none
  | fuel + 1, base =>
      if base = table.words.size then some ([], [])
      else if base > table.words.size then none
      else match free.find? (fun block ↦ block.base = base) with
        | some block => do
          let (live, visited) ← table.scan free fuel block.stop
          some (live, block :: visited)
        | none => do
          let (block, header, _) ← table.read? base
          let (live, visited) ← table.scan free fuel block.stop
          some ((block, header) :: live, visited)

def Raw.check? (table : Raw) : Option (List (Block × Header) × List Block) := do
  if table.intrusive.zeroRange 0 4 then pure () else none
  let free ← table.intrusive.decodeFree?
  let (live, visited) ← table.scan free (table.words.size + 1) 4
  if visited.length = free.length then some (live, free) else none

/-- Sticky sharing changes neither length nor application tag. -/
def Header.share (header : Header) : Header := { header with shared := true }

def Header.mustCopy (header : Header) : Bool := header.shared

def Header.mayRelease (header : Header) : Bool := !header.shared

@[simp] theorem Header.share_length (header : Header) : header.share.length = header.length := rfl
@[simp] theorem Header.share_tag (header : Header) : header.share.tag = header.tag := rfl
@[simp] theorem Header.shared_mustCopy (header : Header) : header.share.mustCopy = true := rfl
@[simp] theorem Header.shared_not_released (header : Header) :
    header.share.mayRelease = false := rfl

/-- Meaning of a successful raw slot write. The allocation policy is captured
separately from payload interpretation, which belongs to the arena. -/
def writeSlots (slots : List α) (index : Nat) (value : α) : List α :=
  slots.set index value

/-- A shared write must preserve the old allocation and select a fresh address.
This is a contract on the allocator refinement, not an assumption of logic. -/
def WriteContract (before after : Nat → Option (List α))
    (source target index : Nat) (value : α) (header : Header) : Prop :=
  ∃ slots, before source = some slots ∧ index < slots.length ∧
    after target = some (writeSlots slots index value) ∧
    (header.shared = true → target ≠ source ∧ after source = before source)

theorem shared_write_preserves {before after : Nat → Option (List α)}
    {source target index : Nat} {value : α} {header : Header}
    (write : WriteContract before after source target index value header)
    (shared : header.shared = true) : after source = before source :=
  (write.choose_spec.2.2.2 shared).2

end Nucleus.Classical.ArrayTable
