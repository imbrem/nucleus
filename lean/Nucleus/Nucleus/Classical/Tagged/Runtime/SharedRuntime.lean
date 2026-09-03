import Nucleus.Classical.Tagged.Runtime.Shared

/-!
# Executable shared-header codec

This is the word-level front end for the reference-counted runtime. The older
tagged-reference runtime is a separate comparative model.
-/

namespace Nucleus.Classical.Tagged.Runtime.SharedRuntime

open Nucleus.Classical.Tagged.Runtime.Shared

def constructor? : Nat → Option Constructor
  | 0 => some .and
  | 1 => some .or
  | 2 => some .sat
  | _ => none

def header? (raw : Nat) : Option Header := do
  if _ : raw < 2 ^ 32 then pure () else none
  let tag := raw % 4
  let constructor ← constructor? tag
  let sizeClass := (raw / 4) % 2 ^ classBits
  let refcount := raw / 2 ^ refcountShift
  if classBound : sizeClass < classLimit then
    if countPositive : 0 < refcount then
      if countBound : refcount < refcountLimit then
        some ⟨constructor, sizeClass, refcount, classBound, countPositive, countBound⟩
      else
        none
    else
      none
  else
    none

theorem constructor?_code (constructor : Constructor) :
    constructor? constructor.code = some constructor := by
  cases constructor <;> rfl

theorem header?_roundtrip (header : Header) :
    header? header.raw = some header := by
  unfold header?
  simp only [dif_pos header.fitsWord, Header.tag, constructor?_code,
    Header.decodeClass, Header.decodeRefcount, header.classBound,
    header.countPositive, header.countBound]
  simp

theorem maxHeader_decodes (constructor : Constructor) (sizeClass : Nat)
    (classBound : sizeClass < classLimit) :
    header? (maxHeader constructor sizeClass classBound).raw =
      some (maxHeader constructor sizeClass classBound) :=
  header?_roundtrip _

def RepresentsHeader (raw : Nat) (header : Header) : Prop :=
  header? raw = some header

theorem RepresentsHeader.functional {raw : Nat} {left right : Header}
    (leftRepresents : RepresentsHeader raw left)
    (rightRepresents : RepresentsHeader raw right) : left = right := by
  exact Option.some.inj (leftRepresents.symm.trans rightRepresents)

structure RawArena where
  words : List Nat
  freeRoot : Nat
  roots : List (Nat × Nat)
  deriving DecidableEq, Repr

def word? (arena : RawArena) (index : Nat) : Option Nat := arena.words[index]?

def decodeReference? (raw : Nat) : Option Reference := do
  let kind ← referenceKind? raw
  let negative := decide (2 ^ 31 ≤ raw)
  let payload := raw % 2 ^ 31
  match kind with
  | .block => some (.block payload negative)
  | .literal => some (.literal (payload / 4) negative)

/-- Decode a child region only when the first zero terminates it and the
complete remaining tail is zero. -/
def decodeChildren? : List Nat → Option (List Reference)
  | [] => none
  | 0 :: tail => if tail.all (· = 0) then some [] else none
  | raw :: tail => do
      let reference ← decodeReference? raw
      let children ← decodeChildren? tail
      some (reference :: children)

def readNode? (arena : RawArena) (base : Nat) : Option Node := do
  let rawHeader ← word? arena base
  let header ← header? rawHeader
  let capacity := header.capacity
  if base + capacity ≤ arena.words.length then pure () else none
  let children ← decodeChildren?
    ((arena.words.drop (base + 1)).take (capacity - 1))
  some ⟨header, children⟩

def RepresentsNode (arena : RawArena) (base : Nat) (node : Node) : Prop :=
  readNode? arena base = some node

theorem RepresentsNode.functional {arena : RawArena} {base : Nat}
    {left right : Node} (leftRepresents : RepresentsNode arena base left)
    (rightRepresents : RepresentsNode arena base right) : left = right := by
  exact Option.some.inj (leftRepresents.symm.trans rightRepresents)

theorem readNode?_usesHeaderCapacity {arena : RawArena} {base : Nat} {node : Node}
    (read : readNode? arena base = some node) :
    base + node.header.capacity ≤ arena.words.length := by
  unfold readNode? at read
  cases wordRead : word? arena base with
  | none => simp [wordRead] at read
  | some rawHeader =>
      cases headerRead : header? rawHeader with
      | none => simp [wordRead, headerRead] at read
      | some header =>
          by_cases fits : base + header.capacity ≤ arena.words.length
          · cases childrenRead : decodeChildren?
                ((arena.words.drop (base + 1)).take (header.capacity - 1)) with
            | none => simp [wordRead, headerRead, fits, childrenRead] at read
            | some children =>
                have equal : node = ⟨header, children⟩ := by
                  have result : some ⟨header, children⟩ = some node := by
                    simpa [wordRead, headerRead, fits, childrenRead] using read
                  exact (Option.some.inj result).symm
                subst node
                exact fits
          · simp [wordRead, headerRead, fits] at read

end Nucleus.Classical.Tagged.Runtime.SharedRuntime
