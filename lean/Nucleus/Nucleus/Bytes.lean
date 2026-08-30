import Mathlib.Data.Nat.Basic

/-!
# Byte strings

A `Bytes` is a compact finite byte string.  `ByteArray` is kept as the runtime
representation, while every algebraic lemma below is stated over `Bytes.toList`:
Lean's simp set for lists is far richer than the one for byte arrays, so the
list view is the normal form in which byte-string reasoning is done.  `O256`
already follows this shape, describing a hash by `O256.bytes : List UInt8` and
touching `ByteArray` only at the `O256.encode` boundary.

Slicing is deliberately *checked*.  An out-of-range span yields `none` rather
than a clamped or truncated result, matching `Nucleus.HashSeq.slice?` and the
`SliceError` conditions of the Rust `covalence-logic-cas` crate.  A silently
truncating slice would let a blob-expression calculus derive false facts, so
"out of range" must mean "denotes nothing" everywhere.
-/

namespace Nucleus

/-- A compact finite byte string. -/
structure Bytes where
  data : ByteArray
  deriving DecidableEq

namespace Bytes

/-- The number of octets. -/
def length (bytes : Bytes) : Nat := bytes.data.size

/-- Append one octet after every existing position. -/
def push (bytes : Bytes) (byte : UInt8) : Bytes := ⟨bytes.data.push byte⟩

/-- The byte string with no octets. -/
def empty : Bytes := ⟨ByteArray.empty⟩

/-- Concatenation, retaining every position of both operands. -/
def append (left right : Bytes) : Bytes := ⟨left.data.append right.data⟩

/-- The octets as a list.  This is the normal form for byte-string reasoning. -/
def toList (bytes : Bytes) : List UInt8 := bytes.data.data.toList

/-- Pack a list of octets. -/
def ofList (values : List UInt8) : Bytes := ⟨values.toByteArray⟩

@[simp] theorem toList_ofList (values : List UInt8) : (ofList values).toList = values := by
  simp [toList, ofList]

@[simp] theorem ofList_toList (bytes : Bytes) : ofList bytes.toList = bytes := by
  rcases bytes with ⟨⟨data⟩⟩
  simp only [ofList, toList]
  apply congrArg Bytes.mk
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact List.toList_data_toByteArray

/-- Byte strings are equal when they list the same octets. -/
@[ext]
theorem ext {left right : Bytes} (equal : left.toList = right.toList) : left = right := by
  rw [← ofList_toList left, ← ofList_toList right, equal]

theorem length_eq_toList_length (bytes : Bytes) : bytes.length = bytes.toList.length := by
  simp [length, toList]

@[simp] theorem length_toList (bytes : Bytes) : bytes.toList.length = bytes.length :=
  (length_eq_toList_length bytes).symm

@[simp] theorem length_ofList (values : List UInt8) : (ofList values).length = values.length := by
  rw [length_eq_toList_length, toList_ofList]

@[simp] theorem toList_empty : empty.toList = [] := rfl

@[simp] theorem length_empty : empty.length = 0 := rfl

@[simp] theorem toList_push (bytes : Bytes) (byte : UInt8) :
    (bytes.push byte).toList = bytes.toList ++ [byte] := by
  simp [toList, push, ByteArray.push]

@[simp] theorem length_push (bytes : Bytes) (byte : UInt8) :
    (bytes.push byte).length = bytes.length + 1 := by
  rw [length_eq_toList_length, toList_push]
  simp

@[simp] theorem toList_append (left right : Bytes) :
    (left.append right).toList = left.toList ++ right.toList := rfl

@[simp] theorem length_append (left right : Bytes) :
    (left.append right).length = left.length + right.length := by
  rw [length_eq_toList_length, toList_append]
  simp

@[simp] theorem append_empty (bytes : Bytes) : bytes.append empty = bytes := by
  ext
  simp

@[simp] theorem empty_append (bytes : Bytes) : empty.append bytes = bytes := by
  ext
  simp

theorem append_assoc (first second third : Bytes) :
    (first.append second).append third = first.append (second.append third) := by
  ext
  simp

/--
Concatenation is injective once the two heads have a common length.

This is the entire content of blob-expression cancellation: knowing that two
concatenations are the same byte string says nothing on its own, because the
split point is not recoverable, but one agreed head length pins it.
-/
theorem append_inj {leftHead leftTail rightHead rightTail : Bytes}
    (equal : leftHead.append leftTail = rightHead.append rightTail)
    (heads : leftHead.length = rightHead.length) :
    leftHead = rightHead ∧ leftTail = rightTail := by
  have lists : leftHead.toList ++ leftTail.toList = rightHead.toList ++ rightTail.toList := by
    rw [← toList_append, ← toList_append, equal]
  obtain ⟨headsEqual, tailsEqual⟩ := List.append_inj lists (by simpa using heads)
  exact ⟨ext headsEqual, ext tailsEqual⟩

/-- Concatenation is injective once the two tails have a common length. -/
theorem append_inj' {leftHead leftTail rightHead rightTail : Bytes}
    (equal : leftHead.append leftTail = rightHead.append rightTail)
    (tails : leftTail.length = rightTail.length) :
    leftHead = rightHead ∧ leftTail = rightTail := by
  have lists : leftHead.toList ++ leftTail.toList = rightHead.toList ++ rightTail.toList := by
    rw [← toList_append, ← toList_append, equal]
  obtain ⟨headsEqual, tailsEqual⟩ := List.append_inj' lists (by simpa using tails)
  exact ⟨ext headsEqual, ext tailsEqual⟩

/-- The byte string of `count` copies of one octet. -/
def replicate (count : Nat) (byte : UInt8) : Bytes := ofList (List.replicate count byte)

@[simp] theorem toList_replicate (count : Nat) (byte : UInt8) :
    (replicate count byte).toList = List.replicate count byte := by
  simp [replicate]

@[simp] theorem length_replicate (count : Nat) (byte : UInt8) :
    (replicate count byte).length = count := by
  rw [length_eq_toList_length, toList_replicate]
  simp

/--
A checked half-open octet slice.

`stop` is the exclusive upper bound; `none` runs to the end of `bytes`, which
is how a span pins a whole byte string without naming its length.  A span that
runs backwards or past the end selects nothing: the result is `none` rather
than a clamped shorter answer.
-/
def slice? (bytes : Bytes) (start : Nat) (stop : Option Nat) : Option Bytes :=
  if start ≤ stop.getD bytes.length ∧ stop.getD bytes.length ≤ bytes.length then
    some (ofList ((bytes.toList.drop start).take (stop.getD bytes.length - start)))
  else
    none

theorem slice?_eq_some_iff {bytes part : Bytes} {start : Nat} {stop : Option Nat} :
    bytes.slice? start stop = some part ↔
      start ≤ stop.getD bytes.length ∧ stop.getD bytes.length ≤ bytes.length ∧
        part = ofList ((bytes.toList.drop start).take (stop.getD bytes.length - start)) := by
  unfold slice?
  constructor
  · intro sliced
    split at sliced
    · rename_i bounded
      exact ⟨bounded.1, bounded.2, (Option.some.inj sliced).symm⟩
    · simp at sliced
  · rintro ⟨lower, upper, equal⟩
    rw [if_pos ⟨lower, upper⟩, equal]

theorem slice?_of_le {bytes : Bytes} {start : Nat} {stop : Option Nat}
    (lower : start ≤ stop.getD bytes.length) (upper : stop.getD bytes.length ≤ bytes.length) :
    bytes.slice? start stop =
      some (ofList ((bytes.toList.drop start).take (stop.getD bytes.length - start))) :=
  slice?_eq_some_iff.mpr ⟨lower, upper, rfl⟩

theorem slice?_eq_none {bytes : Bytes} {start : Nat} {stop : Option Nat}
    (unbounded : ¬(start ≤ stop.getD bytes.length ∧ stop.getD bytes.length ≤ bytes.length)) :
    bytes.slice? start stop = none :=
  if_neg unbounded

/-- The whole-byte-string span selects exactly its subject. -/
@[simp] theorem slice?_zero_none (bytes : Bytes) : bytes.slice? 0 none = some bytes := by
  rw [slice?_of_le (by simp) (by simp)]
  simp only [Option.getD_none, Nat.sub_zero, List.drop_zero]
  rw [← length_toList, List.take_length, ofList_toList]

/-- A slice that exists has exactly the width its bounds describe. -/
theorem length_of_slice? {bytes part : Bytes} {start : Nat} {stop : Option Nat}
    (sliced : bytes.slice? start stop = some part) :
    part.length = stop.getD bytes.length - start := by
  obtain ⟨lower, upper, equal⟩ := slice?_eq_some_iff.mp sliced
  subst equal
  simp only [length_ofList, List.length_take, List.length_drop, length_toList]
  omega

end Bytes

end Nucleus
