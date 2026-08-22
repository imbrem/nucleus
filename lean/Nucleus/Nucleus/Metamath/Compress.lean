import Nucleus.Metamath.Database
import Mathlib.Tactic

/-!
# The compressed-proof letter block

Metamath's compressed proofs encode a sequence of positive integers in a mixed
radix: the letters `U`–`Y` are continuation digits with values 1–5, the letters
`A`–`T` are terminal digits with values 1–20, and `Z` marks a save to the heap.
An integer addresses, in order, the mandatory hypotheses of the theorem being
proved, then the entries of the parenthesised label block, then the heap.

This file mirrors `decompress_proof` in `crates/logic/metamath/src/verify.rs`
and proves the decoder correct against an explicit encoder: `decodeInt_encodeInt`
says every positive integer round-trips, and does so *within a longer stream*,
which is the form the letter-block decoder needs.

The Lean decoder accumulates into `Nat`, so the case the Rust decoder gets
wrong — `n = n * 20 + t` on a `usize`, which overflows on a long digit run —
does not arise here. That is a reason to write the specification in a language
without machine integers, not a reason to leave the Rust unfixed.
-/

namespace Nucleus.Metamath

/-- The terminal digits, in value order: `A` is 1 through `T` is 20. -/
def terminalChars : List Char := "ABCDEFGHIJKLMNOPQRST".toList

/-- The continuation digits, in value order: `U` is 1 through `Y` is 5. -/
def continuationChars : List Char := "UVWXY".toList

/-- The terminal digits are exactly the contiguous range `A`–`T`. -/
example : terminalChars = (List.range 20).map (fun i => Char.ofNat ('A'.toNat + i)) := by
  decide

/-- The continuation digits are exactly the contiguous range `U`–`Y`. -/
example : continuationChars = (List.range 5).map (fun i => Char.ofNat ('U'.toNat + i)) := by
  decide

/-- Value of a terminal letter, 1–20. -/
def terminalDigit (c : Char) : Option Nat :=
  (terminalChars.findIdx? (· == c)).map (· + 1)

/-- Value of a continuation letter, 1–5. -/
def continuationDigit (c : Char) : Option Nat :=
  (continuationChars.findIdx? (· == c)).map (· + 1)

/-- The letter carrying terminal digit value `r + 1`. -/
def terminalChar (r : Nat) : Char := terminalChars.getD r 'A'

/-- The letter carrying continuation digit value `r + 1`. -/
def continuationChar (r : Nat) : Char := continuationChars.getD r 'U'

theorem terminalDigit_terminalChar {r : Nat} (h : r < 20) :
    terminalDigit (terminalChar r) = some (r + 1) := by
  interval_cases r <;> decide

theorem continuationDigit_continuationChar {r : Nat} (h : r < 5) :
    continuationDigit (continuationChar r) = some (r + 1) := by
  interval_cases r <;> decide

/-- No letter is both a terminal and a continuation digit. -/
theorem terminalDigit_continuationChar {r : Nat} (h : r < 5) :
    terminalDigit (continuationChar r) = none := by
  interval_cases r <;> decide

/-- Decode one proof integer from the head of `letters`, returning it together
with the remaining stream. `acc` is the value accumulated from the continuation
digits read so far. -/
def decodeIntAux (acc : Nat) : List Char → Option (Nat × List Char)
  | [] => none
  | c :: rest =>
    match terminalDigit c with
    | some t => some (acc * 20 + t, rest)
    | none =>
      match continuationDigit c with
      | some d => decodeIntAux (acc * 5 + d) rest
      | none => none

/-- Decode one proof integer from the head of a letter block. -/
def decodeInt (letters : List Char) : Option (Nat × List Char) := decodeIntAux 0 letters

/-- Decoding always consumes at least one letter, so a loop that decodes
integers until the block is exhausted terminates. -/
theorem decodeIntAux_length_lt {acc : Nat} {letters : List Char} {n : Nat} {rest : List Char}
    (h : decodeIntAux acc letters = some (n, rest)) : rest.length < letters.length := by
  induction letters generalizing acc with
  | nil => simp [decodeIntAux] at h
  | cons c tail ih =>
    unfold decodeIntAux at h
    rcases ht : terminalDigit c with _ | t
    · rw [ht] at h
      rcases hd : continuationDigit c with _ | d
      · rw [hd] at h
        simp at h
      · rw [hd] at h
        exact Nat.lt_succ_of_lt (ih h)
    · rw [ht] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp [h.2]

/-- The continuation digits of `m`, in bijective base 5.

Bijective, not ordinary, base 5: the digits run 1–5 with no zero, so every
natural number has exactly one representation and zero is the empty string.
That is what makes the Metamath scheme a bijection rather than a code with
redundant leading digits. -/
def highDigits : Nat → List Char
  | 0 => []
  | m + 1 => highDigits (m / 5) ++ [continuationChar (m % 5)]
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self m 5)

theorem highDigits_succ (m : Nat) :
    highDigits (m + 1) = highDigits (m / 5) ++ [continuationChar (m % 5)] := by
  rw [highDigits]

/-- The letter block encoding a single positive proof integer. -/
def encodeInt (n : Nat) : List Char :=
  highDigits ((n - 1) / 20) ++ [terminalChar ((n - 1) % 20)]

/-- Continuation digits accumulate their bijective-base-5 value, leaving the
rest of the stream to be decoded from that accumulator. -/
theorem decodeIntAux_highDigits (m : Nat) :
    ∀ (acc : Nat) (rest : List Char),
      decodeIntAux acc (highDigits m ++ rest)
        = decodeIntAux (acc * 5 ^ (highDigits m).length + m) rest := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro acc rest
    match m with
    | 0 => simp [highDigits]
    | m + 1 =>
      have hlt : m / 5 < m + 1 := Nat.lt_succ_of_le (Nat.div_le_self m 5)
      have hmod : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hdm : 5 * (m / 5) + m % 5 = m := Nat.div_add_mod m 5
      rw [highDigits_succ, List.append_assoc, ih _ hlt, List.singleton_append]
      have hstep : ∀ acc' : Nat,
          decodeIntAux acc' (continuationChar (m % 5) :: rest)
            = decodeIntAux (acc' * 5 + (m % 5 + 1)) rest := by
        intro acc'
        simp only [decodeIntAux, terminalDigit_continuationChar hmod,
          continuationDigit_continuationChar hmod]
      rw [hstep, List.length_append, List.length_singleton, pow_succ]
      have expand : ∀ a p q r : Nat,
          (a * p + q) * 5 + (r + 1) = a * (p * 5) + (5 * q + r + 1) := by
        intro a p q r; ring
      rw [expand, hdm]

/-- **Every positive proof integer round-trips**, including when it is followed
by more of the letter block. -/
theorem decodeInt_encodeInt {n : Nat} (hn : 0 < n) (rest : List Char) :
    decodeInt (encodeInt n ++ rest) = some (n, rest) := by
  have hmod : (n - 1) % 20 < 20 := Nat.mod_lt _ (by norm_num)
  have hdm : 20 * ((n - 1) / 20) + (n - 1) % 20 = n - 1 := Nat.div_add_mod (n - 1) 20
  unfold decodeInt encodeInt
  rw [List.append_assoc, decodeIntAux_highDigits, List.singleton_append]
  simp only [decodeIntAux, terminalDigit_terminalChar hmod, Option.some.injEq,
    Prod.mk.injEq, and_true]
  omega

/-- A decoded proof step: the common currency of both proof encodings.

The heap is what preserves a compressed proof's sharing — a saved subproof is
re-pushed, never re-derived — so replaying one never expands exponentially. -/
inductive ProofStep where
  /-- Cite a statement by label. -/
  | label (l : Sym)
  /-- `Z`: save the top of the stack to the heap. -/
  | save
  /-- Push a previously saved heap entry. -/
  | heap (idx : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Why a letter block failed to decode. -/
inductive DecodeError where
  /-- The block contains the incomplete-proof placeholder `?`. -/
  | incomplete
  /-- A character outside `A`–`Z` and `?`. -/
  | invalidChar (c : Char)
  /-- A `Z` appeared between the digits of an integer. -/
  | saveMidInteger
  /-- The block ended between the digits of an integer. -/
  | endsMidInteger
  /-- A heap backreference beyond what has been saved. -/
  | heapOutOfRange (idx : Nat) (saved : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Resolve a decoded proof integer, 1-based, against the three address spaces
it ranges over in order: the mandatory hypotheses, then the label-block entries,
then the heap backreferences. -/
def resolveIndex (mandatory labels : List Sym) (savedCount n : Nat) :
    Except DecodeError ProofStep :=
  if n ≤ mandatory.length then
    .ok (.label (mandatory.getD (n - 1) ""))
  else if n ≤ mandatory.length + labels.length then
    .ok (.label (labels.getD (n - mandatory.length - 1) ""))
  else
    let idx := n - mandatory.length - labels.length - 1
    if idx < savedCount then .ok (.heap idx)
    else .error (.heapOutOfRange idx savedCount)

/-- Decode a letter block into proof steps.

`acc` is the integer under construction — `none` when not inside one — and
`savedCount` is the number of `Z` markers seen so far, which bounds the legal
heap backreferences. Recursion is structural on the character list, so unlike
the Rust loop there is no separate termination argument to get wrong. -/
def decodeLetters (mandatory labels : List Sym) :
    Nat → Option Nat → List Char → Except DecodeError (List ProofStep)
  | _, some _, [] => .error .endsMidInteger
  | _, none, [] => .ok []
  | savedCount, acc, c :: rest =>
    if c = 'Z' then
      match acc with
      | some _ => .error .saveMidInteger
      | none => (ProofStep.save :: ·) <$> decodeLetters mandatory labels (savedCount + 1) none rest
    else if c = '?' then
      .error .incomplete
    else
      match terminalDigit c with
      | some t => do
          let step ← resolveIndex mandatory labels savedCount (acc.getD 0 * 20 + t)
          (step :: ·) <$> decodeLetters mandatory labels savedCount none rest
      | none =>
        match continuationDigit c with
        | some d => decodeLetters mandatory labels savedCount (some (acc.getD 0 * 5 + d)) rest
        | none => .error (.invalidChar c)

/-- The labels of a frame's mandatory hypotheses, in the order a compressed
proof addresses them: all floats, then all essentials. -/
def Frame.mandatoryLabels (frame : Frame) : List Sym :=
  frame.floats.map FloatHyp.label ++ frame.essentials.map Hypothesis.label

/-- Decompress a compressed proof into proof steps. -/
def decompress (frame : Frame) (labels : List Sym) (letters : List Char) :
    Except DecodeError (List ProofStep) :=
  decodeLetters frame.mandatoryLabels labels 0 none letters

/-- An assertion's proof as a uniform proof-step sequence. An axiom yields no
steps. -/
def Assertion.steps (a : Assertion) : Except DecodeError (List ProofStep) :=
  match a.proof with
  | none => .ok []
  | some (.normal labels) => .ok (labels.map ProofStep.label)
  | some (.compressed labels letters) => decompress a.frame labels letters

end Nucleus.Metamath
