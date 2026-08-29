import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Fixed-width polarity words

The packed classical designs use one polarity bit and a fixed-width unsigned
payload.  Treating polarity separately is the sign-magnitude view of a machine
word: complementing a proposition flips one bit and leaves its low payload tag
unchanged.  The tagged design reserves payload residues modulo four for AND,
OR, SAT, and literals; the alternating design uses only array and literal
residues.

`payloadWidth` counts the payload bits, so a `Word payloadWidth` occupies
`payloadWidth + 1` bits including polarity.  Concrete formats should state this
width explicitly.
-/

namespace Nucleus.Classical.Packed

/-- A fixed-width sign-magnitude word. -/
structure Word (payloadWidth : Nat) where
  negative : Bool
  payload : Fin (2 ^ payloadWidth)
  deriving DecidableEq, Repr

namespace Word

variable {payloadWidth : Nat}

/-- The sole canonical zero word, used as an array terminator and padding. -/
def zero (payloadWidth : Nat) : Word payloadWidth :=
  ⟨false, ⟨0, Nat.two_pow_pos payloadWidth⟩⟩

/-- Complement the proposition named by a nonzero word. -/
def neg (word : Word payloadWidth) : Word payloadWidth :=
  { word with negative := !word.negative }

@[simp] theorem neg_negative (word : Word payloadWidth) :
    word.neg.negative = !word.negative := rfl

@[simp] theorem neg_payload (word : Word payloadWidth) :
    word.neg.payload = word.payload := rfl

@[simp] theorem neg_neg (word : Word payloadWidth) : word.neg.neg = word := by
  cases word
  simp [neg]

@[simp] theorem zero_negative : (zero payloadWidth).negative = false := rfl

@[simp] theorem zero_payload : (zero payloadWidth).payload.val = 0 := rfl

/-- Zero with negative polarity is deliberately noncanonical. -/
def CanonicalZero (word : Word payloadWidth) : Prop :=
  word = zero payloadWidth

instance (word : Word payloadWidth) : Decidable word.CanonicalZero :=
  inferInstanceAs (Decidable (word = zero payloadWidth))

/-- A proposition reference is any nonzero payload. -/
def IsRef (word : Word payloadWidth) : Prop :=
  word.payload.val ≠ 0

instance (word : Word payloadWidth) : Decidable word.IsRef :=
  inferInstanceAs (Decidable (word.payload.val ≠ 0))

/-- Low two payload bits, represented arithmetically. -/
def tag (word : Word payloadWidth) : Nat :=
  word.payload.val % 4

/-- Remove the low-two-bit tag from a payload. -/
def base (word : Word payloadWidth) : Nat :=
  word.payload.val - word.tag

@[simp] theorem tag_neg (word : Word payloadWidth) : word.neg.tag = word.tag := rfl

@[simp] theorem base_neg (word : Word payloadWidth) : word.neg.base = word.base := rfl

theorem tag_lt_four (word : Word payloadWidth) : word.tag < 4 := by
  exact Nat.mod_lt _ (by decide)

theorem base_aligned (word : Word payloadWidth) : word.base % 4 = 0 := by
  exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- The unsigned payload with the requested low-bit tag, when it fits. -/
def withTag? (payloadWidth base tag : Nat) (negative : Bool) : Option (Word payloadWidth) :=
  if base % 4 = 0 ∧ tag < 4 then
    if h : base + tag < 2 ^ payloadWidth then
      some ⟨negative, ⟨base + tag, h⟩⟩
    else none
  else none

theorem withTag?_payload {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : withTag? payloadWidth base tag negative = some word) :
    word.payload.val = base + tag := by
  unfold withTag? at encoded
  split at encoded
  · split at encoded
    · simp only [Option.some.injEq] at encoded
      subst word
      rfl
    · contradiction
  · contradiction

theorem withTag?_negative {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : withTag? payloadWidth base tag negative = some word) :
    word.negative = negative := by
  unfold withTag? at encoded
  split at encoded
  · split at encoded
    · simp only [Option.some.injEq] at encoded
      subst word
      rfl
    · contradiction
  · contradiction

theorem withTag?_valid {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : withTag? payloadWidth base tag negative = some word) :
    base % 4 = 0 ∧ tag < 4 := by
  unfold withTag? at encoded
  split at encoded
  · assumption
  · contradiction

theorem withTag?_tag {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : withTag? payloadWidth base tag negative = some word) :
    word.tag = tag := by
  have payload := withTag?_payload encoded
  have valid := withTag?_valid encoded
  simp only [Word.tag, payload]
  rw [Nat.add_mod]
  simp [valid.1, Nat.mod_eq_of_lt valid.2]

theorem withTag?_base {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : withTag? payloadWidth base tag negative = some word) :
    word.base = base := by
  have payload := withTag?_payload encoded
  have decodedTag := withTag?_tag encoded
  simp [Word.base, payload, decodedTag]

/-- Encode literal atom `n` in the residue-three namespace. -/
def literal? (payloadWidth atom : Nat) (negative : Bool := false) : Option (Word payloadWidth) :=
  withTag? payloadWidth (4 * atom) 3 negative

theorem literal?_tag {payloadWidth atom : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : literal? payloadWidth atom negative = some word) :
    word.tag = 3 := by
  exact withTag?_tag encoded

/-- Encode an aligned nonliteral node pointer.  Tag three belongs exclusively
to literals and is rejected here. -/
def pointer? (payloadWidth base tag : Nat) (negative : Bool := false) :
    Option (Word payloadWidth) :=
  if tag = 3 then none
  else if base = 0 then none
  else withTag? payloadWidth base tag negative

theorem pointer?_isRef {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : pointer? payloadWidth base tag negative = some word) :
    word.IsRef := by
  simp only [pointer?] at encoded
  split at encoded
  · contradiction
  · split at encoded
    · simp at encoded
    · rename_i nonzero
      have payload := withTag?_payload encoded
      intro zero
      have : base + tag = 0 := payload.symm.trans zero
      omega

theorem pointer?_not_literal {payloadWidth base tag : Nat} {negative : Bool}
    {word : Word payloadWidth} (encoded : pointer? payloadWidth base tag negative = some word) :
    word.tag ≠ 3 := by
  unfold pointer? at encoded
  split at encoded
  · contradiction
  · rename_i notLiteral
    split at encoded
    · contradiction
    · rw [withTag?_tag encoded]
      exact notLiteral

/-- A checked nonzero packed proposition reference. -/
structure Ref (payloadWidth : Nat) where
  word : Word payloadWidth
  isRef : word.IsRef
  deriving Repr

namespace Ref

instance : DecidableEq (Ref payloadWidth) :=
  fun left right ↦
    if equal : left.word = right.word then
      isTrue (by cases left; cases right; simp_all)
    else isFalse fun same ↦ equal (congrArg Ref.word same)

/-- Complement is total because it preserves the nonzero payload. -/
def neg (reference : Ref payloadWidth) : Ref payloadWidth :=
  ⟨reference.word.neg, reference.isRef⟩

@[simp] theorem neg_neg (reference : Ref payloadWidth) : reference.neg.neg = reference := by
  cases reference
  simp [neg]

end Ref
end Word
end Nucleus.Classical.Packed
