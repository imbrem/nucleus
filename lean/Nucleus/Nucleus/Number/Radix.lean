import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Exact radix-scaled integers

`RadixNumber r` represents `mantissa * r ^ exponent` exactly. It is a reusable
representation layer for decimal fractions (`r = 10`) and dyadic/binary
fractions (`r = 2`), independent of CBOR. Representations are intentionally
not normalized: equality of representations and equality of values are kept
separate, which is essential when reasoning about parsing and pretty-printing.
-/

namespace Nucleus

/-- An exact integer mantissa scaled by an integral power of `radix`. -/
structure RadixNumber (radix : Nat) where
  exponent : Int
  mantissa : Int
  deriving DecidableEq, Repr

/-- Exact decimal fraction representation. -/
abbrev DecimalFraction := RadixNumber 10

/-- Exact binary fraction, traditionally called a dyadic number. -/
abbrev Dyadic := RadixNumber 2

namespace RadixNumber

variable {radix : Nat}

/-- Exact rational denotation. -/
def value (number : RadixNumber radix) : ℚ :=
  number.mantissa * (radix : ℚ) ^ number.exponent

/-- Two representations denote the same exact number. -/
def Equivalent (a b : RadixNumber radix) : Prop := a.value = b.value

instance : Setoid (RadixNumber radix) where
  r := Equivalent
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Additive inverse preserves the scale. -/
def neg (number : RadixNumber radix) : RadixNumber radix :=
  ⟨number.exponent, -number.mantissa⟩

/-- Exact multiplication adds exponents and multiplies mantissas. -/
def mul (a b : RadixNumber radix) : RadixNumber radix :=
  ⟨a.exponent + b.exponent, a.mantissa * b.mantissa⟩

/-- Rescale a mantissa upward to a smaller common exponent. -/
private def rescaleMantissa (radix : Nat) (mantissa : Int) (places : Nat) : Int :=
  mantissa * (radix : Int) ^ places

/-- Exact addition aligns both operands at the smaller exponent. -/
def add (a b : RadixNumber radix) : RadixNumber radix :=
  let exponent := min a.exponent b.exponent
  ⟨exponent,
    rescaleMantissa radix a.mantissa (a.exponent - exponent).toNat +
    rescaleMantissa radix b.mantissa (b.exponent - exponent).toNat⟩

@[simp] theorem value_neg (number : RadixNumber radix) :
    number.neg.value = -number.value := by
  simp [neg, value]

@[simp] theorem value_mul (a b : RadixNumber radix) (hradix : radix ≠ 0) :
    (a.mul b).value = a.value * b.value := by
  have hr : (radix : ℚ) ≠ 0 := by exact_mod_cast hradix
  simp only [mul, value, Int.cast_mul, zpow_add₀ hr]
  ring

end RadixNumber

end Nucleus
