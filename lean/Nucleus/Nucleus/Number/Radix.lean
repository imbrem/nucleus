import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring

/-!
# Exact radix-scaled integers

`RadixNumber r` represents `mantissa * r ^ exponent` exactly. `ExactRadix r`
adds an IEEE-like normal-form invariant: zero has exponent zero, and a nonzero
mantissa has no trailing radix factor. Raw representations remain available
because parsers may need to preserve non-preferred syntax.
-/

namespace Nucleus

/-- An exact integer mantissa scaled by an integral power of `radix`. -/
structure RadixNumber (radix : Nat) where
  exponent : Int
  mantissa : Int
  deriving DecidableEq, Repr

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

/-- IEEE-like normal form for an unbounded radix number. Zero has a unique
representation; every nonzero significand has had all trailing radix factors
removed. The `1 < radix` premise excludes degenerate bases. -/
def RadixNormal (radix : Nat) (number : RadixNumber radix) : Prop :=
  1 < radix ∧
    if number.mantissa = 0 then number.exponent = 0
    else number.mantissa % (radix : Int) ≠ 0

/-- A canonical exact radix number: representation plus normal-form proof. -/
structure ExactRadix (radix : Nat) extends RadixNumber radix where
  normal : RadixNormal radix toRadixNumber

namespace ExactRadix

variable {radix : Nat}

/-- Forget normality and expose the exponent/mantissa representation. -/
def rep (number : ExactRadix radix) : RadixNumber radix := number.toRadixNumber

/-- Exact rational denotation. -/
def toRat (number : ExactRadix radix) : ℚ := number.rep.value

@[simp] theorem toRat_def (number : ExactRadix radix) :
    number.toRat = number.mantissa * (radix : ℚ) ^ number.exponent := rfl

/-- Canonical zero. -/
def zero (hradix : 1 < radix) : ExactRadix radix where
  exponent := 0
  mantissa := 0
  normal := ⟨hradix, by simp⟩

end ExactRadix

/-- Concrete decimal exponent/mantissa representation, including non-normal
forms preserved from syntax. -/
abbrev DecimalFractionRep := RadixNumber 10

/-- Decimal values modulo representation choices. -/
abbrev DecimalFraction := ExactRadix 10

/-- Concrete binary exponent/mantissa representation, including non-normal
forms preserved from syntax. -/
abbrev DyadicRep := RadixNumber 2

/-- Dyadic values modulo representation choices. -/
abbrev Dyadic := ExactRadix 2

end Nucleus
