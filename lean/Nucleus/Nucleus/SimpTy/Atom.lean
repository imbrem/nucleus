import Nucleus.SimpTy.Basic

/-!
# Distinguished atoms for simple types

`SimpTy1` adds a unit atom to a caller-supplied base family. `SimpTy0` adds
both unit and empty atoms. These are atom extensions rather than recursive
constructors, so they share all recursion principles with `SimpTy`.
-/

namespace Nucleus

universe u v

namespace SimpTy

variable {Base : Type u}

/-- Atoms for the fragment with a distinguished unit type. -/
inductive Atom1 (Base : Type u) where
  | ofBase (code : Base)
  | unit
  deriving DecidableEq, Repr

/-- Atoms for the fragment with distinguished unit and empty types. -/
inductive Atom0 (Base : Type u) where
  | ofBase (code : Base)
  | unit
  | empty
  deriving DecidableEq, Repr

instance [Denotes Base] : Denotes (Atom1 Base) where
  denote
    | .ofBase code => code
    | .unit => PUnit

instance [Denotes Base] : HasUnit (Atom1 Base) where
  unit := .unit
  encodes := ⟨(Equiv.equivPUnit Unit).symm⟩

instance [Denotes Base] : Denotes (Atom0 Base) where
  denote
    | .ofBase code => code
    | .unit => PUnit
    | .empty => PEmpty

instance [Denotes Base] : HasUnit (Atom0 Base) where
  unit := .unit
  encodes := ⟨(Equiv.equivPUnit Unit).symm⟩

instance [Denotes Base] : HasEmpty (Atom0 Base) where
  empty := .empty
  encodes := ⟨(Equiv.equivPEmpty Empty).symm⟩

/-- Include unit-bearing atoms in the unit-and-empty atom language. -/
def Atom1.toAtom0 : Atom1 Base → Atom0 Base
  | .ofBase code => .ofBase code
  | .unit => .unit

theorem Atom1.toAtom0_injective : Function.Injective (@Atom1.toAtom0 Base) := by
  intro left right equality
  cases left <;> cases right <;> simp_all [Atom1.toAtom0]

end SimpTy

/-- Simple types with a distinguished unit atom. -/
abbrev SimpTy1 (Base : Type u) := SimpTy (SimpTy.Atom1 Base)

/-- Simple types with distinguished unit and empty atoms. -/
abbrev SimpTy0 (Base : Type u) := SimpTy (SimpTy.Atom0 Base)

namespace SimpTy1

variable {Base : Type u}

def ofBase (code : Base) : SimpTy1 Base := .base (.ofBase code)
def unit : SimpTy1 Base := .base .unit

instance : One (SimpTy1 Base) where one := unit

/-- The canonical positive numeral code. There is deliberately no zero. -/
def positive : Nat → SimpTy1 Base
  | 0 => unit
  | n + 1 => .sum unit (positive n)

instance (n : Nat) : OfNat (SimpTy1 Base) (n + 1) where
  ofNat := positive n

def denoteAtom (base : Base → Type v) : SimpTy.Atom1 Base → Type v
  | .ofBase code => base code
  | .unit => PUnit.{v + 1}

/-- Interpret `SimpTy1`; unit reduces through the distinguished atom. -/
abbrev denote (base : Base → Type v) : SimpTy1 Base → Type v :=
  SimpTy.denote (denoteAtom base)

end SimpTy1

namespace SimpTy0

variable {Base : Type u}

def ofBase (code : Base) : SimpTy0 Base := .base (.ofBase code)
def unit : SimpTy0 Base := .base .unit
def empty : SimpTy0 Base := .base .empty

instance : Zero (SimpTy0 Base) where zero := empty
instance : One (SimpTy0 Base) where one := unit

/-- The canonical numeral code: zero is empty and positive numerals are sums
of units. -/
def numeral : Nat → SimpTy0 Base
  | 0 => empty
  | n + 1 => (SimpTy1.positive n).map SimpTy.Atom1.toAtom0

instance (n : Nat) : OfNat (SimpTy0 Base) n where
  ofNat := numeral n

def denoteAtom (base : Base → Type v) : SimpTy.Atom0 Base → Type v
  | .ofBase code => base code
  | .unit => PUnit.{v + 1}
  | .empty => PEmpty.{v + 1}

/-- Interpret `SimpTy0`; unit and empty reduce through distinguished atoms. -/
abbrev denote (base : Base → Type v) : SimpTy0 Base → Type v :=
  SimpTy.denote (denoteAtom base)

end SimpTy0

namespace SimpTy1

variable {Base : Type u}

/-- Include the no-empty simple types in the language with an empty atom. -/
def toSimpTy0 (code : SimpTy1 Base) : SimpTy0 Base := code.map SimpTy.Atom1.toAtom0

theorem toSimpTy0_injective : Function.Injective (@toSimpTy0 Base) :=
  SimpTy.map_injective SimpTy.Atom1.toAtom0_injective

/-- Inclusion into `SimpTy0` preserves denotation by a canonical equivalence. -/
def denoteToSimpTy0Equiv (base : Base → Type v) (code : SimpTy1 Base) :
    SimpTy0.denote base code.toSimpTy0 ≃ denote base code := match code with
  | .base (.ofBase _) => Equiv.refl _
  | .base .unit => Equiv.refl _
  | .sum left right =>
      Equiv.sumCongr (denoteToSimpTy0Equiv base left) (denoteToSimpTy0Equiv base right)
  | .prod left right =>
      Equiv.prodCongr (denoteToSimpTy0Equiv base left) (denoteToSimpTy0Equiv base right)
  | .arr domain codomain =>
      Equiv.arrowCongr (denoteToSimpTy0Equiv base domain)
        (denoteToSimpTy0Equiv base codomain)

end SimpTy1

section Examples

variable {Base : Type u}

example : (0 : SimpTy0 Empty) = SimpTy0.empty := rfl
example : (1 : SimpTy0 Empty) = SimpTy0.unit := rfl
example : (3 : SimpTy1 Empty) = .sum SimpTy1.unit (.sum SimpTy1.unit SimpTy1.unit) := rfl
example (base : Base → Type v) : SimpTy1.denote base SimpTy1.unit = PUnit := rfl
example (base : Base → Type v) : SimpTy0.denote base SimpTy0.empty = PEmpty := rfl

end Examples

end Nucleus
