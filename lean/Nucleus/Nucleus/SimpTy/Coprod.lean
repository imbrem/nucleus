import Nucleus.SimpTy.Atom

/-! # Free coproduct types -/

namespace Nucleus

universe u v

/-- Free coproduct expressions over a family of atoms. -/
inductive CoprodTy (Base : Type u) where
  | base (code : Base)
  | sum (left right : CoprodTy Base)
  deriving DecidableEq, Repr

abbrev CoprodTy1 (Base : Type u) := CoprodTy (SimpTy.Atom1 Base)
abbrev CoprodTy0 (Base : Type u) := CoprodTy (SimpTy.Atom0 Base)

namespace CoprodTy

variable {Base : Type u}

instance : Add (CoprodTy Base) where add := .sum

def denote (base : Base → Type v) : CoprodTy Base → Type v
  | .base code => base code
  | .sum left right => denote base left ⊕ denote base right

instance [Denotes Base] : Denotes (CoprodTy Base) where
  denote := denote fun code => code

instance [Denotes Base] : HasCoproduct (CoprodTy Base) where
  coproduct := .sum
  encodes _ _ := ⟨Equiv.refl _⟩

instance [Denotes Base] [HasEmpty Base] : HasEmpty (CoprodTy Base) where
  empty := .base HasEmpty.empty
  encodes := ⟨HasEmpty.encodes.equiv⟩

instance [Denotes Base] [HasUnit Base] : HasUnit (CoprodTy Base) where
  unit := .base HasUnit.unit
  encodes := ⟨HasUnit.encodes.equiv⟩

instance [Denotes Base] [HasNat Base] : HasNat (CoprodTy Base) where
  nat := .base HasNat.nat
  encodes := ⟨HasNat.encodes.equiv⟩

instance [Denotes Base] [HasBool Base] : HasBool (CoprodTy Base) where
  bool := .base HasBool.bool
  encodes := ⟨HasBool.encodes.equiv⟩

/-- Include coproduct expressions in unrestricted simple types. -/
def toSimpTy : CoprodTy Base → SimpTy Base
  | .base code => .base code
  | .sum left right => .sum left.toSimpTy right.toSimpTy

def denoteToSimpTyEquiv (base : Base → Type v) :
    (code : CoprodTy Base) → SimpTy.denote base code.toSimpTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .sum left right =>
      Equiv.sumCongr (denoteToSimpTyEquiv base left) (denoteToSimpTyEquiv base right)

end CoprodTy

end Nucleus
