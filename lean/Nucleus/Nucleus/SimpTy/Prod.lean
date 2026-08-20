import Nucleus.SimpTy.Atom

/-! # Free product types -/

namespace Nucleus

universe u v

/-- Free product expressions over a family of atoms. -/
inductive ProdTy (Base : Type u) where
  | base (code : Base)
  | prod (left right : ProdTy Base)
  deriving DecidableEq, Repr

abbrev ProdTy1 (Base : Type u) := ProdTy (SimpTy.Atom1 Base)
abbrev ProdTy0 (Base : Type u) := ProdTy (SimpTy.Atom0 Base)

namespace ProdTy

variable {Base : Type u}

instance : Mul (ProdTy Base) where mul := .prod

def denote (base : Base → Type v) : ProdTy Base → Type v
  | .base code => base code
  | .prod left right => denote base left × denote base right

instance [Denotes Base] : Denotes (ProdTy Base) where
  denote := denote fun code => code

instance [Denotes Base] : HasProduct (ProdTy Base) where
  product := .prod
  encodes _ _ := ⟨Equiv.refl _⟩

instance [Denotes Base] [HasEmpty Base] : HasEmpty (ProdTy Base) where
  empty := .base HasEmpty.empty
  encodes := ⟨HasEmpty.encodes.equiv⟩

instance [Denotes Base] [HasUnit Base] : HasUnit (ProdTy Base) where
  unit := .base HasUnit.unit
  encodes := ⟨HasUnit.encodes.equiv⟩

instance [Denotes Base] [HasNat Base] : HasNat (ProdTy Base) where
  nat := .base HasNat.nat
  encodes := ⟨HasNat.encodes.equiv⟩

instance [Denotes Base] [HasBool Base] : HasBool (ProdTy Base) where
  bool := .base HasBool.bool
  encodes := ⟨HasBool.encodes.equiv⟩

/-- Include product expressions in unrestricted simple types. -/
def toSimpTy : ProdTy Base → SimpTy Base
  | .base code => .base code
  | .prod left right => .prod left.toSimpTy right.toSimpTy

def denoteToSimpTyEquiv (base : Base → Type v) :
    (code : ProdTy Base) → SimpTy.denote base code.toSimpTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .prod left right =>
      Equiv.prodCongr (denoteToSimpTyEquiv base left) (denoteToSimpTyEquiv base right)

end ProdTy

end Nucleus
