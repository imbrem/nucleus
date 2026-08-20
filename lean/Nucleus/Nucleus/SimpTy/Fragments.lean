import Nucleus.SimpTy

/-!
# Fragments of simple types

These are free syntax trees for smaller collections of type formers.  In
particular, `PolyTy` is the ordinary polynomial fragment: natural powers are
represented by repeated products, while arbitrary function-space exponents
belong to `SimpTy` (or a future `IndexedPolyTy Base Arity`).
-/

namespace Nucleus

universe u v

variable {Base : Type u}

/-- Free coproduct expressions over a family of atoms. -/
inductive CoprodTy (Base : Type u) where
  | base (code : Base)
  | sum (left right : CoprodTy Base)
  deriving DecidableEq, Repr

/-- Free product expressions over a family of atoms. -/
inductive ProdTy (Base : Type u) where
  | base (code : Base)
  | prod (left right : ProdTy Base)
  deriving DecidableEq, Repr

/-- Free polynomial expressions—coproducts and products—over atoms. -/
inductive PolyTy (Base : Type u) where
  | base (code : Base)
  | sum (left right : PolyTy Base)
  | prod (left right : PolyTy Base)
  deriving DecidableEq, Repr

abbrev CoprodTy1 (Base : Type u) := CoprodTy (SimpTy.Atom1 Base)
abbrev CoprodTy0 (Base : Type u) := CoprodTy (SimpTy.Atom0 Base)
abbrev ProdTy1 (Base : Type u) := ProdTy (SimpTy.Atom1 Base)
abbrev ProdTy0 (Base : Type u) := ProdTy (SimpTy.Atom0 Base)
abbrev PolyTy1 (Base : Type u) := PolyTy (SimpTy.Atom1 Base)
abbrev PolyTy0 (Base : Type u) := PolyTy (SimpTy.Atom0 Base)

namespace PolyTy

def denote (base : Base → Type v) : PolyTy Base → Type v
  | .base code => base code
  | .sum left right => denote base left ⊕ denote base right
  | .prod left right => denote base left × denote base right

end PolyTy

namespace CoprodTy

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

def toPolyTy : CoprodTy Base → PolyTy Base
  | .base code => .base code
  | .sum left right => .sum left.toPolyTy right.toPolyTy

def denoteToPolyTyEquiv (base : Base → Type v) :
    (code : CoprodTy Base) → PolyTy.denote base code.toPolyTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .sum left right =>
      Equiv.sumCongr (denoteToPolyTyEquiv base left) (denoteToPolyTyEquiv base right)

end CoprodTy

namespace ProdTy

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

def toPolyTy : ProdTy Base → PolyTy Base
  | .base code => .base code
  | .prod left right => .prod left.toPolyTy right.toPolyTy

def denoteToPolyTyEquiv (base : Base → Type v) :
    (code : ProdTy Base) → PolyTy.denote base code.toPolyTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .prod left right =>
      Equiv.prodCongr (denoteToPolyTyEquiv base left) (denoteToPolyTyEquiv base right)

end ProdTy

namespace PolyTy

instance : Add (PolyTy Base) where add := .sum
instance : Mul (PolyTy Base) where mul := .prod

instance [Denotes Base] : Denotes (PolyTy Base) where
  denote := denote fun code => code

instance [Denotes Base] : HasCoproduct (PolyTy Base) where
  coproduct := .sum
  encodes _ _ := ⟨Equiv.refl _⟩

instance [Denotes Base] : HasProduct (PolyTy Base) where
  product := .prod
  encodes _ _ := ⟨Equiv.refl _⟩

instance [Denotes Base] [HasEmpty Base] : HasEmpty (PolyTy Base) where
  empty := .base HasEmpty.empty
  encodes := ⟨HasEmpty.encodes.equiv⟩

instance [Denotes Base] [HasUnit Base] : HasUnit (PolyTy Base) where
  unit := .base HasUnit.unit
  encodes := ⟨HasUnit.encodes.equiv⟩

instance [Denotes Base] [HasNat Base] : HasNat (PolyTy Base) where
  nat := .base HasNat.nat
  encodes := ⟨HasNat.encodes.equiv⟩

instance [Denotes Base] [HasBool Base] : HasBool (PolyTy Base) where
  bool := .base HasBool.bool
  encodes := ⟨HasBool.encodes.equiv⟩

def toSimpTy : PolyTy Base → SimpTy Base
  | .base code => .base code
  | .sum left right => .sum left.toSimpTy right.toSimpTy
  | .prod left right => .prod left.toSimpTy right.toSimpTy

def denoteToSimpTyEquiv (base : Base → Type v) :
    (code : PolyTy Base) → SimpTy.denote base code.toSimpTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .sum left right =>
      Equiv.sumCongr (denoteToSimpTyEquiv base left) (denoteToSimpTyEquiv base right)
  | .prod left right =>
      Equiv.prodCongr (denoteToSimpTyEquiv base left) (denoteToSimpTyEquiv base right)

end PolyTy

end Nucleus
