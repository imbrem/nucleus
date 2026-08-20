import Nucleus.SimpTy.Coprod
import Nucleus.SimpTy.Prod

/-!
# Free polynomial types

`PolyTy` is the ordinary coproduct-and-product fragment. Natural powers are
represented by repeated products; arbitrary function-space exponents belong
to `SimpTy` (or a future `IndexedPolyTy Base Arity`).
-/

namespace Nucleus

universe u v

/-- Free polynomial expressions—coproducts and products—over atoms. -/
inductive PolyTy (Base : Type u) where
  | base (code : Base)
  | sum (left right : PolyTy Base)
  | prod (left right : PolyTy Base)
  deriving DecidableEq, Repr

abbrev PolyTy1 (Base : Type u) := PolyTy (SimpTy.Atom1 Base)
abbrev PolyTy0 (Base : Type u) := PolyTy (SimpTy.Atom0 Base)

namespace PolyTy

variable {Base : Type u}

instance : Add (PolyTy Base) where add := .sum
instance : Mul (PolyTy Base) where mul := .prod

def denote (base : Base → Type v) : PolyTy Base → Type v
  | .base code => base code
  | .sum left right => denote base left ⊕ denote base right
  | .prod left right => denote base left × denote base right

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

/-- Include polynomial expressions in unrestricted simple types. -/
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

namespace CoprodTy

variable {Base : Type u}

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

variable {Base : Type u}

def toPolyTy : ProdTy Base → PolyTy Base
  | .base code => .base code
  | .prod left right => .prod left.toPolyTy right.toPolyTy

def denoteToPolyTyEquiv (base : Base → Type v) :
    (code : ProdTy Base) → PolyTy.denote base code.toPolyTy ≃ denote base code
  | .base _ => Equiv.refl _
  | .prod left right =>
      Equiv.prodCongr (denoteToPolyTyEquiv base left) (denoteToPolyTyEquiv base right)

end ProdTy

end Nucleus
