import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-!
# Simple index types

This module defines free syntax for host/index types, independently of any HOL
object language. `SimpleType0` includes the empty type. `SimpleType1` is its
nonempty fragment, intended for settings whose carriers must be inhabited.

Exponentiation follows cardinal arithmetic: `B ^ A` denotes the function
space `A → B`.
-/

namespace Nucleus.IndexType

universe u v

/-- A minimal capability for a type of codes with binary coproducts. -/
class HasCoproduct (Code : Type u) where
  coproduct : Code → Code → Code

/-- Free simple index types including the empty type. -/
inductive SimpleType0 (Base : Type u) where
  | base (code : Base)
  | empty
  | unit
  | sum (left right : SimpleType0 Base)
  | prod (left right : SimpleType0 Base)
  | arr (domain codomain : SimpleType0 Base)
  deriving DecidableEq, Repr

/-- Free nonempty simple index types. -/
inductive SimpleType1 (Base : Type u) where
  | base (code : Base)
  | unit
  | sum (left right : SimpleType1 Base)
  | prod (left right : SimpleType1 Base)
  | arr (domain codomain : SimpleType1 Base)
  deriving DecidableEq, Repr

namespace SimpleType0

variable {Base : Type u}

instance : HasCoproduct (SimpleType0 Base) where
  coproduct := .sum

instance : Zero (SimpleType0 Base) where
  zero := .empty

instance : One (SimpleType0 Base) where
  one := .unit

instance : Add (SimpleType0 Base) where
  add := HasCoproduct.coproduct

instance : Mul (SimpleType0 Base) where
  mul := .prod

/-- `codomain ^ domain` is the code for `domain → codomain`. -/
instance : HomogeneousPow (SimpleType0 Base) where
  pow codomain domain := .arr domain codomain

/-- The code for a positive finite cardinality, indexed one below its size. -/
def positive : Nat → SimpleType0 Base
  | 0 => .unit
  | n + 1 => .sum .unit (positive n)

/-- The canonical numeral code: zero is empty and positive numerals are sums
of units. -/
def numeral : Nat → SimpleType0 Base
  | 0 => .empty
  | n + 1 => positive n

instance (n : Nat) : OfNat (SimpleType0 Base) n where
  ofNat := numeral n

/-- Interpret a simple index-type code as a Lean type. -/
def denote (base : Base → Type v) : SimpleType0 Base → Type v
  | .base code => base code
  | .empty => PEmpty.{v + 1}
  | .unit => PUnit.{v + 1}
  | .sum left right => denote base left ⊕ denote base right
  | .prod left right => denote base left × denote base right
  | .arr domain codomain => denote base domain → denote base codomain

@[simp] theorem denote_base_id (X : Type u) :
    denote (Base := Type u) id (.base X) = X := rfl

end SimpleType0

namespace SimpleType1

variable {Base : Type u}

instance : HasCoproduct (SimpleType1 Base) where
  coproduct := .sum

instance : One (SimpleType1 Base) where
  one := .unit

instance : Add (SimpleType1 Base) where
  add := HasCoproduct.coproduct

instance : Mul (SimpleType1 Base) where
  mul := .prod

/-- `codomain ^ domain` is the code for `domain → codomain`. -/
instance : HomogeneousPow (SimpleType1 Base) where
  pow codomain domain := .arr domain codomain

/-- The canonical positive numeral code. There is deliberately no zero
instance for the nonempty fragment. -/
def positive : Nat → SimpleType1 Base
  | 0 => .unit
  | n + 1 => .sum .unit (positive n)

instance (n : Nat) : OfNat (SimpleType1 Base) (n + 1) where
  ofNat := positive n

/-- Interpret a nonempty simple index-type code as a Lean type. Base codes are
not required to denote nonempty types here; that condition belongs to models
which need it. -/
def denote (base : Base → Type v) : SimpleType1 Base → Type v
  | .base code => base code
  | .unit => PUnit.{v + 1}
  | .sum left right => denote base left ⊕ denote base right
  | .prod left right => denote base left × denote base right
  | .arr domain codomain => denote base domain → denote base codomain

/-- Include the no-empty syntax in the syntax which has an empty constructor. -/
def toType0 : SimpleType1 Base → SimpleType0 Base
  | .base code => .base code
  | .unit => .unit
  | .sum left right => .sum left.toType0 right.toType0
  | .prod left right => .prod left.toType0 right.toType0
  | .arr domain codomain => .arr domain.toType0 codomain.toType0

private def ofType0? : SimpleType0 Base → Option (SimpleType1 Base)
  | .base code => some (.base code)
  | .empty => none
  | .unit => some .unit
  | .sum left right => .sum <$> ofType0? left <*> ofType0? right
  | .prod left right => .prod <$> ofType0? left <*> ofType0? right
  | .arr domain codomain => .arr <$> ofType0? domain <*> ofType0? codomain

@[simp] private theorem ofType0?_toType0 (code : SimpleType1 Base) :
    ofType0? code.toType0 = some code := by
  induction code <;> simp [toType0, ofType0?, *] <;> rfl

theorem toType0_injective : Function.Injective (@toType0 Base) := by
  intro left right equality
  have := congrArg ofType0? equality
  simpa using this

/-- Inclusion into `SimpleType0` preserves denotation up to a canonical
structural equivalence. -/
def denoteToType0Equiv (base : Base → Type v) :
    (code : SimpleType1 Base) →
      SimpleType0.denote base code.toType0 ≃ denote base code
  | .base _ => Equiv.refl _
  | .unit => Equiv.refl _
  | .sum left right =>
      Equiv.sumCongr (denoteToType0Equiv base left) (denoteToType0Equiv base right)
  | .prod left right =>
      Equiv.prodCongr (denoteToType0Equiv base left) (denoteToType0Equiv base right)
  | .arr domain codomain =>
      Equiv.arrowCongr (denoteToType0Equiv base domain)
        (denoteToType0Equiv base codomain)

@[simp] theorem denote_base_id (X : Type u) :
    denote (Base := Type u) id (.base X) = X := rfl

end SimpleType1

section Examples

variable {Base : Type u}

example : (0 : SimpleType0 Empty) = .empty := rfl
example : (1 : SimpleType0 Empty) = .unit := rfl
example : (3 : SimpleType1 Empty) = .sum .unit (.sum .unit .unit) := rfl

example (left right : SimpleType0 Empty) : left + right = .sum left right := rfl
example (left right : SimpleType0 Empty) : left * right = .prod left right := rfl
example (domain codomain : SimpleType0 Empty) :
    codomain ^ domain = .arr domain codomain := rfl

example (base : Base → Type v) (domain codomain : SimpleType0 Base) :
    SimpleType0.denote base (codomain ^ domain) =
      (SimpleType0.denote base domain → SimpleType0.denote base codomain) := rfl

end Examples

end Nucleus.IndexType
