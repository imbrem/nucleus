import Mathlib.Logic.Equiv.Defs
import Nucleus.HolOmega.TotalSubtype

/-! The part of the semantic universe needed by ordinary (monomorphic) HOL. -/

universe u

namespace Nucleus.Hol

set_option warn.classDefReducibility false

/-- Ordinary HOL requires no universe ranks and no closure under quantification
over codes.  Keeping this interface separate makes the predicative extension
needed by HOL-omega visible in types. -/
class Universe where
  Code : Type u
  El : Code → Type u
  inhabited : ∀ A, Inhabited (El A)
  boolCode : Code
  boolEquiv : El boolCode ≃ Bool
  arr : Code → Code → Code
  arrEquiv : ∀ A B, El (arr A B) ≃ (El A → El B)
  subCode : (A : Code) → (El A → Prop) → Code
  subEquiv : ∀ A P, El (subCode A P) ≃ HolOmega.TotalSubtype (El A) P

attribute [instance] Universe.inhabited

end Nucleus.Hol
