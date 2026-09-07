import Nucleus.HolE.ClassicalNaturals
import Mathlib.Logic.Equiv.List

/-!
# Integers and finite words from the infinity-derived natural model

An integer is a sign and a natural magnitude, with negative zero excluded.
This is a subtype construction over the existing natural model, not a new
integer axiom. The equivalence below supplies the concrete interpretation of
the compact integer carrier. It uses the classical choice already used by
`CNatModel.toNat`; it assumes neither integer axioms nor a lowering oracle.
-/

namespace Nucleus.Hol.Propane

open Nucleus.HolE.Infinity

noncomputable section

/-- A canonical signed magnitude over a particular natural model. -/
def ModelInt (naturals : CNatModel) :=
  { value : Bool × naturals.carrier // value.1 = true → naturals.toNat value.2 ≠ 0 }

namespace ModelInt

variable (naturals : CNatModel)

def toInt (value : ModelInt naturals) : Int :=
  if value.val.1 then -(naturals.toNat value.val.2 : Int)
  else (naturals.toNat value.val.2 : Int)

def ofInt : Int → ModelInt naturals
  | .ofNat value => ⟨(false, naturals.ofNat value), by simp⟩
  | .negSucc value => ⟨(true, naturals.ofNat (value + 1)), by simp⟩

@[simp] theorem toInt_ofInt (value : Int) :
    toInt naturals (ofInt naturals value) = value := by
  cases value <;> simp [ofInt, toInt, Int.negSucc_eq]

@[simp] theorem ofInt_toInt (value : ModelInt naturals) :
    ofInt naturals (toInt naturals value) = value := by
  rcases value with ⟨⟨sign, magnitude⟩, normal⟩
  apply Subtype.ext
  cases sign with
  | false => simp [toInt, ofInt]
  | true =>
      have nonzero := normal rfl
      obtain ⟨number, equality⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
      simp only [toInt, ↓reduceIte]
      rw [equality]
      change (true, naturals.ofNat (number + 1)) = (true, magnitude)
      congr 1
      change naturals.ofNat number.succ = magnitude
      rw [← equality]
      exact naturals.ofNat_toNat magnitude

/-- Concrete categoricity of the integer construction. -/
def equivInt : ModelInt naturals ≃ Int where
  toFun := toInt naturals
  invFun := ofInt naturals
  left_inv := ofInt_toInt naturals
  right_inv := toInt_ofInt naturals

end ModelInt

/-- The existing infinity witness suffices to construct the integer carrier;
there is no independently postulated integer model. -/
def integerEquivOfInfinity {carrier : Nucleus.HolE.CPointed}
    (infinity : CInfinityStructure carrier) : ModelInt infinity.natModel ≃ Int :=
  ModelInt.equivInt infinity.natModel

/-- Fixed-width values are bounded elements of the same natural carrier. -/
def ModelWord (naturals : CNatModel) (width : Nat) :=
  { value : naturals.carrier // naturals.toNat value < 2 ^ width }

def modelWordEquiv (naturals : CNatModel) (width : Nat) :
    ModelWord naturals width ≃ Fin (2 ^ width) where
  toFun value := ⟨naturals.toNat value.val, value.property⟩
  invFun value := ⟨naturals.ofNat value.val, by simp [value.isLt]⟩
  left_inv value := by apply Subtype.ext; exact naturals.ofNat_toNat value.val
  right_inv value := by apply Fin.ext; exact naturals.toNat_ofNat value.val

/-- Bytes are actual finite lists of octets over the natural model. -/
abbrev ModelBytes (naturals : CNatModel) := List (ModelWord naturals 8)

def modelBytesEquiv (naturals : CNatModel) :
    ModelBytes naturals ≃ List (Fin 256) :=
  Equiv.listEquivOfEquiv (modelWordEquiv naturals 8)

end

end Nucleus.Hol.Propane
