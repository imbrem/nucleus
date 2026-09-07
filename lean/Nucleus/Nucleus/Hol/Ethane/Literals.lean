import Nucleus.Hol.Propane.IntegerModel
import Nucleus.Hol.Propane.Builtin

/-!
# Concrete Ethane literal extension

This named model describes the literal/builtin extension of the running Rust
kernel. Older Ethane modules remain models of the opcode-free design. Base
carriers are constructed from the existing infinity-derived natural model;
their interpretation is fixed here, rather than supplied by an assumed sound
lowering package. `Builtin.eval` is the complete mathematical operation
inventory. Compact wire decoding is a separate boundary.

The trusted computation rule requires successful evaluation. Its theorem below
applies to every builtin and arbitrary operands, including partial operations.
The model introduces no independent integer, word, or bytes axiom.
-/

namespace Nucleus.Hol.Ethane.Literals

open Nucleus.Hol.Propane Nucleus.HolE.Infinity

noncomputable section

def Carrier (naturals : CNatModel) : LiteralTy → Type
  | .bool => Bool
  | .nat => naturals.carrier
  | .int => ModelInt naturals
  | .word width => ModelWord naturals width.bits
  | .bytes => ModelBytes naturals

private def octetEquiv : Fin 256 ≃ UInt8 where
  toFun := UInt8.ofFin
  invFun := UInt8.toFin
  left_inv := UInt8.toFin_ofFin
  right_inv := UInt8.ofFin_toFin

/-- The specific interpretation of each base carrier, with inverse laws proved. -/
def carrierEquiv (naturals : CNatModel) : (type : LiteralTy) →
    Carrier naturals type ≃ type.denote
  | .bool => Equiv.refl _
  | .nat => ⟨naturals.toNat, naturals.ofNat, naturals.ofNat_toNat, naturals.toNat_ofNat⟩
  | .int => ModelInt.equivInt naturals
  | .word width => (modelWordEquiv naturals width.bits).trans BitVec.equivFin.toEquiv.symm
  | .bytes => (modelBytesEquiv naturals).trans (Equiv.listEquivOfEquiv octetEquiv)

/-- A semantic value retains its carrier; allocation indices are absent. -/
abbrev Value (naturals : CNatModel) := (type : LiteralTy) × Carrier naturals type

def quote (naturals : CNatModel) (literal : LiteralValue) : Value naturals :=
  ⟨literal.type, (carrierEquiv naturals literal.type).symm literal.denote⟩

def unquote (naturals : CNatModel) (value : Value naturals) : LiteralValue :=
  LiteralValue.ofDenote value.1 (carrierEquiv naturals value.1 value.2)

@[simp] theorem unquote_quote (naturals : CNatModel) (literal : LiteralValue) :
    unquote naturals (quote naturals literal) = literal := by
  change LiteralValue.ofDenote literal.type
    ((carrierEquiv naturals literal.type)
      ((carrierEquiv naturals literal.type).symm literal.denote)) = literal
  rw [Equiv.apply_symm_apply, LiteralValue.ofDenote_denote]

@[simp] theorem quote_unquote (naturals : CNatModel) (value : Value naturals) :
    quote naturals (unquote naturals value) = value := by
  rcases value with ⟨type, value⟩
  cases type <;>
    exact congrArg (Sigma.mk _) ((carrierEquiv naturals _).symm_apply_apply value)

theorem quote_injective (naturals : CNatModel) : Function.Injective (quote naturals) := by
  intro left right equal
  have := congrArg (unquote naturals) equal
  simpa only [unquote_quote] using this

/-- Literal equality reflects equality in the concrete semantic carriers. -/
theorem quote_eq_iff (naturals : CNatModel) (left right : LiteralValue) :
    quote naturals left = quote naturals right ↔ left = right :=
  ⟨fun equal => quote_injective naturals equal, congrArg (quote naturals)⟩

/-- Concrete primitive meaning on the constructed Ethane carriers. -/
def interpret (naturals : CNatModel) (op : Builtin) (args : List (Value naturals)) :
    Option (Value naturals) :=
  (op.eval (args.map (unquote naturals))).map (quote naturals)

/-- All successful builtin reductions preserve the concrete interpretation.
There is no soundness field or arbitrary interpretation premise. -/
theorem builtin_sound (naturals : CNatModel) (op : Builtin)
    (args : List LiteralValue) (result : LiteralValue)
    (checked : op.eval args = some result) :
    interpret naturals op (args.map (quote naturals)) = some (quote naturals result) := by
  simp [interpret, List.map_map, Function.comp_def, checked]

end

end Nucleus.Hol.Ethane.Literals
