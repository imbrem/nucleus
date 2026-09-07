import Nucleus.Hol.Propane.Semantics
import Nucleus.Hol.Ethane.Literals

/-!
# Propane and concrete Ethane literal correspondence

The computation rule is proved simultaneously in intrinsically typed Propane
and in the explicitly constructed Ethane carriers. It assumes the evaluator's
successful check, never a package asserting that arbitrary lowering is sound.
Builtin constants also apply to symbolic operands; the symbolic example below
is universally quantified over terms, valuations, and bound environments.
-/

namespace Nucleus.Hol.Propane

open Nucleus.HolE.Infinity

noncomputable section

theorem literal_reduction_correspondence (naturals : CNatModel) (op : Builtin)
    {Γ : List Ty} {inputs : List LiteralTy} {output : LiteralTy}
    (signature : op.signature = some (inputs, output))
    (args : LiteralArgs inputs) (result : output.denote)
    (checked : op.eval args.values = some (LiteralValue.ofDenote output result)) :
    SemEq ((Tm.builtin op signature : Tm Γ (Ty.arrows inputs output)).applyLiterals args)
      (.literal output result) ∧
    Nucleus.Hol.Ethane.Literals.interpret naturals op
      (args.values.map (Nucleus.Hol.Ethane.Literals.quote naturals)) =
      some (Nucleus.Hol.Ethane.Literals.quote naturals
        (LiteralValue.ofDenote output result)) :=
  ⟨(EqTm.builtinReduce op signature args result checked).sound,
    Nucleus.Hol.Ethane.Literals.builtin_sound naturals op args.values _ checked⟩

def Tm.nat {Γ : List Ty} (value : Nat) : Tm Γ .nat := .literal .nat value
def Tm.int {Γ : List Ty} (value : Int) : Tm Γ .int := .literal .int value
def Tm.bytes {Γ : List Ty} (value : List UInt8) : Tm Γ .bytes := .literal .bytes value
def Tm.word {Γ : List Ty} (width : Width) (value : BitVec width.bits) : Tm Γ (.word width) :=
  .literal (.word width) value

def Tm.natAdd {Γ : List Ty} (left right : Tm Γ .nat) : Tm Γ .nat :=
  .app (.app (.builtin (.nat .add) rfl) left) right

theorem Tm.eval_natAdd {Γ : List Ty} (left right : Tm Γ .nat)
    (valuation : Valuation) (env : Env Γ) :
    (left.natAdd right).eval valuation env =
      left.eval valuation env + right.eval valuation env := by
  rfl

/-- Symbolic operands retain their ordinary natural arithmetic interpretation. -/
theorem Tm.natAdd_comm {Γ : List Ty} (left right : Tm Γ .nat) :
    SemEq (left.natAdd right) (right.natAdd left) := by
  intro valuation env
  rw [Tm.eval_natAdd, Tm.eval_natAdd, Nat.add_comm]

end

end Nucleus.Hol.Propane
