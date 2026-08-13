import Mathlib.Logic.Equiv.Set
import Nucleus.HolLN.Intrinsic

/-!
# The intrinsically typed HOL term model

Closed checked terms are identified when the empty-context kernel proves them
equal.  Boolean and natural quotation are injective into these quotients by
soundness.  They are consequently bijections onto the subtypes of quoted
values.  Surjectivity onto the whole quotient is the stronger closed-term
canonicity theorem and is intentionally not inferred from consistency alone.
-/

namespace Nucleus.HolLN.Intrinsic

universe u

abbrev ClosedChecked (Base : Type u) (A : Ty Base) :=
  Checked (emptyBound : BoundCtx Base 0) A

def ProvablyEq {Base : Type u} {A : Ty Base}
    (left right : ClosedChecked Base A) : Prop :=
  Nonempty (Nucleus.HolLN.EqTm (emptyBound : BoundCtx Base 0) left.tm right.tm A)

instance termSetoid (Base : Type u) (A : Ty Base) : Setoid (ClosedChecked Base A) where
  r := ProvablyEq
  iseqv := {
    refl := fun term => ⟨.refl term.typing⟩
    symm := fun ⟨proof⟩ => ⟨.symm proof⟩
    trans := fun ⟨left⟩ ⟨right⟩ => ⟨.trans left right⟩
  }

/-- The closed syntactic/term model at an HOL type. -/
abbrev TermModel (Base : Type u) (A : Ty Base) :=
  Quotient (termSetoid Base A)

abbrev BoolTermModel (Base : Type u) := TermModel Base .boolTy
abbrev NatTermModel (Base : Type u) := TermModel Base .natTy

def quoteBool {Base : Type u} (value : Bool) : BoolTermModel Base :=
  Quotient.mk _ (Checked.boolean value)

def quoteNat {Base : Type u} (value : Nat) : NatTermModel Base :=
  Quotient.mk _ (Checked.natural value)

private theorem evalBoolLiteral {Base : Type u} (value : Bool) :
    Eval (emptyBound : BoundCtx Base 0) defaultFreeEnv emptyBoundEnv
      (Checked.boolean (Γ := emptyBound) value).tm .boolTy value :=
  .boolean value

private theorem evalNatLiteral {Base : Type u} : (value : Nat) ->
    Eval (emptyBound : BoundCtx Base 0) defaultFreeEnv emptyBoundEnv
      (Checked.natural (Γ := emptyBound) value).tm .natTy value
  | 0 => .naturalZero
  | n + 1 => .naturalSucc (evalNatLiteral n)

theorem quoteBool_injective {Base : Type u} :
    Function.Injective (@quoteBool Base) := by
  intro left right equality
  obtain ⟨proof⟩ := Quotient.exact equality
  exact proof.sound defaultFreeEnv emptyBoundEnv
    (evalBoolLiteral left) (evalBoolLiteral right)

theorem quoteNat_injective {Base : Type u} :
    Function.Injective (@quoteNat Base) := by
  intro left right equality
  obtain ⟨proof⟩ := Quotient.exact equality
  exact proof.sound defaultFreeEnv emptyBoundEnv
    (evalNatLiteral left) (evalNatLiteral right)

/-- The part of the Boolean term model represented by Boolean literals. -/
abbrev QuotedBool (Base : Type u) := Set.range (@quoteBool Base)

/-- The part of the natural term model represented by numerals. -/
abbrev QuotedNat (Base : Type u) := Set.range (@quoteNat Base)

noncomputable def boolEquivQuoted (Base : Type u) : Bool ≃ QuotedBool Base :=
  Equiv.ofInjective (@quoteBool Base) quoteBool_injective

noncomputable def natEquivQuoted (Base : Type u) : Nat ≃ QuotedNat Base :=
  Equiv.ofInjective (@quoteNat Base) quoteNat_injective

end Nucleus.HolLN.Intrinsic
