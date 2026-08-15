import Nucleus.Hol.FamilySub.Product
import Nucleus.Hol.FamilySub.BoolLogic

/-! # Derived implication and quantifiers -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

namespace Checked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A : Ty Sig types}

def imp (left right : Checked Sig Γ .boolTy) : Checked Sig Γ .boolTy :=
  Checked.eq .boolTy (Checked.and left right) left

/-- Universal quantification by classical duality, `∀x. p x = ¬∃x. ¬p x`. -/
def forallTm (hA : Kinded A)
    (body : Checked Sig (extendBound A Γ) .boolTy) : Checked Sig Γ .boolTy :=
  Checked.not (Checked.existsTm hA (Checked.lam hA (Checked.not body)))

end Checked

namespace DefEqChecked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A : Ty Sig types}

/-- Universal quantification by classical duality on definitionally typed terms. -/
def forallTm (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy) : BoolTm Γ :=
  DefEqChecked.not (DefEqChecked.existsTm hA (DefEqChecked.not body))

theorem not_openBound (typed : TypedCtx Γ)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (argument : DefEqChecked Sig Γ A) :
    (DefEqChecked.not body).openBound typed argument =
      DefEqChecked.not (body.openBound typed argument) := by
  apply DefEqChecked.ext
  simp [DefEqChecked.not, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.falsehood, DefEqChecked.boolean, FamilySub.openBound, instantiate]

end DefEqChecked

namespace Intrinsic.Proves

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {A : Ty Sig types}

/-- Universal elimination for the classical dual definition of `forall`. -/
noncomputable def forallElim (typed : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (argument : DefEqChecked Sig Γ A)
    (universal : Intrinsic.Proves Γ H (DefEqChecked.forallTm hA body)) :
    Intrinsic.Proves Γ H (body.openBound typed argument) := by
  let target := body.openBound typed argument
  apply doubleNegElim typed
  apply notIntro typed (DefEqChecked.not target)
  have universal' := Intrinsic.Proves.weakenHyp (DefEqChecked.not target) universal
  have negated : Intrinsic.Proves Γ (DefEqChecked.not target :: H)
      (DefEqChecked.not target) := Intrinsic.Proves.hyp (by simp)
  have witness : Intrinsic.Proves Γ (DefEqChecked.not target :: H)
      (DefEqChecked.existsTm hA (DefEqChecked.not body)) := by
    apply Intrinsic.Proves.existsIntroBody typed hA (DefEqChecked.not body) argument
    simpa [target, DefEqChecked.not_openBound typed body argument] using negated
  exact notElim typed universal' witness

end Intrinsic.Proves

end Nucleus.Hol.FamilySub
