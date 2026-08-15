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

/-- Universal quantification is equality with the constantly true predicate. -/
def forallTm (hA : Kinded A)
    (body : Checked Sig (extendBound A Γ) .boolTy) : Checked Sig Γ .boolTy :=
  Checked.eq (.arr hA .boolTy) (Checked.lam hA body)
    (Checked.lam hA Checked.truth)

end Checked

namespace DefEqChecked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A : Ty Sig types}

/-- Universal quantification is equality with the constantly true predicate. -/
def forallTm (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy) : BoolTm Γ :=
  DefEqChecked.eq (.arr hA .boolTy) (DefEqChecked.lam hA body)
    (DefEqChecked.lam hA DefEqChecked.truth)

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

/-- Universal elimination by application congruence and beta reduction. -/
noncomputable def forallElim (typed : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (argument : DefEqChecked Sig Γ A)
    (universal : Intrinsic.Proves Γ H (DefEqChecked.forallTm hA body)) :
    Intrinsic.Proves Γ H (body.openBound typed argument) := by
  have applied := Intrinsic.Proves.appCongr typed hA .boolTy
    (DefEqChecked.lam hA body) (DefEqChecked.lam hA DefEqChecked.truth)
    argument universal
  have leftReduction := Intrinsic.EqTm.beta typed hA body argument
  have rightReduction := Intrinsic.EqTm.beta typed hA
    (DefEqChecked.truth (Γ := extendBound A Γ)) argument
  have truthOpen :
      (DefEqChecked.truth (Γ := extendBound A Γ)).openBound typed argument =
        (DefEqChecked.truth : BoolTm Γ) := by
    apply DefEqChecked.ext
    simp [DefEqChecked.truth, DefEqChecked.boolean, DefEqChecked.openBound,
      FamilySub.openBound, instantiate]
  rw [truthOpen] at rightReduction
  have equality := Intrinsic.Proves.eqTrans typed .boolTy
    (body.openBound typed argument)
    ((DefEqChecked.lam hA DefEqChecked.truth).app argument) DefEqChecked.truth
    (Intrinsic.Proves.eqTrans typed .boolTy _
      ((DefEqChecked.lam hA body).app argument) _
      (Intrinsic.Proves.eqSymm typed .boolTy _ _
        (Intrinsic.Proves.eqOfEqTm .boolTy leftReduction)) applied)
    (Intrinsic.Proves.eqOfEqTm .boolTy rightReduction)
  exact Intrinsic.Proves.ofEqTrue typed equality

/-- Universal introduction delegates to the sound generalization certificate. -/
def forallIntro (hA : Kinded A) (body : BoolTm (extendBound A Γ))
    (premise : Intrinsic.Proves (extendBound A Γ) (PropCtx.weaken (A := A) H) body) :
    Intrinsic.Proves Γ H (DefEqChecked.forallTm hA body) :=
  Intrinsic.Proves.generalize hA body premise

end Intrinsic.Proves

end Nucleus.Hol.FamilySub
