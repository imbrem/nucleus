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

end DefEqChecked

end Nucleus.Hol.FamilySub
