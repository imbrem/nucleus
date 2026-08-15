import Nucleus.Hol.FamilySub.Algebraic

/-! # Abstract finite-list structure -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

/-- Syntax needed to use finite lists independently of their representation. -/
class ListOps (Sig : Signature) [SigTyping Sig] where
  list {types : List Kind} {A : Ty Sig types} : Kinded A → Ty Sig types
  listKinded {types : List Kind} {A : Ty Sig types} (hA : Kinded A) :
    Kinded (list hA)
  nil {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A : Ty Sig types} (hA : Kinded A) : DefEqChecked Sig Γ (list hA)
  cons {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A : Ty Sig types} (hA : Kinded A) :
    DefEqChecked Sig Γ A → DefEqChecked Sig Γ (list hA) →
      DefEqChecked Sig Γ (list hA)
  recurse {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B)
    (base : DefEqChecked Sig Γ B)
    (step : DefEqChecked Sig Γ (.arr A (.arr (list hA) (.arr B B))))
    (value : DefEqChecked Sig Γ (list hA)) : DefEqChecked Sig Γ B

class ListRules (Sig : Signature) [SigTyping Sig] [ListOps Sig] where
  recurseNil {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (base : DefEqChecked Sig Γ B)
    (step : DefEqChecked Sig Γ (.arr A (.arr (ListOps.list hA) (.arr B B)))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB
      (ListOps.recurse hA hB base step (ListOps.nil hA)) base)
  recurseCons {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (base : DefEqChecked Sig Γ B)
    (step : DefEqChecked Sig Γ (.arr A (.arr (ListOps.list hA) (.arr B B))))
    (head : DefEqChecked Sig Γ A) (tail : DefEqChecked Sig Γ (ListOps.list hA)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB
      (ListOps.recurse hA hB base step (ListOps.cons hA head tail))
      (((step.app head).app tail).app (ListOps.recurse hA hB base step tail)))
  consInjectiveHead {types : List Kind} {depth : Nat}
    {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {A : Ty Sig types}
    (typed : TypedCtx Γ) (hA : Kinded A)
    (head₁ head₂ : DefEqChecked Sig Γ A)
    (tail₁ tail₂ : DefEqChecked Sig Γ (ListOps.list hA))
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (ListOps.listKinded hA)
        (ListOps.cons hA head₁ tail₁) (ListOps.cons hA head₂ tail₂))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA head₁ head₂)
  consInjectiveTail {types : List Kind} {depth : Nat}
    {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {A : Ty Sig types}
    (typed : TypedCtx Γ) (hA : Kinded A)
    (head₁ head₂ : DefEqChecked Sig Γ A)
    (tail₁ tail₂ : DefEqChecked Sig Γ (ListOps.list hA))
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (ListOps.listKinded hA)
        (ListOps.cons hA head₁ tail₁) (ListOps.cons hA head₂ tail₂))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq (ListOps.listKinded hA) tail₁ tail₂)
  nilNeCons {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (head : DefEqChecked Sig Γ A)
    (tail : DefEqChecked Sig Γ (ListOps.list hA)) :
    Intrinsic.Proves Γ H (DefEqChecked.not
      (DefEqChecked.eq (ListOps.listKinded hA) (ListOps.nil hA)
        (ListOps.cons hA head tail)))

/-- First-class `* → *` presentation of lists. -/
class ListFamilyOps (Sig : Signature) [SigTyping Sig] [ListOps Sig] where
  family : Fam Sig [] (.arr .star .star)
  familyKinded : Kinded family
  applyEq {A : Ty Sig []} (hA : Kinded A) :
    FamEq Sig (.tyApp family A) (ListOps.list hA)

class ListTheory (Sig : Signature) [SigTyping Sig] extends
    ListOps Sig, ListRules Sig, ListFamilyOps Sig

end Nucleus.Hol.FamilySub
