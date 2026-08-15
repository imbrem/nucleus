import Nucleus.Hol.FamilySub.Recursion

/-! # Basic Peano arithmetic equations from abstract recursion -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] [NaturalOps Sig]
  {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
  {H : PropCtx Γ}

def naturalAddAfterIndexBody :
    DefEqChecked Sig (extendBound NaturalOps.nat Γ) NaturalOps.nat :=
  NaturalOps.succ (DefEqChecked.bv NaturalOps.natKinded 0 rfl)

def naturalAddAfterIndex :
    DefEqChecked Sig Γ (.arr NaturalOps.nat NaturalOps.nat) :=
  DefEqChecked.lam NaturalOps.natKinded naturalAddAfterIndexBody

theorem naturalAddOuterBody_open (typed : TypedCtx Γ)
    (index : NatTm (Sig := Sig) (Γ := Γ)) :
    (naturalSuccFunction (Sig := Sig) (Γ := Γ)).weaken.openBound typed index =
      naturalAddAfterIndex := by
  apply DefEqChecked.ext
  simp [naturalSuccFunction, naturalSuccBody, naturalAddAfterIndex,
    naturalAddAfterIndexBody, DefEqChecked.openBound, DefEqChecked.lam,
    DefEqChecked.weaken, DefEqChecked.bv, FamilySub.openBound]

theorem naturalAddAfterIndexBody_open [NaturalSubstitutionLaws Sig]
    (typed : TypedCtx Γ)
    (accumulator : NatTm (Sig := Sig) (Γ := Γ)) :
    naturalAddAfterIndexBody.openBound typed accumulator =
      NaturalOps.succ accumulator := by
  have law := NaturalSubstitutionLaws.succOpen typed
    (DefEqChecked.bv NaturalOps.natKinded 0 rfl) accumulator
  have opened : (DefEqChecked.bv NaturalOps.natKinded 0 rfl).openBound
      typed accumulator = accumulator := by
    apply DefEqChecked.ext
    simp [DefEqChecked.openBound, DefEqChecked.bv, FamilySub.openBound]
  rw [opened] at law
  exact law

def naturalAddStep_apply [NaturalSubstitutionLaws Sig] (typed : TypedCtx Γ)
    (index accumulator : NatTm (Sig := Sig) (Γ := Γ)) :
    Intrinsic.EqTm (((naturalAddStep (Sig := Sig) (Γ := Γ)).app index).app accumulator)
      (NaturalOps.succ accumulator) := by
  have outer := Intrinsic.EqTm.beta typed NaturalOps.natKinded
    (naturalSuccFunction (Sig := Sig) (Γ := Γ)).weaken index
  rw [naturalAddOuterBody_open typed index] at outer
  have applied := Intrinsic.EqTm.app outer (Intrinsic.EqTm.refl accumulator)
  have inner := Intrinsic.EqTm.beta typed NaturalOps.natKinded
    naturalAddAfterIndexBody accumulator
  rw [naturalAddAfterIndexBody_open typed accumulator] at inner
  exact applied.trans inner

noncomputable def naturalAdd_zero [NaturalSubstitutionLaws Sig]
    [NaturalRecursorExistence Sig] (typed : TypedCtx Γ)
    (left : NatTm (Sig := Sig) (Γ := Γ)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq NaturalOps.natKinded
      (naturalAdd left NaturalOps.zero) left) :=
  NaturalRecursorRules.recZero typed NaturalOps.natKinded left naturalAddStep

noncomputable def naturalAdd_succ [NaturalSubstitutionLaws Sig]
    [NaturalRecursorExistence Sig] (typed : TypedCtx Γ)
    (left right : NatTm (Sig := Sig) (Γ := Γ)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq NaturalOps.natKinded
      (naturalAdd left (NaturalOps.succ right))
      (NaturalOps.succ (naturalAdd left right))) := by
  have unfolded := NaturalRecursorRules.recSucc (H := H) typed
    NaturalOps.natKinded left naturalAddStep right
  have reduced := naturalAddStep_apply typed right (naturalAdd left right)
  exact Intrinsic.Proves.eqTrans typed NaturalOps.natKinded _ _ _ unfolded
    (Intrinsic.Proves.eqOfEqTm (H := H) NaturalOps.natKinded reduced)

end Nucleus.Hol.FamilySub
