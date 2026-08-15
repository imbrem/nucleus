import Nucleus.Hol.FamilySub.Coproduct
import Nucleus.Hol.FamilySub.ProductLaws
import Nucleus.Hol.FamilySub.BoolLogic

/-! # Derived coproduct laws -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def inlBodyRight (_hA : Kinded A) (_hB : Kinded B)
    (value : DefEqChecked Sig Γ A)
    (left : DefEqChecked Sig Γ (.arr A .boolTy)) :
    BoolTm (extendBound (.arr B .boolTy) Γ) :=
  left.weaken.app value.weaken

def inlAfterLeft (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ A)
    (left : DefEqChecked Sig Γ (.arr A .boolTy)) :
    DefEqChecked Sig Γ (.arr (.arr B .boolTy) .boolTy) :=
  DefEqChecked.lam (.arr hB .boolTy) (inlBodyRight hA hB value left)

def inlBodyLeft (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) :
    DefEqChecked Sig (extendBound (.arr A .boolTy) Γ) (.arr (.arr B .boolTy) .boolTy) := by
  let hLeft : Kinded (.arr A .boolTy) := .arr hA .boolTy
  let left := DefEqChecked.bv
    (Γ := extendBound (.arr A .boolTy) Γ) hLeft 0 rfl
  exact inlAfterLeft hA hB value.weaken left

def inlChurchChecked (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) : DefEqChecked Sig Γ (coproductCarrier A B) :=
  DefEqChecked.lam (.arr hA .boolTy) (inlBodyLeft hA hB value)

theorem inlFirst_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) (left : DefEqChecked Sig Γ (.arr A .boolTy)) :
    (inlBodyLeft hA hB value).openBound typed left =
      inlAfterLeft hA hB value left := by
  apply DefEqChecked.ext
  simp [inlBodyLeft, inlAfterLeft, inlBodyRight, DefEqChecked.openBound,
    DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate, liftSub]

theorem inlSecond_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) (left : DefEqChecked Sig Γ (.arr A .boolTy))
    (right : DefEqChecked Sig Γ (.arr B .boolTy)) :
    (inlBodyRight hA hB value left).openBound typed right = left.app value := by
  apply DefEqChecked.ext
  simp [inlBodyRight, DefEqChecked.openBound, DefEqChecked.app,
    DefEqChecked.weaken, FamilySub.openBound, instantiate]

def inlChurch_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) (left : DefEqChecked Sig Γ (.arr A .boolTy))
    (right : DefEqChecked Sig Γ (.arr B .boolTy)) :
    Intrinsic.EqTm (((inlChurchChecked hA hB value).app left).app right)
      (left.app value) := by
  have first := Intrinsic.EqTm.beta typed (.arr hA .boolTy)
    (inlBodyLeft hA hB value) left
  rw [inlFirst_open typed hA hB value left] at first
  have applied := first.app (Intrinsic.EqTm.refl right)
  have second := Intrinsic.EqTm.beta typed (.arr hB .boolTy)
    (inlBodyRight hA hB value left) right
  rw [inlSecond_open typed hA hB value left right] at second
  exact applied.trans second

def inrBodyRight (_hA : Kinded A) (_hB : Kinded B)
    (value : DefEqChecked Sig Γ B) :
    BoolTm (extendBound (.arr B .boolTy) Γ) :=
  let boundRight := DefEqChecked.bv
    (Γ := extendBound (.arr B .boolTy) Γ) (.arr _hB .boolTy) 0 rfl
  boundRight.app value.weaken

def inrAfterLeft (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (.arr (.arr B .boolTy) .boolTy) :=
  DefEqChecked.lam (.arr hB .boolTy)
    (inrBodyRight hA hB value)

def inrBodyLeft (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) :
    DefEqChecked Sig (extendBound (.arr A .boolTy) Γ) (.arr (.arr B .boolTy) .boolTy) :=
  (inrAfterLeft hA hB value).weaken

def inrChurchChecked (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) : DefEqChecked Sig Γ (coproductCarrier A B) :=
  DefEqChecked.lam (.arr hA .boolTy) (inrBodyLeft hA hB value)

theorem inrFirst_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) (left : DefEqChecked Sig Γ (.arr A .boolTy)) :
    (inrBodyLeft hA hB value).openBound typed left = inrAfterLeft hA hB value := by
  apply DefEqChecked.ext
  simp [inrBodyLeft, inrAfterLeft, DefEqChecked.openBound,
    DefEqChecked.weaken, FamilySub.openBound]

theorem inrSecond_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) (right : DefEqChecked Sig Γ (.arr B .boolTy)) :
    (inrBodyRight hA hB value).openBound typed right =
      right.app value := by
  apply DefEqChecked.ext
  simp [inrBodyRight, DefEqChecked.openBound, DefEqChecked.app,
    DefEqChecked.bv, DefEqChecked.weaken, FamilySub.openBound, instantiate]

def inrChurch_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) (left : DefEqChecked Sig Γ (.arr A .boolTy))
    (right : DefEqChecked Sig Γ (.arr B .boolTy)) :
    Intrinsic.EqTm (((inrChurchChecked hA hB value).app left).app right)
      (right.app value) := by
  have first := Intrinsic.EqTm.beta typed (.arr hA .boolTy)
    (inrBodyLeft hA hB value) left
  rw [inrFirst_open typed hA hB value left] at first
  have applied := first.app (Intrinsic.EqTm.refl right)
  have second := Intrinsic.EqTm.beta typed (.arr hB .boolTy)
    (inrBodyRight hA hB value) right
  rw [inrSecond_open typed hA hB value right] at second
  exact applied.trans second

def coproductLeftBody (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) :
    BoolTm (extendBound A Γ) :=
  let value := DefEqChecked.bv (Γ := extendBound A Γ) hA 0 rfl
  DefEqChecked.eq (coproductCarrier_kinded hA hB) represented.weaken
    (inlChurchChecked hA hB value)

def coproductRightBody (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) :
    BoolTm (extendBound B Γ) :=
  let value := DefEqChecked.bv (Γ := extendBound B Γ) hB 0 rfl
  DefEqChecked.eq (coproductCarrier_kinded hA hB) represented.weaken
    (inrChurchChecked hA hB value)

def coproductLeftImage (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) : BoolTm Γ :=
  DefEqChecked.existsTm hA (coproductLeftBody hA hB represented)

def coproductRightImage (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) : BoolTm Γ :=
  DefEqChecked.existsTm hB (coproductRightBody hA hB represented)

def coproductMembership (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) : BoolTm Γ :=
  DefEqChecked.or (coproductLeftImage hA hB represented)
    (coproductRightImage hA hB represented)

def coproductPredicateAt (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) : BoolTm Γ :=
  ⟨instantiateOne (coproductPredicate hA hB).tm represented.tm,
    Checks.instantiateDefEq (coproductPredicate hA hB).typing
      (fun _ => represented.tm)
      (fun i => Fin.cases represented.typing (fun j => Fin.elim0 j) i)⟩

theorem coproductLeftBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B))
    (value : DefEqChecked Sig Γ A) :
    (coproductLeftBody hA hB represented).openBound typed value =
      DefEqChecked.eq (coproductCarrier_kinded hA hB) represented
        (inlChurchChecked hA hB value) := by
  apply DefEqChecked.ext
  simp [coproductLeftBody, inlChurchChecked, inlBodyLeft, inlAfterLeft,
    inlBodyRight, DefEqChecked.openBound, DefEqChecked.eq, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate, liftSub]

theorem coproductRightBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B))
    (value : DefEqChecked Sig Γ B) :
    (coproductRightBody hA hB represented).openBound typed value =
      DefEqChecked.eq (coproductCarrier_kinded hA hB) represented
        (inrChurchChecked hA hB value) := by
  apply DefEqChecked.ext
  simp [coproductRightBody, inrChurchChecked, inrBodyLeft, inrAfterLeft,
    inrBodyRight, DefEqChecked.openBound, DefEqChecked.eq, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate]
  simp [weaken, rename, instantiate, liftSub, liftRen]
  rw [rename_comp, rename_comp]
  congr 1

def coproductLeftImage_inl (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H (coproductLeftImage hA hB (inlChurchChecked hA hB value)) := by
  apply Intrinsic.Proves.existsIntroBody typed hA _ value
  rw [coproductLeftBody_open typed hA hB]
  exact Intrinsic.Proves.eqRefl (H := H) (coproductCarrier_kinded hA hB)
    (inlChurchChecked hA hB value)

def coproductRightImage_inr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (coproductRightImage hA hB (inrChurchChecked hA hB value)) := by
  apply Intrinsic.Proves.existsIntroBody typed hB _ value
  rw [coproductRightBody_open typed hA hB]
  exact Intrinsic.Proves.eqRefl (H := H) (coproductCarrier_kinded hA hB)
    (inrChurchChecked hA hB value)

noncomputable def coproductMembership_inl (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H (coproductMembership hA hB (inlChurchChecked hA hB value)) :=
  orIntroLeft typed (coproductLeftImage_inl typed hA hB value)

noncomputable def coproductMembership_inr (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (coproductMembership hA hB (inrChurchChecked hA hB value)) :=
  orIntroRight typed (coproductRightImage_inr typed hA hB value)

theorem coproductPredicateAt_eq_membership (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (coproductCarrier A B)) :
    coproductPredicateAt hA hB represented = coproductMembership hA hB represented := by
  apply DefEqChecked.ext
  simp [coproductPredicateAt, coproductMembership, coproductLeftImage,
    coproductRightImage, coproductLeftBody, coproductRightBody,
    coproductPredicate, inlChurchChecked, inrChurchChecked, inlBodyLeft,
    inlAfterLeft, inlBodyRight, inrBodyLeft, inrAfterLeft, inrBodyRight,
    DefEqChecked.or, DefEqChecked.not, DefEqChecked.and,
    DefEqChecked.andLhs, DefEqChecked.andLhsBody, DefEqChecked.andRhs,
    DefEqChecked.existsTm, DefEqChecked.lam, DefEqChecked.app,
    DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.weaken, DefEqChecked.bv,
    DefEqChecked.boolean, DefEqChecked.truth, DefEqChecked.falsehood,
    Checked.or, Checked.not, Checked.and, Checked.existsTm, Checked.lam,
    Checked.app, Checked.eps, Checked.eq, Checked.weaken, Checked.bv,
    Checked.truth, Checked.falsehood, instantiateOne, instantiate, liftSub,
    weaken, rename, inlChurch, inrChurch]
  simp only [liftRen, Fin.cases_zero, finCasesOne, finCasesTwo]
  simp only [Fin.cases_succ]
  simp [Fin.cases_zero]
  all_goals
    rw [rename_comp, rename_comp]
    congr 1

noncomputable def coproductPredicate_inl (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H
      (coproductPredicateAt hA hB (inlChurchChecked hA hB value)) := by
  rw [coproductPredicateAt_eq_membership]
  exact coproductMembership_inl typed hA hB value

noncomputable def coproductPredicate_inr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (coproductPredicateAt hA hB (inrChurchChecked hA hB value)) := by
  rw [coproductPredicateAt_eq_membership]
  exact coproductMembership_inr typed hA hB value

def inlChecked (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (coproductTy hA hB) :=
  DefEqChecked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).tm
    (coproductPredicate hA hB).typing (inlChurchChecked hA hB value)

def inrChecked (hA : Kinded A) (hB : Kinded B) (value : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (coproductTy hA hB) :=
  DefEqChecked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).tm
    (coproductPredicate hA hB).typing (inrChurchChecked hA hB value)

def repCoproduct (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (coproductTy hA hB)) :
    DefEqChecked Sig Γ (coproductCarrier A B) :=
  DefEqChecked.rep (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).tm
    (coproductPredicate hA hB).typing value

noncomputable def rep_inl (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductCarrier_kinded hA hB)
        (repCoproduct hA hB (inlChecked hA hB value))
        (inlChurchChecked hA hB value)) :=
  Intrinsic.Proves.repAbs (coproductCarrier_kinded hA hB)
    (coproductPredicate hA hB).tm (coproductPredicate hA hB).typing
    (inlChurchChecked hA hB value)
    (coproductPredicateAt hA hB (inlChurchChecked hA hB value)) rfl
    (coproductPredicate_inl typed hA hB value)

noncomputable def rep_inr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductCarrier_kinded hA hB)
        (repCoproduct hA hB (inrChecked hA hB value))
        (inrChurchChecked hA hB value)) :=
  Intrinsic.Proves.repAbs (coproductCarrier_kinded hA hB)
    (coproductPredicate hA hB).tm (coproductPredicate hA hB).typing
    (inrChurchChecked hA hB value)
    (coproductPredicateAt hA hB (inrChurchChecked hA hB value)) rfl
    (coproductPredicate_inr typed hA hB value)

end Nucleus.Hol.FamilySub
