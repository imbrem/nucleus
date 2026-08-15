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

def leftResultBody (hA : Kinded A) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (left : DefEqChecked Sig Γ (.arr A C)) :
    BoolTm (extendBound A Γ) :=
  let value := DefEqChecked.bv (Γ := extendBound A Γ) hA 0 rfl
  DefEqChecked.eq hC candidate.weaken (left.weaken.app value)

def leftResultPredicate (hA : Kinded A) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (left : DefEqChecked Sig Γ (.arr A C)) :
    DefEqChecked Sig Γ (.arr A .boolTy) :=
  DefEqChecked.lam hA (leftResultBody hA hC candidate left)

def rightResultBody (hB : Kinded B) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (right : DefEqChecked Sig Γ (.arr B C)) :
    BoolTm (extendBound B Γ) :=
  let value := DefEqChecked.bv (Γ := extendBound B Γ) hB 0 rfl
  DefEqChecked.eq hC candidate.weaken (right.weaken.app value)

def rightResultPredicate (hB : Kinded B) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (right : DefEqChecked Sig Γ (.arr B C)) :
    DefEqChecked Sig Γ (.arr B .boolTy) :=
  DefEqChecked.lam hB (rightResultBody hB hC candidate right)

theorem leftResultBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (left : DefEqChecked Sig Γ (.arr A C))
    (value : DefEqChecked Sig Γ A) :
    (leftResultBody hA hC candidate left).openBound typed value =
      DefEqChecked.eq hC candidate (left.app value) := by
  apply DefEqChecked.ext
  simp [leftResultBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate]

theorem rightResultBody_open (typed : TypedCtx Γ) (hB : Kinded B) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ B) :
    (rightResultBody hB hC candidate right).openBound typed value =
      DefEqChecked.eq hC candidate (right.app value) := by
  apply DefEqChecked.ext
  simp [rightResultBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate]

def leftResultPredicate_apply (typed : TypedCtx Γ) (hA : Kinded A) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (left : DefEqChecked Sig Γ (.arr A C))
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.EqTm ((leftResultPredicate hA hC candidate left).app value)
      (DefEqChecked.eq hC candidate (left.app value)) := by
  have reduction := Intrinsic.EqTm.beta typed hA
    (leftResultBody hA hC candidate left) value
  rw [leftResultBody_open typed hA hC candidate left value] at reduction
  exact reduction

def rightResultPredicate_apply (typed : TypedCtx Γ) (hB : Kinded B) (hC : Kinded C)
    (candidate : DefEqChecked Sig Γ C) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ B) :
    Intrinsic.EqTm ((rightResultPredicate hB hC candidate right).app value)
      (DefEqChecked.eq hC candidate (right.app value)) := by
  have reduction := Intrinsic.EqTm.beta typed hB
    (rightResultBody hB hC candidate right) value
  rw [rightResultBody_open typed hB hC candidate right value] at reduction
  exact reduction

def casePredicateAt (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (sum : DefEqChecked Sig Γ (coproductTy hA hB))
    (candidate : DefEqChecked Sig Γ C) : BoolTm Γ :=
  ((repCoproduct hA hB sum).app (leftResultPredicate hA hC candidate left)).app
    (rightResultPredicate hB hC candidate right)

def caseBody (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (sum : DefEqChecked Sig Γ (coproductTy hA hB)) : BoolTm (extendBound C Γ) :=
  let candidate := DefEqChecked.bv (Γ := extendBound C Γ) hC 0 rfl
  casePredicateAt hA hB hC left.weaken right.weaken sum.weaken candidate

def caseChecked (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (sum : DefEqChecked Sig Γ (coproductTy hA hB)) : DefEqChecked Sig Γ C :=
  DefEqChecked.eps hC (DefEqChecked.lam hC (caseBody hA hB hC left right sum))

theorem caseBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (hC : Kinded C) (left : DefEqChecked Sig Γ (.arr A C))
    (right : DefEqChecked Sig Γ (.arr B C))
    (sum : DefEqChecked Sig Γ (coproductTy hA hB))
    (candidate : DefEqChecked Sig Γ C) :
    (caseBody hA hB hC left right sum).openBound typed candidate =
      casePredicateAt hA hB hC left right sum candidate := by
  apply DefEqChecked.ext
  simp [caseBody, casePredicateAt, repCoproduct, leftResultPredicate,
    rightResultPredicate, leftResultBody, rightResultBody,
    DefEqChecked.openBound, DefEqChecked.rep, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.eq, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate, liftSub]

noncomputable def casePredicateAt_inl_eq (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ A) (candidate : DefEqChecked Sig Γ C) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy
        (casePredicateAt hA hB hC left right (inlChecked hA hB value) candidate)
        (DefEqChecked.eq hC candidate (left.app value))) := by
  let leftPredicate := leftResultPredicate hA hC candidate left
  let rightPredicate := rightResultPredicate hB hC candidate right
  have representation := rep_inl (H := H) typed hA hB value
  have afterLeft := Intrinsic.Proves.appCongr typed (.arr hA .boolTy)
    (.arr (.arr hB .boolTy) .boolTy)
    (repCoproduct hA hB (inlChecked hA hB value))
    (inlChurchChecked hA hB value) leftPredicate representation
  have applied := Intrinsic.Proves.appCongr typed (.arr hB .boolTy) .boolTy
    ((repCoproduct hA hB (inlChecked hA hB value)).app leftPredicate)
    ((inlChurchChecked hA hB value).app leftPredicate) rightPredicate afterLeft
  have reduction := (inlChurch_apply typed hA hB value leftPredicate rightPredicate).trans
    (leftResultPredicate_apply typed hA hC candidate left value)
  exact Intrinsic.Proves.eqTrans typed .boolTy
    (casePredicateAt hA hB hC left right (inlChecked hA hB value) candidate)
    (((inlChurchChecked hA hB value).app leftPredicate).app rightPredicate)
    (DefEqChecked.eq hC candidate (left.app value)) applied
    (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy reduction)

noncomputable def casePredicateAt_inr_eq (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ B) (candidate : DefEqChecked Sig Γ C) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy
        (casePredicateAt hA hB hC left right (inrChecked hA hB value) candidate)
        (DefEqChecked.eq hC candidate (right.app value))) := by
  let leftPredicate := leftResultPredicate hA hC candidate left
  let rightPredicate := rightResultPredicate hB hC candidate right
  have representation := rep_inr (H := H) typed hA hB value
  have afterLeft := Intrinsic.Proves.appCongr typed (.arr hA .boolTy)
    (.arr (.arr hB .boolTy) .boolTy)
    (repCoproduct hA hB (inrChecked hA hB value))
    (inrChurchChecked hA hB value) leftPredicate representation
  have applied := Intrinsic.Proves.appCongr typed (.arr hB .boolTy) .boolTy
    ((repCoproduct hA hB (inrChecked hA hB value)).app leftPredicate)
    ((inrChurchChecked hA hB value).app leftPredicate) rightPredicate afterLeft
  have reduction := (inrChurch_apply typed hA hB value leftPredicate rightPredicate).trans
    (rightResultPredicate_apply typed hB hC candidate right value)
  exact Intrinsic.Proves.eqTrans typed .boolTy
    (casePredicateAt hA hB hC left right (inrChecked hA hB value) candidate)
    (((inrChurchChecked hA hB value).app leftPredicate).app rightPredicate)
    (DefEqChecked.eq hC candidate (right.app value)) applied
    (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy reduction)

noncomputable def case_inl (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (hC : Kinded C) (left : DefEqChecked Sig Γ (.arr A C))
    (right : DefEqChecked Sig Γ (.arr B C)) (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hC (caseChecked hA hB hC left right (inlChecked hA hB value))
        (left.app value)) := by
  let target := left.app value
  let sum := inlChecked hA hB value
  let body := caseBody hA hB hC left right sum
  let predicate := DefEqChecked.lam hC body
  have atTargetEquality := casePredicateAt_inl_eq (H := H) typed hA hB hC
    left right value target
  have atTarget : Intrinsic.Proves Γ H
      (casePredicateAt hA hB hC left right sum target) :=
    Intrinsic.Proves.ofEqBool typed (DefEqChecked.eq hC target target)
      (casePredicateAt hA hB hC left right sum target)
      (Intrinsic.Proves.eqSymm typed .boolTy _ _ atTargetEquality)
      (Intrinsic.Proves.eqRefl hC target)
  have predicateAtTarget : Intrinsic.Proves Γ H (predicate.app target) :=
    Intrinsic.Proves.betaExpand typed hC body target
      (caseBody_open typed hA hB hC left right sum target ▸ atTarget)
  have predicateAtChoice : Intrinsic.Proves Γ H (predicate.app (predicate.eps hC)) :=
    Intrinsic.Proves.choice hC predicate target predicateAtTarget
  have opened : Intrinsic.Proves Γ H
      (casePredicateAt hA hB hC left right sum (caseChecked hA hB hC left right sum)) := by
    have reduced := Intrinsic.Proves.betaReduce typed hC body (predicate.eps hC)
      predicateAtChoice
    simpa [predicate, caseChecked] using
      (caseBody_open typed hA hB hC left right sum (predicate.eps hC) ▸ reduced)
  exact Intrinsic.Proves.ofEqBool typed
    (casePredicateAt hA hB hC left right sum (caseChecked hA hB hC left right sum))
    (DefEqChecked.eq hC (caseChecked hA hB hC left right sum) target)
    (casePredicateAt_inl_eq (H := H) typed hA hB hC left right value
      (caseChecked hA hB hC left right sum)) opened

noncomputable def case_inr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (hC : Kinded C) (left : DefEqChecked Sig Γ (.arr A C))
    (right : DefEqChecked Sig Γ (.arr B C)) (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hC (caseChecked hA hB hC left right (inrChecked hA hB value))
        (right.app value)) := by
  let target := right.app value
  let sum := inrChecked hA hB value
  let body := caseBody hA hB hC left right sum
  let predicate := DefEqChecked.lam hC body
  have atTargetEquality := casePredicateAt_inr_eq (H := H) typed hA hB hC
    left right value target
  have atTarget : Intrinsic.Proves Γ H
      (casePredicateAt hA hB hC left right sum target) :=
    Intrinsic.Proves.ofEqBool typed (DefEqChecked.eq hC target target)
      (casePredicateAt hA hB hC left right sum target)
      (Intrinsic.Proves.eqSymm typed .boolTy _ _ atTargetEquality)
      (Intrinsic.Proves.eqRefl hC target)
  have predicateAtTarget : Intrinsic.Proves Γ H (predicate.app target) :=
    Intrinsic.Proves.betaExpand typed hC body target
      (caseBody_open typed hA hB hC left right sum target ▸ atTarget)
  have predicateAtChoice : Intrinsic.Proves Γ H (predicate.app (predicate.eps hC)) :=
    Intrinsic.Proves.choice hC predicate target predicateAtTarget
  have opened : Intrinsic.Proves Γ H
      (casePredicateAt hA hB hC left right sum (caseChecked hA hB hC left right sum)) := by
    have reduced := Intrinsic.Proves.betaReduce typed hC body (predicate.eps hC)
      predicateAtChoice
    simpa [predicate, caseChecked] using
      (caseBody_open typed hA hB hC left right sum (predicate.eps hC) ▸ reduced)
  exact Intrinsic.Proves.ofEqBool typed
    (casePredicateAt hA hB hC left right sum (caseChecked hA hB hC left right sum))
    (DefEqChecked.eq hC (caseChecked hA hB hC left right sum) target)
    (casePredicateAt_inr_eq (H := H) typed hA hB hC left right value
      (caseChecked hA hB hC left right sum)) opened

def equalityPredicateBody (hA : Kinded A) (target : DefEqChecked Sig Γ A) :
    BoolTm (extendBound A Γ) :=
  DefEqChecked.eq hA (DefEqChecked.bv hA 0 rfl) target.weaken

def equalityPredicate (hA : Kinded A) (target : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (.arr A .boolTy) :=
  DefEqChecked.lam hA (equalityPredicateBody hA target)

theorem equalityPredicateBody_open (typed : TypedCtx Γ) (hA : Kinded A)
    (target value : DefEqChecked Sig Γ A) :
    (equalityPredicateBody hA target).openBound typed value =
      DefEqChecked.eq hA value target := by
  apply DefEqChecked.ext
  simp [equalityPredicateBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.bv, DefEqChecked.weaken, FamilySub.openBound, instantiate]

def equalityPredicate_apply (typed : TypedCtx Γ) (hA : Kinded A)
    (target value : DefEqChecked Sig Γ A) :
    Intrinsic.EqTm ((equalityPredicate hA target).app value)
      (DefEqChecked.eq hA value target) := by
  have reduction := Intrinsic.EqTm.beta typed hA (equalityPredicateBody hA target) value
  rw [equalityPredicateBody_open typed hA target value] at reduction
  exact reduction

/-- Equality of left Church injections determines their payloads. -/
noncomputable def inlChurch_injective (typed : TypedCtx Γ) (hA : Kinded A)
    (hB : Kinded B) (left right : DefEqChecked Sig Γ A)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductCarrier_kinded hA hB)
        (inlChurchChecked hA hB left) (inlChurchChecked hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA left right) := by
  let test := equalityPredicate hA left
  let ignored : DefEqChecked Sig Γ (.arr B .boolTy) :=
    DefEqChecked.arbitrary (.arr hB .boolTy)
  have afterTest := Intrinsic.Proves.appCongr typed (.arr hA .boolTy)
    (.arr (.arr hB .boolTy) .boolTy)
    (inlChurchChecked hA hB left) (inlChurchChecked hA hB right) test equality
  have applied := Intrinsic.Proves.appCongr typed (.arr hB .boolTy) .boolTy
    ((inlChurchChecked hA hB left).app test)
    ((inlChurchChecked hA hB right).app test) ignored afterTest
  have leftReduction := (inlChurch_apply typed hA hB left test ignored).trans
    (equalityPredicate_apply typed hA left left)
  have rightReduction := (inlChurch_apply typed hA hB right test ignored).trans
    (equalityPredicate_apply typed hA left right)
  have leftProof : Intrinsic.Proves Γ H
      (((inlChurchChecked hA hB left).app test).app ignored) :=
    Intrinsic.Proves.convert leftReduction.symm (Intrinsic.Proves.eqRefl hA left)
  have rightProof : Intrinsic.Proves Γ H
      (((inlChurchChecked hA hB right).app test).app ignored) :=
    Intrinsic.Proves.ofEqBool typed _ _ applied leftProof
  have payload : Intrinsic.Proves Γ H (DefEqChecked.eq hA right left) :=
    Intrinsic.Proves.convert rightReduction rightProof
  exact Intrinsic.Proves.eqSymm typed hA right left payload

/-- Equality of right Church injections determines their payloads. -/
noncomputable def inrChurch_injective (typed : TypedCtx Γ) (hA : Kinded A)
    (hB : Kinded B) (left right : DefEqChecked Sig Γ B)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductCarrier_kinded hA hB)
        (inrChurchChecked hA hB left) (inrChurchChecked hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB left right) := by
  let ignored : DefEqChecked Sig Γ (.arr A .boolTy) :=
    DefEqChecked.arbitrary (.arr hA .boolTy)
  let test := equalityPredicate hB left
  have afterIgnored := Intrinsic.Proves.appCongr typed (.arr hA .boolTy)
    (.arr (.arr hB .boolTy) .boolTy)
    (inrChurchChecked hA hB left) (inrChurchChecked hA hB right) ignored equality
  have applied := Intrinsic.Proves.appCongr typed (.arr hB .boolTy) .boolTy
    ((inrChurchChecked hA hB left).app ignored)
    ((inrChurchChecked hA hB right).app ignored) test afterIgnored
  have leftReduction := (inrChurch_apply typed hA hB left ignored test).trans
    (equalityPredicate_apply typed hB left left)
  have rightReduction := (inrChurch_apply typed hA hB right ignored test).trans
    (equalityPredicate_apply typed hB left right)
  have leftProof : Intrinsic.Proves Γ H
      (((inrChurchChecked hA hB left).app ignored).app test) :=
    Intrinsic.Proves.convert leftReduction.symm (Intrinsic.Proves.eqRefl hB left)
  have rightProof : Intrinsic.Proves Γ H
      (((inrChurchChecked hA hB right).app ignored).app test) :=
    Intrinsic.Proves.ofEqBool typed _ _ applied leftProof
  have payload : Intrinsic.Proves Γ H (DefEqChecked.eq hB right left) :=
    Intrinsic.Proves.convert rightReduction rightProof
  exact Intrinsic.Proves.eqSymm typed hB right left payload

def repFunctionBody (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig (extendBound (coproductTy hA hB) Γ) (coproductCarrier A B) :=
  repCoproduct hA hB (DefEqChecked.bv (coproductTy_kinded hA hB) 0 rfl)

def repFunctionChecked (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ (.arr (coproductTy hA hB) (coproductCarrier A B)) :=
  DefEqChecked.lam (coproductTy_kinded hA hB) (repFunctionBody hA hB)

theorem repFunctionBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (coproductTy hA hB)) :
    (repFunctionBody hA hB).openBound typed value = repCoproduct hA hB value := by
  apply DefEqChecked.ext
  simp [repFunctionBody, repCoproduct, DefEqChecked.openBound,
    DefEqChecked.rep, DefEqChecked.bv, FamilySub.openBound, instantiate]

def repFunction_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (coproductTy hA hB)) :
    Intrinsic.EqTm ((repFunctionChecked hA hB).app value) (repCoproduct hA hB value) := by
  have reduction := Intrinsic.EqTm.beta typed (coproductTy_kinded hA hB)
    (repFunctionBody hA hB) value
  rw [repFunctionBody_open typed hA hB value] at reduction
  exact reduction

noncomputable def inl_injective (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (left right : DefEqChecked Sig Γ A)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductTy_kinded hA hB)
        (inlChecked hA hB left) (inlChecked hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA left right) := by
  let representation := repFunctionChecked (Γ := Γ) hA hB
  have applied := Intrinsic.Proves.appArgCongr typed (coproductTy_kinded hA hB)
    (coproductCarrier_kinded hA hB) representation
    (inlChecked hA hB left) (inlChecked hA hB right) equality
  have leftReduction := repFunction_apply typed hA hB (inlChecked hA hB left)
  have rightReduction := repFunction_apply typed hA hB (inlChecked hA hB right)
  have reps := Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB)
    (repCoproduct hA hB (inlChecked hA hB left))
    (representation.app (inlChecked hA hB right))
    (repCoproduct hA hB (inlChecked hA hB right))
    (Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB) _
      (representation.app (inlChecked hA hB left)) _
      (Intrinsic.Proves.eqSymm typed (coproductCarrier_kinded hA hB) _ _
        (Intrinsic.Proves.eqOfEqTm (H := H) (coproductCarrier_kinded hA hB)
          leftReduction)) applied)
    (Intrinsic.Proves.eqOfEqTm (H := H) (coproductCarrier_kinded hA hB) rightReduction)
  have churches := Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB)
    (inlChurchChecked hA hB left)
    (repCoproduct hA hB (inlChecked hA hB right))
    (inlChurchChecked hA hB right)
    (Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB) _
      (repCoproduct hA hB (inlChecked hA hB left)) _
      (Intrinsic.Proves.eqSymm typed (coproductCarrier_kinded hA hB) _ _
        (rep_inl typed hA hB left)) reps)
    (rep_inl typed hA hB right)
  exact inlChurch_injective typed hA hB left right churches

noncomputable def inr_injective (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (left right : DefEqChecked Sig Γ B)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (coproductTy_kinded hA hB)
        (inrChecked hA hB left) (inrChecked hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB left right) := by
  let representation := repFunctionChecked (Γ := Γ) hA hB
  have applied := Intrinsic.Proves.appArgCongr typed (coproductTy_kinded hA hB)
    (coproductCarrier_kinded hA hB) representation
    (inrChecked hA hB left) (inrChecked hA hB right) equality
  have leftReduction := repFunction_apply typed hA hB (inrChecked hA hB left)
  have rightReduction := repFunction_apply typed hA hB (inrChecked hA hB right)
  have reps := Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB)
    (repCoproduct hA hB (inrChecked hA hB left))
    (representation.app (inrChecked hA hB right))
    (repCoproduct hA hB (inrChecked hA hB right))
    (Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB) _
      (representation.app (inrChecked hA hB left)) _
      (Intrinsic.Proves.eqSymm typed (coproductCarrier_kinded hA hB) _ _
        (Intrinsic.Proves.eqOfEqTm (H := H) (coproductCarrier_kinded hA hB)
          leftReduction)) applied)
    (Intrinsic.Proves.eqOfEqTm (H := H) (coproductCarrier_kinded hA hB) rightReduction)
  have churches := Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB)
    (inrChurchChecked hA hB left)
    (repCoproduct hA hB (inrChecked hA hB right))
    (inrChurchChecked hA hB right)
    (Intrinsic.Proves.eqTrans typed (coproductCarrier_kinded hA hB) _
      (repCoproduct hA hB (inrChecked hA hB left)) _
      (Intrinsic.Proves.eqSymm typed (coproductCarrier_kinded hA hB) _ _
        (rep_inr typed hA hB left)) reps)
    (rep_inr typed hA hB right)
  exact inrChurch_injective typed hA hB left right churches

end Nucleus.Hol.FamilySub
