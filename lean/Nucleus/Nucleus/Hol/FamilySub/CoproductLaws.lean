import Nucleus.Hol.FamilySub.Coproduct
import Nucleus.Hol.FamilySub.ProductLaws

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

end Nucleus.Hol.FamilySub
