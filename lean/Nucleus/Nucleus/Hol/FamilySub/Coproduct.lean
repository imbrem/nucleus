import Nucleus.Hol.FamilySub.Product

/-! # Coproducts from type-family lambda and ordinary subtypes -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def coproductCarrier (A B : Ty Sig types) : Ty Sig types :=
  .arr (.arr A .boolTy) (.arr (.arr B .boolTy) .boolTy)

theorem coproductCarrier_kinded (hA : Kinded A) (hB : Kinded B) :
    Kinded (coproductCarrier A B) :=
  .arr (.arr hA .boolTy) (.arr (.arr hB .boolTy) .boolTy)

def inlChurch (hA : Kinded A) (hB : Kinded B) (a : Checked Sig Γ A) :
    Checked Sig Γ (coproductCarrier A B) := by
  let leftTy : Ty Sig types := .arr A .boolTy
  let rightTy : Ty Sig types := .arr B .boolTy
  let hLeft : Kinded leftTy := .arr hA .boolTy
  let hRight : Kinded rightTy := .arr hB .boolTy
  let Γl := extendBound leftTy Γ
  let Γr := extendBound rightTy Γl
  let l : Checked Sig Γr leftTy := Checked.bv hLeft 1 rfl
  exact Checked.lam hLeft (Checked.lam hRight (l.app a.weaken.weaken))

def inrChurch (hA : Kinded A) (hB : Kinded B) (b : Checked Sig Γ B) :
    Checked Sig Γ (coproductCarrier A B) := by
  let leftTy : Ty Sig types := .arr A .boolTy
  let rightTy : Ty Sig types := .arr B .boolTy
  let hLeft : Kinded leftTy := .arr hA .boolTy
  let hRight : Kinded rightTy := .arr hB .boolTy
  let Γl := extendBound leftTy Γ
  let Γr := extendBound rightTy Γl
  let r : Checked Sig Γr rightTy := Checked.bv hRight 0 rfl
  exact Checked.lam hLeft (Checked.lam hRight (r.app b.weaken.weaken))

def coproductPredicate (hA : Kinded A) (hB : Kinded B) :
    Checked Sig (extendBound (coproductCarrier A B) emptyBound) .boolTy := by
  let carrier := coproductCarrier A B
  let hCarrier := coproductCarrier_kinded hA hB
  let Γs : BoundCtx Sig types 1 := extendBound carrier emptyBound
  let Γa := extendBound A Γs
  let a : Checked Sig Γa A := Checked.bv hA 0 rfl
  let sA : Checked Sig Γa carrier := Checked.bv hCarrier 1 rfl
  let leftEq := Checked.eq hCarrier sA (inlChurch hA hB a)
  let leftImage : Checked Sig Γs .boolTy := Checked.existsTm hA (Checked.lam hA leftEq)
  let Γb := extendBound B Γs
  let b : Checked Sig Γb B := Checked.bv hB 0 rfl
  let sB : Checked Sig Γb carrier := Checked.bv hCarrier 1 rfl
  let rightEq := Checked.eq hCarrier sB (inrChurch hA hB b)
  let rightImage : Checked Sig Γs .boolTy := Checked.existsTm hB (Checked.lam hB rightEq)
  exact Checked.or leftImage rightImage

def coproductTy (hA : Kinded A) (hB : Kinded B) : Ty Sig types :=
  .sub (coproductCarrier A B) (coproductPredicate hA hB).tm

theorem coproductTy_kinded (hA : Kinded A) (hB : Kinded B) :
    Kinded (coproductTy hA hB) :=
  .sub (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).typing

def inl (hA : Kinded A) (hB : Kinded B) (a : Checked Sig Γ A) :
    Checked Sig Γ (coproductTy hA hB) :=
  Checked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB)
    (inlChurch hA hB a)

def inr (hA : Kinded A) (hB : Kinded B) (b : Checked Sig Γ B) :
    Checked Sig Γ (coproductTy hA hB) :=
  Checked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB)
    (inrChurch hA hB b)

/-- Coproduct elimination.  The Church carrier only needs Boolean results:
choice selects a candidate result whose equality predicate is accepted by the
represented injection. -/
def coproductCaseFunction (hA : Kinded A) (hB : Kinded B) (hC : Kinded C) :
    Checked Sig Γ (.arr (.arr A C) (.arr (.arr B C) (.arr (coproductTy hA hB) C))) := by
  let hAC : Kinded (.arr A C) := .arr hA hC
  let hBC : Kinded (.arr B C) := .arr hB hC
  let hSum := coproductTy_kinded hA hB
  let hCarrier := coproductCarrier_kinded hA hB
  let Γf := extendBound (.arr A C) Γ
  let Γg := extendBound (.arr B C) Γf
  let Γs := extendBound (coproductTy hA hB) Γg
  let Γc := extendBound C Γs
  let Γa := extendBound A Γc
  let a : Checked Sig Γa A := Checked.bv hA 0 rfl
  let cA : Checked Sig Γa C := Checked.bv hC 1 rfl
  let f : Checked Sig Γa (.arr A C) := Checked.bv hAC 4 rfl
  let leftPredicate : Checked Sig Γc (.arr A .boolTy) :=
    Checked.lam hA (Checked.eq hC cA (f.app a))
  let Γb := extendBound B Γc
  let b : Checked Sig Γb B := Checked.bv hB 0 rfl
  let cB : Checked Sig Γb C := Checked.bv hC 1 rfl
  let g : Checked Sig Γb (.arr B C) := Checked.bv hBC 3 rfl
  let rightPredicate : Checked Sig Γc (.arr B .boolTy) :=
    Checked.lam hB (Checked.eq hC cB (g.app b))
  let s : Checked Sig Γc (coproductTy hA hB) := Checked.bv hSum 1 rfl
  let represented := Checked.rep hCarrier (coproductPredicate hA hB) s
  let resultPredicate : Checked Sig Γc .boolTy :=
    (represented.app leftPredicate).app rightPredicate
  let chosen : Checked Sig Γs C := Checked.eps hC (Checked.lam hC resultPredicate)
  exact Checked.lam hAC (Checked.lam hBC (Checked.lam hSum chosen))

def coproductCase (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : Checked Sig Γ (.arr A C)) (right : Checked Sig Γ (.arr B C))
    (value : Checked Sig Γ (coproductTy hA hB)) : Checked Sig Γ C :=
  (((coproductCaseFunction hA hB hC).app left).app right).app value

def coproductFam (Sig : Signature) [SigTyping Sig] :
    Fam Sig [] (.arr .star (.arr .star .star)) :=
  .tyLam (.tyLam (coproductTy (.tyBv (.succ .zero)) (.tyBv .zero)))

theorem coproductFam_kinded (Sig : Signature) [SigTyping Sig] :
    Kinded (coproductFam Sig) :=
  .tyLam (.tyLam (coproductTy_kinded (.tyBv (.succ .zero)) (.tyBv .zero)))

def appliedCoproductFam (Sig : Signature) [SigTyping Sig]
    (A B : Ty Sig []) : Ty Sig [] :=
  .tyApp (.tyApp (coproductFam Sig) A) B

def appliedCoproductFam_defeq {A B : Ty Sig []} (hA : Kinded A) (hB : Kinded B) :
    FamEq Sig (appliedCoproductFam Sig A B) (coproductTy hA hB) := by
  let body : Fam Sig [.star] (.arr .star .star) :=
    .tyLam (coproductTy (.tyBv (.succ .zero)) (.tyBv .zero))
  let bodyAfterA : Fam Sig [.star] .star :=
    instantiateTypes (liftTySub (headTySub A))
      (coproductTy (.tyBv (.succ .zero)) (.tyBv .zero))
  have outer : FamEq Sig (.tyApp (.tyLam body) A) (openType body A) :=
    .beta body A
  have lifted : FamEq Sig (.tyApp (.tyApp (.tyLam body) A) B)
      (.tyApp (openType body A) B) := .app outer .refl
  refine .trans (B := .tyApp (openType body A) B) ?_ ?_
  · simpa [appliedCoproductFam, coproductFam, body] using lifted
  · simpa [body, bodyAfterA, openType, headTySub, liftTySub,
      coproductTy, coproductPredicate, coproductCarrier,
      inlChurch, inrChurch, Checked.existsTm, Checked.or, Checked.and,
      Checked.not, Checked.truth, Checked.falsehood, Checked.lam, Checked.app,
      Checked.eps, Checked.eq, Checked.bv, Checked.weaken,
      FamilySub.weaken, rename, liftRen] using
      (FamEq.beta (Sig := Sig) bodyAfterA B)

theorem appliedCoproductFam_kinded {A B : Ty Sig []} (hA : Kinded A) (hB : Kinded B) :
    Kinded (appliedCoproductFam Sig A B) :=
  .tyApp (.tyApp (coproductFam_kinded Sig) hA) hB

def inlAtFamily {A B : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B) (a : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (appliedCoproductFam Sig A B) := by
  let leftTy : Ty Sig [] := .arr A .boolTy
  let rightTy : Ty Sig [] := .arr B .boolTy
  let hLeft : Kinded leftTy := .arr hA .boolTy
  let hRight : Kinded rightTy := .arr hB .boolTy
  let Γl := extendBound leftTy Γ
  let Γr := extendBound rightTy Γl
  let left : DefEqChecked Sig Γr leftTy :=
    .ofRaw (.bv 1) (.bv (i := 1) hLeft rfl)
  let represented : DefEqChecked Sig Γ (coproductCarrier A B) :=
    DefEqChecked.lam hLeft (DefEqChecked.lam hRight (left.app a.weaken.weaken))
  let value : DefEqChecked Sig Γ (coproductTy hA hB) :=
    DefEqChecked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).tm
      (coproductPredicate hA hB).typing represented
  exact value.conv (appliedCoproductFam_kinded hA hB)
    (.symm (appliedCoproductFam_defeq hA hB))

def inrAtFamily {A B : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B) (b : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (appliedCoproductFam Sig A B) := by
  let leftTy : Ty Sig [] := .arr A .boolTy
  let rightTy : Ty Sig [] := .arr B .boolTy
  let hLeft : Kinded leftTy := .arr hA .boolTy
  let hRight : Kinded rightTy := .arr hB .boolTy
  let Γl := extendBound leftTy Γ
  let Γr := extendBound rightTy Γl
  let right : DefEqChecked Sig Γr rightTy :=
    .ofRaw (.bv 0) (.bv (i := 0) hRight rfl)
  let represented : DefEqChecked Sig Γ (coproductCarrier A B) :=
    DefEqChecked.lam hLeft (DefEqChecked.lam hRight (right.app b.weaken.weaken))
  let value : DefEqChecked Sig Γ (coproductTy hA hB) :=
    DefEqChecked.abs (coproductCarrier_kinded hA hB) (coproductPredicate hA hB).tm
      (coproductPredicate hA hB).typing represented
  exact value.conv (appliedCoproductFam_kinded hA hB)
    (.symm (appliedCoproductFam_defeq hA hB))

def caseAtFamily {A B C : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C))
    (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ (appliedCoproductFam Sig A B)) :
    DefEqChecked Sig Γ C := by
  let represented := value.conv (coproductTy_kinded hA hB)
    (appliedCoproductFam_defeq hA hB)
  let eliminator := DefEqChecked.ofRaw (coproductCaseFunction (Γ := Γ) hA hB hC).tm
    (coproductCaseFunction (Γ := Γ) hA hB hC).typing
  exact ((eliminator.app left).app right).app represented

end Nucleus.Hol.FamilySub
