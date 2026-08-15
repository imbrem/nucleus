import Nucleus.Hol.FamilySub.Product

/-! # Derived product laws -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

namespace TypedCtx

theorem extend {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
    {Γ : BoundCtx Sig types depth} {A : Ty Sig types}
    (typed : TypedCtx Γ) (hA : Kinded A) : TypedCtx (extendBound A Γ) := by
  intro i
  refine Fin.cases hA (fun j => typed j) i

end TypedCtx

@[simp] theorem finCasesOne {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 1) → α) :
    Fin.cases zero succ 1 = succ 0 := by
  exact Fin.cases_succ 0

@[simp] theorem finCasesTwo {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 2) → α) :
    Fin.cases zero succ 2 = succ 1 := by
  exact Fin.cases_succ 1

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def pairChurchChecked (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (productCarrier A B) :=
  ((DefEqChecked.ofRaw (pairFunction (Γ := Γ) hA hB).tm
    (pairFunction (Γ := Γ) hA hB).typing).app a).app b

def pairBodyC (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    BoolTm (extendBound (.arr A (.arr B .boolTy)) Γ) :=
  let hF : Kinded (.arr A (.arr B .boolTy)) := .arr hA (.arr hB .boolTy)
  let f := DefEqChecked.bv (Γ := extendBound (.arr A (.arr B .boolTy)) Γ) hF 0 rfl
  (f.app a.weaken).app b.weaken

def pairAfterB (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (productCarrier A B) :=
  DefEqChecked.lam (.arr hA (.arr hB .boolTy)) (pairBodyC hA hB a b)

def pairBodyB (hA : Kinded A) (hB : Kinded B) (a : DefEqChecked Sig Γ A) :
    DefEqChecked Sig (extendBound B Γ) (productCarrier A B) :=
  let b := DefEqChecked.bv (Γ := extendBound B Γ) hB 0 rfl
  pairAfterB hA hB a.weaken b

def pairAfterA (hA : Kinded A) (hB : Kinded B) (a : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (.arr B (productCarrier A B)) :=
  DefEqChecked.lam hB (pairBodyB hA hB a)

def pairBodyA (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig (extendBound A Γ) (.arr B (productCarrier A B)) :=
  let a := DefEqChecked.bv (Γ := extendBound A Γ) hA 0 rfl
  pairAfterA hA hB a

theorem pairConstructor_eq_lam (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked.ofRaw (pairFunction (Γ := Γ) hA hB).tm
        (pairFunction (Γ := Γ) hA hB).typing =
      DefEqChecked.lam hA (pairBodyA hA hB) := by
  apply DefEqChecked.ext
  simp [pairFunction, pairBodyA, pairAfterA, pairBodyB, pairAfterB, pairBodyC,
    DefEqChecked.ofRaw, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, Checked.lam, Checked.app, Checked.bv, weaken]

theorem pairBodyA_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) :
    (pairBodyA hA hB).openBound typed a = pairAfterA hA hB a := by
  apply DefEqChecked.ext
  simp only [pairBodyA, pairAfterA, pairBodyB, pairAfterB, pairBodyC,
    DefEqChecked.openBound, DefEqChecked.lam, DefEqChecked.app,
    DefEqChecked.bv, DefEqChecked.weaken, FamilySub.openBound]
  simp [instantiate, liftSub]

theorem pairBodyB_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    (pairBodyB hA hB a).openBound typed b = pairAfterB hA hB a b := by
  apply DefEqChecked.ext
  simp only [pairBodyB, pairAfterB, pairBodyC, DefEqChecked.openBound,
    DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound]
  simp [instantiate, liftSub]

theorem pairBodyC_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (continuation : DefEqChecked Sig Γ (.arr A (.arr B .boolTy))) :
    (pairBodyC hA hB a b).openBound typed continuation =
      (continuation.app a).app b := by
  apply DefEqChecked.ext
  simp only [pairBodyC, DefEqChecked.openBound, DefEqChecked.app,
    DefEqChecked.bv, DefEqChecked.weaken, FamilySub.openBound]
  simp [instantiate]

def pairChurch_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (continuation : DefEqChecked Sig Γ (.arr A (.arr B .boolTy))) :
    Intrinsic.EqTm ((pairChurchChecked hA hB a b).app continuation)
      ((continuation.app a).app b) := by
  have constructorEq := pairConstructor_eq_lam (Γ := Γ) hA hB
  have first := Intrinsic.EqTm.beta typed hA (pairBodyA (Γ := Γ) hA hB) a
  rw [← constructorEq, pairBodyA_open typed hA hB a] at first
  have firstApplied := first.app (Intrinsic.EqTm.refl b)
  have second := Intrinsic.EqTm.beta typed hB (pairBodyB hA hB a) b
  rw [pairBodyB_open typed hA hB a b] at second
  have throughSecond := firstApplied.trans second
  have secondApplied := throughSecond.app (Intrinsic.EqTm.refl continuation)
  have hContinuation : Kinded (.arr A (.arr B .boolTy)) := .arr hA (.arr hB .boolTy)
  have third := Intrinsic.EqTm.beta typed hContinuation (pairBodyC hA hB a b) continuation
  rw [pairBodyC_open typed hA hB a b continuation] at third
  exact secondApplied.trans third

def firstTestBodyB (hA : Kinded A) (_hB : Kinded B)
    (target : DefEqChecked Sig Γ A) :
    BoolTm (extendBound B (extendBound A Γ)) :=
  let candidate := DefEqChecked.bv
    (Γ := extendBound B (extendBound A Γ)) hA 1 rfl
  DefEqChecked.eq hA candidate target.weaken.weaken

def firstTestBodyA (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ A) :
    DefEqChecked Sig (extendBound A Γ) (.arr B .boolTy) :=
  DefEqChecked.lam hB (firstTestBodyB hA hB target)

def firstTest (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (.arr A (.arr B .boolTy)) :=
  DefEqChecked.lam hA (firstTestBodyA hA hB target)

theorem firstTestBodyA_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (target candidate : DefEqChecked Sig Γ A) :
    (firstTestBodyA hA hB target).openBound typed candidate =
      DefEqChecked.lam hB
        (DefEqChecked.eq hA candidate.weaken target.weaken) := by
  apply DefEqChecked.ext
  simp only [firstTestBodyA, firstTestBodyB, DefEqChecked.openBound,
    DefEqChecked.lam, DefEqChecked.eq, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound]
  simp [instantiate, liftSub]

theorem firstTestBodyB_open (typed : TypedCtx Γ) (hA : Kinded A) (_hB : Kinded B)
    (target candidate : DefEqChecked Sig Γ A) (ignored : DefEqChecked Sig Γ B) :
    (DefEqChecked.eq hA candidate.weaken target.weaken).openBound typed ignored =
      DefEqChecked.eq hA candidate target := by
  apply DefEqChecked.ext
  simp [DefEqChecked.openBound, DefEqChecked.eq, DefEqChecked.weaken,
    FamilySub.openBound, instantiate]

def firstTest_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (target candidate : DefEqChecked Sig Γ A) (ignored : DefEqChecked Sig Γ B) :
    Intrinsic.EqTm (((firstTest hA hB target).app candidate).app ignored)
      (DefEqChecked.eq hA candidate target) := by
  have first := Intrinsic.EqTm.beta typed hA (firstTestBodyA hA hB target) candidate
  rw [firstTestBodyA_open typed hA hB target candidate] at first
  have applied := first.app (Intrinsic.EqTm.refl ignored)
  have second := Intrinsic.EqTm.beta typed hB
    (DefEqChecked.eq hA candidate.weaken target.weaken) ignored
  rw [firstTestBodyB_open typed hA hB target candidate ignored] at second
  exact applied.trans second

/-- Equality of Church pairs determines their first components. -/
def pair_first_injective (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a a' : DefEqChecked Sig Γ A) (b b' : DefEqChecked Sig Γ B)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB)
        (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a' b'))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA a a') := by
  let hContinuation : Kinded (.arr A (.arr B .boolTy)) := .arr hA (.arr hB .boolTy)
  let test := firstTest hA hB a
  have applied := Intrinsic.Proves.appCongr typed hContinuation .boolTy
    (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a' b') test equality
  have leftReduction := (pairChurch_apply typed hA hB a b test).trans
    (firstTest_apply typed hA hB a a b)
  have rightReduction := (pairChurch_apply typed hA hB a' b' test).trans
    (firstTest_apply typed hA hB a a' b')
  have leftTrue : Intrinsic.Proves Γ H
      ((pairChurchChecked hA hB a b).app test) :=
    Intrinsic.Proves.convert leftReduction.symm (Intrinsic.Proves.eqRefl hA a)
  have rightTrue := Intrinsic.Proves.ofEqBool typed
    ((pairChurchChecked hA hB a b).app test)
    ((pairChurchChecked hA hB a' b').app test) applied leftTrue
  have reverse : Intrinsic.Proves Γ H (DefEqChecked.eq hA a' a) :=
    Intrinsic.Proves.convert rightReduction rightTrue
  exact Intrinsic.Proves.eqSymm typed hA a' a reverse

@[simp] theorem instantiate_pairFunction {m n : Nat}
    {Γm : BoundCtx Sig types m} {Γn : BoundCtx Sig types n}
    (hA : Kinded A) (hB : Kinded B) (σ : Fin m → Tm Sig types n) :
    instantiate σ (pairFunction (Γ := Γm) hA hB).tm =
      (pairFunction (Γ := Γn) hA hB).tm := by
  simp [pairFunction, Checked.lam, Checked.app, Checked.bv,
    instantiate, liftSub, weaken, Fin.cases_zero]

def productEquationBody (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) :
    DefEqChecked Sig (extendBound B (extendBound A Γ)) .boolTy :=
  let a := DefEqChecked.bv (Γ := extendBound B (extendBound A Γ)) hA 1 rfl
  let b := DefEqChecked.bv (Γ := extendBound B (extendBound A Γ)) hB 0 rfl
  DefEqChecked.eq (productCarrier_kinded hA hB) represented.weaken.weaken
    (pairChurchChecked hA hB a b)

def productMembership (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) : BoolTm Γ :=
  let inner := DefEqChecked.existsTm hB (productEquationBody hA hB represented)
  DefEqChecked.existsTm hA inner

def productPredicateAt (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) : BoolTm Γ :=
  ⟨instantiateOne (productPredicate hA hB).tm represented.tm,
    Checks.instantiateDefEq (productPredicate hA hB).typing
      (fun _ => represented.tm)
      (fun i => Fin.cases represented.typing (fun j => Fin.elim0 j) i)⟩

def productEquationAfterFirst (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (a : DefEqChecked Sig Γ A) :
    DefEqChecked Sig (extendBound B Γ) .boolTy :=
  let b := DefEqChecked.bv (Γ := extendBound B Γ) hB 0 rfl
  DefEqChecked.eq (productCarrier_kinded hA hB) represented.weaken
    (pairChurchChecked hA hB a.weaken b)

theorem productPredicateAt_eq_membership (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) :
    productPredicateAt hA hB represented = productMembership hA hB represented := by
  apply DefEqChecked.ext
  simp [productPredicateAt, productMembership, productPredicate,
    productEquationBody, pairChurchChecked, DefEqChecked.existsTm,
    DefEqChecked.lam, DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq,
    DefEqChecked.weaken, DefEqChecked.bv, DefEqChecked.ofRaw, Checked.existsTm,
    Checked.lam, Checked.app, Checked.eps, Checked.eq, Checked.bv,
    instantiateOne, instantiate, liftSub, weaken,
    pairChurch, pairFunction]

/-- Every constructed Church pair satisfies the image predicate used by the
guarded subtype definition. -/
def productMembership_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (productMembership hA hB (pairChurchChecked hA hB a b)) := by
  apply Intrinsic.Proves.existsIntroBody typed hA _ a
  have openedFirst :
      (DefEqChecked.existsTm hB
        (productEquationBody hA hB (pairChurchChecked hA hB a b))).openBound typed a =
        DefEqChecked.existsTm hB (productEquationAfterFirst hA hB
          (pairChurchChecked hA hB a b) a) := by
    apply DefEqChecked.ext
    simp only [DefEqChecked.existsTm, productEquationBody, productEquationAfterFirst,
      pairChurchChecked, DefEqChecked.openBound, DefEqChecked.lam,
      DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.weaken,
      DefEqChecked.bv, DefEqChecked.ofRaw, FamilySub.openBound]
    simp [instantiate, liftSub]
    exact instantiate_pairFunction
      (Γm := extendBound B (extendBound A Γ)) (Γn := extendBound B Γ)
      hA hB (liftSub (Fin.cases a.tm .bv))
  rw [openedFirst]
  apply Intrinsic.Proves.existsIntroBody typed hB _ b
  have openedSecond :
      (productEquationAfterFirst hA hB (pairChurchChecked hA hB a b) a).openBound
          typed b =
        DefEqChecked.eq (productCarrier_kinded hA hB)
          (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a b) := by
    apply DefEqChecked.ext
    simp only [productEquationAfterFirst, pairChurchChecked, DefEqChecked.openBound,
      DefEqChecked.app, DefEqChecked.eq, DefEqChecked.weaken, DefEqChecked.bv,
      DefEqChecked.ofRaw, FamilySub.openBound]
    simp [instantiate]
    exact instantiate_pairFunction (Γm := extendBound B Γ) (Γn := Γ)
      hA hB (Fin.cases b.tm .bv)
  rw [openedSecond]
  exact Intrinsic.Proves.eqRefl (H := H) (productCarrier_kinded hA hB)
    (pairChurchChecked hA hB a b)

def productPredicate_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (productPredicateAt hA hB (pairChurchChecked hA hB a b)) := by
  rw [productPredicateAt_eq_membership]
  exact productMembership_pair typed hA hB a b

def pairChecked (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (productTy hA hB) :=
  DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
    (productPredicate hA hB).typing (pairChurchChecked hA hB a b)

def repPair (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    DefEqChecked Sig Γ (productCarrier A B) :=
  DefEqChecked.rep (productCarrier_kinded hA hB) (productPredicate hA hB).tm
    (productPredicate hA hB).typing value

/-- The guarded subtype representation of a constructed pair computes to its
Church representation. -/
def rep_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB)
        (repPair hA hB (pairChecked hA hB a b))
        (pairChurchChecked hA hB a b)) :=
  Intrinsic.Proves.repAbs (productCarrier_kinded hA hB)
    (productPredicate hA hB).tm (productPredicate hA hB).typing
    (pairChurchChecked hA hB a b)
    (productPredicateAt hA hB (pairChurchChecked hA hB a b)) rfl
    (productPredicate_pair typed hA hB a b)

end Nucleus.Hol.FamilySub
