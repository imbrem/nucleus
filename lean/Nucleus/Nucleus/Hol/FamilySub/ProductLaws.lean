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

def secondTestBodyB (_hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ B) :
    BoolTm (extendBound B (extendBound A Γ)) :=
  let candidate := DefEqChecked.bv
    (Γ := extendBound B (extendBound A Γ)) hB 0 rfl
  DefEqChecked.eq hB candidate target.weaken.weaken

def secondTestBodyA (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ B) :
    DefEqChecked Sig (extendBound A Γ) (.arr B .boolTy) :=
  DefEqChecked.lam hB (secondTestBodyB hA hB target)

def secondTest (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (.arr A (.arr B .boolTy)) :=
  DefEqChecked.lam hA (secondTestBodyA hA hB target)

theorem secondTestBodyA_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ B) (ignored : DefEqChecked Sig Γ A) :
    (secondTestBodyA hA hB target).openBound typed ignored =
      DefEqChecked.lam hB (DefEqChecked.eq hB
        (DefEqChecked.bv hB 0 rfl) target.weaken) := by
  apply DefEqChecked.ext
  simp only [secondTestBodyA, secondTestBodyB, DefEqChecked.openBound,
    DefEqChecked.lam, DefEqChecked.eq, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound]
  simp [instantiate, liftSub]

theorem secondTestBodyB_open (typed : TypedCtx Γ) (hB : Kinded B)
    (target candidate : DefEqChecked Sig Γ B) :
    (DefEqChecked.eq hB (DefEqChecked.bv hB 0 rfl) target.weaken).openBound
        typed candidate = DefEqChecked.eq hB candidate target := by
  apply DefEqChecked.ext
  simp [DefEqChecked.openBound, DefEqChecked.eq, DefEqChecked.weaken,
    DefEqChecked.bv, FamilySub.openBound, instantiate]

def secondTest_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (target : DefEqChecked Sig Γ B) (ignored : DefEqChecked Sig Γ A)
    (candidate : DefEqChecked Sig Γ B) :
    Intrinsic.EqTm (((secondTest hA hB target).app ignored).app candidate)
      (DefEqChecked.eq hB candidate target) := by
  have first := Intrinsic.EqTm.beta typed hA (secondTestBodyA hA hB target) ignored
  rw [secondTestBodyA_open typed hA hB target ignored] at first
  have applied := first.app (Intrinsic.EqTm.refl candidate)
  have second := Intrinsic.EqTm.beta typed hB
    (DefEqChecked.eq hB (DefEqChecked.bv hB 0 rfl) target.weaken) candidate
  rw [secondTestBodyB_open typed hB target candidate] at second
  exact applied.trans second

/-- Equality of Church pairs determines their second components. -/
def pair_second_injective (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a a' : DefEqChecked Sig Γ A) (b b' : DefEqChecked Sig Γ B)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB)
        (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a' b'))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB b b') := by
  let hContinuation : Kinded (.arr A (.arr B .boolTy)) := .arr hA (.arr hB .boolTy)
  let test := secondTest hA hB b
  have applied := Intrinsic.Proves.appCongr typed hContinuation .boolTy
    (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a' b') test equality
  have leftReduction := (pairChurch_apply typed hA hB a b test).trans
    (secondTest_apply typed hA hB b a b)
  have rightReduction := (pairChurch_apply typed hA hB a' b' test).trans
    (secondTest_apply typed hA hB b a' b')
  have leftTrue : Intrinsic.Proves Γ H
      ((pairChurchChecked hA hB a b).app test) :=
    Intrinsic.Proves.convert leftReduction.symm (Intrinsic.Proves.eqRefl hB b)
  have rightTrue := Intrinsic.Proves.ofEqBool typed
    ((pairChurchChecked hA hB a b).app test)
    ((pairChurchChecked hA hB a' b').app test) applied leftTrue
  have reverse : Intrinsic.Proves Γ H (DefEqChecked.eq hB b' b) :=
    Intrinsic.Proves.convert rightReduction rightTrue
  exact Intrinsic.Proves.eqSymm typed hB b' b reverse

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

theorem productExistsBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (a : DefEqChecked Sig Γ A) :
    (DefEqChecked.existsTm hB (productEquationBody hA hB represented)).openBound typed a =
      DefEqChecked.existsTm hB (productEquationAfterFirst hA hB represented a) := by
  apply DefEqChecked.ext
  simp only [DefEqChecked.existsTm, productEquationBody, productEquationAfterFirst,
    pairChurchChecked, DefEqChecked.openBound, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.weaken,
    DefEqChecked.bv, DefEqChecked.ofRaw, FamilySub.openBound]
  simp [instantiate, liftSub]
  exact instantiate_pairFunction
    (Γm := extendBound B (extendBound A Γ)) (Γn := extendBound B Γ)
    hA hB (liftSub (Fin.cases a.tm .bv))

theorem productEquationAfterFirst_open (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    (productEquationAfterFirst hA hB represented a).openBound typed b =
      DefEqChecked.eq (productCarrier_kinded hA hB) represented
        (pairChurchChecked hA hB a b) := by
  apply DefEqChecked.ext
  simp only [productEquationAfterFirst, pairChurchChecked, DefEqChecked.openBound,
    DefEqChecked.app, DefEqChecked.eq, DefEqChecked.weaken, DefEqChecked.bv,
    DefEqChecked.ofRaw, FamilySub.openBound]
  simp [instantiate]
  exact instantiate_pairFunction (Γm := extendBound B Γ) (Γn := Γ)
    hA hB (Fin.cases b.tm .bv)

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
  rw [productExistsBody_open typed hA hB]
  apply Intrinsic.Proves.existsIntroBody typed hB _ b
  rw [productEquationAfterFirst_open typed hA hB]
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

def productPredicate_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H (productPredicateAt hA hB (repPair hA hB value)) := by
  let a : DefEqChecked Sig Γ A := DefEqChecked.arbitrary hA
  let b : DefEqChecked Sig Γ B := DefEqChecked.arbitrary hB
  let witness := pairChurchChecked hA hB a b
  exact Intrinsic.Proves.repPredOfWitness (productCarrier_kinded hA hB)
    (productPredicate hA hB).tm (productPredicate hA hB).typing witness
    (productPredicateAt hA hB witness) rfl value
    (productPredicateAt hA hB (repPair hA hB value)) rfl
    (productPredicate_pair typed hA hB a b)

def productMembership_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H (productMembership hA hB (repPair hA hB value)) := by
  rw [← productPredicateAt_eq_membership]
  exact productPredicate_rep typed hA hB value

def decompositionFirst (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) : DefEqChecked Sig Γ A :=
  let body := DefEqChecked.existsTm hB (productEquationBody hA hB represented)
  DefEqChecked.eps hA (DefEqChecked.lam hA body)

def decompositionSecond (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) : DefEqChecked Sig Γ B :=
  let first := decompositionFirst hA hB represented
  let body := productEquationAfterFirst hA hB represented first
  DefEqChecked.eps hB (DefEqChecked.lam hB body)

/-- Every product representation is provably a Church pair.  Nonemptiness is
derived from total choice, not required by subtype formation. -/
def rep_decompose (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB
          (decompositionFirst hA hB (repPair hA hB value))
          (decompositionSecond hA hB (repPair hA hB value)))) := by
  let represented := repPair hA hB value
  let first := decompositionFirst hA hB represented
  let second := decompositionSecond hA hB represented
  have membership := productMembership_rep (H := H) typed hA hB value
  have afterFirst : Intrinsic.Proves Γ H
      ((DefEqChecked.existsTm hB (productEquationBody hA hB represented)).openBound
        typed first) :=
    Intrinsic.Proves.betaReduce typed hA
      (DefEqChecked.existsTm hB (productEquationBody hA hB represented)) first membership
  rw [productExistsBody_open typed hA hB represented first] at afterFirst
  have equation : Intrinsic.Proves Γ H
      ((productEquationAfterFirst hA hB represented first).openBound typed second) :=
    Intrinsic.Proves.betaReduce typed hB
      (productEquationAfterFirst hA hB represented first) second afterFirst
  rw [productEquationAfterFirst_open typed hA hB represented first second] at equation
  exact equation

def firstSelectorBody (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
  BoolTm (extendBound A Γ) :=
  DefEqChecked.existsTm hB
    (productEquationBody hA hB (repPair hA hB value))

def firstSelector (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    DefEqChecked Sig Γ (.arr A .boolTy) :=
  DefEqChecked.lam hA (firstSelectorBody hA hB value)

def fstChoice (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) : DefEqChecked Sig Γ A :=
  DefEqChecked.eps hA (firstSelector hA hB value)

def firstSelector_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      ((firstSelector hA hB (pairChecked hA hB a b)).app a) := by
  apply Intrinsic.Proves.betaExpand typed hA _ a
  rw [show (firstSelectorBody hA hB (pairChecked hA hB a b)).openBound typed a =
      DefEqChecked.existsTm hB
        (productEquationAfterFirst hA hB
          (repPair hA hB (pairChecked hA hB a b)) a) by
    simpa [firstSelectorBody] using
      productExistsBody_open typed hA hB
        (repPair hA hB (pairChecked hA hB a b)) a]
  apply Intrinsic.Proves.existsIntroBody typed hB _ b
  rw [productEquationAfterFirst_open typed hA hB]
  exact rep_pair typed hA hB a b

def firstSelector_of_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB))
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (representation : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB a b))) :
    Intrinsic.Proves Γ H ((firstSelector hA hB value).app a) := by
  apply Intrinsic.Proves.betaExpand typed hA _ a
  rw [show (firstSelectorBody hA hB value).openBound typed a =
      DefEqChecked.existsTm hB
        (productEquationAfterFirst hA hB (repPair hA hB value) a) by
    simpa [firstSelectorBody] using
      productExistsBody_open typed hA hB (repPair hA hB value) a]
  apply Intrinsic.Proves.existsIntroBody typed hB _ b
  rw [productEquationAfterFirst_open typed hA hB]
  exact representation

def fstChoice_of_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB))
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (representation : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB a b))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA (fstChoice hA hB value) a) := by
  let selector := firstSelector hA hB value
  let chosen := fstChoice hA hB value
  have atA : Intrinsic.Proves Γ H (selector.app a) :=
    firstSelector_of_rep typed hA hB value a b representation
  have atChosen : Intrinsic.Proves Γ H (selector.app chosen) :=
    Intrinsic.Proves.choice hA selector a atA
  have openedChosen : Intrinsic.Proves Γ H
      ((firstSelectorBody hA hB value).openBound typed chosen) :=
    Intrinsic.Proves.betaReduce typed hA (firstSelectorBody hA hB value) chosen atChosen
  rw [show (firstSelectorBody hA hB value).openBound typed chosen =
      DefEqChecked.existsTm hB
        (productEquationAfterFirst hA hB (repPair hA hB value) chosen) by
    simpa [firstSelectorBody] using
      productExistsBody_open typed hA hB (repPair hA hB value) chosen] at openedChosen
  let equation := productEquationAfterFirst hA hB (repPair hA hB value) chosen
  let companion := DefEqChecked.eps hB (DefEqChecked.lam hB equation)
  have selectedEquation : Intrinsic.Proves Γ H (equation.openBound typed companion) :=
    Intrinsic.Proves.betaReduce typed hB equation companion openedChosen
  rw [productEquationAfterFirst_open typed hA hB] at selectedEquation
  have pairEquality := Intrinsic.Proves.eqTrans typed (productCarrier_kinded hA hB)
    (pairChurchChecked hA hB a b) (repPair hA hB value)
    (pairChurchChecked hA hB chosen companion)
    (Intrinsic.Proves.eqSymm typed (productCarrier_kinded hA hB)
      (repPair hA hB value) (pairChurchChecked hA hB a b) representation)
    selectedEquation
  have components := pair_first_injective typed hA hB a chosen b companion pairEquality
  exact Intrinsic.Proves.eqSymm typed hA a chosen components

/-- The choice-based first projection computes on constructed products. -/
def fstChoice_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hA (fstChoice hA hB (pairChecked hA hB a b)) a) :=
  fstChoice_of_rep typed hA hB (pairChecked hA hB a b) a b
    (rep_pair typed hA hB a b)

def fstBody (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig (extendBound (productTy hA hB) Γ) A :=
  let value := DefEqChecked.bv (productTy_kinded hA hB) 0 rfl
  fstChoice hA hB value

def fstChecked (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) : DefEqChecked Sig Γ A :=
  (DefEqChecked.ofRaw (fstFunction (Γ := Γ) hA hB).tm
    (fstFunction (Γ := Γ) hA hB).typing).app value

theorem fstFunction_eq_lam (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked.ofRaw (fstFunction (Γ := Γ) hA hB).tm
        (fstFunction (Γ := Γ) hA hB).typing =
      DefEqChecked.lam (productTy_kinded hA hB) (fstBody hA hB) := by
  apply DefEqChecked.ext
  simp [fstFunction, fstBody, fstChoice, firstSelector, firstSelectorBody,
    productEquationBody, repPair, pairChurchChecked, pairChurch, pairFunction,
    DefEqChecked.ofRaw, DefEqChecked.existsTm, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.eps,
    DefEqChecked.eq, DefEqChecked.rep, DefEqChecked.bv, DefEqChecked.weaken,
    Checked.existsTm, Checked.lam, Checked.app, Checked.eps, Checked.eq, Checked.rep,
    Checked.bv, weaken, rename]

theorem fstBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    (fstBody hA hB).openBound typed value = fstChoice hA hB value := by
  apply DefEqChecked.ext
  simp [fstBody, fstChoice, firstSelector, firstSelectorBody,
    productEquationBody, repPair,
    pairChurchChecked, DefEqChecked.openBound, DefEqChecked.existsTm,
    DefEqChecked.lam, DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq,
    DefEqChecked.rep, DefEqChecked.bv, DefEqChecked.weaken,
    DefEqChecked.ofRaw, FamilySub.openBound, instantiate, liftSub]
  constructor
  · simp [weaken, rename, instantiate, liftSub]
  · exact instantiate_pairFunction
      (Γm := extendBound B (extendBound A (extendBound (productTy hA hB) Γ)))
      (Γn := extendBound B (extendBound A Γ)) hA hB
      (liftSub (liftSub (Fin.cases value.tm .bv)))

def fstChecked_eq_choice (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.EqTm (fstChecked hA hB value) (fstChoice hA hB value) := by
  have functionEq := fstFunction_eq_lam (Γ := Γ) hA hB
  have reduction := Intrinsic.EqTm.beta typed (productTy_kinded hA hB)
    (fstBody (Γ := Γ) hA hB) value
  rw [← functionEq, fstBody_open typed hA hB value] at reduction
  exact reduction

/-- The public first projection satisfies its product β-law. -/
def fst_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hA (fstChecked hA hB (pairChecked hA hB a b)) a) :=
  Intrinsic.Proves.eqTrans typed hA
    (fstChecked hA hB (pairChecked hA hB a b))
    (fstChoice hA hB (pairChecked hA hB a b)) a
    (Intrinsic.Proves.eqOfEqTm hA
      (fstChecked_eq_choice typed hA hB (pairChecked hA hB a b)))
    (fstChoice_pair typed hA hB a b)

def secondEquationBody (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) :
    BoolTm (extendBound A (extendBound B Γ)) :=
  let a := DefEqChecked.bv (Γ := extendBound A (extendBound B Γ)) hA 0 rfl
  let b := DefEqChecked.bv (Γ := extendBound A (extendBound B Γ)) hB 1 rfl
  DefEqChecked.eq (productCarrier_kinded hA hB) represented.weaken.weaken
    (pairChurchChecked hA hB a b)

def secondEquationAfterSecond (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (b : DefEqChecked Sig Γ B) : BoolTm (extendBound A Γ) :=
  let a := DefEqChecked.bv (Γ := extendBound A Γ) hA 0 rfl
  DefEqChecked.eq (productCarrier_kinded hA hB) represented.weaken
    (pairChurchChecked hA hB a b.weaken)

theorem secondExistsBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (b : DefEqChecked Sig Γ B) :
    (DefEqChecked.existsTm hA (secondEquationBody hA hB represented)).openBound typed b =
      DefEqChecked.existsTm hA (secondEquationAfterSecond hA hB represented b) := by
  apply DefEqChecked.ext
  simp only [DefEqChecked.existsTm, secondEquationBody, secondEquationAfterSecond,
    pairChurchChecked, DefEqChecked.openBound, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.weaken,
    DefEqChecked.bv, DefEqChecked.ofRaw, FamilySub.openBound]
  simp [instantiate, liftSub]
  exact instantiate_pairFunction
    (Γm := extendBound A (extendBound B Γ)) (Γn := extendBound A Γ)
    hA hB (liftSub (Fin.cases b.tm .bv))

theorem secondEquationAfterSecond_open (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B))
    (b : DefEqChecked Sig Γ B) (a : DefEqChecked Sig Γ A) :
    (secondEquationAfterSecond hA hB represented b).openBound typed a =
      DefEqChecked.eq (productCarrier_kinded hA hB) represented
        (pairChurchChecked hA hB a b) := by
  apply DefEqChecked.ext
  simp only [secondEquationAfterSecond, pairChurchChecked, DefEqChecked.openBound,
    DefEqChecked.app, DefEqChecked.eq, DefEqChecked.weaken, DefEqChecked.bv,
    DefEqChecked.ofRaw, FamilySub.openBound]
  simp [instantiate]
  exact instantiate_pairFunction (Γm := extendBound A Γ) (Γn := Γ)
    hA hB (Fin.cases a.tm .bv)

def secondSelectorBody (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) : BoolTm (extendBound B Γ) :=
  DefEqChecked.existsTm hA (secondEquationBody hA hB (repPair hA hB value))

def secondSelector (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    DefEqChecked Sig Γ (.arr B .boolTy) :=
  DefEqChecked.lam hB (secondSelectorBody hA hB value)

def sndChoice (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) : DefEqChecked Sig Γ B :=
  DefEqChecked.eps hB (secondSelector hA hB value)

def secondSelector_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      ((secondSelector hA hB (pairChecked hA hB a b)).app b) := by
  apply Intrinsic.Proves.betaExpand typed hB _ b
  rw [show (secondSelectorBody hA hB (pairChecked hA hB a b)).openBound typed b =
      DefEqChecked.existsTm hA
        (secondEquationAfterSecond hA hB
          (repPair hA hB (pairChecked hA hB a b)) b) by
    simpa [secondSelectorBody] using
      secondExistsBody_open typed hA hB
        (repPair hA hB (pairChecked hA hB a b)) b]
  apply Intrinsic.Proves.existsIntroBody typed hA _ a
  rw [secondEquationAfterSecond_open typed hA hB]
  exact rep_pair typed hA hB a b

def secondSelector_of_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB))
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (representation : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB a b))) :
    Intrinsic.Proves Γ H ((secondSelector hA hB value).app b) := by
  apply Intrinsic.Proves.betaExpand typed hB _ b
  rw [show (secondSelectorBody hA hB value).openBound typed b =
      DefEqChecked.existsTm hA
        (secondEquationAfterSecond hA hB (repPair hA hB value) b) by
    simpa [secondSelectorBody] using
      secondExistsBody_open typed hA hB (repPair hA hB value) b]
  apply Intrinsic.Proves.existsIntroBody typed hA _ a
  rw [secondEquationAfterSecond_open typed hA hB]
  exact representation

def sndChoice_of_rep (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB))
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B)
    (representation : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB a b))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB (sndChoice hA hB value) b) := by
  let selector := secondSelector hA hB value
  let chosen := sndChoice hA hB value
  have atB : Intrinsic.Proves Γ H (selector.app b) :=
    secondSelector_of_rep typed hA hB value a b representation
  have atChosen : Intrinsic.Proves Γ H (selector.app chosen) :=
    Intrinsic.Proves.choice hB selector b atB
  have openedChosen : Intrinsic.Proves Γ H
      ((secondSelectorBody hA hB value).openBound typed chosen) :=
    Intrinsic.Proves.betaReduce typed hB (secondSelectorBody hA hB value) chosen atChosen
  rw [show (secondSelectorBody hA hB value).openBound typed chosen =
      DefEqChecked.existsTm hA
        (secondEquationAfterSecond hA hB (repPair hA hB value) chosen) by
    simpa [secondSelectorBody] using
      secondExistsBody_open typed hA hB (repPair hA hB value) chosen] at openedChosen
  let equation := secondEquationAfterSecond hA hB (repPair hA hB value) chosen
  let companion := DefEqChecked.eps hA (DefEqChecked.lam hA equation)
  have selectedEquation : Intrinsic.Proves Γ H (equation.openBound typed companion) :=
    Intrinsic.Proves.betaReduce typed hA equation companion openedChosen
  rw [secondEquationAfterSecond_open typed hA hB] at selectedEquation
  have pairEquality := Intrinsic.Proves.eqTrans typed (productCarrier_kinded hA hB)
    (pairChurchChecked hA hB a b) (repPair hA hB value)
    (pairChurchChecked hA hB companion chosen)
    (Intrinsic.Proves.eqSymm typed (productCarrier_kinded hA hB)
      (repPair hA hB value) (pairChurchChecked hA hB a b) representation)
    selectedEquation
  have components := pair_second_injective typed hA hB a companion b chosen pairEquality
  exact Intrinsic.Proves.eqSymm typed hB b chosen components

def sndChoice_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hB (sndChoice hA hB (pairChecked hA hB a b)) b) :=
  sndChoice_of_rep typed hA hB (pairChecked hA hB a b) a b
    (rep_pair typed hA hB a b)

def sndBody (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig (extendBound (productTy hA hB) Γ) B :=
  let value := DefEqChecked.bv (productTy_kinded hA hB) 0 rfl
  sndChoice hA hB value

def sndChecked (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) : DefEqChecked Sig Γ B :=
  (DefEqChecked.ofRaw (sndFunction (Γ := Γ) hA hB).tm
    (sndFunction (Γ := Γ) hA hB).typing).app value

theorem sndFunction_eq_lam (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked.ofRaw (sndFunction (Γ := Γ) hA hB).tm
        (sndFunction (Γ := Γ) hA hB).typing =
      DefEqChecked.lam (productTy_kinded hA hB) (sndBody hA hB) := by
  apply DefEqChecked.ext
  simp [sndFunction, sndBody, sndChoice, secondSelector, secondSelectorBody,
    secondEquationBody, repPair, pairChurchChecked, pairChurch, pairFunction,
    DefEqChecked.ofRaw, DefEqChecked.existsTm, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.rep,
    DefEqChecked.bv, DefEqChecked.weaken, Checked.existsTm, Checked.lam,
    Checked.app, Checked.eps, Checked.eq, Checked.rep, Checked.bv,
    weaken, rename]

theorem sndBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    (sndBody hA hB).openBound typed value = sndChoice hA hB value := by
  apply DefEqChecked.ext
  simp [sndBody, sndChoice, secondSelector, secondSelectorBody,
    secondEquationBody, repPair, pairChurchChecked, DefEqChecked.openBound,
    DefEqChecked.existsTm, DefEqChecked.lam, DefEqChecked.app,
    DefEqChecked.eps, DefEqChecked.eq, DefEqChecked.rep, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.ofRaw, FamilySub.openBound,
    instantiate, liftSub]
  constructor
  · simp [weaken, rename, instantiate, liftSub]
  · exact instantiate_pairFunction
      (Γm := extendBound A (extendBound B (extendBound (productTy hA hB) Γ)))
      (Γn := extendBound A (extendBound B Γ)) hA hB
      (liftSub (liftSub (Fin.cases value.tm .bv)))

def sndChecked_eq_choice (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.EqTm (sndChecked hA hB value) (sndChoice hA hB value) := by
  have functionEq := sndFunction_eq_lam (Γ := Γ) hA hB
  have reduction := Intrinsic.EqTm.beta typed (productTy_kinded hA hB)
    (sndBody (Γ := Γ) hA hB) value
  rw [← functionEq, sndBody_open typed hA hB value] at reduction
  exact reduction

/-- The public second projection satisfies its product β-law. -/
def snd_pair (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hB (sndChecked hA hB (pairChecked hA hB a b)) b) :=
  Intrinsic.Proves.eqTrans typed hB
    (sndChecked hA hB (pairChecked hA hB a b))
    (sndChoice hA hB (pairChecked hA hB a b)) b
    (Intrinsic.Proves.eqOfEqTm hB
      (sndChecked_eq_choice typed hA hB (pairChecked hA hB a b)))
    (sndChoice_pair typed hA hB a b)

def pair_congr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (a a' : DefEqChecked Sig Γ A) (b b' : DefEqChecked Sig Γ B)
    (first : Intrinsic.Proves Γ H (DefEqChecked.eq hA a a'))
    (second : Intrinsic.Proves Γ H (DefEqChecked.eq hB b b')) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB)
        (pairChurchChecked hA hB a b) (pairChurchChecked hA hB a' b')) := by
  let constructor : DefEqChecked Sig Γ (.arr A (.arr B (productCarrier A B))) :=
    DefEqChecked.ofRaw (pairFunction (Γ := Γ) hA hB).tm
      (pairFunction (Γ := Γ) hA hB).typing
  have afterFirst := Intrinsic.Proves.appArgCongr typed hA
    (.arr hB (productCarrier_kinded hA hB)) constructor a a' first
  have functions := Intrinsic.Proves.appCongr typed hB (productCarrier_kinded hA hB)
    (constructor.app a) (constructor.app a') b afterFirst
  have argument := Intrinsic.Proves.appArgCongr typed hB (productCarrier_kinded hA hB)
    (constructor.app a') b b' second
  exact Intrinsic.Proves.eqTrans typed (productCarrier_kinded hA hB)
    ((constructor.app a).app b) ((constructor.app a').app b)
    ((constructor.app a').app b') functions argument

def rep_eta (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) (repPair hA hB value)
        (pairChurchChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))) := by
  let represented := repPair hA hB value
  let a := decompositionFirst hA hB represented
  let b := decompositionSecond hA hB represented
  have decomposition := rep_decompose (H := H) typed hA hB value
  have first := fstChoice_of_rep typed hA hB value a b decomposition
  have second := sndChoice_of_rep typed hA hB value a b decomposition
  have rebuilt := pair_congr typed hA hB (fstChoice hA hB value) a
    (sndChoice hA hB value) b first second
  exact Intrinsic.Proves.eqTrans typed (productCarrier_kinded hA hB)
    represented (pairChurchChecked hA hB a b)
    (pairChurchChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))
    decomposition (Intrinsic.Proves.eqSymm typed (productCarrier_kinded hA hB)
      (pairChurchChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))
      (pairChurchChecked hA hB a b) rebuilt)

def absBody (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig (extendBound (productCarrier A B) Γ) (productTy hA hB) :=
  let represented := DefEqChecked.bv (productCarrier_kinded hA hB) 0 rfl
  DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
    (productPredicate hA hB).typing represented

def absFunctionChecked (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ (.arr (productCarrier A B) (productTy hA hB)) :=
  DefEqChecked.lam (productCarrier_kinded hA hB) (absBody hA hB)

theorem absBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) :
    (absBody hA hB).openBound typed represented =
      DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
        (productPredicate hA hB).typing represented := by
  apply DefEqChecked.ext
  simp [absBody, DefEqChecked.openBound, DefEqChecked.abs, DefEqChecked.bv,
    FamilySub.openBound, instantiate]

def absFunction_apply (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (represented : DefEqChecked Sig Γ (productCarrier A B)) :
    Intrinsic.EqTm ((absFunctionChecked hA hB).app represented)
      (DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
        (productPredicate hA hB).typing represented) := by
  have reduction := Intrinsic.EqTm.beta typed (productCarrier_kinded hA hB)
    (absBody (Γ := Γ) hA hB) represented
  rw [absBody_open typed hA hB represented] at reduction
  exact reduction

def abs_congr (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (left right : DefEqChecked Sig Γ (productCarrier A B))
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (productCarrier_kinded hA hB) left right)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productTy_kinded hA hB)
        (DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
          (productPredicate hA hB).typing left)
        (DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
          (productPredicate hA hB).typing right)) := by
  let function := absFunctionChecked (Γ := Γ) hA hB
  have applied := Intrinsic.Proves.appArgCongr typed (productCarrier_kinded hA hB)
    (productTy_kinded hA hB) function left right equality
  have leftReduction := absFunction_apply typed hA hB left
  have rightReduction := absFunction_apply typed hA hB right
  exact Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB)
    _ (function.app right) _
    (Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB)
      _ (function.app left) (function.app right)
      (Intrinsic.Proves.eqSymm typed (productTy_kinded hA hB) _ _
        (Intrinsic.Proves.eqOfEqTm (H := H) (productTy_kinded hA hB) leftReduction))
      applied)
    (Intrinsic.Proves.eqOfEqTm (H := H) (productTy_kinded hA hB) rightReduction)

def product_eta_choice (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productTy_kinded hA hB) value
        (pairChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))) := by
  have representation := rep_eta (H := H) typed hA hB value
  have abstractions := abs_congr typed hA hB (repPair hA hB value)
    (pairChurchChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))
    representation
  have roundTrip := Intrinsic.Proves.absRep (H := H) (productCarrier_kinded hA hB)
    (productPredicate hA hB).tm (productPredicate hA hB).typing value
  exact Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB) value
    (DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
      (productPredicate hA hB).typing (repPair hA hB value))
    (pairChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))
    (Intrinsic.Proves.eqSymm typed (productTy_kinded hA hB) _ _ roundTrip)
    abstractions

def product_eta (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (productTy hA hB)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (productTy_kinded hA hB) value
        (pairChecked hA hB (fstChecked hA hB value) (sndChecked hA hB value))) := by
  have fstEq := Intrinsic.Proves.eqOfEqTm (H := H) hA
    (fstChecked_eq_choice typed hA hB value)
  have sndEq := Intrinsic.Proves.eqOfEqTm (H := H) hB
    (sndChecked_eq_choice typed hA hB value)
  have pairs := pair_congr typed hA hB (fstChoice hA hB value)
    (fstChecked hA hB value) (sndChoice hA hB value) (sndChecked hA hB value)
    (Intrinsic.Proves.eqSymm typed hA _ _ fstEq)
    (Intrinsic.Proves.eqSymm typed hB _ _ sndEq)
  exact Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB) value
    (pairChecked hA hB (fstChoice hA hB value) (sndChoice hA hB value))
    (pairChecked hA hB (fstChecked hA hB value) (sndChecked hA hB value))
    (product_eta_choice typed hA hB value)
    (abs_congr typed hA hB _ _ pairs)

/-- Products are extensional with respect to the two public projections. -/
def product_ext (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (left right : DefEqChecked Sig Γ (productTy hA hB))
    (first : Intrinsic.Proves Γ H
      (DefEqChecked.eq hA (fstChecked hA hB left) (fstChecked hA hB right)))
    (second : Intrinsic.Proves Γ H
      (DefEqChecked.eq hB (sndChecked hA hB left) (sndChecked hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq (productTy_kinded hA hB) left right) := by
  have pairs := pair_congr typed hA hB (fstChecked hA hB left)
    (fstChecked hA hB right) (sndChecked hA hB left) (sndChecked hA hB right)
    first second
  have paired := abs_congr typed hA hB _ _ pairs
  exact Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB) left
    (pairChecked hA hB (fstChecked hA hB left) (sndChecked hA hB left)) right
    (product_eta typed hA hB left)
    (Intrinsic.Proves.eqTrans typed (productTy_kinded hA hB) _
      (pairChecked hA hB (fstChecked hA hB right) (sndChecked hA hB right)) right
      paired
      (Intrinsic.Proves.eqSymm typed (productTy_kinded hA hB) _ _
        (product_eta typed hA hB right)))

end Nucleus.Hol.FamilySub
