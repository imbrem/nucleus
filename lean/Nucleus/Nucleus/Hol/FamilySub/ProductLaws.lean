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

@[simp] theorem instantiate_pairFunction {m n : Nat}
    {Γm : BoundCtx Sig types m} {Γn : BoundCtx Sig types n}
    (hA : Kinded A) (hB : Kinded B) (σ : Fin m → Tm Sig types n) :
    instantiate σ (pairFunction (Γ := Γm) hA hB).tm =
      (pairFunction (Γ := Γn) hA hB).tm := by
  simp [pairFunction, Checked.lam, Checked.app, Checked.bv,
    instantiate, liftSub, weaken, rename, Fin.cases_zero]

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
    instantiateOne, instantiate, liftSub, weaken, rename,
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
