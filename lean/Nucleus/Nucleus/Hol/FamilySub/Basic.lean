import Nucleus.Hol.FamilySub.Algebraic

/-! # Unit and option types from guarded subtypes and coproducts -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {A C : Ty Sig types}

/-- The singleton predicate on `bool`. -/
def unitPredicate :
    Checked Sig (extendBound (.boolTy : Ty Sig types) emptyBound) .boolTy :=
  Checked.eq .boolTy (Checked.bv .boolTy 0 rfl) Checked.truth

/-- Unit is the guarded subtype containing exactly `true`. -/
def unitTy (Sig : Signature) [SigTyping Sig] (types : List Kind) : Ty Sig types :=
  .sub .boolTy (unitPredicate (Sig := Sig) (types := types)).tm

theorem unitTy_kinded : Kinded (unitTy Sig types) :=
  .sub .boolTy (unitPredicate (Sig := Sig) (types := types)).typing

def unitStar : DefEqChecked Sig Γ (unitTy Sig types) :=
  DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
    (unitPredicate (Sig := Sig) (types := types)).typing DefEqChecked.truth

def repUnit (value : DefEqChecked Sig Γ (unitTy Sig types)) : BoolTm Γ :=
  DefEqChecked.rep .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
    (unitPredicate (Sig := Sig) (types := types)).typing value

def unitPredicateAt (value : BoolTm Γ) : BoolTm Γ :=
  DefEqChecked.eq .boolTy value DefEqChecked.truth

theorem unitPredicateAt_term_eq (value : BoolTm Γ) :
    (unitPredicateAt value).tm = instantiateOne
      (unitPredicate (Sig := Sig) (types := types)).tm value.tm := by
  simp [unitPredicateAt, unitPredicate, DefEqChecked.eq, Checked.eq,
    Checked.bv, Checked.truth, DefEqChecked.truth, DefEqChecked.boolean,
    instantiateOne, instantiate]

def unitPredicate_truth : Intrinsic.Proves Γ H
    (unitPredicateAt (DefEqChecked.truth : BoolTm Γ)) :=
  Intrinsic.Proves.eqRefl .boolTy DefEqChecked.truth

/-- A represented unit value satisfies the singleton predicate. -/
def repUnit_eq_truth (value : DefEqChecked Sig Γ (unitTy Sig types)) :
    Intrinsic.Proves Γ H (unitPredicateAt (repUnit value)) :=
  Intrinsic.Proves.repPredOfWitness .boolTy
    (unitPredicate (Sig := Sig) (types := types)).tm
    (unitPredicate (Sig := Sig) (types := types)).typing
    (DefEqChecked.truth : BoolTm Γ) (unitPredicateAt DefEqChecked.truth)
    (unitPredicateAt_term_eq DefEqChecked.truth) value
    (unitPredicateAt (repUnit value)) (unitPredicateAt_term_eq (repUnit value))
    unitPredicate_truth

def unitAbsBody : DefEqChecked Sig
    (extendBound (.boolTy : Ty Sig types) Γ) (unitTy Sig types) :=
  DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
    (unitPredicate (Sig := Sig) (types := types)).typing
    (DefEqChecked.bv .boolTy 0 rfl)

def unitAbsFunction : DefEqChecked Sig Γ (.arr .boolTy (unitTy Sig types)) :=
  DefEqChecked.lam .boolTy unitAbsBody

theorem unitAbsBody_open (typed : TypedCtx Γ) (value : BoolTm Γ) :
    unitAbsBody.openBound typed value =
      DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
        (unitPredicate (Sig := Sig) (types := types)).typing value := by
  apply DefEqChecked.ext
  simp [unitAbsBody, DefEqChecked.openBound, DefEqChecked.abs, DefEqChecked.bv,
    FamilySub.openBound, instantiate]

def unitAbsFunction_apply (typed : TypedCtx Γ) (value : BoolTm Γ) :
    Intrinsic.EqTm (unitAbsFunction.app value)
      (DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
        (unitPredicate (Sig := Sig) (types := types)).typing value) := by
  have reduction := Intrinsic.EqTm.beta typed .boolTy unitAbsBody value
  rw [unitAbsBody_open typed value] at reduction
  exact reduction

def unitAbs_congr (typed : TypedCtx Γ) (left right : BoolTm Γ)
    (equality : Intrinsic.Proves Γ H (DefEqChecked.eq .boolTy left right)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq unitTy_kinded
        (DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
          (unitPredicate (Sig := Sig) (types := types)).typing left)
        (DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
          (unitPredicate (Sig := Sig) (types := types)).typing right)) := by
  have applied := Intrinsic.Proves.appArgCongr typed .boolTy unitTy_kinded
    unitAbsFunction left right equality
  exact Intrinsic.Proves.eqTrans typed unitTy_kinded _ (unitAbsFunction.app right) _
    (Intrinsic.Proves.eqTrans typed unitTy_kinded _ (unitAbsFunction.app left) _
      (Intrinsic.Proves.eqSymm typed unitTy_kinded _ _
        (Intrinsic.Proves.eqOfEqTm unitTy_kinded (unitAbsFunction_apply typed left)))
      applied)
    (Intrinsic.Proves.eqOfEqTm unitTy_kinded (unitAbsFunction_apply typed right))

/-- Every checked inhabitant of `unit` is provably equal to `star`. -/
def unit_unique (typed : TypedCtx Γ) (value : DefEqChecked Sig Γ (unitTy Sig types)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq unitTy_kinded value unitStar) := by
  have unfoldValue := Intrinsic.Proves.eqSymm (H := H) typed unitTy_kinded _ _
    (Intrinsic.Proves.absRep (H := H) .boolTy
      (unitPredicate (Sig := Sig) (types := types)).tm
      (unitPredicate (Sig := Sig) (types := types)).typing value)
  have representations := repUnit_eq_truth (H := H) value
  exact Intrinsic.Proves.eqTrans typed unitTy_kinded value
    (DefEqChecked.abs .boolTy (unitPredicate (Sig := Sig) (types := types)).tm
      (unitPredicate (Sig := Sig) (types := types)).typing (repUnit value)) unitStar
    unfoldValue (unitAbs_congr typed (repUnit value) DefEqChecked.truth representations)

/-- Option is the coproduct of unit and the payload type. -/
def optionTy (hA : Kinded A) : Ty Sig types := coproductTy unitTy_kinded hA

theorem optionTy_kinded (hA : Kinded A) : Kinded (optionTy hA) :=
  coproductTy_kinded unitTy_kinded hA

def optionNone (hA : Kinded A) : DefEqChecked Sig Γ (optionTy hA) :=
  inlChecked unitTy_kinded hA unitStar

def optionSome (hA : Kinded A) (value : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ (optionTy hA) :=
  inrChecked unitTy_kinded hA value

def optionCase (hA : Kinded A) (hC : Kinded C)
    (none : DefEqChecked Sig Γ C) (some : DefEqChecked Sig Γ (.arr A C))
    (value : DefEqChecked Sig Γ (optionTy hA)) : DefEqChecked Sig Γ C :=
  let noneBranch : DefEqChecked Sig Γ (.arr (unitTy Sig types) C) :=
    DefEqChecked.lam unitTy_kinded none.weaken
  caseChecked unitTy_kinded hA hC noneBranch some value

theorem constantUnitBody_open (typed : TypedCtx Γ)
    (value : DefEqChecked Sig Γ C) (argument : DefEqChecked Sig Γ (unitTy Sig types)) :
    value.weaken.openBound typed argument = value := by
  apply DefEqChecked.ext
  simp [DefEqChecked.openBound, DefEqChecked.weaken, FamilySub.openBound]

def constantUnitFunction_apply (typed : TypedCtx Γ)
    (value : DefEqChecked Sig Γ C) (argument : DefEqChecked Sig Γ (unitTy Sig types)) :
    Intrinsic.EqTm ((DefEqChecked.lam unitTy_kinded value.weaken).app argument) value := by
  have reduction := Intrinsic.EqTm.beta typed unitTy_kinded value.weaken argument
  rw [constantUnitBody_open typed value argument] at reduction
  exact reduction

/-- Option case analysis computes on `none`. -/
noncomputable def optionCase_none (typed : TypedCtx Γ) (hA : Kinded A)
    (hC : Kinded C) (none : DefEqChecked Sig Γ C)
    (some : DefEqChecked Sig Γ (.arr A C)) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hC (optionCase hA hC none some (optionNone hA)) none) := by
  let noneBranch := DefEqChecked.lam unitTy_kinded none.weaken
  have computation := case_inl (H := H) typed unitTy_kinded hA hC
    noneBranch some (unitStar (Γ := Γ))
  exact Intrinsic.Proves.eqTrans typed hC _ (noneBranch.app unitStar) none computation
    (Intrinsic.Proves.eqOfEqTm hC
      (constantUnitFunction_apply typed none (unitStar (Γ := Γ))))

/-- Option case analysis computes on `some`. -/
noncomputable def optionCase_some (typed : TypedCtx Γ) (hA : Kinded A)
    (hC : Kinded C) (none : DefEqChecked Sig Γ C)
    (some : DefEqChecked Sig Γ (.arr A C)) (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq hC
        (optionCase hA hC none some (optionSome hA value)) (some.app value)) :=
  case_inr typed unitTy_kinded hA hC
    (DefEqChecked.lam unitTy_kinded none.weaken) some value

/-- `some` is injective. -/
noncomputable def optionSome_injective (typed : TypedCtx Γ) (hA : Kinded A)
    (left right : DefEqChecked Sig Γ A)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (optionTy_kinded hA)
        (optionSome hA left) (optionSome hA right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA left right) :=
  inr_injective typed unitTy_kinded hA left right equality

/-- `none` is distinct from every `some`. -/
noncomputable def optionNone_ne_some (typed : TypedCtx Γ) (hA : Kinded A)
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H (DefEqChecked.not
      (DefEqChecked.eq (optionTy_kinded hA) (optionNone hA) (optionSome hA value))) :=
  inl_ne_inr typed unitTy_kinded hA unitStar value

end Nucleus.Hol.FamilySub
