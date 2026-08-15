import Nucleus.Hol.FamilySub.Intrinsic

/-! # Derived Boolean logic for intrinsic FamilySub terms -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {p q : BoolTm Γ}

@[simp] theorem boolLogicFinCasesOne {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 1) → α) : Fin.cases zero succ 1 = succ 0 :=
  Fin.cases_succ 0

def andLeftBody (right : BoolTm Γ) :
    BoolTm (extendBound (.boolTy : Ty Sig types) Γ) :=
  DefEqChecked.and (DefEqChecked.bv .boolTy 0 rfl) right.weaken

def andRightBody (left : BoolTm Γ) :
    BoolTm (extendBound (.boolTy : Ty Sig types) Γ) :=
  DefEqChecked.and left.weaken (DefEqChecked.bv .boolTy 0 rfl)

theorem andLeftBody_open (typed : TypedCtx Γ) (right value : BoolTm Γ) :
    (andLeftBody right).openBound typed value = DefEqChecked.and value right := by
  apply DefEqChecked.ext
  simp [andLeftBody, DefEqChecked.and, DefEqChecked.openBound,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    FamilySub.openBound, instantiate, liftSub]
  simp [weaken, rename, instantiate]

theorem andRightBody_open (typed : TypedCtx Γ) (left value : BoolTm Γ) :
    (andRightBody left).openBound typed value = DefEqChecked.and left value := by
  apply DefEqChecked.ext
  simp [andRightBody, DefEqChecked.and, DefEqChecked.openBound,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    FamilySub.openBound, instantiate, liftSub]
  simp [weaken, rename, instantiate]

/-- The defining equation for conjunction is reflexive at `true, true`. -/
def andTrueTrue : Intrinsic.Proves Γ H
    (DefEqChecked.and DefEqChecked.truth DefEqChecked.truth) := by
  let functionTy : Ty Sig types := .arr .boolTy (.arr .boolTy .boolTy)
  let hFunction : Kinded functionTy := .arr .boolTy (.arr .boolTy .boolTy)
  let f := DefEqChecked.bv (Γ := extendBound functionTy Γ) hFunction 0 rfl
  let applied := (f.app (DefEqChecked.truth (Γ := Γ)).weaken).app
    (DefEqChecked.truth (Γ := Γ)).weaken
  let abstraction := DefEqChecked.lam hFunction applied
  simpa [DefEqChecked.and, functionTy, hFunction, f, applied, abstraction] using
    (Intrinsic.Proves.eqRefl (H := H) (.arr hFunction .boolTy) abstraction)

/-- Standard conjunction introduction, derived from equality substitution. -/
noncomputable def andIntro (typed : TypedCtx Γ)
    (left : Intrinsic.Proves Γ H p) (right : Intrinsic.Proves Γ H q) :
    Intrinsic.Proves Γ H (DefEqChecked.and p q) := by
  let truth : BoolTm Γ := DefEqChecked.truth
  have qTrue := Intrinsic.Proves.eqTrue typed right
  have trueQ := Intrinsic.Proves.eqSymm typed .boolTy q truth qTrue
  let rightPredicate := DefEqChecked.lam .boolTy (andRightBody truth)
  have atTrue : Intrinsic.Proves Γ H (rightPredicate.app truth) :=
    Intrinsic.Proves.betaExpand typed .boolTy (andRightBody truth) truth
      (andRightBody_open typed truth truth ▸ andTrueTrue (H := H))
  have atQ : Intrinsic.Proves Γ H (rightPredicate.app q) :=
    Intrinsic.Proves.eqMp .boolTy rightPredicate truth q trueQ atTrue
  have truthAndQ : Intrinsic.Proves Γ H (DefEqChecked.and truth q) :=
    andRightBody_open typed truth q ▸
      Intrinsic.Proves.betaReduce typed .boolTy (andRightBody truth) q atQ
  have pTrue := Intrinsic.Proves.eqTrue typed left
  have trueP := Intrinsic.Proves.eqSymm typed .boolTy p truth pTrue
  let leftPredicate := DefEqChecked.lam .boolTy (andLeftBody q)
  have atTruth : Intrinsic.Proves Γ H (leftPredicate.app truth) :=
    Intrinsic.Proves.betaExpand typed .boolTy (andLeftBody q) truth
      (andLeftBody_open typed q truth ▸ truthAndQ)
  have atP : Intrinsic.Proves Γ H (leftPredicate.app p) :=
    Intrinsic.Proves.eqMp .boolTy leftPredicate truth p trueP atTruth
  exact andLeftBody_open typed q p ▸
    Intrinsic.Proves.betaReduce typed .boolTy (andLeftBody q) p atP

end Nucleus.Hol.FamilySub
