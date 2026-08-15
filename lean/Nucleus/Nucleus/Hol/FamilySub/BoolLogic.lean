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
  simp [andLeftBody, DefEqChecked.and, DefEqChecked.andLhs,
    DefEqChecked.andLhsBody, DefEqChecked.andRhs,
    DefEqChecked.openBound,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    FamilySub.openBound, instantiate, liftSub]
  simp [weaken, rename, instantiate]

theorem andRightBody_open (typed : TypedCtx Γ) (left value : BoolTm Γ) :
    (andRightBody left).openBound typed value = DefEqChecked.and left value := by
  apply DefEqChecked.ext
  simp [andRightBody, DefEqChecked.and, DefEqChecked.andLhs,
    DefEqChecked.andLhsBody, DefEqChecked.andRhs,
    DefEqChecked.openBound,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    FamilySub.openBound, instantiate, liftSub]
  simp [weaken, rename, instantiate]

theorem andLhsBody_open (typed : TypedCtx Γ) (left right : BoolTm Γ)
    (operator : DefEqChecked Sig Γ (.arr .boolTy (.arr .boolTy .boolTy))) :
    (DefEqChecked.andLhsBody left right).openBound typed operator =
      (operator.app left).app right := by
  apply DefEqChecked.ext
  simp [DefEqChecked.andLhsBody, DefEqChecked.openBound, DefEqChecked.app,
    DefEqChecked.bv, DefEqChecked.weaken, FamilySub.openBound, instantiate]

def andLhs_apply (typed : TypedCtx Γ) (left right : BoolTm Γ)
    (operator : DefEqChecked Sig Γ (.arr .boolTy (.arr .boolTy .boolTy))) :
    Intrinsic.EqTm ((DefEqChecked.andLhs left right).app operator)
      ((operator.app left).app right) := by
  have reduction := Intrinsic.EqTm.beta typed (.arr .boolTy (.arr .boolTy .boolTy))
    (DefEqChecked.andLhsBody left right) operator
  rw [andLhsBody_open typed left right operator] at reduction
  exact reduction

def firstBoolAfterFirst (first : BoolTm Γ) :
    DefEqChecked Sig Γ (.arr .boolTy .boolTy) :=
  DefEqChecked.lam .boolTy first.weaken

def firstBoolBody :
    DefEqChecked Sig (extendBound (.boolTy : Ty Sig types) Γ) (.arr .boolTy .boolTy) :=
  firstBoolAfterFirst (DefEqChecked.bv .boolTy 0 rfl)

def firstBool : DefEqChecked Sig Γ (.arr .boolTy (.arr .boolTy .boolTy)) :=
  DefEqChecked.lam .boolTy firstBoolBody

theorem firstBoolBody_open (typed : TypedCtx Γ) (first : BoolTm Γ) :
    firstBoolBody.openBound typed first = firstBoolAfterFirst first := by
  apply DefEqChecked.ext
  simp [firstBoolBody, firstBoolAfterFirst, DefEqChecked.openBound,
    DefEqChecked.lam, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate, liftSub]

theorem firstBoolAfterFirst_open (typed : TypedCtx Γ) (first second : BoolTm Γ) :
    first.weaken.openBound typed second = first := by
  apply DefEqChecked.ext
  simp [DefEqChecked.openBound, DefEqChecked.weaken, FamilySub.openBound]

def firstBool_apply (typed : TypedCtx Γ) (first second : BoolTm Γ) :
    Intrinsic.EqTm ((firstBool.app first).app second) first := by
  have outer := Intrinsic.EqTm.beta typed .boolTy firstBoolBody first
  rw [firstBoolBody_open typed first] at outer
  have applied := outer.app (Intrinsic.EqTm.refl second)
  have inner := Intrinsic.EqTm.beta typed .boolTy first.weaken second
  rw [firstBoolAfterFirst_open typed first second] at inner
  exact applied.trans inner

def secondBoolBody :
    DefEqChecked Sig (extendBound (.boolTy : Ty Sig types) Γ) (.arr .boolTy .boolTy) :=
  DefEqChecked.lam .boolTy (DefEqChecked.bv .boolTy 0 rfl)

def secondBool : DefEqChecked Sig Γ (.arr .boolTy (.arr .boolTy .boolTy)) :=
  DefEqChecked.lam .boolTy secondBoolBody

theorem secondBoolBody_open (typed : TypedCtx Γ) (first : BoolTm Γ) :
    secondBoolBody.openBound typed first =
      DefEqChecked.lam .boolTy (DefEqChecked.bv .boolTy 0 rfl) := by
  apply DefEqChecked.ext
  simp [secondBoolBody, DefEqChecked.openBound, DefEqChecked.lam,
    DefEqChecked.bv, FamilySub.openBound, instantiate, liftSub]

theorem secondBoolInner_open (typed : TypedCtx Γ) (second : BoolTm Γ) :
    (DefEqChecked.bv (.boolTy : Kinded (.boolTy : Ty Sig types)) 0 rfl).openBound
      typed second = second := by
  apply DefEqChecked.ext
  simp [DefEqChecked.openBound, DefEqChecked.bv, FamilySub.openBound]

def secondBool_apply (typed : TypedCtx Γ) (first second : BoolTm Γ) :
    Intrinsic.EqTm ((secondBool.app first).app second) second := by
  have outer := Intrinsic.EqTm.beta typed .boolTy secondBoolBody first
  rw [secondBoolBody_open typed first] at outer
  have applied := outer.app (Intrinsic.EqTm.refl second)
  have inner := Intrinsic.EqTm.beta typed .boolTy
    (DefEqChecked.bv (.boolTy : Kinded (.boolTy : Ty Sig types)) 0 rfl) second
  rw [secondBoolInner_open typed second] at inner
  exact applied.trans inner

/-- The defining equation for conjunction is reflexive at `true, true`. -/
def andTrueTrue : Intrinsic.Proves Γ H
    (DefEqChecked.and DefEqChecked.truth DefEqChecked.truth) := by
  let functionTy : Ty Sig types := .arr .boolTy (.arr .boolTy .boolTy)
  let hFunction : Kinded functionTy := .arr .boolTy (.arr .boolTy .boolTy)
  let f := DefEqChecked.bv (Γ := extendBound functionTy Γ) hFunction 0 rfl
  let applied := (f.app (DefEqChecked.truth (Γ := Γ)).weaken).app
    (DefEqChecked.truth (Γ := Γ)).weaken
  let abstraction := DefEqChecked.lam hFunction applied
  simpa [DefEqChecked.and, DefEqChecked.andLhs, DefEqChecked.andLhsBody,
    DefEqChecked.andRhs,
    functionTy, hFunction, f, applied, abstraction] using
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

/-- Left elimination for equality-defined conjunction. -/
def andElimLeft (typed : TypedCtx Γ)
    (conjunction : Intrinsic.Proves Γ H (DefEqChecked.and p q)) :
    Intrinsic.Proves Γ H p := by
  let hOperator : Kinded (.arr .boolTy (.arr .boolTy .boolTy) : Ty Sig types) :=
    .arr .boolTy (.arr .boolTy .boolTy)
  have applied := Intrinsic.Proves.appCongr typed hOperator .boolTy
    (DefEqChecked.andLhs p q) DefEqChecked.andRhs firstBool conjunction
  have leftReduction := (andLhs_apply typed p q firstBool).trans
    (firstBool_apply typed p q)
  have rightReduction := (andLhs_apply typed DefEqChecked.truth DefEqChecked.truth
    firstBool).trans (firstBool_apply typed DefEqChecked.truth DefEqChecked.truth)
  have first : Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy p (DefEqChecked.andRhs.app firstBool)) :=
    Intrinsic.Proves.eqTrans typed .boolTy p
      ((DefEqChecked.andLhs p q).app firstBool)
      (DefEqChecked.andRhs.app firstBool)
      (Intrinsic.Proves.eqSymm typed .boolTy _ _
        (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy leftReduction)) applied
  have equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy p DefEqChecked.truth) :=
    Intrinsic.Proves.eqTrans typed .boolTy p
      (DefEqChecked.andRhs.app firstBool) DefEqChecked.truth first
      (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy rightReduction)
  exact Intrinsic.Proves.ofEqTrue typed equality

/-- Right elimination for equality-defined conjunction. -/
def andElimRight (typed : TypedCtx Γ)
    (conjunction : Intrinsic.Proves Γ H (DefEqChecked.and p q)) :
    Intrinsic.Proves Γ H q := by
  let hOperator : Kinded (.arr .boolTy (.arr .boolTy .boolTy) : Ty Sig types) :=
    .arr .boolTy (.arr .boolTy .boolTy)
  have applied := Intrinsic.Proves.appCongr typed hOperator .boolTy
    (DefEqChecked.andLhs p q) DefEqChecked.andRhs secondBool conjunction
  have leftReduction := (andLhs_apply typed p q secondBool).trans
    (secondBool_apply typed p q)
  have rightReduction := (andLhs_apply typed DefEqChecked.truth DefEqChecked.truth
    secondBool).trans (secondBool_apply typed DefEqChecked.truth DefEqChecked.truth)
  have first : Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy q (DefEqChecked.andRhs.app secondBool)) :=
    Intrinsic.Proves.eqTrans typed .boolTy q
      ((DefEqChecked.andLhs p q).app secondBool)
      (DefEqChecked.andRhs.app secondBool)
      (Intrinsic.Proves.eqSymm typed .boolTy _ _
        (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy leftReduction)) applied
  have equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq .boolTy q DefEqChecked.truth) :=
    Intrinsic.Proves.eqTrans typed .boolTy q
      (DefEqChecked.andRhs.app secondBool) DefEqChecked.truth first
      (Intrinsic.Proves.eqOfEqTm (H := H) .boolTy rightReduction)
  exact Intrinsic.Proves.ofEqTrue typed equality

/-- Negation introduction, with negation represented as equality to false. -/
noncomputable def notIntro (_typed : TypedCtx Γ) (proposition : BoolTm Γ)
    (contradiction : Intrinsic.Proves Γ (proposition :: H) DefEqChecked.falsehood) :
    Intrinsic.Proves Γ H (DefEqChecked.not proposition) := by
  apply Intrinsic.Proves.antisymm proposition DefEqChecked.falsehood
  · exact contradiction
  · exact Intrinsic.Proves.falseElim proposition
      (Intrinsic.Proves.hyp (H := DefEqChecked.falsehood :: H) (by simp))

/-- Negation elimination is equality substitution into false. -/
def notElim (typed : TypedCtx Γ) (negated : Intrinsic.Proves Γ H (DefEqChecked.not p))
    (premise : Intrinsic.Proves Γ H p) :
    Intrinsic.Proves Γ H DefEqChecked.falsehood :=
  Intrinsic.Proves.ofEqBool typed p DefEqChecked.falsehood negated premise

/-- Implication introduction for the equality definition `p ∧ q = p`. -/
noncomputable def impIntro (typed : TypedCtx Γ)
    (consequence : Intrinsic.Proves Γ (p :: H) q) :
    Intrinsic.Proves Γ H (DefEqChecked.imp p q) := by
  unfold DefEqChecked.imp
  apply Intrinsic.Proves.antisymm (DefEqChecked.and p q) p
  · have conjunction : Intrinsic.Proves Γ (DefEqChecked.and p q :: H)
        (DefEqChecked.and p q) := Intrinsic.Proves.hyp (by simp)
    exact andElimLeft typed conjunction
  · have premise : Intrinsic.Proves Γ (p :: H) p := Intrinsic.Proves.hyp (by simp)
    exact andIntro typed premise consequence

/-- Modus ponens for equality-defined implication. -/
def impElim (typed : TypedCtx Γ)
    (implication : Intrinsic.Proves Γ H (DefEqChecked.imp p q))
    (premise : Intrinsic.Proves Γ H p) : Intrinsic.Proves Γ H q := by
  have expanded : Intrinsic.Proves Γ H (DefEqChecked.and p q) :=
    Intrinsic.Proves.ofEqBool typed p (DefEqChecked.and p q)
      (Intrinsic.Proves.eqSymm typed .boolTy (DefEqChecked.and p q) p implication)
      premise
  exact andElimRight typed expanded

/-- Left introduction for the De Morgan definition of disjunction. -/
noncomputable def orIntroLeft (typed : TypedCtx Γ)
    (premise : Intrinsic.Proves Γ H p) :
    Intrinsic.Proves Γ H (DefEqChecked.or p q) := by
  let notP := DefEqChecked.not p
  let notQ := DefEqChecked.not q
  let denied := DefEqChecked.and notP notQ
  apply notIntro typed denied
  have conjunction : Intrinsic.Proves Γ (denied :: H) denied :=
    Intrinsic.Proves.hyp (by simp)
  have deniedP : Intrinsic.Proves Γ (denied :: H) notP :=
    andElimLeft typed conjunction
  have pProof : Intrinsic.Proves Γ (denied :: H) p :=
    Intrinsic.Proves.weakenHyp denied premise
  exact Intrinsic.Proves.ofEqBool typed p DefEqChecked.falsehood deniedP pProof

/-- Right introduction for the De Morgan definition of disjunction. -/
noncomputable def orIntroRight (typed : TypedCtx Γ)
    (premise : Intrinsic.Proves Γ H q) :
    Intrinsic.Proves Γ H (DefEqChecked.or p q) := by
  let notP := DefEqChecked.not p
  let notQ := DefEqChecked.not q
  let denied := DefEqChecked.and notP notQ
  apply notIntro typed denied
  have conjunction : Intrinsic.Proves Γ (denied :: H) denied :=
    Intrinsic.Proves.hyp (by simp)
  have deniedQ : Intrinsic.Proves Γ (denied :: H) notQ :=
    andElimRight typed conjunction
  have qProof : Intrinsic.Proves Γ (denied :: H) q :=
    Intrinsic.Proves.weakenHyp denied premise
  exact Intrinsic.Proves.ofEqBool typed q DefEqChecked.falsehood deniedQ qProof

end Nucleus.Hol.FamilySub
