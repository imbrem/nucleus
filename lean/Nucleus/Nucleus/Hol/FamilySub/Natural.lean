import Nucleus.Hol.FamilySub.Infinity
import Nucleus.Hol.FamilySub.Quantifiers

/-! # Natural-number syntax derived from an infinite type -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] [InfiniteOps Sig]
  {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}

/-- The intersection-of-inductive-sets predicate defining the naturals inside
the designated infinite type. -/
def natPredicate : Checked Sig
    (extendBound (InfiniteOps.ind (Sig := Sig) (types := types))
      (emptyBound : BoundCtx Sig types 0)) (.boolTy : Ty Sig types) := by
  let I : Ty Sig types := InfiniteOps.ind
  let hI : Kinded I := InfiniteOps.indKinded
  let predTy : Ty Sig types := .arr I .boolTy
  let hPred : Kinded predTy := .arr hI .boolTy
  let Γx : BoundCtx Sig types 1 := extendBound I emptyBound
  let Γp : BoundCtx Sig types 2 := extendBound predTy Γx
  let Γy : BoundCtx Sig types 3 := extendBound I Γp
  let y : Checked Sig Γy I := Checked.bv hI 0 rfl
  let pAtY : Checked Sig Γy predTy := Checked.bv hPred 1 rfl
  let stepBody : Checked Sig Γy .boolTy :=
    Checked.imp (pAtY.app y) (pAtY.app (indSuccChecked.app y))
  let step : Checked Sig Γp .boolTy := Checked.forallTm hI stepBody
  let p : Checked Sig Γp predTy := Checked.bv hPred 0 rfl
  let x : Checked Sig Γp I := Checked.bv hI 1 rfl
  let base : Checked Sig Γp .boolTy := p.app indZeroChecked
  let closed : Checked Sig Γp .boolTy := Checked.and base step
  let contains : Checked Sig Γp .boolTy := p.app x
  exact Checked.forallTm hPred (Checked.imp closed contains)

/-- Naturals are the guarded subtype of `ind` selected by `natPredicate`. -/
def naturalTy (Sig : Signature) [SigTyping Sig] [InfiniteOps Sig]
    (types : List Kind) : Ty Sig types :=
  .sub InfiniteOps.ind (natPredicate (Sig := Sig) (types := types)).tm

theorem naturalTy_kinded : Kinded (naturalTy Sig types) :=
  .sub InfiniteOps.indKinded (natPredicate (Sig := Sig) (types := types)).typing

def natStepBody : BoolTm
    (extendBound InfiniteOps.ind
      (extendBound (.arr InfiniteOps.ind .boolTy) Γ)) :=
  let hI : Kinded (InfiniteOps.ind (Sig := Sig) (types := types)) :=
    InfiniteOps.indKinded
  let hPred : Kinded (.arr InfiniteOps.ind .boolTy : Ty Sig types) :=
    .arr hI .boolTy
  let y := DefEqChecked.bv (Γ := extendBound InfiniteOps.ind
    (extendBound (.arr InfiniteOps.ind .boolTy) Γ)) hI 0 rfl
  let predicate := DefEqChecked.bv (Γ := extendBound InfiniteOps.ind
    (extendBound (.arr InfiniteOps.ind .boolTy) Γ)) hPred 1 rfl
  DefEqChecked.imp (predicate.app y) (predicate.app (indSucc.app y))

def natStep : BoolTm (extendBound (.arr InfiniteOps.ind .boolTy) Γ) :=
  DefEqChecked.forallTm InfiniteOps.indKinded natStepBody

def natStepAtBody
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy)) :
    BoolTm (extendBound InfiniteOps.ind Γ) :=
  let y := DefEqChecked.bv (Sig := Sig) (types := types)
    (Γ := extendBound InfiniteOps.ind Γ) InfiniteOps.indKinded 0 rfl
  DefEqChecked.imp (predicate.weaken.app y)
    (predicate.weaken.app (indSucc.app y))

def natStepAt
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy)) : BoolTm Γ :=
  DefEqChecked.forallTm InfiniteOps.indKinded (natStepAtBody predicate)

theorem natStepAtBody_open (typed : TypedCtx Γ)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy))
    (value : DefEqChecked Sig Γ InfiniteOps.ind) :
    (natStepAtBody predicate).openBound typed value =
      DefEqChecked.imp (predicate.app value)
        (predicate.app (indSucc.app value)) := by
  apply DefEqChecked.ext
  simp [natStepAtBody, DefEqChecked.imp, DefEqChecked.and,
    DefEqChecked.andLhs, DefEqChecked.andLhsBody, DefEqChecked.andRhs,
    DefEqChecked.openBound, DefEqChecked.eq, DefEqChecked.lam,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    DefEqChecked.truth, DefEqChecked.boolean, indSucc, indSuccChecked,
    DefEqChecked.ofRaw, FamilySub.openBound, instantiate, liftSub]

noncomputable def natStepElim (typed : TypedCtx Γ)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy))
    (value : DefEqChecked Sig Γ InfiniteOps.ind)
    (step : Intrinsic.Proves Γ H (natStepAt predicate))
    (premise : Intrinsic.Proves Γ H (predicate.app value)) :
    Intrinsic.Proves Γ H (predicate.app (indSucc.app value)) := by
  have implication := Intrinsic.Proves.forallElim typed InfiniteOps.indKinded
    (natStepAtBody predicate) value step
  rw [natStepAtBody_open typed predicate value] at implication
  exact impElim typed implication premise

theorem natStep_open (typed : TypedCtx Γ)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy)) :
    (natStep (Sig := Sig) (Γ := Γ)).openBound typed predicate =
      natStepAt predicate := by
  apply DefEqChecked.ext
  simp [natStep, natStepBody, natStepAt, natStepAtBody, DefEqChecked.forallTm,
    DefEqChecked.imp, DefEqChecked.and, DefEqChecked.andLhs,
    DefEqChecked.andLhsBody, DefEqChecked.andRhs, DefEqChecked.openBound,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    indSucc, indSuccChecked, DefEqChecked.ofRaw, FamilySub.openBound,
    instantiate, liftSub]

theorem natStep_bound_eq :
    natStep (Sig := Sig) (Γ := Γ) =
      natStepAt (DefEqChecked.bv
        (.arr InfiniteOps.indKinded .boolTy) 0 rfl) := by
  apply DefEqChecked.ext
  simp [natStep, natStepBody, natStepAt, natStepAtBody,
    DefEqChecked.forallTm, DefEqChecked.imp, DefEqChecked.and,
    DefEqChecked.andLhs, DefEqChecked.andLhsBody, DefEqChecked.andRhs,
    DefEqChecked.eq, DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv,
    DefEqChecked.weaken, DefEqChecked.truth, DefEqChecked.boolean,
    indSucc, indSuccChecked, DefEqChecked.ofRaw]

def natClosureBody (represented : DefEqChecked Sig Γ InfiniteOps.ind) :
    BoolTm (extendBound (.arr InfiniteOps.ind .boolTy) Γ) :=
  let hPred : Kinded (.arr InfiniteOps.ind .boolTy : Ty Sig types) :=
    .arr InfiniteOps.indKinded .boolTy
  let predicate := DefEqChecked.bv (Γ := extendBound
    (.arr InfiniteOps.ind .boolTy) Γ) hPred 0 rfl
  let base := predicate.app (indZero (Γ := extendBound
    (.arr InfiniteOps.ind .boolTy) Γ))
  let closed := DefEqChecked.and base natStep
  DefEqChecked.imp closed (predicate.app represented.weaken)

def natClosureAt (represented : DefEqChecked Sig Γ InfiniteOps.ind)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy)) : BoolTm Γ :=
  DefEqChecked.imp
    (DefEqChecked.and (predicate.app indZero) (natStepAt predicate))
    (predicate.app represented)

theorem natClosureBody_open (typed : TypedCtx Γ)
    (represented : DefEqChecked Sig Γ InfiniteOps.ind)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy)) :
    (natClosureBody represented).openBound typed predicate =
      natClosureAt represented predicate := by
  have stepOpen : instantiate (Fin.cases predicate.tm .bv)
      (natStep (Sig := Sig) (Γ := Γ)).tm = (natStepAt predicate).tm := by
    simpa [DefEqChecked.openBound, FamilySub.openBound] using
      congrArg DefEqChecked.tm (natStep_open typed predicate)
  apply DefEqChecked.ext
  simp [natClosureBody, natClosureAt, stepOpen, DefEqChecked.imp,
    DefEqChecked.and, DefEqChecked.andLhs, DefEqChecked.andLhsBody,
    DefEqChecked.andRhs, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.lam, DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    DefEqChecked.truth, DefEqChecked.boolean, indZero, indZeroChecked,
    DefEqChecked.ofRaw, FamilySub.openBound, instantiate, liftSub]

def natPredicateAt (represented : DefEqChecked Sig Γ InfiniteOps.ind) : BoolTm Γ :=
  DefEqChecked.forallTm (.arr InfiniteOps.indKinded .boolTy)
    (natClosureBody represented)

theorem natPredicateAt_term_eq
    (represented : DefEqChecked Sig Γ InfiniteOps.ind) :
    (natPredicateAt represented).tm = instantiateOne
      (natPredicate (Sig := Sig) (types := types)).tm represented.tm := by
  simp [natPredicateAt, natClosureBody, natStep, natStepBody, natPredicate,
    DefEqChecked.forallTm, Checked.forallTm, DefEqChecked.imp, Checked.imp,
    DefEqChecked.and, DefEqChecked.andLhs, DefEqChecked.andLhsBody,
    DefEqChecked.andRhs, Checked.and, DefEqChecked.eq, Checked.eq,
    DefEqChecked.app, Checked.app, DefEqChecked.lam, Checked.lam,
    DefEqChecked.bv, Checked.bv, DefEqChecked.truth, Checked.truth,
    DefEqChecked.boolean, DefEqChecked.weaken, Checked.weaken,
    indZero, indSucc, indZeroChecked, indSuccChecked, DefEqChecked.ofRaw,
    instantiateOne, instantiate, liftSub]

@[simp] theorem natPredicateAt_weaken
    (represented : DefEqChecked Sig Γ InfiniteOps.ind) {A : Ty Sig types} :
    (natPredicateAt represented).weaken =
      natPredicateAt (represented.weaken (C := A)) := by
  apply DefEqChecked.ext
  change weaken (natPredicateAt represented).tm =
    (natPredicateAt (represented.weaken (C := A))).tm
  rw [natPredicateAt_term_eq, natPredicateAt_term_eq]
  unfold instantiateOne DefEqChecked.weaken
  exact rename_instantiate_fusion
    (natPredicate (Sig := Sig) (types := types)).tm
    (fun _ ↦ represented.tm) Fin.succ

/-- Zero belongs to the intersection of all inductive predicates. -/
noncomputable def natPredicate_zero (typed : TypedCtx Γ) :
    Intrinsic.Proves Γ H (natPredicateAt (indZero (Γ := Γ))) := by
  unfold natPredicateAt
  apply Intrinsic.Proves.forallIntro
  unfold natClosureBody
  apply impIntro (TypedCtx.extend typed (.arr InfiniteOps.indKinded .boolTy))
  have closure : Intrinsic.Proves _
      (DefEqChecked.and
        ((DefEqChecked.bv (.arr InfiniteOps.indKinded .boolTy) 0 rfl).app indZero)
        natStep :: PropCtx.weaken (A := .arr InfiniteOps.ind .boolTy) H)
      (DefEqChecked.and
        ((DefEqChecked.bv (.arr InfiniteOps.indKinded .boolTy) 0 rfl).app indZero)
        natStep) := Intrinsic.Proves.hyp (by simp)
  have base := andElimLeft
    (p := (DefEqChecked.bv (.arr InfiniteOps.indKinded .boolTy) 0 rfl).app
      (indZero (Γ := extendBound (.arr InfiniteOps.ind .boolTy) Γ)))
    (q := natStep) (TypedCtx.extend typed (.arr InfiniteOps.indKinded .boolTy)) closure
  simpa only [indZero_weaken] using base

/-- The intersection-of-inductive-predicates definition is closed under the
designated successor. -/
noncomputable def natPredicate_succ (typed : TypedCtx Γ)
    (represented : DefEqChecked Sig Γ InfiniteOps.ind)
    (premise : Intrinsic.Proves Γ H (natPredicateAt represented)) :
    Intrinsic.Proves Γ H (natPredicateAt (indSucc.app represented)) := by
  apply Intrinsic.Proves.forallIntro
  let hPred : Kinded (.arr InfiniteOps.ind .boolTy : Ty Sig types) :=
    .arr InfiniteOps.indKinded .boolTy
  let Γp := extendBound (.arr InfiniteOps.ind .boolTy) Γ
  let typedP : TypedCtx Γp := TypedCtx.extend typed hPred
  let predicate : DefEqChecked Sig Γp (.arr InfiniteOps.ind .boolTy) :=
    DefEqChecked.bv hPred 0 rfl
  apply impIntro typedP
  let closure := DefEqChecked.and (predicate.app indZero)
    (natStep (Sig := Sig) (Γ := Γ))
  have closureProof : Intrinsic.Proves Γp
      (closure :: PropCtx.weaken (A := .arr InfiniteOps.ind .boolTy) H) closure :=
    Intrinsic.Proves.hyp (by simp)
  have step : Intrinsic.Proves Γp
      (closure :: PropCtx.weaken (A := .arr InfiniteOps.ind .boolTy) H)
      (natStepAt predicate) := by
    have raw := andElimRight typedP closureProof
    exact natStep_bound_eq (Sig := Sig) (Γ := Γ) ▸ raw
  have base : Intrinsic.Proves Γp
      (closure :: PropCtx.weaken (A := .arr InfiniteOps.ind .boolTy) H)
      (predicate.app indZero) := andElimLeft typedP closureProof
  have closureAt : Intrinsic.Proves Γp
      (closure :: PropCtx.weaken (A := .arr InfiniteOps.ind .boolTy) H)
      (DefEqChecked.and (predicate.app indZero) (natStepAt predicate)) :=
    andIntro typedP base step
  have weakened := Intrinsic.Proves.weakenBound hPred premise
  rw [natPredicateAt_weaken represented] at weakened
  have closed := Intrinsic.Proves.forallElim typedP hPred
    (natClosureBody represented.weaken) predicate weakened
  rw [natClosureBody_open typedP represented.weaken predicate] at closed
  have contained := impElim typedP
    (Intrinsic.Proves.weakenHyp closure closed) closureAt
  have successorWeaken :
      (indSucc.app represented).weaken
        (C := (.arr InfiniteOps.ind .boolTy : Ty Sig types)) =
      indSucc.app (represented.weaken
        (C := (.arr InfiniteOps.ind .boolTy : Ty Sig types))) := by
    apply DefEqChecked.ext
    simp [DefEqChecked.app, DefEqChecked.weaken, FamilySub.weaken, rename]
    exact congrArg DefEqChecked.tm
      (indSucc_weaken (Sig := Sig) (Γ := Γ)
        (A := (.arr InfiniteOps.ind .boolTy : Ty Sig types)))
  rw [successorWeaken]
  exact natStepElim typedP predicate represented.weaken step contained

def naturalZero : DefEqChecked Sig Γ (naturalTy Sig types) :=
  DefEqChecked.abs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing indZero

def repNatural (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    DefEqChecked Sig Γ InfiniteOps.ind :=
  DefEqChecked.rep InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing value

/-- Every representation of the guarded natural subtype satisfies its
intersection-of-inductive-predicates definition. -/
noncomputable def repNatural_predicate (typed : TypedCtx Γ)
    (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    Intrinsic.Proves Γ H (natPredicateAt (repNatural value)) :=
  Intrinsic.Proves.repPredOfWitness InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing
    (indZero (Sig := Sig) (Γ := Γ)) (natPredicateAt indZero)
    (natPredicateAt_term_eq indZero) value
    (natPredicateAt (repNatural value)) (natPredicateAt_term_eq (repNatural value))
    (natPredicate_zero typed)

/-- Induction over the `ind` representation of a guarded natural. -/
noncomputable def naturalInduction (typed : TypedCtx Γ)
    (predicate : DefEqChecked Sig Γ (.arr InfiniteOps.ind .boolTy))
    (value : DefEqChecked Sig Γ (naturalTy Sig types))
    (base : Intrinsic.Proves Γ H (predicate.app indZero))
    (step : Intrinsic.Proves Γ H (natStepAt predicate)) :
    Intrinsic.Proves Γ H (predicate.app (repNatural value)) := by
  have universal := repNatural_predicate (H := H) typed value
  have closed := Intrinsic.Proves.forallElim typed
    (.arr InfiniteOps.indKinded .boolTy) (natClosureBody (repNatural value))
    predicate universal
  rw [natClosureBody_open typed (repNatural value) predicate] at closed
  exact impElim typed closed (andIntro typed base step)

/-- Successor is inherited from `ind` and re-abstracted into the guarded
natural subtype.  Closure proofs establish its expected laws later; subtype
formation and the term itself require no nonemptiness premise. -/
def naturalSucc (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    DefEqChecked Sig Γ (naturalTy Sig types) :=
  DefEqChecked.abs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing
    (indSucc.app (repNatural value))

noncomputable def repNatural_zero (typed : TypedCtx Γ) :
    Intrinsic.Proves Γ H (DefEqChecked.eq InfiniteOps.indKinded
      (repNatural (naturalZero (Sig := Sig) (Γ := Γ))) indZero) :=
  Intrinsic.Proves.repAbs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing indZero
    (natPredicateAt indZero) (natPredicateAt_term_eq indZero)
    (natPredicate_zero typed)

noncomputable def repNatural_succ (typed : TypedCtx Γ)
    (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq InfiniteOps.indKinded
      (repNatural (naturalSucc value)) (indSucc.app (repNatural value))) :=
  Intrinsic.Proves.repAbs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing
    (indSucc.app (repNatural value))
    (natPredicateAt (indSucc.app (repNatural value)))
    (natPredicateAt_term_eq (indSucc.app (repNatural value)))
    (natPredicate_succ typed (repNatural value) (repNatural_predicate typed value))

class NaturalOps (Sig : Signature) [SigTyping Sig] where
  nat {types : List Kind} : Ty Sig types
  natKinded {types : List Kind} : Kinded (nat (types := types))
  zero {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    DefEqChecked Sig Γ (nat (types := types))
  succ {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    DefEqChecked Sig Γ (nat (types := types)) →
      DefEqChecked Sig Γ (nat (types := types))

instance (Sig : Signature) [SigTyping Sig] [InfiniteOps Sig] : NaturalOps Sig where
  nat := fun {types} => naturalTy Sig types
  natKinded := fun {types} => naturalTy_kinded (Sig := Sig) (types := types)
  zero := naturalZero
  succ := naturalSucc

end Nucleus.Hol.FamilySub
