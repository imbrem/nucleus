import Nucleus.Hol.FamilySub.Natural

/-! # Abstract natural recursion and generic arithmetic syntax -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] [NaturalOps Sig]
  {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
  {H : PropCtx Γ} {A : Ty Sig types}

abbrev NatTm := DefEqChecked Sig Γ (NaturalOps.nat (Sig := Sig))

def naturalOfNat : Nat → NatTm (Sig := Sig) (Γ := Γ)
  | 0 => NaturalOps.zero
  | n + 1 => NaturalOps.succ (naturalOfNat n)

instance (n : Nat) : OfNat (NatTm (Sig := Sig) (Γ := Γ)) n where
  ofNat := naturalOfNat n

/-- Syntax of primitive recursion, independent of its implementation.  The
step receives the predecessor and the recursively computed accumulator. -/
class NaturalRecursorOps (Sig : Signature) [SigTyping Sig] [NaturalOps Sig] where
  recurse {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A : Ty Sig types} (hA : Kinded A)
    (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ
      (.arr NaturalOps.nat (.arr A A)))
    (value : DefEqChecked Sig Γ NaturalOps.nat) :
    DefEqChecked Sig Γ A

/-- The two computation laws are separate from recursor syntax. -/
class NaturalRecursorRules (Sig : Signature) [SigTyping Sig] [NaturalOps Sig]
    [NaturalRecursorOps Sig] where
  recZero {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A : Ty Sig types} (typed : TypedCtx Γ) (hA : Kinded A)
    (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA
      (NaturalRecursorOps.recurse hA base step NaturalOps.zero) base)
  recSucc {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A : Ty Sig types} (typed : TypedCtx Γ) (hA : Kinded A)
    (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (value : DefEqChecked Sig Γ NaturalOps.nat) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA
      (NaturalRecursorOps.recurse hA base step (NaturalOps.succ value))
      ((step.app value).app (NaturalRecursorOps.recurse hA base step value)))

def recursorStepBody (hA : Kinded A) (_base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (function : DefEqChecked Sig Γ (.arr NaturalOps.nat A)) :
    BoolTm (extendBound NaturalOps.nat Γ) :=
  let value := DefEqChecked.bv (Sig := Sig) (types := types)
    (NaturalOps.natKinded (Sig := Sig)) 0 rfl
  let result := function.weaken.app value
  DefEqChecked.eq hA (function.weaken.app (NaturalOps.succ value))
    ((step.weaken.app value).app result)

def recursorStep (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (function : DefEqChecked Sig Γ (.arr NaturalOps.nat A)) : BoolTm Γ :=
  DefEqChecked.forallTm NaturalOps.natKinded
    (recursorStepBody hA base step function)

def recursorSpec (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (function : DefEqChecked Sig Γ (.arr NaturalOps.nat A)) : BoolTm Γ :=
  DefEqChecked.and
    (DefEqChecked.eq hA (function.app NaturalOps.zero) base)
    (recursorStep hA base step function)

def recursorPredicateBody (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A))) :
    BoolTm (extendBound (.arr NaturalOps.nat A) Γ) :=
  let hFunction : Kinded (.arr NaturalOps.nat A) :=
    .arr NaturalOps.natKinded hA
  let function := DefEqChecked.bv (Sig := Sig) (types := types) hFunction 0 rfl
  recursorSpec hA base.weaken step.weaken function

def recursorPredicate (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A))) :
    DefEqChecked Sig Γ (.arr (.arr NaturalOps.nat A) .boolTy) :=
  DefEqChecked.lam (.arr NaturalOps.natKinded hA)
    (recursorPredicateBody hA base step)

def chosenRecursor (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A))) :
    DefEqChecked Sig Γ (.arr NaturalOps.nat A) :=
  DefEqChecked.eps (.arr NaturalOps.natKinded hA)
    (recursorPredicate hA base step)

def graphRecurse (hA : Kinded A) (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (value : DefEqChecked Sig Γ NaturalOps.nat) : DefEqChecked Sig Γ A :=
  (chosenRecursor hA base step).app value

instance (Sig : Signature) [SigTyping Sig] [NaturalOps Sig] :
    NaturalRecursorOps Sig where
  recurse := graphRecurse

/-- The sole existence obligation for choice-defined recursion.  A graph
construction supplies this certificate; choice then yields both beta laws. -/
class NaturalRecursorExistence (Sig : Signature) [SigTyping Sig] [NaturalOps Sig] where
  chosenSpec {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A : Ty Sig types} (typed : TypedCtx Γ) (hA : Kinded A)
    (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A))) :
    Intrinsic.Proves Γ H (recursorSpec hA base step
      (chosenRecursor hA base step))

theorem recursorStepBody_open [NaturalSubstitutionLaws Sig]
    (typed : TypedCtx Γ) (hA : Kinded A)
    (base : DefEqChecked Sig Γ A)
    (step : DefEqChecked Sig Γ (.arr NaturalOps.nat (.arr A A)))
    (function : DefEqChecked Sig Γ (.arr NaturalOps.nat A))
    (value : DefEqChecked Sig Γ NaturalOps.nat) :
    (recursorStepBody hA base step function).openBound typed value =
      DefEqChecked.eq hA (function.app (NaturalOps.succ value))
        ((step.app value).app (function.app value)) := by
  apply DefEqChecked.ext
  simp [recursorStepBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.app, DefEqChecked.bv, DefEqChecked.weaken,
    FamilySub.openBound, instantiate]
  simpa [DefEqChecked.openBound, FamilySub.openBound, DefEqChecked.bv,
    instantiate] using congrArg DefEqChecked.tm
      (NaturalSubstitutionLaws.succOpen typed
        (DefEqChecked.bv NaturalOps.natKinded 0 rfl) value)

noncomputable instance (Sig : Signature) [SigTyping Sig] [NaturalOps Sig]
    [NaturalSubstitutionLaws Sig] [NaturalRecursorExistence Sig] :
    NaturalRecursorRules Sig where
  recZero := by
    intro types depth Γ H A typed hA base step
    exact andElimLeft typed (NaturalRecursorExistence.chosenSpec typed hA base step)
  recSucc := by
    intro types depth Γ H A typed hA base step value
    have specification := NaturalRecursorExistence.chosenSpec
      (H := H) typed hA base step
    have universally := andElimRight typed specification
    have specialized := Intrinsic.Proves.forallElim typed NaturalOps.natKinded
      (recursorStepBody hA base step (chosenRecursor hA base step)) value universally
    rw [recursorStepBody_open typed hA base step (chosenRecursor hA base step) value]
      at specialized
    exact specialized

class NaturalRecursionTheory (Sig : Signature) [SigTyping Sig] extends
    NaturalOps Sig, NaturalRules Sig, NaturalSubstitutionLaws Sig,
      NaturalRecursorOps Sig,
      NaturalRecursorRules Sig

def naturalSuccBody :
    DefEqChecked Sig (extendBound NaturalOps.nat Γ) NaturalOps.nat :=
  NaturalOps.succ (DefEqChecked.bv NaturalOps.natKinded 0 rfl)

def naturalSuccFunction :
    DefEqChecked Sig Γ (.arr NaturalOps.nat NaturalOps.nat) :=
  DefEqChecked.lam NaturalOps.natKinded naturalSuccBody

def naturalAddStepBody : DefEqChecked Sig
    (extendBound NaturalOps.nat (extendBound NaturalOps.nat Γ))
    NaturalOps.nat :=
  NaturalOps.succ (DefEqChecked.bv NaturalOps.natKinded 0 rfl)

/-- `fun _ accumulator => succ accumulator`. -/
def naturalAddStep : DefEqChecked Sig Γ
    (.arr NaturalOps.nat (.arr NaturalOps.nat NaturalOps.nat)) :=
  DefEqChecked.lam NaturalOps.natKinded
    (DefEqChecked.lam NaturalOps.natKinded naturalAddStepBody)

def naturalAdd [NaturalRecursorOps Sig] (left right : NatTm (Sig := Sig) (Γ := Γ)) :
    NatTm (Sig := Sig) (Γ := Γ) :=
  NaturalRecursorOps.recurse NaturalOps.natKinded left naturalAddStep right

def naturalMulStepBody [NaturalRecursorOps Sig]
    (multiplicand : NatTm (Sig := Sig) (Γ := Γ)) : DefEqChecked Sig
    (extendBound NaturalOps.nat (extendBound NaturalOps.nat Γ)) NaturalOps.nat :=
  let accumulator := DefEqChecked.bv (Sig := Sig) (types := types)
    (NaturalOps.natKinded (Sig := Sig)) 0 rfl
  naturalAdd multiplicand.weaken.weaken accumulator

/-- `fun _ accumulator => multiplicand + accumulator`. -/
def naturalMulStep [NaturalRecursorOps Sig] (multiplicand : NatTm (Sig := Sig) (Γ := Γ)) :
    DefEqChecked Sig Γ
      (.arr NaturalOps.nat (.arr NaturalOps.nat NaturalOps.nat)) :=
  DefEqChecked.lam NaturalOps.natKinded
    (DefEqChecked.lam NaturalOps.natKinded (naturalMulStepBody multiplicand))

def naturalMul [NaturalRecursorOps Sig] (left right : NatTm (Sig := Sig) (Γ := Γ)) :
    NatTm (Sig := Sig) (Γ := Γ) :=
  NaturalRecursorOps.recurse NaturalOps.natKinded NaturalOps.zero
    (naturalMulStep left) right

instance [NaturalRecursorOps Sig] :
    HAdd (NatTm (Sig := Sig) (Γ := Γ)) (NatTm (Sig := Sig) (Γ := Γ))
      (NatTm (Sig := Sig) (Γ := Γ)) where
  hAdd := naturalAdd

instance [NaturalRecursorOps Sig] :
    HMul (NatTm (Sig := Sig) (Γ := Γ)) (NatTm (Sig := Sig) (Γ := Γ))
      (NatTm (Sig := Sig) (Γ := Γ)) where
  hMul := naturalMul

end Nucleus.Hol.FamilySub
