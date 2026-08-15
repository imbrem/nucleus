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

class NaturalRecursionTheory (Sig : Signature) [SigTyping Sig] extends
    NaturalOps Sig, NaturalRules Sig, NaturalRecursorOps Sig,
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
