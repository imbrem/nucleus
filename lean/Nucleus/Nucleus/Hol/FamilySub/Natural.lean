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
    Checked.imp (pAtY.app y) (pAtY.app (InfiniteOps.succ.app y))
  let step : Checked Sig Γp .boolTy := Checked.forallTm hI stepBody
  let p : Checked Sig Γp predTy := Checked.bv hPred 0 rfl
  let x : Checked Sig Γp I := Checked.bv hI 1 rfl
  let base : Checked Sig Γp .boolTy := p.app InfiniteOps.zero
  let closed : Checked Sig Γp .boolTy := Checked.and base step
  let contains : Checked Sig Γp .boolTy := p.app x
  exact Checked.forallTm hPred (Checked.imp closed contains)

/-- Naturals are the guarded subtype of `ind` selected by `natPredicate`. -/
def naturalTy (Sig : Signature) [SigTyping Sig] [InfiniteOps Sig]
    (types : List Kind) : Ty Sig types :=
  .sub InfiniteOps.ind (natPredicate (Sig := Sig) (types := types)).tm

theorem naturalTy_kinded : Kinded (naturalTy Sig types) :=
  .sub InfiniteOps.indKinded (natPredicate (Sig := Sig) (types := types)).typing

def naturalZero : DefEqChecked Sig Γ (naturalTy Sig types) :=
  DefEqChecked.abs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing indZero

def repNatural (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    DefEqChecked Sig Γ InfiniteOps.ind :=
  DefEqChecked.rep InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing value

/-- Successor is inherited from `ind` and re-abstracted into the guarded
natural subtype.  Closure proofs establish its expected laws later; subtype
formation and the term itself require no nonemptiness premise. -/
def naturalSucc (value : DefEqChecked Sig Γ (naturalTy Sig types)) :
    DefEqChecked Sig Γ (naturalTy Sig types) :=
  DefEqChecked.abs InfiniteOps.indKinded
    (natPredicate (Sig := Sig) (types := types)).tm
    (natPredicate (Sig := Sig) (types := types)).typing
    (indSucc.app (repNatural value))

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
