import Nucleus.Hol.FamilySub.Basic

/-! # Abstract infinity structure for bootstrapping natural numbers -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

/-- Syntax/operations witnessing a designated infinite type.  This class adds
no proof rule by itself: signatures may provide the operations without
asserting that they satisfy infinity. -/
class InfiniteOps (Sig : Signature) [SigTyping Sig] where
  ind {types : List Kind} : Ty Sig types
  indKinded {types : List Kind} : Kinded (ind (types := types))
  zero {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    Checked Sig Γ (ind (types := types))
  succ {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    Checked Sig Γ (.arr (ind (types := types)) (ind (types := types)))

def indZero {Sig : Signature} [SigTyping Sig] [InfiniteOps Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    DefEqChecked Sig Γ (InfiniteOps.ind (Sig := Sig)) :=
  DefEqChecked.ofRaw InfiniteOps.zero.tm InfiniteOps.zero.typing

def indSucc {Sig : Signature} [SigTyping Sig] [InfiniteOps Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    DefEqChecked Sig Γ (.arr (InfiniteOps.ind (Sig := Sig)) InfiniteOps.ind) :=
  DefEqChecked.ofRaw InfiniteOps.succ.tm InfiniteOps.succ.typing

/-- The proof component of infinity, deliberately independent from its syntax.
An implementation can therefore expose constants without granting rules, or
grant rules for derived terms without adding primitive syntax. -/
class InfiniteRules (Sig : Signature) [SigTyping Sig] [InfiniteOps Sig] where
  succInjective {types : List Kind} {depth : Nat}
    {Γ : BoundCtx Sig types depth} {H : PropCtx Γ}
    (typed : TypedCtx Γ)
    (left right : DefEqChecked Sig Γ (InfiniteOps.ind (Sig := Sig)))
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq InfiniteOps.indKinded
        (indSucc.app left) (indSucc.app right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq InfiniteOps.indKinded left right)
  zeroNeSucc {types : List Kind} {depth : Nat}
    {Γ : BoundCtx Sig types depth} {H : PropCtx Γ}
    (typed : TypedCtx Γ)
    (value : DefEqChecked Sig Γ (InfiniteOps.ind (Sig := Sig))) :
    Intrinsic.Proves Γ H (DefEqChecked.not
      (DefEqChecked.eq InfiniteOps.indKinded indZero (indSucc.app value)))

/-- A convenient bundled view when both operations and their laws are needed. -/
class InfiniteTheory (Sig : Signature) [SigTyping Sig] extends
    InfiniteOps Sig, InfiniteRules Sig

end Nucleus.Hol.FamilySub
