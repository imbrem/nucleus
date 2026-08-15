import Nucleus.Hol.FamilySub.Basic

/-! # Canonical nonempty finite types -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {C : Ty Sig types}

/-- A finite type bundled with its kinding derivation, permitting structural
recursion even though the coproduct construction consumes kinding evidence. -/
def finSuccData (Sig : Signature) [SigTyping Sig] (types : List Kind) :
    (n : Nat) → {A : Ty Sig types // Kinded A}
  | 0 => ⟨unitTy Sig types, unitTy_kinded⟩
  | n + 1 =>
      let previous := finSuccData Sig types n
      ⟨coproductTy unitTy_kinded previous.property,
        coproductTy_kinded unitTy_kinded previous.property⟩

/-- `finSuccTy n` has cardinality `n + 1`.  HOL has no empty type, so this is
the canonical finite-number family available without adding partial types. -/
def finSuccTy (Sig : Signature) [SigTyping Sig] (types : List Kind) (n : Nat) :
    Ty Sig types := (finSuccData Sig types n).1

theorem finSuccTy_kinded (n : Nat) : Kinded (finSuccTy Sig types n) :=
  (finSuccData Sig types n).2

/-- The first element of every nonempty finite type. -/
def finZero : (n : Nat) → DefEqChecked Sig Γ (finSuccTy Sig types n)
  | 0 => unitStar
  | n + 1 => inlChecked unitTy_kinded (finSuccTy_kinded n) unitStar

/-- Embed `Fin (n+1)` as the successor portion of `Fin (n+2)`. -/
def finSucc (n : Nat) (value : DefEqChecked Sig Γ (finSuccTy Sig types n)) :
    DefEqChecked Sig Γ (finSuccTy Sig types (n + 1)) :=
  inrChecked unitTy_kinded (finSuccTy_kinded n) value

/-- Case analysis for the decomposition `Fin (n+2) = 1 + Fin (n+1)`. -/
def finSuccCase (n : Nat) (hC : Kinded C) (zero : DefEqChecked Sig Γ C)
    (succ : DefEqChecked Sig Γ (.arr (finSuccTy Sig types n) C))
    (value : DefEqChecked Sig Γ (finSuccTy Sig types (n + 1))) :
    DefEqChecked Sig Γ C :=
  optionCase (finSuccTy_kinded n) hC zero succ value

noncomputable def finSuccCase_zero (typed : TypedCtx Γ) (n : Nat)
    (hC : Kinded C) (zero : DefEqChecked Sig Γ C)
    (succ : DefEqChecked Sig Γ (.arr (finSuccTy Sig types n) C)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hC
      (finSuccCase n hC zero succ (finZero (n + 1))) zero) :=
  optionCase_none typed (finSuccTy_kinded n) hC zero succ

noncomputable def finSuccCase_succ (typed : TypedCtx Γ) (n : Nat)
    (hC : Kinded C) (zero : DefEqChecked Sig Γ C)
    (succ : DefEqChecked Sig Γ (.arr (finSuccTy Sig types n) C))
    (value : DefEqChecked Sig Γ (finSuccTy Sig types n)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hC
      (finSuccCase n hC zero succ (finSucc n value)) (succ.app value)) :=
  optionCase_some typed (finSuccTy_kinded n) hC zero succ value

noncomputable def finSucc_injective (typed : TypedCtx Γ) (n : Nat)
    (left right : DefEqChecked Sig Γ (finSuccTy Sig types n))
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (finSuccTy_kinded (n + 1))
        (finSucc n left) (finSucc n right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq (finSuccTy_kinded n) left right) :=
  optionSome_injective typed (finSuccTy_kinded n) left right equality

noncomputable def finZero_ne_succ (typed : TypedCtx Γ) (n : Nat)
    (value : DefEqChecked Sig Γ (finSuccTy Sig types n)) :
    Intrinsic.Proves Γ H (DefEqChecked.not
      (DefEqChecked.eq (finSuccTy_kinded (n + 1))
        (finZero (n + 1)) (finSucc n value))) :=
  optionNone_ne_some typed (finSuccTy_kinded n) value

/-- Abstract interface for a nonempty finite-number family. -/
class FiniteSuccOps (Sig : Signature) [SigTyping Sig] where
  fin {types : List Kind} : Nat → Ty Sig types
  finKinded {types : List Kind} (n : Nat) : Kinded (fin (types := types) n)
  zero {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} (n : Nat) :
    DefEqChecked Sig Γ (fin (types := types) n)
  succ {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} (n : Nat) :
    DefEqChecked Sig Γ (fin (types := types) n) →
      DefEqChecked Sig Γ (fin (types := types) (n + 1))

instance (Sig : Signature) [SigTyping Sig] : FiniteSuccOps Sig where
  fin := fun {types} => finSuccTy Sig types
  finKinded := finSuccTy_kinded
  zero := finZero
  succ := finSucc

end Nucleus.Hol.FamilySub
