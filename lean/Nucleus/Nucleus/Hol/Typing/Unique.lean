import Nucleus.Hol.Signature

/-! # Uniqueness of typing

Typing is relational in the base interface.  This file isolates the optional
property needed by signatures whose raw terms have a unique type.
-/

namespace Nucleus.Hol

universe u

class UniqueSigTyping (Sig : Signature) [SigTyping Sig] : Prop where
  unique {symbol : Sig .tm} {A B : Ty Sig} :
    SigTyping.HasType symbol A → SigTyping.HasType symbol B → A = B

theorem Checks.unique {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    {sort : HolSort} {depth : Nat} {Γ : BoundCtx Sig depth}
    {expr : Expr Sig sort depth} {c d : Classification Sig sort}
    (hc : Checks Γ expr c) (hd : Checks Γ expr d) : c = d := by
  induction hc with
  | primFam => cases hd; rfl
  | primTm rule =>
      cases hd with
      | primTm rule' => exact congrArg Classification.tm (UniqueSigTyping.unique rule rule')
  | boolTy => cases hd; rfl
  | arr => cases hd; rfl
  | tyApp => cases hd; rfl
  | sub => cases hd; rfl
  | bv hK lookup =>
      cases hd with
      | bv hK' lookup' => exact congrArg Classification.tm (lookup.symm.trans lookup')
  | fv => cases hd; rfl
  | app hf hx ihf ihx =>
      cases hd with
      | app hf' hx' =>
          cases ihf hf'
          rfl
  | lam body hK hb ihK ihb =>
      cases hd with
      | lam _ _ hb' =>
          cases ihb hb'
          rfl
  | bool => cases hd; rfl
  | eq => cases hd; rfl
  | eps => cases hd; rfl
  | abs => cases hd; rfl
  | rep => cases hd; rfl

theorem HasType.unique {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} {tm : Tm Sig depth} {A B : Ty Sig}
    (hA : HasType Γ tm A) (hB : HasType Γ tm B) : A = B := by
  exact Classification.tm.inj (Checks.unique hA hB)

instance (Sig : Signature) [SigTyping Sig] [FunctionalSigTyping Sig] :
    UniqueSigTyping Sig where
  unique hA hB :=
    (FunctionalSigTyping.hasType_iff.mp hA).trans
      (FunctionalSigTyping.hasType_iff.mp hB).symm

end Nucleus.Hol
