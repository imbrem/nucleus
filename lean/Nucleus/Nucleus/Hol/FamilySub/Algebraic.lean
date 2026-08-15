import Nucleus.Hol.FamilySub.ProductLaws
import Nucleus.Hol.FamilySub.CoproductLaws

/-! # Reusable product and coproduct interfaces -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

universe u

/-- Operations needed to use binary products independently of their concrete
Church/subtype representation. -/
class ProductOps (Sig : Signature) [SigTyping Sig] where
  product {types : List Kind} {A B : Ty Sig types} :
    Kinded A → Kinded B → Ty Sig types
  productKinded {types : List Kind} {A B : Ty Sig types}
    (hA : Kinded A) (hB : Kinded B) : Kinded (product hA hB)
  pair {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ A → DefEqChecked Sig Γ B → DefEqChecked Sig Γ (product hA hB)
  fst {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ (product hA hB) → DefEqChecked Sig Γ A
  snd {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ (product hA hB) → DefEqChecked Sig Γ B

/-- Proof laws for a product implementation.  Keeping these separate permits
syntax-only signatures and rule-only extensions. -/
class ProductRules (Sig : Signature) [SigTyping Sig] [ProductOps Sig] where
  fstPair {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (a : DefEqChecked Sig Γ A)
    (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA
      (ProductOps.fst hA hB (ProductOps.pair hA hB a b)) a)
  sndPair {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (a : DefEqChecked Sig Γ A)
    (b : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB
      (ProductOps.snd hA hB (ProductOps.pair hA hB a b)) b)
  eta {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (ProductOps.product hA hB)) :
    Intrinsic.Proves Γ H (DefEqChecked.eq (ProductOps.productKinded hA hB) value
      (ProductOps.pair hA hB (ProductOps.fst hA hB value) (ProductOps.snd hA hB value)))
  ext {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B)
    (left right : DefEqChecked Sig Γ (ProductOps.product hA hB))
    (first : Intrinsic.Proves Γ H
      (DefEqChecked.eq hA (ProductOps.fst hA hB left) (ProductOps.fst hA hB right)))
    (second : Intrinsic.Proves Γ H
      (DefEqChecked.eq hB (ProductOps.snd hA hB left) (ProductOps.snd hA hB right))) :
    Intrinsic.Proves Γ H
      (DefEqChecked.eq (ProductOps.productKinded hA hB) left right)

/-- Operations needed to use binary coproducts independently of their concrete
Church/subtype representation. -/
class CoproductOps (Sig : Signature) [SigTyping Sig] where
  coproduct {types : List Kind} {A B : Ty Sig types} :
    Kinded A → Kinded B → Ty Sig types
  coproductKinded {types : List Kind} {A B : Ty Sig types}
    (hA : Kinded A) (hB : Kinded B) : Kinded (coproduct hA hB)
  inl {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ A → DefEqChecked Sig Γ (coproduct hA hB)
  inr {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B : Ty Sig types} (hA : Kinded A) (hB : Kinded B) :
    DefEqChecked Sig Γ B → DefEqChecked Sig Γ (coproduct hA hB)
  case {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {A B C : Ty Sig types} (hA : Kinded A) (hB : Kinded B) (hC : Kinded C) :
    DefEqChecked Sig Γ (.arr A C) → DefEqChecked Sig Γ (.arr B C) →
    DefEqChecked Sig Γ (coproduct hA hB) → DefEqChecked Sig Γ C

/-- Core computation and no-confusion rules expected of coproducts. -/
class CoproductRules (Sig : Signature) [SigTyping Sig] [CoproductOps Sig] where
  caseInl {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B C : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ A) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hC
      (CoproductOps.case hA hB hC left right (CoproductOps.inl hA hB value))
      (left.app value))
  caseInr {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B C : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (hC : Kinded C)
    (left : DefEqChecked Sig Γ (.arr A C)) (right : DefEqChecked Sig Γ (.arr B C))
    (value : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hC
      (CoproductOps.case hA hB hC left right (CoproductOps.inr hA hB value))
      (right.app value))
  inlInjective {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (left right : DefEqChecked Sig Γ A)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (CoproductOps.coproductKinded hA hB)
        (CoproductOps.inl hA hB left) (CoproductOps.inl hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hA left right)
  inrInjective {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (left right : DefEqChecked Sig Γ B)
    (equality : Intrinsic.Proves Γ H
      (DefEqChecked.eq (CoproductOps.coproductKinded hA hB)
        (CoproductOps.inr hA hB left) (CoproductOps.inr hA hB right))) :
    Intrinsic.Proves Γ H (DefEqChecked.eq hB left right)
  inlNeInr {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {H : PropCtx Γ} {A B : Ty Sig types} (typed : TypedCtx Γ)
    (hA : Kinded A) (hB : Kinded B) (left : DefEqChecked Sig Γ A)
    (right : DefEqChecked Sig Γ B) :
    Intrinsic.Proves Γ H (DefEqChecked.not
      (DefEqChecked.eq (CoproductOps.coproductKinded hA hB)
        (CoproductOps.inl hA hB left) (CoproductOps.inr hA hB right)))

instance (Sig : Signature) [SigTyping Sig] : ProductOps Sig where
  product := productTy
  productKinded := productTy_kinded
  pair := pairChecked
  fst := fstChecked
  snd := sndChecked

instance (Sig : Signature) [SigTyping Sig] : ProductRules Sig where
  fstPair := fst_pair
  sndPair := snd_pair
  eta := product_eta
  ext := product_ext

instance (Sig : Signature) [SigTyping Sig] : CoproductOps Sig where
  coproduct := coproductTy
  coproductKinded := coproductTy_kinded
  inl := inlChecked
  inr := inrChecked
  case := caseChecked

noncomputable instance (Sig : Signature) [SigTyping Sig] : CoproductRules Sig where
  caseInl := case_inl
  caseInr := case_inr
  inlInjective := inl_injective
  inrInjective := inr_injective
  inlNeInr := inl_ne_inr

end Nucleus.Hol.FamilySub
