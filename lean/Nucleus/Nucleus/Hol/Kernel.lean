import Nucleus.Hol.Substitution

/-! # Complete core HOL proof certificates over sorted signatures -/

namespace Nucleus.Hol

universe u

inductive EqTm {Sig : Signature} [SigTyping Sig] : {depth : Nat} →
    BoundCtx Sig depth → Tm Sig depth → Tm Sig depth → Ty Sig → Type u where
  | refl (typing : HasType Γ t A) : EqTm Γ t t A
  | symm : EqTm Γ t u A → EqTm Γ u t A
  | trans : EqTm Γ t u A → EqTm Γ u v A → EqTm Γ t v A
  | app : EqTm Γ f g (.arr A B) → EqTm Γ x y A →
      EqTm Γ (.app f x) (.app g y) B
  | lam (hA : Kinded A) : EqTm (extendBound A Γ) t u B →
      EqTm Γ (.lam A t) (.lam A u) (.arr A B)
  | beta {depth : Nat} {Γ : BoundCtx Sig depth} (body : Tm Sig (depth + 1))
      (x : Tm Sig depth) (hA : Kinded A)
      (bodyTyping : HasType (extendBound A Γ) body B)
      (argumentTyping : HasType Γ x A)
      (resultTyping : HasType Γ (openBound body x) B) :
      EqTm Γ (.app (.lam A body) x) (openBound body x) B
  | eta (name : Nat) (fresh : Fresh name f)
      (functionTyping : HasType Γ f (.arr A B))
      (etaTyping : HasType Γ (.lam A (.app (weaken f) (.bv 0))) (.arr A B)) :
      EqTm Γ (.lam A (.app (weaken f) (.bv 0))) f (.arr A B)

def TypedHyps {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) (hypotheses : List (Tm Sig depth)) : Prop :=
  ∀ p, p ∈ hypotheses → HasType Γ p .boolTy

inductive Proves {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) : List (Tm Sig depth) → Tm Sig depth → Type u where
  | hyp (typed : TypedHyps Γ H) (member : p ∈ H) : Proves Γ H p
  | truth (typed : TypedHyps Γ H) : Proves Γ H (.bool true)
  | eqRefl (typed : TypedHyps Γ H) (hA : Kinded A)
      (hx : HasType Γ x A) : Proves Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType Γ p (.arr A .boolTy)) (hx : HasType Γ x A)
      (hy : HasType Γ y A) : Proves Γ H (.eq A x y) → Proves Γ H (.app p x) →
      Proves Γ H (.app p y)
  | choice (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType Γ p (.arr A .boolTy)) (hx : HasType Γ x A) :
      Proves Γ H (.app p x) → Proves Γ H (.app p (.eps A p))
  | convert (typed : TypedHyps Γ H) : EqTm Γ p q .boolTy →
      Proves Γ H p → Proves Γ H q
  | eqOfEqTm (typed : TypedHyps Γ H) (hA : Kinded A) :
      EqTm Γ x y A → Proves Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Γ H) (hp : HasType Γ p .boolTy)
      (hq : HasType Γ q .boolTy) (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (q :: H)) : Proves Γ (p :: H) q →
      Proves Γ (q :: H) p → Proves Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasType Γ x (.sub A p)) :
      Proves Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy) (hx : HasType Γ x A)
      (predicateTyping : HasType Γ (instantiateOne p x) .boolTy) :
      Proves Γ H (instantiateOne p x) →
      Proves Γ H (.eq A (.rep A p (.abs A p x)) x)

end Nucleus.Hol
