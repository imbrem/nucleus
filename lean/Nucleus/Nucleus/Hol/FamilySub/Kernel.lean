import Nucleus.Hol.FamilySub.Substitution

/-! # Proof certificates for type-variable-scoped HOL -/

namespace Nucleus.Hol.FamilySub

universe u
set_option relaxedAutoImplicit true

inductive EqTm {Sig : Signature} [SigTyping Sig] : {types : List Kind} → {depth : Nat} →
    BoundCtx Sig types depth → Tm Sig types depth → Tm Sig types depth → Ty Sig types →
    Type u where
  | refl (typing : HasTypeDefEq Γ t A) : EqTm Γ t t A
  | symm : EqTm Γ t u A → EqTm Γ u t A
  | trans : EqTm Γ t u A → EqTm Γ u v A → EqTm Γ t v A
  | app : EqTm Γ f g (.arr A B) → EqTm Γ x y A →
      EqTm Γ (.app f x) (.app g y) B
  | lam (hA : Kinded A) : EqTm (extendBound A Γ) t u B →
      EqTm Γ (.lam A t) (.lam A u) (.arr A B)
  | beta (body : Tm Sig types (depth + 1)) (x : Tm Sig types depth) (hA : Kinded A)
      (bodyTyping : HasTypeDefEq (extendBound A Γ) body B)
      (argumentTyping : HasTypeDefEq Γ x A)
      (resultTyping : HasTypeDefEq Γ (openBound body x) B) :
      EqTm Γ (.app (.lam A body) x) (openBound body x) B
  | eta (name : Nat) (fresh : Fresh name f)
      (functionTyping : HasTypeDefEq Γ f (.arr A B))
      (etaTyping : HasTypeDefEq Γ (.lam A (.app (weaken f) (.bv 0))) (.arr A B)) :
      EqTm Γ (.lam A (.app (weaken f) (.bv 0))) f (.arr A B)

def TypedHyps {Sig : Signature} [SigTyping Sig] (Γ : BoundCtx Sig types depth)
    (hypotheses : List (Tm Sig types depth)) : Prop :=
  ∀ p, p ∈ hypotheses → HasTypeDefEq Γ p .boolTy

inductive Proves {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) : List (Tm Sig types depth) → Tm Sig types depth →
    Type u where
  | hyp (typed : TypedHyps Γ H) (member : p ∈ H) : Proves Γ H p
  | truth (typed : TypedHyps Γ H) : Proves Γ H (.bool true)
  | eqRefl (typed : TypedHyps Γ H) (hA : Kinded A) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A)
      (hy : HasTypeDefEq Γ y A) :
      Proves Γ H (.eq A x y) → Proves Γ H (.app p x) → Proves Γ H (.app p y)
  | choice (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.app p x) → Proves Γ H (.app p (.eps A p))
  | convert (typed : TypedHyps Γ H) : EqTm Γ p q .boolTy →
      Proves Γ H p → Proves Γ H q
  | eqOfEqTm (typed : TypedHyps Γ H) (hA : Kinded A) :
      EqTm Γ x y A → Proves Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy)
      (hq : HasTypeDefEq Γ q .boolTy) (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (q :: H)) : Proves Γ (p :: H) q →
      Proves Γ (q :: H) p → Proves Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq (extendBound A emptyBound) p .boolTy)
      (hx : HasTypeDefEq Γ x (.sub A p)) :
      Proves Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq (extendBound A emptyBound) p .boolTy)
      (hx : HasTypeDefEq Γ x A)
      (predicateTyping : HasTypeDefEq Γ (instantiateOne p x) .boolTy) :
      Proves Γ H (instantiateOne p x) →
      Proves Γ H (.eq A (.rep A p (.abs A p x)) x)
  /-- Every representation of a subtype value satisfies its predicate.  The
  witness premise is the HOL type-definition side condition and prevents an
  empty predicate from manufacturing an inhabited type. -/
  | repPred (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq (extendBound A emptyBound) p .boolTy)
      (witnessTyping : HasTypeDefEq Γ witness A)
      (witnessPredicateTyping : HasTypeDefEq Γ (instantiateOne p witness) .boolTy)
      (subtypeTyping : HasTypeDefEq Γ x (.sub A p))
      (representationPredicateTyping :
        HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy) :
      Proves Γ H (instantiateOne p witness) →
      Proves Γ H (instantiateOne p (.rep A p x))

end Nucleus.Hol.FamilySub
