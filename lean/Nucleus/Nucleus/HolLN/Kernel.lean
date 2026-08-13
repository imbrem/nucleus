import Nucleus.HolLN.TypeSubstitution

/-!
# Ordinary HOL proof certificates

Ordinary term equality has seven constructors: reflexivity, symmetry,
transitivity, application congruence, lambda congruence, beta, and eta.
Intrinsic `Fin` binders make lambda capture impossible; eta additionally
records a locally nameless freshness witness.  The natural-number extension
adds successor congruence.

Entailment has exactly ten constructors: hypothesis, truth, Boolean equality
reflexivity, equality modus ponens, choice, conversion by term equality,
introduction of Boolean equality from term equality, deduction antisymmetry,
`ABS_REP`, and predicate-guarded `REP_ABS`.  The infinity extension adds
successor injectivity and zero-not-successor.  Certificates live in `Type` and
remain inspectable; raw typing stays proof-irrelevant in `Prop`.
-/

namespace Nucleus.HolLN

universe u

inductive EqTm {Base : Type u} : {depth : Nat} -> BoundCtx Base depth ->
    Tm Base depth -> Tm Base depth -> Ty Base -> Type u where
  | refl (typing : HasType Γ t A) : EqTm Γ t t A
  | symm : EqTm Γ t u A -> EqTm Γ u t A
  | trans : EqTm Γ t u A -> EqTm Γ u v A -> EqTm Γ t v A
  | app : EqTm Γ f g (.arr A B) -> EqTm Γ x y A ->
      EqTm Γ (.app f x) (.app g y) B
  | succ : EqTm Γ x y .natTy -> EqTm Γ (.succ x) (.succ y) .natTy
  | lam (hA : Kinded A) : EqTm (extendBound A Γ) t u B ->
      EqTm Γ (.lam A t) (.lam A u) (.arr A B)
  | beta {depth : Nat} {Γ : BoundCtx Base depth}
      (body : Tm Base (depth + 1)) (x : Tm Base depth) (hA : Kinded A)
      (bodyTyping : HasType (extendBound A Γ) body B)
      (argumentTyping : HasType Γ x A)
      (resultTyping : HasType Γ (openBound body x) B) :
      EqTm Γ (.app (.lam A body) x) (openBound body x) B
  | eta (name : Nat) (fresh : Fresh name f)
      (functionTyping : HasType Γ f (.arr A B))
      (etaTyping : HasType Γ (.lam A (.app (weaken f) (.bound 0))) (.arr A B)) :
      EqTm Γ (.lam A (.app (weaken f) (.bound 0))) f (.arr A B)

def TypedHyps {Base : Type u} {depth : Nat}
    (Γ : BoundCtx Base depth) (hypotheses : List (Tm Base depth)) : Prop :=
  ∀ p, p ∈ hypotheses -> HasType Γ p .boolTy

inductive Proves {Base : Type u} {depth : Nat}
    (Γ : BoundCtx Base depth) : List (Tm Base depth) -> Tm Base depth -> Type u where
  | hyp (typed : TypedHyps Γ H) (member : p ∈ H) : Proves Γ H p
  | truth (typed : TypedHyps Γ H) : Proves Γ H (.bool true)
  | eqRefl (typed : TypedHyps Γ H) (hA : Kinded A)
      (hx : HasType Γ x A) : Proves Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType Γ p (.arr A .boolTy))
      (hx : HasType Γ x A) (hy : HasType Γ y A) :
      Proves Γ H (.eq A x y) -> Proves Γ H (.app p x) ->
      Proves Γ H (.app p y)
  | choice (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType Γ p (.arr A .boolTy)) (hx : HasType Γ x A) :
      Proves Γ H (.app p x) -> Proves Γ H (.app p (.eps A p))
  | convert (typed : TypedHyps Γ H) :
      EqTm Γ p q .boolTy -> Proves Γ H p -> Proves Γ H q
  | eqOfEqTm (typed : TypedHyps Γ H) (hA : Kinded A) :
      EqTm Γ x y A -> Proves Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Γ H)
      (hp : HasType Γ p .boolTy) (hq : HasType Γ q .boolTy)
      (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (q :: H)) :
      Proves Γ (p :: H) q -> Proves Γ (q :: H) p ->
      Proves Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasType Γ x (.sub A p)) :
      Proves Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasType Γ x A)
      (predicateTyping : HasType Γ (instantiateOne p x) .boolTy) :
      Proves Γ H (instantiateOne p x) ->
      Proves Γ H (.eq A (.rep A p (.abs A p x)) x)
  | succInjective (typed : TypedHyps Γ H)
      (hx : HasType Γ x .natTy) (hy : HasType Γ y .natTy) :
      Proves Γ H (.eq .natTy (.succ x) (.succ y)) ->
      Proves Γ H (.eq .natTy x y)
  | zeroNotSucc (typed : TypedHyps Γ H)
      (hx : HasType Γ x .natTy) :
      Proves Γ H
        (.eq .boolTy (.eq .natTy .zero (.succ x)) (.bool false))

end Nucleus.HolLN
