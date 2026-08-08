import Nucleus.HolLN.Typing

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

inductive EqTm {Base : Type u} (Δ : FreeCtx Base) :
    {depth : Nat} -> BoundCtx Base depth ->
    Tm Base depth -> Tm Base depth -> Ty Base -> Type u where
  | refl (typing : HasType Δ Γ t A) : EqTm Δ Γ t t A
  | symm : EqTm Δ Γ t u A -> EqTm Δ Γ u t A
  | trans : EqTm Δ Γ t u A -> EqTm Δ Γ u v A -> EqTm Δ Γ t v A
  | app : EqTm Δ Γ f g (.arr A B) -> EqTm Δ Γ x y A ->
      EqTm Δ Γ (.app f x) (.app g y) B
  | succ : EqTm Δ Γ x y .natTy -> EqTm Δ Γ (.succ x) (.succ y) .natTy
  | lam (hA : Kinded A) : EqTm Δ (extendBound A Γ) t u B ->
      EqTm Δ Γ (.lam A t) (.lam A u) (.arr A B)
  | beta {depth : Nat} {Γ : BoundCtx Base depth}
      (body : Tm Base (depth + 1)) (x : Tm Base depth) (hA : Kinded A)
      (bodyTyping : HasType Δ (extendBound A Γ) body B)
      (argumentTyping : HasType Δ Γ x A)
      (resultTyping : HasType Δ Γ (openBound body x) B) :
      EqTm Δ Γ (.app (.lam A body) x) (openBound body x) B
  | eta (name : Nat) (fresh : Fresh name f)
      (functionTyping : HasType Δ Γ f (.arr A B))
      (etaTyping : HasType Δ Γ (.lam A (.app (weaken f) (.bound 0))) (.arr A B)) :
      EqTm Δ Γ (.lam A (.app (weaken f) (.bound 0))) f (.arr A B)

def TypedHyps {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) (hypotheses : List (Tm Base depth)) : Prop :=
  ∀ p, p ∈ hypotheses -> HasType Δ Γ p .boolTy

inductive Proves {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) : List (Tm Base depth) -> Tm Base depth -> Type u where
  | hyp (typed : TypedHyps Δ Γ H) (member : p ∈ H) : Proves Δ Γ H p
  | truth (typed : TypedHyps Δ Γ H) : Proves Δ Γ H (.bool true)
  | eqRefl (typed : TypedHyps Δ Γ H) (hA : Kinded A)
      (hx : HasType Δ Γ x A) : Proves Δ Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Δ Γ H) (hA : Kinded A)
      (hp : HasType Δ Γ p (.arr A .boolTy))
      (hx : HasType Δ Γ x A) (hy : HasType Δ Γ y A) :
      Proves Δ Γ H (.eq A x y) -> Proves Δ Γ H (.app p x) ->
      Proves Δ Γ H (.app p y)
  | choice (typed : TypedHyps Δ Γ H) (hA : Kinded A)
      (hp : HasType Δ Γ p (.arr A .boolTy)) (hx : HasType Δ Γ x A) :
      Proves Δ Γ H (.app p x) -> Proves Δ Γ H (.app p (.eps A p))
  | convert (typed : TypedHyps Δ Γ H) :
      EqTm Δ Γ p q .boolTy -> Proves Δ Γ H p -> Proves Δ Γ H q
  | eqOfEqTm (typed : TypedHyps Δ Γ H) (hA : Kinded A) :
      EqTm Δ Γ x y A -> Proves Δ Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Δ Γ H)
      (hp : HasType Δ Γ p .boolTy) (hq : HasType Δ Γ q .boolTy)
      (leftTyped : TypedHyps Δ Γ (p :: H))
      (rightTyped : TypedHyps Δ Γ (q :: H)) :
      Proves Δ Γ (p :: H) q -> Proves Δ Γ (q :: H) p ->
      Proves Δ Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Δ Γ H) (hA : Kinded A)
      (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy)
      (hx : HasType Δ Γ x (.sub A p)) :
      Proves Δ Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Δ Γ H) (hA : Kinded A)
      (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy)
      (hx : HasType Δ Γ x A)
      (predicateTyping : HasType Δ Γ (instantiateOne p x) .boolTy) :
      Proves Δ Γ H (instantiateOne p x) ->
      Proves Δ Γ H (.eq A (.rep A p (.abs A p x)) x)
  | succInjective (typed : TypedHyps Δ Γ H)
      (hx : HasType Δ Γ x .natTy) (hy : HasType Δ Γ y .natTy) :
      Proves Δ Γ H (.eq .natTy (.succ x) (.succ y)) ->
      Proves Δ Γ H (.eq .natTy x y)
  | zeroNotSucc (typed : TypedHyps Δ Γ H)
      (hx : HasType Δ Γ x .natTy) :
      Proves Δ Γ H
        (.eq .boolTy (.eq .natTy .zero (.succ x)) (.bool false))

end Nucleus.HolLN
