import Nucleus.HolE.Substitution

/-! # Proof certificates for type-variable-scoped HOL -/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

inductive EqTm {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig] :
    {types : List Kind} → {depth : Nat} →
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

def TypedHyps {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    (Γ : BoundCtx Sig types depth)
    (hypotheses : List (Tm Sig types depth)) : Prop :=
  ∀ p, p ∈ hypotheses → HasTypeDefEq Γ p .boolTy

inductive Proves {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind} : {depth : Nat} →
    (Γ : BoundCtx Sig types depth) → List (Tm Sig types depth) → Tm Sig types depth →
    Type u where
  | hyp (typed : TypedHyps Γ H) (member : p ∈ H) : Proves Γ H p
  | truth (typed : TypedHyps Γ H) : Proves Γ H (.bool true)
  | falseElim (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy) :
      Proves Γ H (.bool false) → Proves Γ H p
  | boolCases (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy)
      (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (.eq .boolTy p (.bool false) :: H)) :
      Proves Γ (p :: H) q → Proves Γ (.eq .boolTy p (.bool false) :: H) q →
      Proves Γ H q
  | eqRefl (typed : TypedHyps Γ H) (hA : Kinded A) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A)
      (hy : HasTypeDefEq Γ y A) :
      Proves Γ H (.eq A x y) → Proves Γ H (.app p x) → Proves Γ H (.app p y)
  | choice (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.app p x) → Proves Γ H (.app p (.eps A p))
  | generalize (typed : TypedHyps Γ H) (hA : Kinded A)
      (bodyTyping : HasTypeDefEq (extendBound A Γ) body .boolTy) :
      Proves (extendBound A Γ) (H.map weaken) body →
      Proves Γ H (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true)))
  | weakenBound (typed : TypedHyps Γ H) (hA : Kinded A)
      (typedK : TypedHyps (extendBound A Γ) K)
      (embedding : ∀ q, q ∈ H → weaken q ∈ K) :
      Proves Γ H p → Proves (extendBound A Γ) K (weaken p)
  | hypothesisMap (typedK : TypedHyps Γ K)
      (subset : ∀ q, q ∈ H → q ∈ K) : Proves Γ H p → Proves Γ K p
  | convert (typed : TypedHyps Γ H) : EqTm Γ p q .boolTy →
      Proves Γ H p → Proves Γ H q
  | eqOfEqTm (typed : TypedHyps Γ H) (hA : Kinded A) :
      EqTm Γ x y A → Proves Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy)
      (hq : HasTypeDefEq Γ q .boolTy) (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (q :: H)) : Proves Γ (p :: H) q →
      Proves Γ (q :: H) p → Proves Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasTypeDefEq Γ x (.sub A p)) :
      Proves Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasTypeDefEq Γ x A)
      (predicateTyping : HasTypeDefEq Γ (instantiateOne p x) .boolTy) :
      Proves Γ H (instantiateOne p x) →
      Proves Γ H (.eq A (.rep A p (.abs A p x)) x)
  /-- In the guarded interpretation `Sub p = {x | p x ∨ ¬∃y, p y}`, a local
  witness selects the inhabited branch and therefore establishes `p (rep x)`.
  Subtype formation itself has no nonemptiness side condition. -/
  | repPredOfWitness (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (witnessTyping : HasTypeDefEq Γ witness A)
      (witnessPredicateTyping : HasTypeDefEq Γ (instantiateOne p witness) .boolTy)
      (subtypeTyping : HasTypeDefEq Γ x (.sub A p))
      (representationPredicateTyping :
        HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy) :
      Proves Γ H (instantiateOne p witness) →
      Proves Γ H (instantiateOne p (.rep A p x))
  /-- Existential introduction with one concrete well-kinded type witness. -/
  | tyExistsIntro (typed : TypedHyps (emptyBound : BoundCtx Sig types 0) H)
      (hA : Kinded A)
      (predicateTyping : HasTypeDefEq
        (types := .star :: types) emptyBound predicate .boolTy)
      (instanceTyping : HasTypeDefEq emptyBound (openType predicate A) .boolTy) :
      Proves emptyBound H (openType predicate A) →
      Proves emptyBound H (.tyExists predicate)
  /-- Guarded type choice: if a satisfying type exists, `Model predicate`
  itself satisfies the predicate. -/
  | modelSpec (typed : TypedHyps (emptyBound : BoundCtx Sig types 0) H)
      (predicateTyping : HasTypeDefEq
        (types := .star :: types) emptyBound predicate .boolTy)
      (modelInstanceTyping : HasTypeDefEq emptyBound
        (openType predicate (.model predicate)) .boolTy) :
      Proves emptyBound H (.tyExists predicate) →
      Proves emptyBound H (openType predicate (.model predicate))

namespace Proves

/-- Every proof certificate carries the well-typedness of its hypotheses. -/
theorem typedHypotheses {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H : List (Tm Sig types depth)}
    {p : Tm Sig types depth} : Proves Γ H p → TypedHyps Γ H
  | .hyp typed _ | .truth typed | .falseElim typed _ _ |
      .boolCases typed _ _ _ _ _ | .eqRefl typed _ _ |
      .eqMp typed _ _ _ _ _ _ | .choice typed _ _ _ _ |
      .generalize typed _ _ _ |
      .convert typed _ _ | .eqOfEqTm typed _ _ |
      .antisymm typed _ _ _ _ _ _ | .absRep typed _ _ _ |
      .repAbs typed _ _ _ _ _ | .repPredOfWitness typed _ _ _ _ _ _ _ => typed
  | .tyExistsIntro typed _ _ _ _ | .modelSpec typed _ _ _ => typed
  | .weakenBound _ _ typedK _ _ => typedK
  | .hypothesisMap typedK _ _ => typedK

/-- Proofs are monotone in their hypothesis list. -/
noncomputable def mapHypotheses {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig] {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H K : List (Tm Sig types depth)}
    {p : Tm Sig types depth} (typedK : TypedHyps Γ K)
    (subset : ∀ proposition, proposition ∈ H → proposition ∈ K) :
    Proves Γ H p → Proves Γ K p :=
  .hypothesisMap typedK subset

/-- Adding an unused proposition to the local hypothesis list is admissible. -/
noncomputable def weakenHypotheses {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig] {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H : List (Tm Sig types depth)}
    {p q : Tm Sig types depth} (hq : HasTypeDefEq Γ q .boolTy)
    (proof : Proves Γ H p) : Proves Γ (q :: H) p :=
  mapHypotheses
    (fun proposition membership => by
      rcases List.mem_cons.mp membership with rfl | membership
      · exact hq
      · exact proof.typedHypotheses proposition membership)
    (fun proposition membership => List.mem_cons_of_mem _ membership) proof

end Proves

end Nucleus.HolE
