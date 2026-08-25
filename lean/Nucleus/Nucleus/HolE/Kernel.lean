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
  | app (leftRaw : HasType Γ (.app f x) B)
      (rightRaw : HasType Γ (.app g y) B)
      (leftFunctionRaw : HasType Γ f (.arr A B)) (leftArgumentRaw : HasType Γ x A)
      (rightFunctionRaw : HasType Γ g (.arr A B)) (rightArgumentRaw : HasType Γ y A) :
      EqTm Γ f g (.arr A B) → EqTm Γ x y A →
      EqTm Γ (.app f x) (.app g y) B
  | lam (leftRaw : HasType Γ (.lam A t) (.arr A B))
      (rightRaw : HasType Γ (.lam A u) (.arr A B)) (hA : Kinded A) :
      EqTm (extendBound A Γ) t u B →
      EqTm Γ (.lam A t) (.lam A u) (.arr A B)
  | eq (leftRaw : HasType Γ (.eq A x₁ y₁) .boolTy)
      (rightRaw : HasType Γ (.eq A x₂ y₂) .boolTy) (hA : Kinded A) :
      EqTm Γ x₁ x₂ A → EqTm Γ y₁ y₂ A →
      EqTm Γ (.eq A x₁ y₁) (.eq A x₂ y₂) .boolTy
  | eps (leftRaw : HasType Γ (.eps A p) A)
      (rightRaw : HasType Γ (.eps A q) A) (hA : Kinded A) :
      EqTm Γ p q (.arr A .boolTy) →
      EqTm Γ (.eps A p) (.eps A q) A
  | abs (leftRaw : HasType Γ (.abs A p x) (.sub A p))
      (rightRaw : HasType Γ (.abs A p y) (.sub A p))
      (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy) :
      EqTm Γ x y A →
      EqTm Γ (.abs A p x) (.abs A p y) (.sub A p)
  | rep (leftRaw : HasType Γ (.rep A p x) A)
      (rightRaw : HasType Γ (.rep A p y) A)
      (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy) :
      EqTm Γ x y (.sub A p) →
      EqTm Γ (.rep A p x) (.rep A p y) A
  | tyExists (leftRaw : HasType (types := types) Γ (.tyExists p) .boolTy)
      (rightRaw : HasType (types := types) Γ (.tyExists q) .boolTy) :
      EqTm (types := .star :: types) (weakenBoundCtx Γ) p q .boolTy →
      EqTm (types := types) Γ (.tyExists p) (.tyExists q) .boolTy
  /-- Reindex an equality when both endpoints check at the new type. -/
  | tyForall (leftRaw : HasType (types := types) Γ (.tyForall p) .boolTy)
      (rightRaw : HasType (types := types) Γ (.tyForall q) .boolTy) :
      EqTm (types := .star :: types) (weakenBoundCtx Γ) p q .boolTy →
      EqTm (types := types) Γ (.tyForall p) (.tyForall q) .boolTy
  /-- Reindex an equality when both endpoints check at the new type. -/
  | conv (leftTyping : HasTypeDefEq Γ left B)
      (rightTyping : HasTypeDefEq Γ right B) :
      EqTm Γ left right A → EqTm Γ left right B
  | beta (body : Tm Sig types (depth + 1)) (x : Tm Sig types depth) (hA : Kinded A)
      (typedContext : TypedCtx Γ)
      (applicationRaw : HasType Γ (.app (.lam A body) x) B)
      (bodyTyping : HasTypeDefEq (extendBound A Γ) body B)
      (argumentTyping : HasTypeDefEq Γ x A)
      (resultTyping : HasTypeDefEq Γ (openBound body x) B) :
      EqTm Γ (.app (.lam A body) x) (openBound body x) B
  | eta (name : Nat) (fresh : Fresh name f)
      (typedContext : TypedCtx Γ)
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
  | hyp (typed : TypedHyps Γ H) (conclusionTyping : HasTypeDefEq Γ p .boolTy)
      (member : p ∈ H) : Proves Γ H p
  | truth (typed : TypedHyps Γ H)
      (conclusionTyping : HasTypeDefEq Γ (.bool true) .boolTy) :
      Proves Γ H (.bool true)
  | falseElim (typed : TypedHyps Γ H)
      (conclusionTyping : HasTypeDefEq Γ p .boolTy) (hp : HasTypeDefEq Γ p .boolTy) :
      Proves Γ H (.bool false) → Proves Γ H p
  | boolCases (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy)
      (conclusionTyping : HasTypeDefEq Γ q .boolTy)
      (leftTyped : TypedHyps Γ (p :: H))
      (rightTyped : TypedHyps Γ (.eq .boolTy p (.bool false) :: H)) :
      Proves Γ (p :: H) q → Proves Γ (.eq .boolTy p (.bool false) :: H) q →
      Proves Γ H q
  | eqRefl (typed : TypedHyps Γ H)
      (conclusionTyping : HasTypeDefEq Γ (.eq A x x) .boolTy)
      (hA : Kinded A) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.eq A x x)
  | eqMp (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ (.app p y) .boolTy)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A)
      (hy : HasTypeDefEq Γ y A) :
      Proves Γ H (.eq A x y) → Proves Γ H (.app p x) → Proves Γ H (.app p y)
  | choice (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ (.app p (.eps A p)) .boolTy)
      (hp : HasTypeDefEq Γ p (.arr A .boolTy)) (hx : HasTypeDefEq Γ x A) :
      Proves Γ H (.app p x) → Proves Γ H (.app p (.eps A p))
  | generalize (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ
        (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true))) .boolTy)
      (bodyTyping : HasTypeDefEq (extendBound A Γ) body .boolTy) :
      Proves (extendBound A Γ) (H.map weaken) body →
      Proves Γ H (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true)))
  | weakenBound (typed : TypedHyps Γ H) (hA : Kinded A)
      (typedK : TypedHyps (extendBound A Γ) K)
      (conclusionTyping : HasTypeDefEq (extendBound A Γ) (weaken p) .boolTy)
      (embedding : ∀ q, q ∈ H → weaken q ∈ K) :
      Proves Γ H p → Proves (extendBound A Γ) K (weaken p)
  | hypothesisMap (typedK : TypedHyps Γ K)
      (conclusionTyping : HasTypeDefEq Γ p .boolTy)
      (subset : ∀ q, q ∈ H → q ∈ K) : Proves Γ H p → Proves Γ K p
  | convert (typed : TypedHyps Γ H)
      (conclusionTyping : HasTypeDefEq Γ q .boolTy) : EqTm Γ p q .boolTy →
      Proves Γ H p → Proves Γ H q
  | eqOfEqTm (typed : TypedHyps Γ H) (hA : Kinded A) :
      (conclusionTyping : HasTypeDefEq Γ (.eq A x y) .boolTy) →
      EqTm Γ x y A → Proves Γ H (.eq A x y)
  | antisymm (typed : TypedHyps Γ H) (hp : HasTypeDefEq Γ p .boolTy)
      (hq : HasTypeDefEq Γ q .boolTy) (leftTyped : TypedHyps Γ (p :: H))
      (conclusionTyping : HasTypeDefEq Γ (.eq .boolTy p q) .boolTy)
      (rightTyped : TypedHyps Γ (q :: H)) : Proves Γ (p :: H) q →
      Proves Γ (q :: H) p → Proves Γ H (.eq .boolTy p q)
  | absRep (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ
        (.eq (.sub A p) (.abs A p (.rep A p x)) x) .boolTy)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : HasTypeDefEq Γ x (.sub A p)) :
      Proves Γ H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  | repAbs (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ
        (.eq A (.rep A p (.abs A p x)) x) .boolTy)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hxRaw : HasType Γ x A) :
      Proves Γ H (instantiateOne p x) →
      Proves Γ H (.eq A (.rep A p (.abs A p x)) x)
  /-- In the guarded interpretation `Sub p = {x | p x ∨ ¬∃y, p y}`, a local
  witness selects the inhabited branch and therefore establishes `p (rep x)`.
  Subtype formation itself has no nonemptiness side condition. -/
  | repPredOfWitness (typed : TypedHyps Γ H) (hA : Kinded A)
      (conclusionTyping : HasTypeDefEq Γ
        (instantiateOne p (.rep A p x)) .boolTy)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (witnessRaw : HasType Γ witness A)
      (subtypeRaw : HasType Γ x (.sub A p)) :
      Proves Γ H (instantiateOne p witness) →
      Proves Γ H (instantiateOne p (.rep A p x))
  /-- Existential introduction with one concrete well-kinded type witness. -/
  | tyExistsIntro (typed : TypedHyps (emptyBound : BoundCtx Sig types 0) H)
      (conclusionTyping : HasTypeDefEq emptyBound (.tyExists predicate) .boolTy)
      (hA : Kinded A)
      (predicateTyping : HasTypeDefEq
        (types := .star :: types) emptyBound predicate .boolTy)
      (instanceTyping : HasTypeDefEq emptyBound (openType predicate A) .boolTy) :
      Proves emptyBound H (openType predicate A) →
      Proves emptyBound H (.tyExists predicate)
  /-- Guarded type choice: if a satisfying type exists, `Model predicate`
  itself satisfies the predicate. -/
  | modelSpec (typed : TypedHyps (emptyBound : BoundCtx Sig types 0) H)
      (conclusionTyping : HasTypeDefEq emptyBound
        (openType predicate (.model predicate)) .boolTy)
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
    {p : Tm Sig types depth} (proof : Proves Γ H p) : TypedHyps Γ H := by
  cases proof <;> assumption

/-- Every proof certificate carries a typing derivation for its conclusion. -/
theorem conclusionTyping {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H : List (Tm Sig types depth)}
    {p : Tm Sig types depth} (proof : Proves Γ H p) : HasTypeDefEq Γ p .boolTy := by
  cases proof <;> assumption

/-- Proofs are monotone in their hypothesis list. -/
noncomputable def mapHypotheses {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig] {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H K : List (Tm Sig types depth)}
    {p : Tm Sig types depth} (typedK : TypedHyps Γ K)
    (subset : ∀ proposition, proposition ∈ H → proposition ∈ K) :
    Proves Γ H p → Proves Γ K p :=
  fun proof => .hypothesisMap typedK proof.conclusionTyping subset proof

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
