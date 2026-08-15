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
  /-- In the guarded interpretation `Sub p = {x | p x ∨ ¬∃y, p y}`, a local
  witness selects the inhabited branch and therefore establishes `p (rep x)`.
  Subtype formation itself has no nonemptiness side condition. -/
  | repPredOfWitness (typed : TypedHyps Γ H) (hA : Kinded A)
      (hp : HasTypeDefEq (extendBound A emptyBound) p .boolTy)
      (witnessTyping : HasTypeDefEq Γ witness A)
      (witnessPredicateTyping : HasTypeDefEq Γ (instantiateOne p witness) .boolTy)
      (subtypeTyping : HasTypeDefEq Γ x (.sub A p))
      (representationPredicateTyping :
        HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy) :
      Proves Γ H (instantiateOne p witness) →
      Proves Γ H (instantiateOne p (.rep A p x))

namespace Proves

/-- Every proof certificate carries the well-typedness of its hypotheses. -/
theorem typedHypotheses {Sig : Signature} [SigTyping Sig] {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H : List (Tm Sig types depth)}
    {p : Tm Sig types depth} : Proves Γ H p → TypedHyps Γ H
  | .hyp typed _ | .truth typed | .eqRefl typed _ _ |
      .eqMp typed _ _ _ _ _ _ | .choice typed _ _ _ _ |
      .convert typed _ _ | .eqOfEqTm typed _ _ |
      .antisymm typed _ _ _ _ _ _ | .absRep typed _ _ _ |
      .repAbs typed _ _ _ _ _ | .repPredOfWitness typed _ _ _ _ _ _ _ => typed

/-- Proofs are monotone in their hypothesis list. -/
noncomputable def mapHypotheses {Sig : Signature} [SigTyping Sig] {types : List Kind}
    {depth : Nat} {Γ : BoundCtx Sig types depth} {H K : List (Tm Sig types depth)}
    {p : Tm Sig types depth} (typedK : TypedHyps Γ K)
    (subset : ∀ proposition, proposition ∈ H → proposition ∈ K) :
    Proves Γ H p → Proves Γ K p
  | .hyp _ member => .hyp typedK (subset _ member)
  | .truth _ => .truth typedK
  | .eqRefl _ hA hx => .eqRefl typedK hA hx
  | .eqMp _ hA hp hx hy equality application =>
      .eqMp typedK hA hp hx hy
        (mapHypotheses typedK subset equality)
        (mapHypotheses typedK subset application)
  | .choice _ hA hp hx premise =>
      .choice typedK hA hp hx (mapHypotheses typedK subset premise)
  | .convert _ equality premise =>
      .convert typedK equality (mapHypotheses typedK subset premise)
  | .eqOfEqTm _ hA equality => .eqOfEqTm typedK hA equality
  | .antisymm _ hp hq leftTyped rightTyped left right =>
      .antisymm typedK hp hq
        (fun proposition membership => by
          rcases List.mem_cons.mp membership with rfl | membership
          · exact hp
          · exact typedK proposition membership)
        (fun proposition membership => by
          rcases List.mem_cons.mp membership with rfl | membership
          · exact hq
          · exact typedK proposition membership)
        (mapHypotheses
          (fun proposition membership => by
            rcases List.mem_cons.mp membership with rfl | membership
            · exact hp
            · exact typedK proposition membership)
          (fun proposition membership => by
            rcases List.mem_cons.mp membership with rfl | membership
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (subset proposition membership)) left)
        (mapHypotheses
          (fun proposition membership => by
            rcases List.mem_cons.mp membership with rfl | membership
            · exact hq
            · exact typedK proposition membership)
          (fun proposition membership => by
            rcases List.mem_cons.mp membership with rfl | membership
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (subset proposition membership)) right)
  | .absRep _ hA hp hx => .absRep typedK hA hp hx
  | .repAbs _ hA hp hx predicateTyping premise =>
      .repAbs typedK hA hp hx predicateTyping (mapHypotheses typedK subset premise)
  | .repPredOfWitness _ hA hp witnessTyping witnessPredicateTyping subtypeTyping
      representationPredicateTyping premise =>
      .repPredOfWitness typedK hA hp witnessTyping witnessPredicateTyping subtypeTyping
        representationPredicateTyping (mapHypotheses typedK subset premise)

/-- Adding an unused proposition to the local hypothesis list is admissible. -/
noncomputable def weakenHypotheses {Sig : Signature} [SigTyping Sig] {types : List Kind}
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

end Nucleus.Hol.FamilySub
