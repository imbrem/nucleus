import Nucleus.HolE.ClassicalDefEqCoherence

/-! # Semantic soundness of the HolE kernel

The rule induction is kept separate from the semantic proofs of the individual
non-structural rules.  This makes rule coverage mechanically checkable while
the transport-heavy laws (beta, choice, subtypes, and type choice) can be
proved independently.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- The non-structural semantic laws needed by the kernel rule induction.
Every field has exactly the semantic shape of its corresponding `Proves`
constructor; ordinary hypotheses, truth, Boolean cases, reflexivity, and
hypothesis-map are already proved directly in `ClassicalSoundness`. -/
structure ClassicalKernelRuleLaws where
  eqMp : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p x y : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ p (.arr A .boolTy) →
    HasTypeDefEq Γ x A → HasTypeDefEq Γ y A →
    CEntails (Γ := Γ) H (.eq A x y) → CEntails (Γ := Γ) H (.app p x) →
    CEntails (Γ := Γ) H (.app p y)
  choice : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p x : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ p (.arr A .boolTy) → HasTypeDefEq Γ x A →
    CEntails (Γ := Γ) H (.app p x) →
    CEntails (Γ := Γ) H (.app p (.eps A p))
  generalize : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {body : Tm ClassicalSig types (depth + 1)},
    Kinded A → HasTypeDefEq (extendBound A Γ) body .boolTy →
    CEntails (Γ := extendBound A Γ) (H.map weaken) body →
    CEntails (Γ := Γ) H
      (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true)))
  weakenBound : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {K : List (Tm ClassicalSig types (depth + 1))}
      {p : Tm ClassicalSig types depth},
    Kinded A → (∀ q, q ∈ H → weaken q ∈ K) →
    CEntails (Γ := Γ) H p → CEntails (Γ := extendBound A Γ) K (weaken p)
  convert : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {p q : Tm ClassicalSig types depth},
    EqTm Γ p q .boolTy → CEntails (Γ := Γ) H p → CEntails (Γ := Γ) H q
  eqOfEqTm : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {x y : Tm ClassicalSig types depth},
    Kinded A → EqTm Γ x y A → CEntails (Γ := Γ) H (.eq A x y)
  antisymm : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {p q : Tm ClassicalSig types depth},
    HasTypeDefEq Γ p .boolTy → HasTypeDefEq Γ q .boolTy →
    CEntails (Γ := Γ) (p :: H) q → CEntails (Γ := Γ) (q :: H) p →
    CEntails (Γ := Γ) H (.eq .boolTy p q)
  absRep : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth},
    Kinded A → HasType (extendBound A emptyBound) p .boolTy →
    HasTypeDefEq Γ x (.sub A p) →
    CEntails (Γ := Γ) H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  repAbs : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth},
    Kinded A → HasType (extendBound A emptyBound) p .boolTy →
    HasTypeDefEq Γ x A → HasTypeDefEq Γ (instantiateOne p x) .boolTy →
    CEntails (Γ := Γ) H (instantiateOne p x) →
    CEntails (Γ := Γ) H (.eq A (.rep A p (.abs A p x)) x)
  repPredOfWitness : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {witness x : Tm ClassicalSig types depth},
    Kinded A → HasType (extendBound A emptyBound) p .boolTy →
    HasTypeDefEq Γ witness A → HasTypeDefEq Γ (instantiateOne p witness) .boolTy →
    HasTypeDefEq Γ x (.sub A p) →
    HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy →
    CEntails (Γ := Γ) H (instantiateOne p witness) →
    CEntails (Γ := Γ) H (instantiateOne p (.rep A p x))
  tyExistsIntro : ∀ {types} {H : List (Tm ClassicalSig types 0)}
      {A : Ty ClassicalSig types} {predicate : Tm ClassicalSig (.star :: types) 0},
    Kinded A → HasTypeDefEq (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)
      predicate .boolTy →
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate A) .boolTy →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (openType predicate A) →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (.tyExists predicate)
  modelSpec : ∀ {types} {H : List (Tm ClassicalSig types 0)}
      {predicate : Tm ClassicalSig (.star :: types) 0},
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)
      predicate .boolTy →
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate (.model predicate)) .boolTy →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (.tyExists predicate) →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (openType predicate (.model predicate))

/-- Exhaustive kernel-rule induction.  Adding a `Proves` constructor now makes
this theorem fail until its semantic case is supplied. -/
theorem Proves.sound_of_kernel_laws (laws : ClassicalKernelRuleLaws) :
    ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {p : Tm ClassicalSig types depth},
      Proves Γ H p → CEntails (Γ := Γ) H p := by
  intro types depth Γ H p proof
  induction proof with
  | hyp typed member => exact CEntails.hyp member
  | truth typed => exact CEntails.truth
  | falseElim typed hp premise ih => exact CEntails.falseElim ih
  | boolCases typed hp leftTyped rightTyped left right ihl ihr =>
      exact CEntails.boolCases hp ihl ihr
  | eqRefl typed hA hx => exact CEntails.eqRefl hA hx
  | eqMp typed hA hp hx hy equality premise iheq ihp =>
      exact laws.eqMp hA hp hx hy iheq ihp
  | choice typed hA hp hx premise ih => exact laws.choice hA hp hx ih
  | generalize typed hA bodyTyping premise ih =>
      exact laws.generalize hA bodyTyping ih
  | weakenBound typed hA typedK embedding premise ih =>
      exact laws.weakenBound hA embedding ih
  | hypothesisMap typedK subset premise ih => exact CEntails.hypothesisMap subset ih
  | convert typed equality premise ih => exact laws.convert equality ih
  | eqOfEqTm typed hA equality => exact laws.eqOfEqTm hA equality
  | antisymm typed hp hq leftTyped rightTyped left right ihl ihr =>
      exact laws.antisymm hp hq ihl ihr
  | absRep typed hA hp hx => exact laws.absRep hA hp hx
  | repAbs typed hA hp hx predicateTyping premise ih =>
      exact laws.repAbs hA hp hx predicateTyping ih
  | repPredOfWitness typed hA hp witnessTyping witnessPredicateTyping
      subtypeTyping representationPredicateTyping premise ih =>
      exact laws.repPredOfWitness hA hp witnessTyping witnessPredicateTyping
        subtypeTyping representationPredicateTyping ih
  | tyExistsIntro typed hA predicateTyping instanceTyping premise ih =>
      exact laws.tyExistsIntro hA predicateTyping instanceTyping ih
  | modelSpec typed predicateTyping modelInstanceTyping premise ih =>
      exact laws.modelSpec predicateTyping modelInstanceTyping ih

end Nucleus.HolE
