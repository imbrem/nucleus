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
    Kinded A → HasTypeDefEq Γ (.app p y) .boolTy → HasTypeDefEq Γ p (.arr A .boolTy) →
    HasTypeDefEq Γ x A → HasTypeDefEq Γ y A →
    HasTypeDefEq Γ (.eq A x y) .boolTy → HasTypeDefEq Γ (.app p x) .boolTy →
    CEntails (Γ := Γ) H (.eq A x y) → CEntails (Γ := Γ) H (.app p x) →
    CEntails (Γ := Γ) H (.app p y)
  choice : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p x : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ (.app p (.eps A p)) .boolTy →
    HasTypeDefEq Γ p (.arr A .boolTy) → HasTypeDefEq Γ x A →
    HasTypeDefEq Γ (.app p x) .boolTy →
    CEntails (Γ := Γ) H (.app p x) →
    CEntails (Γ := Γ) H (.app p (.eps A p))
  generalize : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {body : Tm ClassicalSig types (depth + 1)},
    TypedHyps Γ H → Kinded A → HasTypeDefEq Γ
      (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true))) .boolTy →
    HasTypeDefEq (extendBound A Γ) body .boolTy →
    CEntails (Γ := extendBound A Γ) (H.map weaken) body →
    CEntails (Γ := Γ) H
      (.eq (.arr A .boolTy) (.lam A body) (.lam A (.bool true)))
  weakenBound : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {K : List (Tm ClassicalSig types (depth + 1))}
      {p : Tm ClassicalSig types depth},
    TypedHyps Γ H → Kinded A →
    HasTypeDefEq (extendBound A Γ) (weaken p) .boolTy →
    (∀ q, q ∈ H → weaken q ∈ K) →
    CEntails (Γ := Γ) H p → CEntails (Γ := extendBound A Γ) K (weaken p)
  convert : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {p q : Tm ClassicalSig types depth},
    HasTypeDefEq Γ q .boolTy → EqTm Γ p q .boolTy →
    CEntails (Γ := Γ) H p → CEntails (Γ := Γ) H q
  eqOfEqTm : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {x y : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ (.eq A x y) .boolTy → EqTm Γ x y A →
    CEntails (Γ := Γ) H (.eq A x y)
  antisymm : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {p q : Tm ClassicalSig types depth},
    HasTypeDefEq Γ p .boolTy → HasTypeDefEq Γ q .boolTy →
    HasTypeDefEq Γ (.eq .boolTy p q) .boolTy →
    CEntails (Γ := Γ) (p :: H) q → CEntails (Γ := Γ) (q :: H) p →
    CEntails (Γ := Γ) H (.eq .boolTy p q)
  absRep : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ
      (.eq (.sub A p) (.abs A p (.rep A p x)) x) .boolTy →
    HasType (extendBound A emptyBound) p .boolTy →
    HasTypeDefEq Γ x (.sub A p) →
    CEntails (Γ := Γ) H (.eq (.sub A p) (.abs A p (.rep A p x)) x)
  repAbs : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {x : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ (.eq A (.rep A p (.abs A p x)) x) .boolTy →
    HasType (extendBound A emptyBound) p .boolTy →
    HasType Γ x A →
    CEntails (Γ := Γ) H (instantiateOne p x) →
    CEntails (Γ := Γ) H (.eq A (.rep A p (.abs A p x)) x)
  repPredOfWitness : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
      {p : Tm ClassicalSig types 1} {witness x : Tm ClassicalSig types depth},
    Kinded A → HasTypeDefEq Γ (instantiateOne p (.rep A p x)) .boolTy →
    HasType (extendBound A emptyBound) p .boolTy →
    HasType Γ witness A →
    HasType Γ x (.sub A p) →
    CEntails (Γ := Γ) H (instantiateOne p witness) →
    CEntails (Γ := Γ) H (instantiateOne p (.rep A p x))
  tyExistsIntro : ∀ {types} {H : List (Tm ClassicalSig types 0)}
      {A : Ty ClassicalSig types} {predicate : Tm ClassicalSig (.star :: types) 0},
    Kinded A → HasTypeDefEq (emptyBound : BoundCtx ClassicalSig types 0)
      (.tyExists predicate) .boolTy →
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)
      predicate .boolTy →
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate A) .boolTy →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (openType predicate A) →
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) H
      (.tyExists predicate)
  modelSpec : ∀ {types} {H : List (Tm ClassicalSig types 0)}
      {predicate : Tm ClassicalSig (.star :: types) 0},
    HasTypeDefEq (emptyBound : BoundCtx ClassicalSig types 0)
      (openType predicate (.model predicate)) .boolTy →
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
  | hyp typed conclusionTyping member => exact CEntails.hyp member
  | truth typed conclusionTyping => exact CEntails.truth
  | falseElim typed conclusionTyping hp premise ih => exact CEntails.falseElim ih
  | boolCases typed hp conclusionTyping leftTyped rightTyped left right ihl ihr =>
      exact CEntails.boolCases hp (rightTyped _ (List.mem_cons_self)) ihl ihr
  | eqRefl typed conclusionTyping hA hx => exact CEntails.eqRefl hA hx conclusionTyping
  | eqMp typed hA conclusionTyping hp hx hy equality premise iheq ihp =>
      exact laws.eqMp hA conclusionTyping hp hx hy equality.conclusionTyping
        premise.conclusionTyping iheq ihp
  | choice typed hA conclusionTyping hp hx premise ih =>
      exact laws.choice hA conclusionTyping hp hx premise.conclusionTyping ih
  | generalize typed hA conclusionTyping bodyTyping premise ih =>
      exact laws.generalize typed hA conclusionTyping bodyTyping ih
  | weakenBound typed hA typedK conclusionTyping embedding premise ih =>
      exact laws.weakenBound typed hA conclusionTyping embedding ih
  | hypothesisMap typedK conclusionTyping subset premise ih =>
      exact CEntails.hypothesisMap subset ih
  | convert typed conclusionTyping equality premise ih =>
      exact laws.convert conclusionTyping equality ih
  | eqOfEqTm typed hA conclusionTyping equality =>
      exact laws.eqOfEqTm hA conclusionTyping equality
  | antisymm typed hp hq leftTyped conclusionTyping rightTyped left right ihl ihr =>
      exact laws.antisymm hp hq conclusionTyping ihl ihr
  | absRep typed hA conclusionTyping hp hx =>
      exact laws.absRep hA conclusionTyping hp hx
  | repAbs typed hA conclusionTyping hp hxRaw premise ih =>
      exact laws.repAbs hA conclusionTyping hp hxRaw ih
  | repPredOfWitness typed hA conclusionTyping hp witnessRaw subtypeRaw premise ih =>
      exact laws.repPredOfWitness hA conclusionTyping hp witnessRaw subtypeRaw ih
  | tyExistsIntro typed conclusionTyping hA predicateTyping instanceTyping premise ih =>
      exact laws.tyExistsIntro hA conclusionTyping predicateTyping instanceTyping ih
  | modelSpec typed conclusionTyping predicateTyping modelInstanceTyping premise ih =>
      exact laws.modelSpec conclusionTyping predicateTyping modelInstanceTyping ih

end Nucleus.HolE
