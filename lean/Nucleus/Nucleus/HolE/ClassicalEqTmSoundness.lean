import Nucleus.HolE.ClassicalDefEqCoherence

/-! # Soundness of kernel term equality

Certificate coherence makes semantic equality independent of the particular
definitionally typed derivations used to evaluate either side.  The congruence
and beta/eta transport equations are isolated so their substitution proofs can
be developed independently.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Extensional semantic equality at a kernel type, quantified over typing
certificates to make transitivity and subsequent proof rules frictionless. -/
def CSemEq {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (left right : Tm ClassicalSig types depth) (A : Ty ClassicalSig types) : Prop :=
  ∀ (leftTyping : HasTypeDefEq Γ left A) (rightTyping : HasTypeDefEq Γ right A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (typed : TypedCtx Γ),
    CBoundValid typed env bound → ∀ (expected : CPointed),
    cDefSem leftTyping.certificate env bound expected =
      cDefSem rightTyping.certificate env bound expected

structure ClassicalEqTmRuleLaws where
  app : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {f g x y : Tm ClassicalSig types depth},
    HasType Γ (.app f x) B → HasType Γ (.app g y) B →
    HasType Γ f (.arr A B) → HasType Γ x A →
    HasType Γ g (.arr A B) → HasType Γ y A →
    CSemEq (Γ := Γ) f g (.arr A B) → CSemEq (Γ := Γ) x y A →
    CSemEq (Γ := Γ) (.app f x) (.app g y) B
  lam : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types}
      {body₁ body₂ : Tm ClassicalSig types (depth + 1)},
    HasType Γ (.lam A body₁) (.arr A B) →
    HasType Γ (.lam A body₂) (.arr A B) → Kinded A →
    CSemEq (Γ := extendBound A Γ) body₁ body₂ B →
    CSemEq (Γ := Γ) (.lam A body₁) (.lam A body₂) (.arr A B)
  eq : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types}
      {x₁ x₂ y₁ y₂ : Tm ClassicalSig types depth},
    HasType Γ (.eq A x₁ y₁) .boolTy →
    HasType Γ (.eq A x₂ y₂) .boolTy → Kinded A →
    CSemEq (Γ := Γ) x₁ x₂ A → CSemEq (Γ := Γ) y₁ y₂ A →
    CSemEq (Γ := Γ) (.eq A x₁ y₁) (.eq A x₂ y₂) .boolTy
  eps : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p q : Tm ClassicalSig types depth},
    HasType Γ (.eps A p) A → HasType Γ (.eps A q) A → Kinded A →
    CSemEq (Γ := Γ) p q (.arr A .boolTy) →
    CSemEq (Γ := Γ) (.eps A p) (.eps A q) A
  abs : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x y : Tm ClassicalSig types depth},
    HasType Γ (.abs A p x) (.sub A p) →
    HasType Γ (.abs A p y) (.sub A p) → Kinded A →
    HasType (extendBound A emptyBound) p .boolTy →
    CSemEq (Γ := Γ) x y A →
    CSemEq (Γ := Γ) (.abs A p x) (.abs A p y) (.sub A p)
  rep : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A : Ty ClassicalSig types} {p : Tm ClassicalSig types 1}
      {x y : Tm ClassicalSig types depth},
    HasType Γ (.rep A p x) A → HasType Γ (.rep A p y) A → Kinded A →
    HasType (extendBound A emptyBound) p .boolTy →
    CSemEq (Γ := Γ) x y (.sub A p) →
    CSemEq (Γ := Γ) (.rep A p x) (.rep A p y) A
  tyExists : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {p q : Tm ClassicalSig (.star :: types) depth},
    HasType Γ (.tyExists p) .boolTy → HasType Γ (.tyExists q) .boolTy →
    CSemEq (Γ := weakenBoundCtx Γ) p q .boolTy →
    CSemEq (Γ := Γ) (.tyExists p) (.tyExists q) .boolTy
  tyForall : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {p q : Tm ClassicalSig (.star :: types) depth},
    HasType Γ (.tyForall p) .boolTy → HasType Γ (.tyForall q) .boolTy →
    CSemEq (Γ := weakenBoundCtx Γ) p q .boolTy →
    CSemEq (Γ := Γ) (.tyForall p) (.tyForall q) .boolTy
  beta : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {body : Tm ClassicalSig types (depth + 1)}
      {x : Tm ClassicalSig types depth},
    Kinded A → TypedCtx Γ → HasType Γ (.app (.lam A body) x) B →
    HasTypeDefEq (extendBound A Γ) body B → HasTypeDefEq Γ x A →
    HasTypeDefEq Γ (openBound body x) B →
    CSemEq (Γ := Γ) (.app (.lam A body) x) (openBound body x) B
  eta : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {f : Tm ClassicalSig types depth},
    (name : Nat) → Fresh name f → TypedCtx Γ →
    HasTypeDefEq Γ f (.arr A B) →
    HasTypeDefEq Γ (.lam A (.app (weaken f) (.bv 0))) (.arr A B) →
    CSemEq (Γ := Γ) (.lam A (.app (weaken f) (.bv 0))) f (.arr A B)

theorem EqTm.sound_of_laws {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {left right : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (laws : ClassicalEqTmRuleLaws)
    (equality : EqTm Γ left right A) : CSemEq (Γ := Γ) left right A := by
  induction equality with
  | refl typing =>
      intro leftTyping rightTyping env bound typed valid expected
      exact leftTyping.certificate.coherent rightTyping.certificate env bound expected
  | symm equality ih =>
      intro leftTyping rightTyping env bound typed valid expected
      exact (ih rightTyping leftTyping env bound typed valid expected).symm
  | trans first second ih₁ ih₂ =>
      intro leftTyping rightTyping env bound typed valid expected
      exact (ih₁ leftTyping first.typing.2 env bound typed valid expected).trans
        (ih₂ second.typing.1 rightTyping env bound typed valid expected)
  | app leftRaw rightRaw leftFunctionRaw leftArgumentRaw rightFunctionRaw
      rightArgumentRaw function argument ihf ihx =>
      exact laws.app leftRaw rightRaw leftFunctionRaw leftArgumentRaw
        rightFunctionRaw rightArgumentRaw ihf ihx
  | lam leftRaw rightRaw hA bodies ih => exact laws.lam leftRaw rightRaw hA ih
  | eq leftRaw rightRaw hA left right ihx ihy =>
      exact laws.eq leftRaw rightRaw hA ihx ihy
  | eps leftRaw rightRaw hA predicates ih => exact laws.eps leftRaw rightRaw hA ih
  | abs leftRaw rightRaw hA hp values ih => exact laws.abs leftRaw rightRaw hA hp ih
  | rep leftRaw rightRaw hA hp values ih => exact laws.rep leftRaw rightRaw hA hp ih
  | tyExists leftRaw rightRaw predicates ih => exact laws.tyExists leftRaw rightRaw ih
  | tyForall leftRaw rightRaw predicates ih => exact laws.tyForall leftRaw rightRaw ih
  | @conv types depth Γ left B right A leftTyping rightTyping equality ih =>
      intro convertedLeft convertedRight env bound typed valid expected
      let sourceLeft : HasTypeDefEq Γ left A := equality.typing.1
      let sourceRight : HasTypeDefEq Γ right A := equality.typing.2
      calc
        cDefSem convertedLeft.certificate env bound expected =
            cDefSem sourceLeft.certificate env bound expected :=
          convertedLeft.certificate.coherent sourceLeft.certificate env bound expected
        _ = cDefSem sourceRight.certificate env bound expected :=
          ih sourceLeft sourceRight env bound typed valid expected
        _ = cDefSem convertedRight.certificate env bound expected :=
          (convertedRight.certificate.coherent sourceRight.certificate env bound expected).symm
  | beta body x hA typedContext applicationRaw bodyTyping argumentTyping resultTyping =>
      exact laws.beta hA typedContext applicationRaw bodyTyping argumentTyping resultTyping
  | eta name fresh typedContext functionTyping etaTyping =>
      exact laws.eta name fresh typedContext functionTyping etaTyping

end Nucleus.HolE
