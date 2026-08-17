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
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed),
    cDefSem leftTyping.certificate env bound expected =
      cDefSem rightTyping.certificate env bound expected

structure ClassicalEqTmRuleLaws where
  app : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {f g x y : Tm ClassicalSig types depth},
    HasType Γ (.app f x) B → HasType Γ (.app g y) B →
    CSemEq (Γ := Γ) f g (.arr A B) → CSemEq (Γ := Γ) x y A →
    CSemEq (Γ := Γ) (.app f x) (.app g y) B
  lam : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types}
      {body₁ body₂ : Tm ClassicalSig types (depth + 1)},
    HasType Γ (.lam A body₁) (.arr A B) →
    HasType Γ (.lam A body₂) (.arr A B) → Kinded A →
    CSemEq (Γ := extendBound A Γ) body₁ body₂ B →
    CSemEq (Γ := Γ) (.lam A body₁) (.lam A body₂) (.arr A B)
  beta : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {body : Tm ClassicalSig types (depth + 1)}
      {x : Tm ClassicalSig types depth},
    Kinded A → HasType Γ (.app (.lam A body) x) B →
    HasTypeDefEq (extendBound A Γ) body B → HasTypeDefEq Γ x A →
    HasTypeDefEq Γ (openBound body x) B →
    CSemEq (Γ := Γ) (.app (.lam A body) x) (openBound body x) B
  eta : ∀ {types depth} {Γ : BoundCtx ClassicalSig types depth}
      {A B : Ty ClassicalSig types} {f : Tm ClassicalSig types depth},
    (name : Nat) → Fresh name f → HasTypeDefEq Γ f (.arr A B) →
    HasTypeDefEq Γ (.lam A (.app (weaken f) (.bv 0))) (.arr A B) →
    CSemEq (Γ := Γ) (.lam A (.app (weaken f) (.bv 0))) f (.arr A B)

theorem EqTm.sound_of_laws {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {left right : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (laws : ClassicalEqTmRuleLaws)
    (equality : EqTm Γ left right A) : CSemEq (Γ := Γ) left right A := by
  induction equality with
  | refl typing =>
      intro leftTyping rightTyping env bound expected
      exact leftTyping.certificate.coherent rightTyping.certificate env bound expected
  | symm equality ih =>
      intro leftTyping rightTyping env bound expected
      exact (ih rightTyping leftTyping env bound expected).symm
  | trans first second ih₁ ih₂ =>
      intro leftTyping rightTyping env bound expected
      exact (ih₁ leftTyping first.typing.2 env bound expected).trans
        (ih₂ second.typing.1 rightTyping env bound expected)
  | app leftRaw rightRaw function argument ihf ihx =>
      exact laws.app leftRaw rightRaw ihf ihx
  | lam leftRaw rightRaw hA bodies ih => exact laws.lam leftRaw rightRaw hA ih
  | beta body x hA applicationRaw bodyTyping argumentTyping resultTyping =>
      exact laws.beta hA applicationRaw bodyTyping argumentTyping resultTyping
  | eta name fresh functionTyping etaTyping =>
      exact laws.eta name fresh functionTyping etaTyping

end Nucleus.HolE
