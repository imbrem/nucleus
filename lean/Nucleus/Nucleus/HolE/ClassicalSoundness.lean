import Nucleus.HolE.ClassicalSemantics

/-! # Soundness interface for the deterministic classical HolE semantics

This file is deliberately downstream of `ClassicalSemantics`: it records the
semantic invariants required by the kernel proof without coupling the evaluator
to the syntactic substitution development.
-/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

/-- Typing modulo family conversion still determines a well-kinded result
type.  This is useful independently of semantics and lets semantic evaluation
always choose the denotation of the advertised result type. -/
theorem HasTypeDefEq.typeKinded {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A) : Kinded A := by
  induction typing with
  | exact raw => exact raw.typeKinded
  | app _ _ ihf _ =>
      cases ihf with
      | arr _ hB => exact hB
  | lam _ hA _ ih => exact .arr hA ih
  | eq | tyExists => exact .boolTy
  | eps hA _ _ | rep hA _ _ _ => exact hA
  | abs hA hp _ _ => exact .sub hA hp
  | conv _ hB _ _ => exact hB

/-- Both sides of a kernel term equality have its advertised type. -/
theorem EqTm.typing {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {left right : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (equality : EqTm Γ left right A) :
    HasTypeDefEq Γ left A ∧ HasTypeDefEq Γ right A := by
  induction equality with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | lam hA _ ih => exact ⟨.lam _ hA ih.1, .lam _ hA ih.2⟩
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      exact ⟨.app (.lam body hA bodyTyping) argumentTyping, resultTyping⟩
  | eta name fresh functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

/-- A typed context paired with the polymorphic bound environment consumed by
`cSem`.  At a lookup, the evaluator specializes `bound` to the denotation of
the type certified by `typed`. -/
structure CContextEnv {types : List Kind} {depth : Nat}
    (Γ : BoundCtx ClassicalSig types depth) where
  typed : TypedCtx Γ
  bound : CBoundEnv depth

/-- Truth of hypotheses, parameterized by the eventual evaluator for typing
modulo `FamEq`.  Keeping this predicate evaluator-parametric separates the
logical induction from the conversion/substitution proof. -/
def CHypsTrue {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (eval : ∀ {term A}, HasTypeDefEq Γ term A →
      CTypeEnv types → CBoundEnv depth → CPointed → Bool)
    (typeEnv : CTypeEnv types) (bound : CBoundEnv depth)
    (hypotheses : List (Tm ClassicalSig types depth)) : Prop :=
  ∀ proposition, proposition ∈ hypotheses →
    ∀ typing : HasTypeDefEq Γ proposition .boolTy,
      eval typing typeEnv bound cBool = true

/-- The two fundamental transport facts needed by beta, eta, generalization,
and type quantification.  They are intentionally named here so the kernel
proof and the substitution proof can be developed independently. -/
structure ClassicalTransportLaws where
  famEq_sound : ∀ {types kind} {A B : Fam ClassicalSig types kind}
      (hA : Kinded A) (hB : Kinded B),
    FamEq ClassicalSig A B → ∀ env,
      denoteChecked hA env = denoteChecked hB env

end Nucleus.HolE
