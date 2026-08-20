import Nucleus.HolE.Normalization.Reduction

/-!
# Eta normalization

Eta contraction strictly decreases `Reduction.Eta.nodeCount`, so every term
has a normal form independently of typing or signature rules.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace Reduction

/-- The propositional eta relation induced by proof-relevant step certificates. -/
abbrev EtaRelation {Sig : Signature} {types : List Kind} {depth : Nat} :
    Tm Sig types depth → Tm Sig types depth → Prop :=
  fun source target => Nonempty (Eta source target)

/-- A term together with an eta-normal reduct. -/
structure EtaNormalForm {Sig : Signature} {types : List Kind} {depth : Nat}
    (source : Tm Sig types depth) where
  term : Tm Sig types depth
  steps : Relation.ReflTransGen EtaRelation source term
  normal : ¬ ∃ target, EtaRelation term target

/-- Select an eta-normal reduct by well-founded recursion on the node count. -/
noncomputable def etaNormalForm (source : Tm Sig types depth) : EtaNormalForm source := by
  by_cases reducible : ∃ target, EtaRelation source target
  · let target := Classical.choose reducible
    let step : EtaRelation source target := Classical.choose_spec reducible
    let result := etaNormalForm target
    exact ⟨result.term, .head step result.steps, result.normal⟩
  · exact ⟨source, .refl, reducible⟩
termination_by Eta.nodeCount source
decreasing_by
  exact step.elim fun certificate => certificate.nodeCount_lt

/-- An eta sequence is also a beta-eta sequence. -/
theorem etaSteps_to_betaEtaSteps {source target : Tm Sig types depth}
    (steps : Relation.ReflTransGen EtaRelation source target) :
    BetaEtaSteps source target := by
  induction steps with
  | refl => exact .refl
  | tail steps step ih => exact .tail ih (Or.inr step)

/-- Eta normalization preserves syntax-directed typing. -/
theorem etaNormalForm_typing {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {source : Tm Sig types depth}
    {A : Ty Sig types} (typed : TypedCtx Γ) (sourceTyping : HasType Γ source A) :
    HasType Γ (etaNormalForm source).term A :=
  (etaSteps_to_betaEtaSteps (etaNormalForm source).steps).preserve typed sourceTyping

/-- Eta normalization preserves typing modulo family conversion. -/
theorem etaNormalForm_typingDefEq {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source : Tm Sig types depth}
    {A : Ty Sig types} (typed : TypedCtx Γ) (sourceTyping : HasTypeDefEq Γ source A) :
    HasTypeDefEq Γ (etaNormalForm source).term A :=
  (etaSteps_to_betaEtaSteps (etaNormalForm source).steps).preserveDefEq typed sourceTyping

/-- Eta normalization is accepted by kernel conversion. -/
theorem etaNormalForm_eqTm_nonempty {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source : Tm Sig types depth}
    {A : Ty Sig types} (typed : TypedCtx Γ) (sourceTyping : HasType Γ source A) :
    Nonempty (EqTm Γ source (etaNormalForm source).term A) :=
  (etaSteps_to_betaEtaSteps (etaNormalForm source).steps).eqTm_nonempty typed sourceTyping

/-- Eta normalization is kernel conversion at every definitionally equal
advertised type of its source. -/
theorem etaNormalForm_eqTmDefEq_nonempty {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {Γ : BoundCtx Sig types depth} {source : Tm Sig types depth}
    {A : Ty Sig types} (typed : TypedCtx Γ) (sourceTyping : HasTypeDefEq Γ source A) :
    Nonempty (EqTm Γ source (etaNormalForm source).term A) :=
  (etaSteps_to_betaEtaSteps (etaNormalForm source).steps).eqTmDefEq_nonempty
    typed sourceTyping

end Reduction

end Nucleus.HolE
