import Nucleus.HolE.ClassicalCoreKernelLaws
import Nucleus.HolE.ClassicalSubtypeKernelLaws
import Nucleus.HolE.ClassicalTypeExistentialKernelLaws
import Nucleus.HolE.ClassicalBoundKernelLaws

/-! # Assembly of the classical kernel soundness laws

This module turns the remaining semantic transport obligations into an exact,
compiler-checked frontier. -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

structure ClassicalRemainingEqTmLaws where
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

theorem ClassicalRemainingEqTmLaws.assemble
    (remaining : ClassicalRemainingEqTmLaws) : ClassicalEqTmRuleLaws where
  app := classical_eqTm_app
  lam := classical_eqTm_lam
  beta := remaining.beta
  eta := remaining.eta

structure ClassicalRemainingKernelLaws where
  eqTm : ClassicalRemainingEqTmLaws
  opening : CInstantiateOneTrueLaw

theorem ClassicalRemainingKernelLaws.assemble
    (remaining : ClassicalRemainingKernelLaws) : ClassicalKernelRuleLaws :=
  let eqLaws := remaining.eqTm.assemble
  { eqMp := classical_eqMp
    choice := classical_choice
    generalize := classical_generalize
    weakenBound := classical_weakenBound
    convert := classical_convert eqLaws
    eqOfEqTm := classical_eqOfEqTm eqLaws
    antisymm := classical_antisymm
    absRep := CEntails.absRepLaw
    repAbs := CEntails.repAbsLaw remaining.opening
    repPredOfWitness := CEntails.repPredOfWitnessLaw remaining.opening
    tyExistsIntro := fun hA conclusionTyping predicateTyping instanceTyping premise =>
      tyExistsIntro_sound conclusionTyping hA predicateTyping instanceTyping premise
    modelSpec := modelSpec_sound }

end Nucleus.HolE
