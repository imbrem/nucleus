import Nucleus.HolE.ClassicalCoreKernelLaws
import Nucleus.HolE.ClassicalSubtypeKernelLaws
import Nucleus.HolE.ClassicalTypeExistentialKernelLaws
import Nucleus.HolE.ClassicalBoundKernelLaws
import Nucleus.HolE.ClassicalEtaKernelLaw
import Nucleus.HolE.ClassicalBetaKernelLaw
import Nucleus.HolE.ClassicalRawOpeningLaw

/-! # Assembly of the classical kernel soundness laws

This module turns the remaining semantic transport obligations into an exact,
compiler-checked frontier. -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem classicalEqTmRuleLaws : ClassicalEqTmRuleLaws where
  app := classical_eqTm_app
  lam := classical_eqTm_lam
  eq := classical_eqTm_eq
  eps := classical_eqTm_eps
  abs := classical_eqTm_abs
  rep := classical_eqTm_rep
  tyExists := classical_eqTm_tyExists
  beta := classical_eqTm_beta
  eta := classical_eqTm_eta

theorem classicalKernelRuleLaws : ClassicalKernelRuleLaws :=
  let eqLaws := classicalEqTmRuleLaws
  { eqMp := classical_eqMp
    choice := classical_choice
    generalize := classical_generalize
    weakenBound := classical_weakenBound
    convert := classical_convert eqLaws
    eqOfEqTm := classical_eqOfEqTm eqLaws
    antisymm := classical_antisymm
    absRep := CEntails.absRepLaw
    repAbs := CEntails.repAbsLaw classicalRawInstantiateOneTrueLaw
    repPredOfWitness :=
      CEntails.repPredOfWitnessLaw classicalRawInstantiateOneTrueLaw
    tyExistsIntro := fun hA conclusionTyping predicateTyping instanceTyping premise =>
      tyExistsIntro_sound conclusionTyping hA predicateTyping instanceTyping premise
    modelSpec := modelSpec_sound }

end Nucleus.HolE
