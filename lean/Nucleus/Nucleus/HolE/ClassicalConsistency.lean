import Nucleus.HolE.ClassicalKernelAssembly
import Nucleus.HolE.ClassicalInfinitySoundness

/-! # End-to-end classical soundness and consistency

All semantic transport laws are assembled concretely below, including the
closed soundness and consistency theorems under the concrete infinity axiom.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem Proves.sound (proof : Proves Γ H proposition) :
    CEntails (Γ := Γ) H proposition :=
  proof.sound_of_kernel_laws classicalKernelRuleLaws

theorem classical_consistent :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0) [] (.bool false) → False :=
  no_closed_false_of_sound fun proof => proof.sound

theorem classical_consistent_with_infinity :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0)
      [Infinity.infinityAxiom (Sig := ClassicalSig)] (.bool false) → False :=
  no_closed_false_under_axiom_of_sound
    (Infinity.infinityAxiom (Sig := ClassicalSig))
    Infinity.infinityAxiom_realized
    (fun proof => proof.sound)

end Nucleus.HolE
