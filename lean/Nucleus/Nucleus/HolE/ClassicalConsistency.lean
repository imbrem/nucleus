import Nucleus.HolE.ClassicalKernelAssembly
import Nucleus.HolE.ClassicalInfinitySoundness

/-! # End-to-end classical soundness and consistency

Supplying the remaining transport record is now the only input needed for the
closed soundness and consistency theorems, including consistency under the
concrete infinity axiom.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem Proves.sound_of_remaining (remaining : ClassicalRemainingKernelLaws)
    (proof : Proves Γ H proposition) : CEntails (Γ := Γ) H proposition :=
  proof.sound_of_kernel_laws remaining.assemble

theorem classical_consistent (remaining : ClassicalRemainingKernelLaws) :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0) [] (.bool false) → False :=
  no_closed_false_of_sound fun proof => proof.sound_of_remaining remaining

theorem classical_consistent_with_infinity
    (remaining : ClassicalRemainingKernelLaws) :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0)
      [Infinity.infinityAxiom (Sig := ClassicalSig)] (.bool false) → False :=
  no_closed_false_under_axiom_of_sound
    (Infinity.infinityAxiom (Sig := ClassicalSig))
    Infinity.infinityAxiom_realized
    (fun proof => proof.sound_of_remaining remaining)

end Nucleus.HolE
