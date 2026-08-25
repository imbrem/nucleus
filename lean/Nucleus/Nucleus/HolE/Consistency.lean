import Nucleus.HolE.Infinity
import Nucleus.HolE.ClassicalSoundness

/-! # Final consistency interfaces for HolE -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Empty-theory consistency is a purely syntactic corollary of consistency
with infinity: a proof using no hypotheses can be weakened to the singleton
infinity hypothesis. -/
theorem empty_consistency_of_infinity_consistency
    (withInfinity : Proves (emptyBound : BoundCtx ClassicalSig [] 0)
      [Infinity.infinityAxiom (Sig := ClassicalSig)] (.bool false) → False) :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0) [] (.bool false) → False := by
  intro proof
  apply withInfinity
  -- `mapHypotheses` reads the conclusion's typing off the proof itself, which
  -- is exactly what weakening an empty hypothesis list needs.
  refine Proves.mapHypotheses
    (K := [Infinity.infinityAxiom (Sig := ClassicalSig)])
    (H := []) ?_ ?_ proof
  · intro proposition member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst proposition
    exact .exact Infinity.axiom_typed
  · intro proposition member
    nomatch member

end Nucleus.HolE
