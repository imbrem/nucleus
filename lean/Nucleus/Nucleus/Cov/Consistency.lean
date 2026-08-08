import Nucleus.Cov.Proof
import Nucleus.Hol.Consistency

/-! Exact empty-context consistency for tree-structured regular HOL. -/

namespace Nucleus.Cov

open Hol

/-- The golden theorem: Covalence cannot prove false.  The universal lowering
theorem is instantiated at the canonical (epsilon-true) shared filling. -/
theorem not_proves_false :
    ¬ Proves ([] : Ctx Empty) [] (At.bool false) := by
  intro h
  exact Hol.raw_not_proves_false (by
    simpa only [lowerHyps, List.map_nil, At.lower_bool] using
      h.sound (canonicalFilling Empty))

end Nucleus.Cov
