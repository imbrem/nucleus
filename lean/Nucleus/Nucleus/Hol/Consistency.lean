import Nucleus.Hol.Proof
import Nucleus.HolOmega.Consistency

/-! Model-independent consistency of the raw monomorphic HOL calculus. -/

namespace Nucleus.Hol

/-- Empty raw HOL cannot derive Boolean false.  The proof is syntactic
reduction to the already model-validated HOL-omega calculus. -/
theorem raw_not_proves_false :
    ¬ Proves ([] : Ctx Empty) [] (.tmBool false) := by
  intro h
  exact HolOmega.raw_not_proves_false (by
    simpa only [Ctx.toOmega, Hyps.toOmega, List.map_nil,
      Expr.toOmega_tmBool] using h.toOmega)

end Nucleus.Hol
