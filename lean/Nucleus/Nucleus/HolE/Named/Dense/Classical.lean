import Nucleus.HolE.Named.Dense.Indexed
import Nucleus.HolE.Named.Lower
import Nucleus.HolE.ClassicalConsistency

/-! # Closed classical relations on an indexed named forest -/

namespace Nucleus.HolE.Named.Unsorted.Dense.Classical

set_option relaxedAutoImplicit true

open Nucleus.HolE
open Nucleus.HolE.Named

/-- Closed provability of an unsorted named tree: check it as a term, lower it,
then ask the classical kernel for a proof with no hypotheses. -/
def Provable (expression : HolE ClassicalSig Nat) : Prop :=
  ∃ named : Named.Tm ClassicalSig,
    Unsorted.check .tm expression = some named ∧
    ∃ lowered : Nucleus.HolE.Tm ClassicalSig [] 0,
      lowerTm .nil .nil named = some lowered ∧
      Nonempty (Nucleus.HolE.Proves
        (emptyBound : BoundCtx ClassicalSig [] 0) [] lowered)

theorem not_provable_false : ¬ Provable (.bool false) := by
  rintro ⟨named, checked, lowered, loweredEq, ⟨proof⟩⟩
  simp only [Unsorted.check, Option.some.injEq] at checked
  subst named
  simp only [lowerTm, Option.some.injEq] at loweredEq
  subst lowered
  exact classical_consistent proof

/-- The concrete consistency statement for an index denoting named `false`. -/
theorem not_isProvable_false {falseIndex : ι}
    (forest : Forest ι (HolE ClassicalSig Nat))
    (lookup : forest falseIndex = some (.bool false)) :
    ¬ IsProvable forest Provable falseIndex :=
  Dense.not_isProvable_false forest Provable (.bool false)
    not_provable_false lookup

end Nucleus.HolE.Named.Unsorted.Dense.Classical
