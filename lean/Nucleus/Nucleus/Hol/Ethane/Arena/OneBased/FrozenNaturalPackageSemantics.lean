import Nucleus.Hol.Ethane.Arena.OneBased.FrozenInit
import Nucleus.Hol.Ethane.Arena.OneBased.NaturalPackageSemantics

/-!
# Exact semantic boundary for the frozen natural package

The generated evidence required here consists only of production-decoder
identity, checked resolution and intrinsic lowering at the three declaration
roots, and exact premise-free theorem rows at the three law roots.  Evaluator
values are selected canonically by deterministic HolE semantics.

The userspace S-expression compiler and its name dictionary are deliberately
absent.
-/

namespace Nucleus.Hol.Ethane.OneBased.Layout

open Nucleus.Hol.Ethane.ClassicalMatrix
open Nucleus.Hol.Ethane.OneBased

set_option relaxedAutoImplicit true

/-- Non-vacuous representation certificate for the six frozen natural roots.
Unlike `IntrinsicNaturalPackageCertificate`, this structure does not assume
semantic evaluator witnesses or an already assembled natural certificate. -/
structure FrozenNaturalPackageRows (resolve : Resolver) (arena : Arena) extends
    IntrinsicNaturalPackageRows resolve arena
      (closedEvaluationInterpretation resolve arena)
      FrozenInit.naturalCarrier FrozenInit.naturalZero
      FrozenInit.naturalSuccessor FrozenInit.naturalSuccessorInjective
      FrozenInit.naturalZeroNeSuccessor FrozenInit.naturalInduction where
  decoded : FrozenInit.arena? = some arena

namespace FrozenNaturalPackageRows

/-- Exact decoded frozen rows certify a classical natural-number model using
only the checked arena invariant and its explicit ambient assumptions. -/
noncomputable def certify {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena} (rows : FrozenNaturalPackageRows resolve arena)
    (valid : arena.KernelValid trusted resolve
      (closedEvaluationInterpretation resolve arena))
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    Nucleus.HolE.Infinity.CNatModel :=
  rows.toIntrinsicNaturalPackageRows.toCertificate.certify valid
    ambientValuation admitted

@[simp] theorem certify_declaration {trusted : Arena → Prop}
    {resolve : Resolver} {arena : Arena}
    (rows : FrozenNaturalPackageRows resolve arena)
    (valid : arena.KernelValid trusted resolve
      (closedEvaluationInterpretation resolve arena))
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    (rows.certify valid ambientValuation admitted).declaration =
      rows.toIntrinsicNaturalPackageRows.toCertificate.toCertificate.declaration := by
  exact IntrinsicNaturalPackageCertificate.certify_declaration _ _ _ _

end FrozenNaturalPackageRows

end Nucleus.Hol.Ethane.OneBased.Layout
