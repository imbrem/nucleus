import Nucleus.HolE.ClassicalInfinitySoundness
import Nucleus.HolE.ClassicalRealization

/-! # Equivalence of intrinsic evaluation and deterministic realization -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace Infinity

/-- The older universally quantified evaluator for an intrinsically checked
term and the newer certificate-based deterministic realization relation have
the same values.  This lets derived userspace syntax reuse its established
semantic laws without adding a second trusted interpretation. -/
theorem IEval.iff_cRealizes
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    {term : InfinityTm ClassicalSig Γ A} {env : CTypeEnv types}
    {bound : CBoundEnv depth} {expected : CPointed}
    {value : expected.carrier} :
    IEval term env bound expected value ↔
      CRealizes (Γ := Γ) env bound term.tm A expected value := by
  constructor
  · intro evaluation
    exact ⟨.exact term.typing.certificate,
      evaluation term.typing.certificate⟩
  · intro realizes
    let canonical := iValue term env bound expected
    have canonicalEvaluation : IEval term env bound expected canonical :=
      IEval.canonical term env bound expected
    have canonicalRealizes :
        CRealizes (Γ := Γ) env bound term.tm A expected canonical :=
      ⟨.exact term.typing.certificate,
        canonicalEvaluation term.typing.certificate⟩
    have equal : value = canonical :=
      realizes.value_unique canonicalRealizes
    rw [equal]
    exact canonicalEvaluation

end Infinity

end Nucleus.HolE
