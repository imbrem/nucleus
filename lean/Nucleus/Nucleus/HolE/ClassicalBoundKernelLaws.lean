import Nucleus.HolE.ClassicalBoundTransport

/-! # Classical kernel laws for bound-variable transport -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

theorem classical_weakenBound
    {Γ : BoundCtx ClassicalSig types depth}
    {H : List (Tm ClassicalSig types depth)} {A : Ty ClassicalSig types}
    {K : List (Tm ClassicalSig types (depth + 1))}
    {p : Tm ClassicalSig types depth}
    (typed : TypedHyps Γ H) (_hA : Kinded A)
    (conclusionTyping : HasTypeDefEq (extendBound A Γ) (weaken p) .boolTy)
    (embedding : ∀ q, q ∈ H → weaken q ∈ K)
    (premise : CEntails (Γ := Γ) H p) :
    CEntails (Γ := extendBound A Γ) K (weaken p) := by
  intro env bound truthsK
  have truthsH : CHypsTrue (Γ := Γ) env (bound.rename Fin.succ) H := by
    intro q member
    exact (truthsK (weaken q) (embedding q member)).of_weakenAt (typed q member)
  obtain ⟨source, sourceTrue⟩ := premise env (bound.rename Fin.succ) truthsH
  let target := conclusionTyping.certificate
  refine ⟨target, ?_⟩
  exact (cDefSem_weaken source target env bound cBool).trans sourceTrue

end Nucleus.HolE
