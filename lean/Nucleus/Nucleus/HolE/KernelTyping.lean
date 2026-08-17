import Nucleus.HolE.ClassicalSoundness

/-! # Typing inversion for HolE proof certificates -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Every proof certificate concludes a Boolean term.  Keeping this theorem
separate from semantic soundness makes the latter's evaluator arguments
canonical and also audits coverage of every kernel rule. -/
theorem Proves.conclusionTyping
    {Γ : BoundCtx ClassicalSig types depth} {H : List (Tm ClassicalSig types depth)}
    {p : Tm ClassicalSig types depth} (proof : Proves Γ H p) :
    HasTypeDefEq Γ p .boolTy := by
  induction proof with
  | hyp typed member => exact typed _ member
  | truth => exact .exact (.bool true)
  | falseElim _ hp _ => exact hp
  | boolCases _ _ _ _ _ _ ihLeft _ => exact ihLeft
  | eqRefl _ hA hx => exact .eq hA hx hx
  | eqMp _ _ hp _ hy _ _ _ => exact .app hp hy
  | choice _ hA hp _ _ _ => exact .app hp (.eps hA hp)
  | generalize _ hA bodyTyping _ _ =>
      exact .eq (.arr hA .boolTy) (.lam _ hA bodyTyping)
        (.lam _ hA (.exact (.bool true)))
  | weakenBound _ _ _ _ _ ih => exact ih.weaken
  | hypothesisMap _ _ _ ih => exact ih
  | convert _ equality _ _ => exact equality.typing.2
  | eqOfEqTm _ hA equality =>
      exact .eq hA equality.typing.1 equality.typing.2
  | antisymm _ hp hq _ _ _ _ _ _ => exact .eq .boolTy hp hq
  | absRep _ hA hp hx =>
      exact .eq (.sub hA hp) (.abs hA hp (.rep hA hp hx)) hx
  | repAbs _ hA hp hx _ _ _ =>
      exact .eq hA (.rep hA hp (.abs hA hp hx)) hx
  | repPredOfWitness _ _ _ _ _ _ resultTyping _ _ => exact resultTyping
  | tyExistsIntro _ _ predicateTyping _ _ _ => exact .tyExists predicateTyping
  | modelSpec _ _ modelInstanceTyping _ _ => exact modelInstanceTyping

end Nucleus.HolE
