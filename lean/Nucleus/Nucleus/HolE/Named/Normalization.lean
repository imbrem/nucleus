import Nucleus.HolE.Named.Kernel
import Nucleus.HolE.Normalization.Reduction

/-!
# Beta and eta reduction for named HolE

The named relations are exact pullbacks of locally nameless reduction. Alpha
equivalent presentations therefore share the same reduction certificates.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

namespace Reduction

/-- One named beta step, represented by the corresponding locally nameless
step between the lowered endpoints. -/
structure Beta {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  loweredSource : Nucleus.HolE.Tm Sig types depth
  loweredTarget : Nucleus.HolE.Tm Sig types depth
  sourceLowering : lowerTm typeScope termScope source = some loweredSource
  targetLowering : lowerTm typeScope termScope target = some loweredTarget
  derivation : Nucleus.HolE.Reduction.Beta loweredSource loweredTarget

/-- One named eta step. -/
structure Eta {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  loweredSource : Nucleus.HolE.Tm Sig types depth
  loweredTarget : Nucleus.HolE.Tm Sig types depth
  sourceLowering : lowerTm typeScope termScope source = some loweredSource
  targetLowering : lowerTm typeScope termScope target = some loweredTarget
  derivation : Nucleus.HolE.Reduction.Eta loweredSource loweredTarget

/-- One named beta-or-eta step. -/
structure BetaEta {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  loweredSource : Nucleus.HolE.Tm Sig types depth
  loweredTarget : Nucleus.HolE.Tm Sig types depth
  sourceLowering : lowerTm typeScope termScope source = some loweredSource
  targetLowering : lowerTm typeScope termScope target = some loweredTarget
  derivation : Nucleus.HolE.Reduction.BetaEta loweredSource loweredTarget

/-- A named beta-eta reduction sequence. -/
structure BetaEtaSteps {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  loweredSource : Nucleus.HolE.Tm Sig types depth
  loweredTarget : Nucleus.HolE.Tm Sig types depth
  sourceLowering : lowerTm typeScope termScope source = some loweredSource
  targetLowering : lowerTm typeScope termScope target = some loweredTarget
  derivation : Nucleus.HolE.Reduction.BetaEtaSteps loweredSource loweredTarget

def Beta.toBetaEta (step : Beta typeScope termScope source target) :
    BetaEta typeScope termScope source target :=
  ⟨step.loweredSource, step.loweredTarget, step.sourceLowering,
    step.targetLowering, Or.inl ⟨step.derivation⟩⟩

def Eta.toBetaEta (step : Eta typeScope termScope source target) :
    BetaEta typeScope termScope source target :=
  ⟨step.loweredSource, step.loweredTarget, step.sourceLowering,
    step.targetLowering, Or.inr ⟨step.derivation⟩⟩

private theorem lowerClassification_tm_some
    {typeScope : TyScope types} {Sig : Signature} {A : Ty Sig}
    {loweredType : Nucleus.HolE.Ty Sig types}
    (lowering : lowerClassification typeScope (.tm A) = some (.tm loweredType)) :
    lowerTy typeScope A = some loweredType := by
  change (do
    let type ← lowerTy typeScope A
    pure (Nucleus.HolE.Classification.tm type)) =
      some (Nucleus.HolE.Classification.tm loweredType) at lowering
  cases equation : lowerTy typeScope A with
  | none => simp [equation] at lowering
  | some actual =>
      simp [equation] at lowering
      subst actual
      rfl

namespace BetaEta

/-- Alpha conversion of the source does not change a named reduction step. -/
theorem alphaSource (step : BetaEta typeScope termScope source target)
    (equivalent : Alpha typeScope termScope source source') :
    Nonempty (BetaEta typeScope termScope source' target) := by
  obtain ⟨lowered, sourceLowering, source'Lowering⟩ := equivalent
  change lowerTm typeScope termScope source = some lowered at sourceLowering
  change lowerTm typeScope termScope source' = some lowered at source'Lowering
  rw [step.sourceLowering] at sourceLowering
  have loweredEqual := Option.some.inj sourceLowering
  subst lowered
  exact ⟨⟨step.loweredSource, step.loweredTarget, source'Lowering,
    step.targetLowering, step.derivation⟩⟩

/-- Alpha conversion of the target does not change a named reduction step. -/
theorem alphaTarget (step : BetaEta typeScope termScope source target)
    (equivalent : Alpha typeScope termScope target target') :
    Nonempty (BetaEta typeScope termScope source target') := by
  obtain ⟨lowered, targetLowering, target'Lowering⟩ := equivalent
  change lowerTm typeScope termScope target = some lowered at targetLowering
  change lowerTm typeScope termScope target' = some lowered at target'Lowering
  rw [step.targetLowering] at targetLowering
  have loweredEqual := Option.some.inj targetLowering
  subst lowered
  exact ⟨⟨step.loweredSource, step.loweredTarget, step.sourceLowering,
    target'Lowering, step.derivation⟩⟩

/-- Named reduction preserves named typing because lowering preserves it. -/
theorem preserve {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {source target : Tm Sig}
    {A : Ty Sig} (step : BetaEta typeScope termScope source target)
    (typed : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source A) :
    HasType typeScope termScope Γ target A := by
  obtain ⟨loweredSource, loweredClassification, sourceLowering,
    classificationLowering, rawTyping⟩ := sourceTyping
  cases loweredClassification with
  | tm loweredType =>
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [step.sourceLowering] at sourceLowering
    have sourceEqual := Option.some.inj sourceLowering
    subst loweredSource
    exact ⟨step.loweredTarget, .tm loweredType, step.targetLowering,
      classificationLowering, step.derivation.preserve typed rawTyping⟩

/-- A typed named step yields a named kernel conversion certificate. -/
theorem eqTm_nonempty {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {source target : Tm Sig}
    {A : Ty Sig} (step : BetaEta typeScope termScope source target)
    (typed : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source A) :
    Nonempty (EqTm typeScope termScope Γ source target A) := by
  obtain ⟨loweredSource, loweredClassification, sourceLowering,
    classificationLowering, rawTyping⟩ := sourceTyping
  cases loweredClassification with
  | tm loweredType =>
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [step.sourceLowering] at sourceLowering
    have sourceEqual := Option.some.inj sourceLowering
    subst loweredSource
    have typeLowering := lowerClassification_tm_some classificationLowering
    obtain ⟨derivation⟩ := step.derivation.eqTm_nonempty typed rawTyping
    exact ⟨⟨step.loweredSource, step.loweredTarget, loweredType,
      step.sourceLowering, step.targetLowering, typeLowering, derivation⟩⟩

end BetaEta

namespace BetaEtaSteps

/-- Named reduction sequences preserve named typing. -/
theorem preserve {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {source target : Tm Sig}
    {A : Ty Sig} (steps : BetaEtaSteps typeScope termScope source target)
    (typed : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source A) :
    HasType typeScope termScope Γ target A := by
  obtain ⟨loweredSource, loweredClassification, sourceLowering,
    classificationLowering, rawTyping⟩ := sourceTyping
  cases loweredClassification with
  | tm loweredType =>
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [steps.sourceLowering] at sourceLowering
    have sourceEqual := Option.some.inj sourceLowering
    subst loweredSource
    exact ⟨steps.loweredTarget, .tm loweredType, steps.targetLowering,
      classificationLowering, steps.derivation.preserve typed rawTyping⟩

/-- A typed named reduction sequence yields named kernel conversion. -/
theorem eqTm_nonempty {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {source target : Tm Sig}
    {A : Ty Sig} (steps : BetaEtaSteps typeScope termScope source target)
    (typed : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source A) :
    Nonempty (EqTm typeScope termScope Γ source target A) := by
  obtain ⟨loweredSource, loweredClassification, sourceLowering,
    classificationLowering, rawTyping⟩ := sourceTyping
  cases loweredClassification with
  | tm loweredType =>
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [steps.sourceLowering] at sourceLowering
    have sourceEqual := Option.some.inj sourceLowering
    subst loweredSource
    have typeLowering := lowerClassification_tm_some classificationLowering
    obtain ⟨derivation⟩ := steps.derivation.eqTm_nonempty typed rawTyping
    exact ⟨⟨steps.loweredSource, steps.loweredTarget, loweredType,
      steps.sourceLowering, steps.targetLowering, typeLowering, derivation⟩⟩

end BetaEtaSteps

end Reduction

end Nucleus.HolE.Named
