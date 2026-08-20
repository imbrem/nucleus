import Nucleus.HolE.Named.Conversion

/-!
# Laws for named HolE conversion

This file proves that the compact named judgments in `Named.Conversion` are
sound and complete pullbacks of the existing locally nameless conversion
rules.  It also records the typing information carried by conversion.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace EqTm

/-- Both endpoints of a term-conversion certificate are well typed. -/
theorem endpointsTyping {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {left right : Tm Sig types depth} {A : Ty Sig types}
    (conversion : EqTm Γ left right A) :
    HasTypeDefEq Γ left A ∧ HasTypeDefEq Γ right A := by
  induction conversion with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ leftMiddle middleRight => exact ⟨leftMiddle.1, middleRight.2⟩
  | app leftRaw rightRaw _ _ _ _ _ _ => exact ⟨.exact leftRaw, .exact rightRaw⟩
  | lam leftRaw rightRaw _ _ => exact ⟨.exact leftRaw, .exact rightRaw⟩
  | beta _ _ _ _ applicationRaw _ _ resultTyping =>
      exact ⟨.exact applicationRaw, resultTyping⟩
  | eta _ _ _ functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

/-- The left endpoint of a term-conversion certificate is well typed. -/
theorem leftTyping {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {left right : Tm Sig types depth} {A : Ty Sig types}
    (conversion : EqTm Γ left right A) : HasTypeDefEq Γ left A :=
  conversion.endpointsTyping.1

/-- The right endpoint of a term-conversion certificate is well typed. -/
theorem rightTyping {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {left right : Tm Sig types depth} {A : Ty Sig types}
    (conversion : EqTm Γ left right A) : HasTypeDefEq Γ right A :=
  conversion.endpointsTyping.2

end EqTm

end Nucleus.HolE

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

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

namespace FamEq

def refl {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {family : Fam Sig kind}
    {lowered : Nucleus.HolE.Fam Sig types kind}
    (lowering : lowerFam typeScope family = some lowered) :
    FamEq typeScope family family :=
  ⟨lowered, lowered, lowering, lowering, .refl⟩

def symm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {left right : Fam Sig kind}
    (conversion : FamEq typeScope left right) :
    FamEq typeScope right left :=
  ⟨conversion.loweredRight, conversion.loweredLeft,
    conversion.rightLowering, conversion.leftLowering, conversion.derivation.symm⟩

/-- Family conversion is transitive when its middle family is well kinded.
This premise is required by the underlying HolE kernel rule. -/
def trans {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {left middle right : Fam Sig kind}
    (leftMiddle : FamEq typeScope left middle)
    (middleKinded : Nucleus.HolE.Kinded leftMiddle.loweredRight)
    (middleRight : FamEq typeScope middle right) :
    FamEq typeScope left right := by
  rcases leftMiddle with ⟨loweredLeft, loweredMiddle, leftLowering,
    middleLowering, leftDerivation⟩
  rcases middleRight with ⟨loweredMiddle', loweredRight, middleLowering',
    rightLowering, rightDerivation⟩
  rw [middleLowering] at middleLowering'
  have same := Option.some.inj middleLowering'
  cases same
  exact ⟨loweredLeft, loweredRight, leftLowering, rightLowering,
    leftDerivation.trans middleKinded rightDerivation⟩

/-- Projection to the locally nameless family-conversion certificate. -/
def sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {left right : Fam Sig kind}
    (conversion : FamEq typeScope left right) :
    Nucleus.HolE.FamEq Sig conversion.loweredLeft conversion.loweredRight :=
  conversion.derivation

/-- Lift a locally nameless family conversion along fixed named preimages. -/
def complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {left right : Fam Sig kind}
    {loweredLeft loweredRight : Nucleus.HolE.Fam Sig types kind}
    (leftLowering : lowerFam typeScope left = some loweredLeft)
    (rightLowering : lowerFam typeScope right = some loweredRight)
    (derivation : Nucleus.HolE.FamEq Sig loweredLeft loweredRight) :
    FamEq typeScope left right :=
  ⟨loweredLeft, loweredRight, leftLowering, rightLowering, derivation⟩

end FamEq

namespace TmConv

theorem refl {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {term : Tm Sig} {A : Ty Sig}
    (typing : HasType typeScope termScope Γ term A) :
    TmConv typeScope termScope Γ term term A := by
  obtain ⟨loweredTerm, loweredClassification, termLowering,
    classificationLowering, derivation⟩ := typing
  cases loweredClassification with
  | tm loweredType =>
      have typeLowering := lowerClassification_tm_some classificationLowering
      exact ⟨⟨loweredTerm, loweredTerm, loweredType, termLowering, termLowering,
        typeLowering, .refl (.exact derivation)⟩⟩

theorem symm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {left right : Tm Sig} {A : Ty Sig}
    (conversion : TmConv typeScope termScope Γ left right A) :
    TmConv typeScope termScope Γ right left A := by
  obtain ⟨conversion⟩ := conversion
  exact ⟨⟨conversion.loweredRight, conversion.loweredLeft, conversion.loweredType,
    conversion.rightLowering, conversion.leftLowering, conversion.typeLowering,
    conversion.derivation.symm⟩⟩

theorem trans {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left middle right : Tm Sig} {A : Ty Sig}
    (leftMiddle : TmConv typeScope termScope Γ left middle A)
    (middleRight : TmConv typeScope termScope Γ middle right A) :
    TmConv typeScope termScope Γ left right A := by
  obtain ⟨⟨loweredLeft, loweredMiddle, loweredType, leftLowering,
    middleLowering, typeLowering, leftDerivation⟩⟩ := leftMiddle
  obtain ⟨⟨loweredMiddle', loweredRight, loweredType', middleLowering',
    rightLowering, typeLowering', rightDerivation⟩⟩ := middleRight
  rw [middleLowering] at middleLowering'
  have termsSame := Option.some.inj middleLowering'
  cases termsSame
  rw [typeLowering] at typeLowering'
  have typesSame := Option.some.inj typeLowering'
  cases typesSame
  exact ⟨⟨loweredLeft, loweredRight, loweredType, leftLowering,
    rightLowering, typeLowering, leftDerivation.trans rightDerivation⟩⟩

/-- Named conversion is sound with respect to locally nameless conversion. -/
theorem sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left right : Tm Sig} {A : Ty Sig}
    (conversion : TmConv typeScope termScope Γ left right A) :
    ∃ loweredLeft loweredRight loweredType,
      lowerTm typeScope termScope left = some loweredLeft ∧
      lowerTm typeScope termScope right = some loweredRight ∧
      lowerTy typeScope A = some loweredType ∧
      Nonempty (Nucleus.HolE.EqTm Γ loweredLeft loweredRight loweredType) := by
  obtain ⟨conversion⟩ := conversion
  exact ⟨conversion.loweredLeft, conversion.loweredRight, conversion.loweredType,
    conversion.leftLowering, conversion.rightLowering, conversion.typeLowering,
    ⟨conversion.derivation⟩⟩

/-- Every locally nameless conversion over fixed named preimages lifts back. -/
theorem complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left right : Tm Sig} {A : Ty Sig}
    {loweredLeft loweredRight : Nucleus.HolE.Tm Sig types depth}
    {loweredType : Nucleus.HolE.Ty Sig types}
    (leftLowering : lowerTm typeScope termScope left = some loweredLeft)
    (rightLowering : lowerTm typeScope termScope right = some loweredRight)
    (typeLowering : lowerTy typeScope A = some loweredType)
    (conversion : Nonempty (Nucleus.HolE.EqTm Γ loweredLeft loweredRight loweredType)) :
    TmConv typeScope termScope Γ left right A := by
  obtain ⟨conversion⟩ := conversion
  exact ⟨⟨loweredLeft, loweredRight, loweredType, leftLowering, rightLowering,
    typeLowering, conversion⟩⟩

/-- Conversion preserves the declared type at its left endpoint. -/
theorem leftTyping {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left right : Tm Sig} {A : Ty Sig}
    (conversion : TmConv typeScope termScope Γ left right A) :
    HasTypeConv typeScope termScope Γ left A := by
  obtain ⟨conversion⟩ := conversion
  exact ⟨conversion.loweredLeft, conversion.loweredType,
    conversion.leftLowering, conversion.typeLowering,
    conversion.derivation.leftTyping⟩

/-- Conversion preserves the declared type at its right endpoint. -/
theorem rightTyping {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left right : Tm Sig} {A : Ty Sig}
    (conversion : TmConv typeScope termScope Γ left right A) :
    HasTypeConv typeScope termScope Γ right A := by
  obtain ⟨conversion⟩ := conversion
  exact ⟨conversion.loweredRight, conversion.loweredType,
    conversion.rightLowering, conversion.typeLowering,
    conversion.derivation.rightTyping⟩

/-- Kernel conversion proves the corresponding object-language equality.

The explicit conclusion check is the premise required by `Proves.eqOfEqTm`:
the kernel deliberately does not reconstruct raw syntax-directed typing from
a conversion-modulo-type-equality certificate. -/
theorem provesEquality {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {termScope : TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {left right : Tm Sig} {A : Ty Sig}
    (conversion : TmConv typeScope termScope Γ left right A)
    (hypothesesTyping : TypedHyps typeScope termScope Γ hypotheses)
    (conclusionTyping : HasType typeScope termScope Γ (.eq A left right) .boolTy) :
    Nonempty (Proves typeScope termScope Γ hypotheses (.eq A left right)) := by
  obtain ⟨conversion⟩ := conversion
  obtain ⟨loweredHypotheses, hypothesesLowering, typedHypotheses⟩ :=
    hypothesesTyping
  obtain ⟨loweredConclusion, loweredClassification, conclusionLowering,
    classificationLowering, rawConclusionTyping⟩ := conclusionTyping
  cases loweredClassification with
  | tm loweredConclusionType =>
      have conclusionTypeLowering :=
        lowerClassification_tm_some classificationLowering
      have conclusionType : loweredConclusionType = Nucleus.HolE.Expr.boolTy := by
        simpa [lowerTy, lowerFam] using conclusionTypeLowering.symm
      subst loweredConclusionType
      have equalityTypeLowering := conversion.typeLowering
      change lowerFam typeScope A = some conversion.loweredType at equalityTypeLowering
      have expectedLowering :
          lowerTm typeScope termScope (.eq A left right) =
            some (.eq conversion.loweredType conversion.loweredLeft
              conversion.loweredRight) := by
        simp [lowerTm, equalityTypeLowering, conversion.leftLowering,
          conversion.rightLowering]
      change lowerTm typeScope termScope (.eq A left right) =
        some loweredConclusion at conclusionLowering
      rw [expectedLowering] at conclusionLowering
      have conclusionSame := Option.some.inj conclusionLowering
      subst loweredConclusion
      let typeKinded := conversion.derivation.leftTyping.typeKinded
      let proof : Nucleus.HolE.Proves Γ loweredHypotheses
          (.eq conversion.loweredType conversion.loweredLeft
            conversion.loweredRight) :=
        .eqOfEqTm typedHypotheses typeKinded (.exact rawConclusionTyping)
          conversion.derivation
      exact ⟨⟨loweredHypotheses,
        .eq conversion.loweredType conversion.loweredLeft conversion.loweredRight,
        hypothesesLowering, expectedLowering, proof⟩⟩

end TmConv

namespace FamBeta

/-- The beta redex is well kinded when its body and argument are. -/
theorem sourceKinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {typeScope : TyScope types} {source target : Fam Sig codomain}
    (step : FamBeta typeScope source target)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    Kinded typeScope source := by
  refine Checks.complete step.sourceLowering rfl ?_
  exact .tyApp (.tyLam bodyKinded) argumentKinded

/-- Type-family beta reduction preserves kinding. -/
theorem targetKinded {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {typeScope : TyScope types} {source target : Fam Sig codomain}
    (step : FamBeta typeScope source target)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    Kinded typeScope target := by
  refine Checks.complete step.targetLowering rfl ?_
  exact bodyKinded.openType argumentKinded

/-- Type-family beta is precisely a named family conversion. -/
def toFamEq {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {typeScope : TyScope types} {source target : Fam Sig codomain}
    (step : FamBeta typeScope source target)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    FamEq typeScope source target :=
  ⟨.tyApp (.tyLam step.body) step.argument,
    Nucleus.HolE.openType step.body step.argument,
    step.sourceLowering, step.targetLowering,
    .beta step.body step.argument bodyKinded argumentKinded⟩

end FamBeta

private theorem betaEqOfTyping {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {domain result : Nucleus.HolE.Ty Sig types}
    {body : Nucleus.HolE.Tm Sig types (depth + 1)}
    {argument : Nucleus.HolE.Tm Sig types depth}
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (typing : Nucleus.HolE.HasType Γ (.app (.lam domain body) argument) result) :
    Nonempty (Nucleus.HolE.EqTm Γ (.app (.lam domain body) argument)
      (Nucleus.HolE.openBound body argument) result) := by
  cases typing with
  | app functionTyping argumentTyping =>
      cases functionTyping with
      | lam _ domainKinded bodyTyping =>
          exact ⟨.beta body argument domainKinded typedContext
            (.app (.lam body domainKinded bodyTyping) argumentTyping)
            (.exact bodyTyping) (.exact argumentTyping)
            (.exact (Nucleus.HolE.HasType.openBound
              typedContext bodyTyping argumentTyping))⟩

namespace TmBeta

/-- A well-typed beta contraction is kernel term equality.  The target typing
is obtained by substitution, rather than assumed. -/
theorem toTmConv {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {source target : Tm Sig} {result : Ty Sig}
    (step : TmBeta typeScope termScope source target)
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source result) :
    TmConv typeScope termScope Γ source target result := by
  obtain ⟨loweredSource, loweredResult, sourceLowering, resultLowering,
    typing⟩ := sourceTyping
  cases loweredResult with
  | tm loweredType =>
    have typeLowering := lowerClassification_tm_some resultLowering
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [step.sourceLowering] at sourceLowering
    have same := Option.some.inj sourceLowering
    subst loweredSource
    obtain ⟨betaDerivation⟩ := betaEqOfTyping typedContext typing
    exact ⟨⟨.app (.lam step.domain step.body) step.argument,
      Nucleus.HolE.openBound step.body step.argument, loweredType,
      step.sourceLowering, step.targetLowering, typeLowering, betaDerivation⟩⟩

/-- Beta reduction preserves typing modulo family conversion. -/
theorem preservation {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {source target : Tm Sig} {result : Ty Sig}
    (step : TmBeta typeScope termScope source target)
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source result) :
    HasTypeConv typeScope termScope Γ target result :=
  (step.toTmConv typedContext sourceTyping).rightTyping

end TmBeta

namespace TmEta

/-- A well-typed eta contraction is kernel term equality. -/
theorem toTmConv {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {source target : Tm Sig} {result : Ty Sig}
    (step : TmEta typeScope termScope source target)
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source result) :
    TmConv typeScope termScope Γ source target result := by
  obtain ⟨loweredSource, loweredResult, sourceLowering, resultLowering,
    sourceRaw⟩ := sourceTyping
  cases loweredResult with
  | tm loweredType =>
    have typeLowering := lowerClassification_tm_some resultLowering
    change lowerTm typeScope termScope source = some loweredSource at sourceLowering
    rw [step.sourceLowering] at sourceLowering
    have sourceSame := Option.some.inj sourceLowering
    subst loweredSource
    cases sourceRaw with
    | lam _ domainKinded bodyTyping =>
        cases bodyTyping with
        | app functionTyping argumentTyping =>
            cases argumentTyping with
            | bv argumentKinded lookup =>
                cases lookup
                let targetRaw := Nucleus.HolE.HasType.ofWeaken functionTyping
                exact ⟨⟨.lam step.domain
                  (.app (Nucleus.HolE.weaken step.function) (.bv 0)),
                  step.function, _, step.sourceLowering, step.targetLowering,
                  typeLowering,
                  .eta step.freshName step.fresh typedContext (.exact targetRaw)
                    (.exact (.lam _ domainKinded
                      (.app functionTyping (.bv argumentKinded rfl))))⟩⟩

/-- Eta reduction preserves typing. -/
theorem preservation {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {source target : Tm Sig} {result : Ty Sig}
    (step : TmEta typeScope termScope source target)
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (sourceTyping : HasType typeScope termScope Γ source result) :
    HasTypeConv typeScope termScope Γ target result :=
  (step.toTmConv typedContext sourceTyping).rightTyping

end TmEta

end Nucleus.HolE.Named
