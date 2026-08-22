import Nucleus.Hol.Ethane.Arena.OneBased.Cas
import Nucleus.Hol.Ethane.Arena.OneBased.Inference
import Nucleus.Hol.Ethane.Reference
import Nucleus.HolE.Named.ConversionLaws

/-!
# Checked one-based Ethane kernel states

Raw arenas may contain open, ill-typed, or unresolved rows.  Kernel validity is
instead attached to the claims the arena exposes: inline sorting and equality
members, the Boolean assumption context, metadata conclusions, and named axiom
capabilities.  Metadata in `assume` remains a premise and is not required to be
established by the arena that records it.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value
/-- Kernel equality for two resolved values.  Kind equality is syntactic;
family and term equality are certificates in the existing HolE kernel. -/
inductive Equal : Value → Value → Prop where
  | kind (kind : Kind) : Equal (.kind kind) (.kind kind)
  | family {kind : Kind}
      {left right : EmptyExpr (.kind kind)}
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) left.toHolE right.toHolE)) :
      Equal (.family kind left) (.family kind right)
  | term {type : EmptyTy} {left right : EmptyTm}
      (conversion : Nonempty (Nucleus.Hol.Ethane.Reference.EqTm
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        Nucleus.HolE.emptyBound left right type)) :
      Equal (.term type left) (.term type right)

/-- Reflexivity is available only after logical well-formedness has been
checked.  This is the first equality rule implemented by the Rust MVP. -/
theorem equal_self {value : Value} (wellFormed : value.WellFormed) :
    Equal value value := by
  cases value with
  | kind value => exact .kind value
  | family kind expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, lowering,
          classificationLowering, kinding⟩
      cases loweredClassification with
      | kind =>
          exact .family ⟨Nucleus.HolE.Named.FamEq.refl lowering⟩
  | term type expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, termLowering,
          classificationLowering, typing⟩
      cases loweredClassification with
      | tm loweredType =>
          have typeLowering :
              type.lowerTy (.nil : TyScope []) = some loweredType := by
            change (do
              let lowered ← type.lowerTy (.nil : TyScope [])
              pure (Nucleus.HolE.Classification.tm lowered)) =
                some (Nucleus.HolE.Classification.tm loweredType)
              at classificationLowering
            cases lowered : type.lowerTy (.nil : TyScope []) <;>
              simp [lowered] at classificationLowering
            simpa [lowered] using classificationLowering
          exact .term ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
            termLowering termLowering typeLowering (.refl (.exact typing))⟩

/-- Kernel equality is symmetric in every value category. -/
theorem Equal.symm {left right : Value} (equality : Equal left right) :
    Equal right left := by
  cases equality with
  | kind kind => exact .kind kind
  | family conversion =>
      rcases conversion with ⟨conversion⟩
      exact .family ⟨conversion.symm⟩
  | term conversion =>
      rcases conversion with ⟨conversion⟩
      exact .term ⟨{
        loweredLeft := conversion.loweredRight
        loweredRight := conversion.loweredLeft
        loweredType := conversion.loweredType
        leftLowering := conversion.rightLowering
        rightLowering := conversion.leftLowering
        typeLowering := conversion.typeLowering
        derivation := conversion.derivation.symm }⟩

theorem WellFormed.family_kinded {kind : Kind}
    {expression : EmptyExpr (.kind kind)}
    (wellFormed : WellFormed (.family kind expression)) :
    ∃ lowered,
      expression.lowerFam (.nil : TyScope []) = some lowered ∧
      Nucleus.HolE.Kinded lowered := by
  rcases wellFormed with
    ⟨lowered, classification, expressionLowering,
      classificationLowering, kinding⟩
  cases classification with
  | kind => exact ⟨lowered, expressionLowering, kinding⟩

/-- A checked term exposes its exact locally nameless type derivation. -/
theorem WellFormed.term_typing {type : EmptyTy} {term : EmptyTm}
    (wellFormed : WellFormed (.term type term)) :
    ∃ loweredTerm loweredType,
      term.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
        some loweredTerm ∧
      type.lowerTy (.nil : TyScope []) = some loweredType ∧
      Nucleus.HolE.HasType Nucleus.HolE.emptyBound loweredTerm loweredType := by
  rcases wellFormed with
    ⟨loweredTerm, classification, termLowering,
      classificationLowering, typing⟩
  cases classification with
  | tm loweredType =>
      have typeLowering : type.lowerTy (.nil : TyScope []) =
          some loweredType := by
        change (do
          let lowered ← type.lowerTy (.nil : TyScope [])
          pure (Nucleus.HolE.Classification.tm lowered)) =
            some (Nucleus.HolE.Classification.tm loweredType)
          at classificationLowering
        cases lowered : type.lowerTy (.nil : TyScope []) <;>
          simp [lowered] at classificationLowering
        simpa [lowered] using classificationLowering
      exact ⟨loweredTerm, loweredType, termLowering, typeLowering, typing⟩

/-- Kernel equality is transitive.  The middle well-formedness premise is
needed only by the underlying family-conversion transitivity rule. -/
theorem Equal.trans {left middle right : Value}
    (leftMiddle : Equal left middle) (middleWellFormed : middle.WellFormed)
    (middleRight : Equal middle right) : Equal left right := by
  cases leftMiddle with
  | kind kind =>
      cases middleRight
      exact .kind kind
  | family leftConversion =>
      rename_i kind leftFamily middleFamily
      cases middleRight with
      | family rightConversion =>
        rcases leftConversion with ⟨leftConversion⟩
        rcases rightConversion with ⟨rightConversion⟩
        rcases WellFormed.family_kinded middleWellFormed with
          ⟨loweredMiddle, middleLowering, middleKinded⟩
        change Nucleus.HolE.Named.lowerFam (.nil : TyScope [])
          middleFamily.toHolE = some loweredMiddle at middleLowering
        rw [leftConversion.rightLowering] at middleLowering
        have same := Option.some.inj middleLowering
        subst loweredMiddle
        exact .family ⟨leftConversion.trans middleKinded rightConversion⟩
  | term leftConversion =>
      cases middleRight with
      | term rightConversion =>
        rcases leftConversion with ⟨leftConversion⟩
        rcases rightConversion with ⟨rightConversion⟩
        have rightMiddleLowering := rightConversion.leftLowering
        rw [leftConversion.rightLowering] at rightMiddleLowering
        have middleSame := Option.some.inj rightMiddleLowering
        have rightTypeLowering := rightConversion.typeLowering
        rw [leftConversion.typeLowering] at rightTypeLowering
        have typeSame := Option.some.inj rightTypeLowering
        have rightDerivation : Nucleus.HolE.EqTm Nucleus.HolE.emptyBound
            leftConversion.loweredRight rightConversion.loweredRight
            leftConversion.loweredType := by
          simpa only [middleSame, typeSame] using rightConversion.derivation
        exact .term ⟨{
          loweredLeft := leftConversion.loweredLeft
          loweredRight := rightConversion.loweredRight
          loweredType := leftConversion.loweredType
          leftLowering := leftConversion.leftLowering
          rightLowering := rightConversion.rightLowering
          typeLowering := leftConversion.typeLowering
          derivation := leftConversion.derivation.trans rightDerivation }⟩

/-- Application is congruent for checked term equality. -/
theorem Equal.app {domain codomain : EmptyTy}
    {leftFunction rightFunction leftArgument rightArgument : EmptyTm}
    (functionEquality : Equal
      (.term (.arr domain codomain) leftFunction)
      (.term (.arr domain codomain) rightFunction))
    (argumentEquality : Equal
      (.term domain leftArgument) (.term domain rightArgument))
    (leftFunctionWellFormed : WellFormed
      (.term (.arr domain codomain) leftFunction))
    (rightFunctionWellFormed : WellFormed
      (.term (.arr domain codomain) rightFunction))
    (leftArgumentWellFormed : WellFormed (.term domain leftArgument))
    (rightArgumentWellFormed : WellFormed (.term domain rightArgument)) :
    Equal (.term codomain (.app leftFunction leftArgument))
      (.term codomain (.app rightFunction rightArgument)) := by
  cases functionEquality with
  | term functionConversion =>
    cases argumentEquality with
    | term argumentConversion =>
      rcases functionConversion with ⟨functionConversion⟩
      rcases argumentConversion with ⟨argumentConversion⟩
      rcases leftFunctionWellFormed.term_typing with
        ⟨loweredLeftFunction, loweredLeftFunctionType,
          leftFunctionLowering, leftFunctionTypeLowering,
          leftFunctionTyping⟩
      rcases rightFunctionWellFormed.term_typing with
        ⟨loweredRightFunction, loweredRightFunctionType,
          rightFunctionLowering, rightFunctionTypeLowering,
          rightFunctionTyping⟩
      rcases leftArgumentWellFormed.term_typing with
        ⟨loweredLeftArgument, loweredLeftArgumentType,
          leftArgumentLowering, leftArgumentTypeLowering,
          leftArgumentTyping⟩
      rcases rightArgumentWellFormed.term_typing with
        ⟨loweredRightArgument, loweredRightArgumentType,
          rightArgumentLowering, rightArgumentTypeLowering,
          rightArgumentTyping⟩
      rw [functionConversion.leftLowering] at leftFunctionLowering
      rw [functionConversion.rightLowering] at rightFunctionLowering
      rw [argumentConversion.leftLowering] at leftArgumentLowering
      rw [argumentConversion.rightLowering] at rightArgumentLowering
      have leftFunctionSame := Option.some.inj leftFunctionLowering
      have rightFunctionSame := Option.some.inj rightFunctionLowering
      have leftArgumentSame := Option.some.inj leftArgumentLowering
      have rightArgumentSame := Option.some.inj rightArgumentLowering
      subst loweredLeftFunction
      subst loweredRightFunction
      subst loweredLeftArgument
      subst loweredRightArgument
      rw [functionConversion.typeLowering] at leftFunctionTypeLowering
      rw [functionConversion.typeLowering] at rightFunctionTypeLowering
      rw [argumentConversion.typeLowering] at leftArgumentTypeLowering
      rw [argumentConversion.typeLowering] at rightArgumentTypeLowering
      have leftFunctionTypeSame := Option.some.inj leftFunctionTypeLowering
      have rightFunctionTypeSame := Option.some.inj rightFunctionTypeLowering
      have leftArgumentTypeSame := Option.some.inj leftArgumentTypeLowering
      have rightArgumentTypeSame := Option.some.inj rightArgumentTypeLowering
      subst loweredLeftFunctionType
      subst loweredRightFunctionType
      subst loweredLeftArgumentType
      subst loweredRightArgumentType
      have functionTypeLowering := functionConversion.typeLowering
      have domainLowering := argumentConversion.typeLowering
      change Nucleus.HolE.Named.lowerFam (.nil : TyScope [])
        ((domain.toHolE).arr codomain.toHolE) =
          some functionConversion.loweredType at functionTypeLowering
      change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) domain.toHolE =
        some argumentConversion.loweredType at domainLowering
      simp only [Nucleus.HolE.Named.lowerFam, domainLowering] at functionTypeLowering
      cases codomainLowering : Nucleus.HolE.Named.lowerFam
          (.nil : TyScope []) codomain.toHolE with
      | none =>
          simp [codomainLowering] at functionTypeLowering
      | some loweredCodomain =>
          have functionTypeShape :
              Nucleus.HolE.Expr.arr argumentConversion.loweredType
                loweredCodomain = functionConversion.loweredType := by
            have equality :
                some (Nucleus.HolE.Expr.arr argumentConversion.loweredType
                  loweredCodomain) = some functionConversion.loweredType := by
              simpa [codomainLowering] using functionTypeLowering
            exact Option.some.inj equality
          have leftFunctionTyping' : Nucleus.HolE.HasType Nucleus.HolE.emptyBound
              functionConversion.loweredLeft
              (.arr argumentConversion.loweredType loweredCodomain) := by
            simpa only [functionTypeShape] using leftFunctionTyping
          have rightFunctionTyping' : Nucleus.HolE.HasType Nucleus.HolE.emptyBound
              functionConversion.loweredRight
              (.arr argumentConversion.loweredType loweredCodomain) := by
            simpa only [functionTypeShape] using rightFunctionTyping
          have functionDerivation : Nucleus.HolE.EqTm Nucleus.HolE.emptyBound
              functionConversion.loweredLeft functionConversion.loweredRight
              (.arr argumentConversion.loweredType loweredCodomain) := by
            simpa only [functionTypeShape] using functionConversion.derivation
          have leftExpected :
              (Nucleus.Hol.Ethane.Expr.app leftFunction leftArgument).lowerTm
                (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
              some (.app functionConversion.loweredLeft
                argumentConversion.loweredLeft) := by
            have functionLowering := functionConversion.leftLowering
            have argumentLowering := argumentConversion.leftLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0) leftFunction.toHolE =
                some functionConversion.loweredLeft at functionLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0) leftArgument.toHolE =
                some argumentConversion.loweredLeft at argumentLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0)
              (.app leftFunction.toHolE leftArgument.toHolE) = _
            simp only [Nucleus.HolE.Named.lowerTm]
            rw [functionLowering, argumentLowering]
            rfl
          have rightExpected :
              (Nucleus.Hol.Ethane.Expr.app rightFunction rightArgument).lowerTm
                (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
              some (.app functionConversion.loweredRight
                argumentConversion.loweredRight) := by
            have functionLowering := functionConversion.rightLowering
            have argumentLowering := argumentConversion.rightLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0) rightFunction.toHolE =
                some functionConversion.loweredRight at functionLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0) rightArgument.toHolE =
                some argumentConversion.loweredRight at argumentLowering
            change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
              (.nil : TmScope ArenaSig 0)
              (.app rightFunction.toHolE rightArgument.toHolE) = _
            simp only [Nucleus.HolE.Named.lowerTm]
            rw [functionLowering, argumentLowering]
            rfl
          exact .term ⟨{
            loweredLeft := .app functionConversion.loweredLeft
              argumentConversion.loweredLeft
            loweredRight := .app functionConversion.loweredRight
              argumentConversion.loweredRight
            loweredType := loweredCodomain
            leftLowering := leftExpected
            rightLowering := rightExpected
            typeLowering := codomainLowering
            derivation := .app
              (.app leftFunctionTyping' leftArgumentTyping)
              (.app rightFunctionTyping' rightArgumentTyping)
              leftFunctionTyping' leftArgumentTyping
              rightFunctionTyping' rightArgumentTyping
              functionDerivation argumentConversion.derivation }⟩

/-- A well-typed root beta step is an Ethane kernel equality. -/
theorem equal_beta {type : EmptyTy} {source target : EmptyTm}
    (wellFormed : WellFormed (.term type source))
    (step : Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term type source) (.term type target) := by
  rcases wellFormed with
    ⟨loweredSource, loweredClassification, sourceLowering,
      classificationLowering, sourceTyping⟩
  cases loweredClassification with
  | tm loweredType =>
      have namedTyping : Nucleus.HolE.Named.HasType
          (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
          Nucleus.HolE.emptyBound source.toHolE type.toHolE := by
        exact ⟨loweredSource, .tm loweredType, sourceLowering,
          classificationLowering, sourceTyping⟩
      obtain ⟨conversion⟩ := step.toTmConv
        (fun index => Fin.elim0 index) namedTyping
      exact .term ⟨{
        loweredLeft := conversion.loweredLeft
        loweredRight := conversion.loweredRight
        loweredType := conversion.loweredType
        leftLowering := conversion.leftLowering
        rightLowering := conversion.rightLowering
        typeLowering := conversion.typeLowering
        derivation := conversion.derivation }⟩

/-- The exact identity-redex shape recognized by the first Rust beta checker. -/
def identityBetaStep (name : Nat) (domain : EmptyTy) (argument : EmptyTm)
    {loweredDomain : Nucleus.HolE.Ty ArenaSig []}
    {loweredArgument : Nucleus.HolE.Tm ArenaSig [] 0}
    (domainLowering : domain.lowerTy (.nil : TyScope []) = some loweredDomain)
    (argumentLowering : argument.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) = some loweredArgument) :
    Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      (Nucleus.Hol.Ethane.Expr.app
        (Nucleus.Hol.Ethane.Expr.lam name domain
          (Nucleus.Hol.Ethane.Expr.tmFv name domain)) argument).toHolE
      argument.toHolE where
  domain := loweredDomain
  body := .bv 0
  argument := loweredArgument
  sourceLowering := by
    change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) domain.toHolE =
      some loweredDomain at domainLowering
    change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) argument.toHolE =
        some loweredArgument at argumentLowering
    simp [Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lowerTm,
      Nucleus.HolE.Named.lookupTm, domainLowering, argumentLowering]
  targetLowering := by
    change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) argument.toHolE =
        some loweredArgument at argumentLowering
    simpa [Nucleus.HolE.openBound, Nucleus.HolE.instantiate] using argumentLowering

/-- Build the named root-beta certificate from the four locally nameless
lowerings computed by the executable checker.  Comparing the opened body
rather than substituting names makes the check capture avoiding and accepts
alpha-equivalent targets. -/
def rootBetaStep (name : Nat) (domain : EmptyTy) (body argument target : EmptyTm)
    {loweredDomain : Nucleus.HolE.Ty ArenaSig []}
    {loweredBody : Nucleus.HolE.Tm ArenaSig [] 1}
    {loweredArgument : Nucleus.HolE.Tm ArenaSig [] 0}
    (domainLowering : domain.lowerTy (.nil : TyScope []) = some loweredDomain)
    (bodyLowering : body.lowerTm (.nil : TyScope [])
      (.cons ⟨name, domain.toHolE⟩ (.nil : TmScope ArenaSig 0)) =
        some loweredBody)
    (argumentLowering : argument.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) = some loweredArgument)
    (targetLowering : target.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) =
        some (Nucleus.HolE.openBound loweredBody loweredArgument)) :
    Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      (Nucleus.Hol.Ethane.Expr.app
        (Nucleus.Hol.Ethane.Expr.lam name domain body) argument).toHolE
      target.toHolE where
  domain := loweredDomain
  body := loweredBody
  argument := loweredArgument
  sourceLowering := by
    change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) domain.toHolE =
      some loweredDomain at domainLowering
    change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
      (.cons ⟨name, domain.toHolE⟩ (.nil : TmScope ArenaSig 0)) body.toHolE =
        some loweredBody at bodyLowering
    change Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) argument.toHolE =
        some loweredArgument at argumentLowering
    simp [Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lowerTm,
      domainLowering, bodyLowering, argumentLowering]
  targetLowering := targetLowering

end Value

/-- Meaning of the optional equality member on one row. -/
def EqualityClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ leftValue rightValue,
        Resolves resolve arena reference leftValue ∧
        Resolves resolve arena right rightValue ∧
        Value.Equal leftValue rightValue

/-- The executable MVP equality check: both references resolve to the same
well-formed value.  More conversion rules extend this relation without
changing `EqualityClaim`. -/
def ReflexiveEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ value,
        Resolves resolve arena reference value ∧
        Resolves resolve arena right value ∧
        value.WellFormed

theorem reflexiveEqualityClaim_sound
    (claim : ReflexiveEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold ReflexiveEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨value, left, right, wellFormed⟩
  exact ⟨value, value, left, right, Value.equal_self wellFormed⟩

/-- A checked root beta equality member. -/
def BetaEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ type source target,
        Resolves resolve arena reference (.term type source) ∧
        Resolves resolve arena right (.term type target) ∧
        Value.WellFormed (.term type source) ∧
        Nonempty (Nucleus.HolE.Named.TmBeta
          (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
          source.toHolE target.toHolE)

theorem betaEqualityClaim_sound
    (claim : BetaEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold BetaEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, source, target, sourceResolves, targetResolves,
    wellFormed, ⟨step⟩⟩
  exact ⟨.term type source, .term type target, sourceResolves, targetResolves,
    Value.equal_beta wellFormed step⟩

/-- The identity-redex specialization used by focused examples. -/
def IdentityBetaEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ type domain name argument loweredDomain loweredArgument,
        Resolves resolve arena reference
          (.term type (.app (.lam name domain (.tmFv name domain)) argument)) ∧
        Resolves resolve arena right (.term type argument) ∧
        Value.WellFormed
          (.term type (.app (.lam name domain (.tmFv name domain)) argument)) ∧
        domain.lowerTy (.nil : TyScope []) = some loweredDomain ∧
        argument.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some loweredArgument

theorem identityBetaEqualityClaim_sound
    (claim : IdentityBetaEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold IdentityBetaEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, domain, name, argument, loweredDomain,
    loweredArgument, sourceResolves, targetResolves, wellFormed,
    domainLowering, argumentLowering⟩
  let source : EmptyTm :=
    Nucleus.Hol.Ethane.Expr.app
      (Nucleus.Hol.Ethane.Expr.lam name domain
        (Nucleus.Hol.Ethane.Expr.tmFv name domain)) argument
  exact ⟨.term type source, .term type argument, sourceResolves, targetResolves,
    Value.equal_beta wellFormed
      (Value.identityBetaStep name domain argument domainLowering argumentLowering)⟩

/-- General root beta, implemented by lowering the named redex and target and
checking that the target is exactly the locally nameless opened body. -/
def RootBetaEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ (type domain : EmptyTy) (name : Nat)
        (body argument target : EmptyTm)
        (loweredDomain : Nucleus.HolE.Ty ArenaSig [])
        (loweredBody : Nucleus.HolE.Tm ArenaSig [] 1)
        (loweredArgument : Nucleus.HolE.Tm ArenaSig [] 0),
        Resolves resolve arena reference
          (.term type (.app (.lam name domain body) argument)) ∧
        Resolves resolve arena right (.term type target) ∧
        Value.WellFormed
          (.term type (.app (.lam name domain body) argument)) ∧
        domain.lowerTy (.nil : TyScope []) = some loweredDomain ∧
        body.lowerTm (.nil : TyScope [])
          (.cons ⟨name, domain.toHolE⟩ (.nil : TmScope ArenaSig 0)) =
            some loweredBody ∧
        argument.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some loweredArgument ∧
        target.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some (Nucleus.HolE.openBound loweredBody loweredArgument)

theorem rootBetaEqualityClaim_sound
    (claim : RootBetaEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold RootBetaEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, domain, name, body, argument, target,
    loweredDomain, loweredBody, loweredArgument,
    sourceResolves, targetResolves, wellFormed,
    domainLowering, bodyLowering, argumentLowering, targetLowering⟩
  exact ⟨.term type (.app (.lam name domain body) argument),
    .term type target, sourceResolves, targetResolves,
    Value.equal_beta wellFormed
      (Value.rootBetaStep name domain body argument target
        domainLowering bodyLowering argumentLowering targetLowering)⟩

/-- The equality alternatives implemented by the initial Rust checker. -/
def ExecutableEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  ReflexiveEqualityClaim resolve arena reference ∨
  RootBetaEqualityClaim resolve arena reference

theorem executableEqualityClaim_sound
    (claim : ExecutableEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  cases claim with
  | inl reflexive => exact reflexiveEqualityClaim_sound reflexive
  | inr beta => exact rootBetaEqualityClaim_sound beta

/-- Meaning of the optional sorting member on one row. -/
def SortingMemberClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.sort? reference with
  | none => True
  | some _ => SortingClaim resolve arena reference

/-- A context reference denotes a well-typed Boolean term. -/
def ContextClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  ∃ expression,
    Resolves resolve arena reference (.term .boolTy expression) ∧
    Value.WellFormed (.term .boolTy expression)

/-- Capabilities understood by the initial empty-signature kernel. -/
def AllowedAxiom : String → Prop
  | "ax.inf" => True
  | _ => False

/-- Local validity, excluding the recursively trusted metadata conclusions. -/
structure Arena.LocallyValid (resolve : Resolver) (arena : Arena) : Prop where
  structural : arena.StructurallyValid
  sorts : ∀ reference, SortingMemberClaim resolve arena reference
  equalities : ∀ reference, EqualityClaim resolve arena reference
  context : ∀ reference ∈ arena.ctx, ContextClaim resolve arena reference
  axioms : ∀ name ∈ arena.axs, AllowedAxiom name

/-- The local checks implemented by the initial Rust validator. -/
structure Arena.ExecutableLocallyValid (resolve : Resolver)
    (arena : Arena) : Prop where
  structural : arena.StructurallyValid
  sorts : ∀ reference, SortingMemberClaim resolve arena reference
  equalities : ∀ reference, ExecutableEqualityClaim resolve arena reference
  context : ∀ reference ∈ arena.ctx, ContextClaim resolve arena reference
  axioms : ∀ name ∈ arena.axs, AllowedAxiom name

theorem Arena.ExecutableLocallyValid.sound
    (valid : Arena.ExecutableLocallyValid resolve arena) :
    Arena.LocallyValid resolve arena where
  structural := valid.structural
  sorts := valid.sorts
  equalities reference := executableEqualityClaim_sound (valid.equalities reference)
  context := valid.context
  axioms := valid.axioms

/-- Metadata checked relative to a caller-supplied class of trusted arenas. -/
def KernelMetaClaim (trusted : Arena → Prop) (resolve : Resolver)
    (arena : Arena) : Meta → Prop
  | .wf source foreignRef sort =>
      MetaClaim resolve arena (.wf source foreignRef sort)
  | .valid source =>
      ∃ entry imported,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        trusted imported

theorem KernelMetaClaim.mono
    {trusted stronger : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {record : Meta}
    (implication : ∀ candidate, trusted candidate → stronger candidate)
    (claim : KernelMetaClaim trusted resolve arena record) :
    KernelMetaClaim stronger resolve arena record := by
  cases record with
  | wf source foreignRef sort => exact claim
  | valid source =>
      rcases claim with ⟨entry, imported, lookup, resolved, valid⟩
      exact ⟨entry, imported, lookup, resolved, implication imported valid⟩

/-- Kernel validity at a finite import-trust depth.  Each `meta.valid` edge
strictly decreases the depth, so cyclic trust requires an independent finite
witness rather than being accepted coinductively. -/
def Arena.KernelValidAt : Nat → Resolver → Arena → Prop
  | 0, _, _ => False
  | depth + 1, resolve, arena =>
      arena.LocallyValid resolve ∧
      ∀ record ∈ arena.assert,
        KernelMetaClaim (Arena.KernelValidAt depth resolve) resolve arena record

/-- The complete subset accepted by the initial Rust validator, including its
finite recursive validation of trusted imports. -/
def Arena.ExecutableKernelValidAt : Nat → Resolver → Arena → Prop
  | 0, _, _ => False
  | depth + 1, resolve, arena =>
      arena.ExecutableLocallyValid resolve ∧
      ∀ record ∈ arena.assert,
        KernelMetaClaim (Arena.ExecutableKernelValidAt depth resolve)
          resolve arena record

theorem Arena.executableKernelValidAt_sound :
    ∀ (depth) (resolve : Resolver) (arena : Arena),
      Arena.ExecutableKernelValidAt depth resolve arena →
      Arena.KernelValidAt depth resolve arena
  | 0, _, _, valid => by contradiction
  | depth + 1, resolve, arena, valid => by
      exact ⟨valid.1.sound, fun record member =>
        KernelMetaClaim.mono
          (fun imported importedValid =>
            Arena.executableKernelValidAt_sound depth resolve imported importedValid)
          (valid.2 record member)⟩

/-- A raw arena is a valid checked-kernel state relative to a resolver.

The resolver is a parameter because successful CAS resolution is persistent
but absence is retryable.  No premise in `assume` is silently promoted to an
assertion. -/
def Arena.KernelValid (resolve : Resolver) (arena : Arena) : Prop :=
  ∃ depth, arena.KernelValidAt depth resolve

/-- Passing the executable validator is sufficient for abstract kernel
validity. -/
theorem Arena.executableKernelValid_sound
    {resolve : Resolver} {arena : Arena}
    (valid : ∃ depth, Arena.ExecutableKernelValidAt depth resolve arena) :
    Arena.KernelValid resolve arena := by
  rcases valid with ⟨depth, valid⟩
  exact ⟨depth, Arena.executableKernelValidAt_sound depth resolve arena valid⟩

/-- An arena paired with the proof that its exposed claims were checked. -/
structure Kernel (resolve : Resolver) where
  arena : Arena
  valid : arena.KernelValid resolve

namespace Arena

@[simp] theorem empty_row? (reference : Ref) : empty.row? reference = none := by
  simp [empty, row?, defs]

@[simp] theorem empty_eq? (reference : Ref) : empty.eq? reference = none := by
  simp [eq?]

@[simp] theorem empty_sort? (reference : Ref) : empty.sort? reference = none := by
  simp [sort?]

/-- The empty arena is a checked kernel for every resolver. -/
theorem empty_kernelValid (resolve : Resolver) : empty.KernelValid resolve := by
  refine ⟨1, ?_⟩
  exact ⟨{
    structural := by simp [StructurallyValid, empty, defs, RowsValid]
    sorts := by simp [SortingMemberClaim]
    equalities := by simp [EqualityClaim]
    context := by simp [empty, ctx]
    axioms := by simp [empty, axs] }, by simp [empty, assert]⟩

end Arena

namespace Kernel

/-- The empty checked kernel. -/
def empty (resolve : Resolver) : Kernel resolve :=
  ⟨Arena.empty, Arena.empty_kernelValid resolve⟩

/-- Any asserted inline equality exposes an actual kernel equality
certificate, never merely a syntactic classification. -/
theorem equality_sound (kernel : Kernel resolve) {reference right : Ref}
    (member : kernel.arena.eq? reference = some right) :
    ∃ leftValue rightValue,
      Resolves resolve kernel.arena reference leftValue ∧
      Resolves resolve kernel.arena right rightValue ∧
      Value.Equal leftValue rightValue := by
  rcases kernel.valid with ⟨depth, valid⟩
  cases depth with
  | zero => contradiction
  | succ depth =>
  have claim := valid.1.equalities reference
  unfold EqualityClaim at claim
  rw [member] at claim
  exact claim

/-- Every context entry is a genuinely well-typed Boolean term. -/
theorem context_sound (kernel : Kernel resolve) {reference : Ref}
    (member : reference ∈ kernel.arena.ctx) :
    ∃ expression,
      Resolves resolve kernel.arena reference (.term .boolTy expression) ∧
      Value.WellFormed (.term .boolTy expression) := by
  rcases kernel.valid with ⟨depth, valid⟩
  cases depth with
  | zero => contradiction
  | succ depth => exact valid.1.context reference member

/-- Assertions are checked conclusions; assumptions are intentionally absent
from this theorem. -/
theorem conclusion_sound (kernel : Kernel resolve) {record : Meta}
    (member : record ∈ kernel.arena.assert) :
    ∃ depth, KernelMetaClaim (Arena.KernelValidAt depth resolve)
      resolve kernel.arena record := by
  rcases kernel.valid with ⟨depth, valid⟩
  cases depth with
  | zero => contradiction
  | succ depth => exact ⟨depth, valid.2 record member⟩

/-- An asserted `meta.wf` has the original sorting meaning. -/
theorem wf_conclusion_sound (kernel : Kernel resolve)
    {source : ImportId} {foreignRef sort : Ref}
    (member : Meta.wf source foreignRef sort ∈ kernel.arena.assert) :
    MetaClaim resolve kernel.arena (.wf source foreignRef sort) := by
  rcases kernel.conclusion_sound member with ⟨depth, claim⟩
  exact claim

/-- An asserted `meta.valid` carries a recursively checked imported kernel,
not merely a promise that its raw rows happened to resolve. -/
theorem valid_conclusion_sound (kernel : Kernel resolve)
    {source : ImportId} (member : Meta.valid source ∈ kernel.arena.assert) :
    ∃ entry imported,
      kernel.arena.import? source = some entry ∧
      resolveImport? resolve entry = some imported ∧
      imported.KernelValid resolve := by
  rcases kernel.conclusion_sound member with
    ⟨depth, entry, imported, lookup, resolved, valid⟩
  exact ⟨entry, imported, lookup, resolved, depth, valid⟩

/-- An opaque checked equality handle over two arena references. -/
structure Equality (kernel : Kernel resolve) (left right : Ref) where
  leftValue : Value
  rightValue : Value
  leftResolves : Resolves resolve kernel.arena left leftValue
  rightResolves : Resolves resolve kernel.arena right rightValue
  equality : Value.Equal leftValue rightValue

/-- Recover an equality handle from a checked inline member. -/
theorem Equality.ofMember (kernel : Kernel resolve) {left right : Ref}
    (member : kernel.arena.eq? left = some right) :
    Nonempty (Equality kernel left right) := by
  rcases kernel.equality_sound member with
    ⟨leftValue, rightValue, leftResolves, rightResolves, equality⟩
  exact ⟨⟨leftValue, rightValue, leftResolves, rightResolves, equality⟩⟩

/-- Checked equality handles are symmetric without mutating the arena. -/
def Equality.symm {kernel : Kernel resolve} {left right : Ref}
    (equality : Equality kernel left right) : Equality kernel right left :=
  ⟨equality.rightValue, equality.leftValue, equality.rightResolves,
    equality.leftResolves, equality.equality.symm⟩

/-- Checked equality handles compose when their independently resolved middle
values agree.  The executable API checks this equality before returning. -/
def Equality.trans {kernel : Kernel resolve} {left middle right : Ref}
    (leftMiddle : Equality kernel left middle)
    (middleRight : Equality kernel middle right)
    (sameMiddle : leftMiddle.rightValue = middleRight.leftValue)
    (middleWellFormed : leftMiddle.rightValue.WellFormed) :
    Equality kernel left right := by
  have transported : Value.Equal leftMiddle.rightValue middleRight.rightValue :=
    sameMiddle ▸ middleRight.equality
  exact ⟨leftMiddle.leftValue, middleRight.rightValue,
    leftMiddle.leftResolves, middleRight.rightResolves,
    leftMiddle.equality.trans middleWellFormed transported⟩

/-- Application congruence for checked equality handles.  The endpoint
equalities state the executable check that the two application rows contain
the handles' function and argument references. -/
def Equality.app {kernel : Kernel resolve}
    {leftFunctionRef rightFunctionRef leftArgumentRef rightArgumentRef : Ref}
    {leftApplicationRef rightApplicationRef : Ref}
    (functionEquality : Equality kernel leftFunctionRef rightFunctionRef)
    (argumentEquality : Equality kernel leftArgumentRef rightArgumentRef)
    {domain codomain : EmptyTy}
    {leftFunction rightFunction leftArgument rightArgument : EmptyTm}
    (leftFunctionValue : functionEquality.leftValue =
      .term (.arr domain codomain) leftFunction)
    (rightFunctionValue : functionEquality.rightValue =
      .term (.arr domain codomain) rightFunction)
    (leftArgumentValue : argumentEquality.leftValue =
      .term domain leftArgument)
    (rightArgumentValue : argumentEquality.rightValue =
      .term domain rightArgument)
    (leftApplicationResolves : Resolves resolve kernel.arena
      leftApplicationRef (.term codomain (.app leftFunction leftArgument)))
    (rightApplicationResolves : Resolves resolve kernel.arena
      rightApplicationRef (.term codomain (.app rightFunction rightArgument)))
    (leftFunctionWellFormed : Value.WellFormed
      (.term (.arr domain codomain) leftFunction))
    (rightFunctionWellFormed : Value.WellFormed
      (.term (.arr domain codomain) rightFunction))
    (leftArgumentWellFormed : Value.WellFormed (.term domain leftArgument))
    (rightArgumentWellFormed : Value.WellFormed (.term domain rightArgument)) :
    Equality kernel leftApplicationRef rightApplicationRef := by
  have functionValueEquality := functionEquality.equality
  rw [leftFunctionValue, rightFunctionValue] at functionValueEquality
  have argumentValueEquality := argumentEquality.equality
  rw [leftArgumentValue, rightArgumentValue] at argumentValueEquality
  exact ⟨.term codomain (.app leftFunction leftArgument),
    .term codomain (.app rightFunction rightArgument),
    leftApplicationResolves, rightApplicationResolves,
    functionValueEquality.app argumentValueEquality
      leftFunctionWellFormed rightFunctionWellFormed
      leftArgumentWellFormed rightArgumentWellFormed⟩

end Kernel

end Nucleus.Hol.Ethane.OneBased
