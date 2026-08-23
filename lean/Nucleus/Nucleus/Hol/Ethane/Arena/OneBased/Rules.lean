import Nucleus.Hol.Ethane.Arena.OneBased.Kernel
import Nucleus.Hol.Ethane.Conversion
import Nucleus.HolE.Normalization.Reduction

/-!
# Sound equality micro-rules for one-based Ethane kernels

The Rust kernel checks alpha, root type beta, root term beta, and root term
eta directly over arena rows, then joins the endpoints' union-find classes.
This file gives the corresponding proof-theoretic boundary.  It deliberately
contains no beta or eta congruence beneath `Model`.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value

private theorem termTyping {type : EmptyTy} {term : EmptyTm}
    (wellFormed : WellFormed (.term type term)) :
    Nucleus.HolE.Named.HasTypeConv (.nil : TyScope [])
      (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound
      term.toHolE type.toHolE :=
  wellFormed

/-- Direct named alpha comparison is a sound family equality. No existing
union-find equality is used to establish the comparison. -/
theorem equal_family_alpha {kind : Kind}
    {left right : EmptyExpr (.kind kind)}
    (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
    Equal (.family kind left) (.family kind right) := by
  rcases equivalent with ⟨lowered, leftLowering, rightLowering⟩
  exact .family ⟨{
    loweredLeft := lowered
    loweredRight := lowered
    leftLowering := leftLowering
    rightLowering := rightLowering
    derivation := .refl }⟩

/-- Direct named alpha comparison is a sound term equality. -/
theorem equal_term_alpha {type : EmptyTy} {left right : EmptyTm}
    (leftWellFormed : WellFormed (.term type left))
    (rightWellFormed : WellFormed (.term type right))
    (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
    Equal (.term type left) (.term type right) := by
  rcases equivalent with ⟨alphaLowered, leftAlpha, rightAlpha⟩
  rcases termTyping leftWellFormed with
    ⟨typedLowered, loweredType, leftTyping, typeLowering, typing⟩
  change Nucleus.Hol.Ethane.Expr.lower (.nil : TyScope [])
    (.nil : TmScope ArenaSig 0) left = some typedLowered at leftTyping
  rw [leftAlpha] at leftTyping
  have same := Option.some.inj leftTyping
  subst typedLowered
  exact .term leftWellFormed rightWellFormed
    ⟨Nucleus.HolE.Named.FamEq.refl typeLowering⟩
    ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
      leftAlpha rightAlpha typeLowering (.refl typing)⟩

/-- A well-kinded root family-beta check is a sound family equality. -/
theorem equal_family_beta {kind : Kind}
    {source target : EmptyExpr (.kind kind)}
    (step : Nucleus.HolE.Named.FamBeta
      (.nil : TyScope []) source.toHolE target.toHolE)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    Equal (.family kind source) (.family kind target) :=
  .family ⟨step.toFamEq bodyKinded argumentKinded⟩

private theorem equal_term_of_conversion {type : EmptyTy} {left right : EmptyTm}
    (conversion : Nucleus.HolE.Named.EqTm
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      Nucleus.HolE.emptyBound left.toHolE right.toHolE type.toHolE) :
    Equal (.term type left) (.term type right) :=
  .term ⟨conversion.loweredLeft, conversion.loweredType,
      conversion.leftLowering, conversion.typeLowering,
      conversion.derivation.leftTyping⟩
    ⟨conversion.loweredRight, conversion.loweredType,
      conversion.rightLowering, conversion.typeLowering,
      conversion.derivation.rightTyping⟩
    ⟨Nucleus.HolE.Named.FamEq.refl conversion.typeLowering⟩ ⟨{
    loweredLeft := conversion.loweredLeft
    loweredRight := conversion.loweredRight
    loweredType := conversion.loweredType
    leftLowering := conversion.leftLowering
    rightLowering := conversion.rightLowering
    typeLowering := conversion.typeLowering
    derivation := conversion.derivation }⟩

/-- A well-typed root term-beta check is a sound term equality. -/
theorem equal_term_beta {sourceType targetType : EmptyTy}
    {source target : EmptyTm}
    (sourceWellFormed : WellFormed (.term sourceType source))
    (targetWellFormed : WellFormed (.term targetType target))
    (classifierConversion : Nonempty (Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) sourceType.toHolE targetType.toHolE))
    (step : Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term sourceType source) (.term targetType target) := by
  have originalSource := sourceWellFormed
  rcases sourceWellFormed with
    ⟨loweredSource, loweredType, sourceLowering, typeLowering, typing⟩
  rw [step.sourceLowering] at sourceLowering
  have sourceSame := Option.some.inj sourceLowering
  subst loweredSource
  let reduction : Nucleus.HolE.Reduction.Beta
      (.app (.lam step.domain step.body) step.argument)
      (Nucleus.HolE.openBound step.body step.argument) :=
    .root step.domain step.body step.argument
  obtain ⟨derivation⟩ := reduction.eqTmDefEq_nonempty
    (fun index => Fin.elim0 index) typing
  exact .term originalSource targetWellFormed classifierConversion ⟨{
    loweredLeft := .app (.lam step.domain step.body) step.argument
    loweredRight := Nucleus.HolE.openBound step.body step.argument
    loweredType := loweredType
    leftLowering := step.sourceLowering
    rightLowering := step.targetLowering
    typeLowering := typeLowering
    derivation := derivation }⟩

/-- A well-typed root term-eta check is a sound term equality. -/
theorem equal_term_eta {sourceType targetType : EmptyTy}
    {source target : EmptyTm}
    (sourceWellFormed : WellFormed (.term sourceType source))
    (targetWellFormed : WellFormed (.term targetType target))
    (classifierConversion : Nonempty (Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) sourceType.toHolE targetType.toHolE))
    (step : Nucleus.HolE.Named.TmEta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term sourceType source) (.term targetType target) := by
  have originalSource := sourceWellFormed
  rcases sourceWellFormed with
    ⟨loweredSource, loweredType, sourceLowering, typeLowering, typing⟩
  rw [step.sourceLowering] at sourceLowering
  have sourceSame := Option.some.inj sourceLowering
  subst loweredSource
  let reduction : Nucleus.HolE.Reduction.Eta
      (.lam step.domain (.app (Nucleus.HolE.weaken step.function) (.bv 0)))
      step.function := .root step.freshName step.fresh
  obtain ⟨derivation⟩ := reduction.eqTmDefEq_nonempty
    (fun index => Fin.elim0 index) typing
  exact .term originalSource targetWellFormed classifierConversion ⟨{
    loweredLeft := .lam step.domain
      (.app (Nucleus.HolE.weaken step.function) (.bv 0))
    loweredRight := step.function
    loweredType := loweredType
    leftLowering := step.sourceLowering
    rightLowering := step.targetLowering
    typeLowering := typeLowering
    derivation := derivation }⟩

end Value

/-- The Ethane reduction relation has no family-beta step rooted at a model.
This is the Lean counterpart of Rust `Kernel::ty_beta` rejecting `ty.model`
before it inspects any predicate row. -/
theorem no_beta_from_model (name : Nat) (predicate : EmptyTm) (target : EmptyTy) :
    IsEmpty (Nucleus.Hol.Ethane.Reduction.FamBeta
      (.nil : TyScope []) (.model name predicate) target) :=
  Nucleus.Hol.Ethane.Reduction.noBetaFromModel name predicate target

end Nucleus.Hol.Ethane.OneBased
